/**
 * @file transferslot.cpp
 * @brief Class for active transfer
 *
 * (c) 2013-2014 by Mega Limited, Auckland, New Zealand
 *
 * This file is part of the MEGA SDK - Client Access Engine.
 *
 * Applications using the MEGA API must present a valid application key
 * and comply with the the rules set forth in the Terms of Service.
 *
 * The MEGA SDK is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * @copyright Simplified (2-clause) BSD License.
 *
 * You should have received a copy of the license along with this
 * program.
 */

#include "mega/transferslot.h"
#include "mega/node.h"
#include "mega/transfer.h"
#include "mega/megaclient.h"
#include "mega/command.h"
#include "mega/base64.h"
#include "mega/megaapp.h"
#include "mega/utils.h"
#include "mega/logging.h"
#include "mega/raid.h"

namespace {

// transfer attempts are considered failed after XFERTIMEOUT deciseconds
// without data flow
constexpr mega::dstime XFERTIMEOUT = 600;

// max time without progress callbacks
constexpr mega::dstime PROGRESSTIMEOUT = 10;

// max request size for downloads and uploads
#if defined(__ANDROID__) || defined(USE_IOS) || defined(WINDOWS_PHONE)
    constexpr m_off_t MAX_REQ_SIZE = 2097152; // 2 MB
#elif defined (_WIN32) || defined(HAVE_AIO_RT)
    constexpr m_off_t MAX_REQ_SIZE = 16777216; // 16 MB
#else
    constexpr m_off_t MAX_REQ_SIZE = 4194304; // 4 MB
#endif

// max allowed difference between the next chunk and the first unfinished chunk
constexpr m_off_t MAX_UPLOAD_GAP = 62914560; // 60 MB (up to 63 chunks)

}

namespace mega {

TransferSlot::TransferSlot(Transfer& transfer)
    : retrybt{transfer.client->rng}
    , m_transfer{transfer}
{
    starttime = 0;
    lastprogressreport = 0;
    progressreported = 0;
    speed = meanSpeed = 0;
    progresscontiguous = 0;
    delayedchunk = false;

    lastdata = Waiter::ds;
    errorcount = 0;
    lasterror = API_OK;

    failure = false;
    retrying = false;
    
    fileattrsmutable = 0;

    connections = 0;
    reqs = NULL;
    asyncIO = NULL;
    pendingcmd = NULL;

    m_transfer.slot = this;
    m_transfer.state = TRANSFERSTATE_ACTIVE;

    fa = m_transfer.client->fsaccess->newfileaccess();

    slots_it = m_transfer.client->tslots.end();

    maxRequestSize = MAX_REQ_SIZE;
#if defined(_WIN32) && !defined(WINDOWS_PHONE)
    MEMORYSTATUSEX statex;
    memset(&statex, 0, sizeof (statex));
    statex.dwLength = sizeof (statex);
    if (GlobalMemoryStatusEx(&statex))
    {
        LOG_debug << "RAM stats. Free physical: " << statex.ullAvailPhys << "   Free virtual: " << statex.ullAvailVirtual;
        if (statex.ullAvailPhys < 1073741824 // 1024 MB
                || statex.ullAvailVirtual < 1073741824)
        {
            if (statex.ullAvailPhys < 536870912 // 512 MB
                    || statex.ullAvailVirtual < 536870912)
            {
                if (statex.ullAvailPhys < 268435456 // 256 MB
                        || statex.ullAvailVirtual < 268435456)
                {
                    maxRequestSize = 2097152; // 2 MB
                }
                else
                {
                    maxRequestSize = 4194304; // 4 MB
                }
            }
            else
            {
                maxRequestSize = 8388608; // 8 MB
            }
        }
        else
        {
            maxRequestSize = 16777216; // 16 MB
        }
    }
    else
    {
        LOG_warn << "Error getting RAM usage info";
    }
#endif
}

// delete slot and associated resources, but keep transfer intact (can be
// reused on a new slot)
TransferSlot::~TransferSlot()
{
    if (m_transfer.type == GET && !m_transfer.finished
            && m_transfer.progresscompleted != m_transfer.size
            && !m_transfer.asyncopencontext)
    {
        bool cachetransfer = false; // need to save in cache

        if (fa && fa->asyncavailable())
        {
            for (int i = 0; i < connections; i++)
            {
                if (reqs[i] && reqs[i]->status == REQ_ASYNCIO && asyncIO[i])
                {
                    asyncIO[i]->finish();
                    if (!asyncIO[i]->failed)
                    {
                        LOG_verbose << "Async write succeeded";
                        transferbuf.bufferWriteCompleted(i);
                        cachetransfer = true;
                    }
                }
                delete asyncIO[i];
                asyncIO[i] = NULL;
            }

            // Open the file in synchonous mode
            delete fa;
            fa = m_transfer.client->fsaccess->newfileaccess();
            if (!fa->fopen(&m_transfer.localfilename, false, true))
            {
                delete fa;
                fa = NULL;
            }
        }

        for (int i = 0; i < connections; i++)
        {
            HttpReqDL *downloadRequest = (HttpReqDL *)reqs[i];
            if (fa && downloadRequest && downloadRequest->status == REQ_INFLIGHT
                    && downloadRequest->contentlength == downloadRequest->size
                    && downloadRequest->bufpos >= SymmCipher::BLOCKSIZE)
            {
                HttpReq::http_buf_t* buf = downloadRequest->release_buf();
                buf->end -= buf->datalen() % RAIDSECTOR;
                transferbuf.submitBuffer(i, new TransferBufferManager::FilePiece(downloadRequest->dlpos, buf)); // resets size & bufpos of downloadrequest.
            }
        }

        for (int j = 0; connections > 0; j++)
        {
            int i = j >= connections ? 0 : j;

            // synchronous writes for all remaining outstanding data, including data from any failed async above
            // check each connection first and then all that were not yet on a connection
            TransferBufferManager::FilePiece* outputPiece = transferbuf.getAsyncOutputBufferPointer(i);
            if (outputPiece)
            {
                if (fa->fwrite(outputPiece->buf.datastart(), static_cast<unsigned>(outputPiece->buf.datalen()), outputPiece->pos))
                {

                    LOG_verbose << "Sync write succeeded";
                    transferbuf.bufferWriteCompleted(i);
                    cachetransfer = true;
                }
                else
                {
                    LOG_err << "Error caching data at: " << outputPiece->pos;
                }
            }
            else if (j >= connections)
            {
                break;
            }
        }

        if (cachetransfer)
        {
            m_transfer.client->transfercacheadd(&m_transfer);
            LOG_debug << "Completed: " << m_transfer.progresscompleted;
        }
    }

    m_transfer.slot = NULL;

    if (slots_it != m_transfer.client->tslots.end())
    {
        // advance main loop iterator if deleting next in line
        if (m_transfer.client->slotit != m_transfer.client->tslots.end() && *m_transfer.client->slotit == this)
        {
            m_transfer.client->slotit++;
        }

        m_transfer.client->tslots.erase(slots_it);
    }

    if (pendingcmd)
    {
        pendingcmd->cancel();
    }

    if (m_transfer.asyncopencontext)
    {
        delete m_transfer.asyncopencontext;
        m_transfer.asyncopencontext = NULL;
        m_transfer.client->asyncfopens--;
    }

    while (connections--)
    {
        delete asyncIO[connections];
        delete reqs[connections];
    }

    delete[] asyncIO;
    delete[] reqs;

    if (fa)
    {
        delete fa;
    }
}

bool TransferSlot::createconnectionsonce()
{
    // delay creating these until we know if it's raid or non-raid
    if (!(connections || reqs || asyncIO))
    {
        if (transferbuf.tempUrlVector().empty())
        {
            return false;   // too soon, we don't know raid / non-raid yet
        }

        connections = transferbuf.isRaid() ? RAIDPARTS : (m_transfer.size > 131072 ? m_transfer.client->connections[m_transfer.type] : 1);
        LOG_debug << "Populating transfer slot with " << connections << " connections, max request size of " << maxRequestSize << " bytes";
        reqs = new HttpReqXfer*[connections]();
        asyncIO = new AsyncIOContext*[connections]();
    }
    return true;
}

void TransferSlot::toggleport(HttpReqXfer *req)
{
    if (!memcmp(req->posturl.c_str(), "http:", 5))
    {
       size_t portendindex = req->posturl.find("/", 8);
       size_t portstartindex = req->posturl.find(":", 8);

       if (portendindex != string::npos)
       {
           if (portstartindex == string::npos)
           {
               LOG_debug << "Enabling alternative port for chunk";
               req->posturl.insert(portendindex, ":8080");
           }
           else
           {
               LOG_debug << "Disabling alternative port for chunk";
               req->posturl.erase(portstartindex, portendindex - portstartindex);
           }
       }
    }
}

// abort all HTTP connections
void TransferSlot::disconnect()
{
    for (int i = connections; i--;)
    {
        if (reqs[i])
        {
            reqs[i]->disconnect();
        }
    }
}

// coalesce block macs into file mac
int64_t TransferSlot::macsmac(chunkmac_map* macs)
{
    byte mac[SymmCipher::BLOCKSIZE] = { 0 };

    SymmCipher *cipher = m_transfer.transfercipher();
    for (chunkmac_map::iterator it = macs->begin(); it != macs->end(); it++)
    {
        SymmCipher::xorblock(it->second.mac, mac);
        cipher->ecb_encrypt(mac);
    }

    uint32_t* m = (uint32_t*)mac;

    m[0] ^= m[1];
    m[1] = m[2] ^ m[3];

    return MemAccess::get<int64_t>((const char*)mac);
}

void chunkmac_map::serialize(string& d) const
{
    unsigned short ll = (unsigned short)size();
    d.append((char*)&ll, sizeof(ll));
    for (const_iterator it = begin(); it != end(); it++)
    {
        d.append((char*)&it->first, sizeof(it->first));
        d.append((char*)&it->second, sizeof(it->second));
    }
}

bool chunkmac_map::unserialize(const char*& ptr, const char* end)
{
    unsigned short ll;
    if ((ptr + sizeof(ll) > end) || ptr + (ll = MemAccess::get<unsigned short>(ptr)) * (sizeof(m_off_t) + sizeof(ChunkMAC)) + sizeof(ll) > end)
    {
        return false;
    }

    ptr += sizeof(ll);

    for (int i = 0; i < ll; i++)
    {
        m_off_t pos = MemAccess::get<m_off_t>(ptr);
        ptr += sizeof(m_off_t);

        memcpy(&((*this)[pos]), ptr, sizeof(ChunkMAC));
        ptr += sizeof(ChunkMAC);
    }
    return true;
}

const Transfer& TransferSlot::transfer() const
{
    return m_transfer;
}

Transfer& TransferSlot::transfer()
{
    return m_transfer;
}

// file transfer state machine
void TransferSlot::doio(MegaClient* client)
{
    if (!fa || (m_transfer.size && m_transfer.progresscompleted == m_transfer.size)
            || (m_transfer.type == PUT && m_transfer.ultoken))
    {
        if (m_transfer.type == GET || m_transfer.ultoken)
        {
            if (fa && m_transfer.type == GET)
            {
                LOG_debug << "Verifying cached download";
                m_transfer.currentmetamac = macsmac(&m_transfer.chunkmacs);
                m_transfer.hascurrentmetamac = true;

                // verify meta MAC
                if (m_transfer.currentmetamac == m_transfer.metamac)
                {
                    return m_transfer.complete();
                }
                else
                {
                    int creqtag = client->reqtag;
                    client->reqtag = 0;
                    client->sendevent(99432, "MAC verification failed for cached download");
                    client->reqtag = creqtag;

                    m_transfer.chunkmacs.clear();
                    return m_transfer.failed(API_EKEY);
                }
            }

            // this is a pending completion, retry every 200 ms by default
            retrybt.backoff(2);
            retrying = true;

            return m_transfer.complete();
        }
        else
        {
            int creqtag = client->reqtag;
            client->reqtag = 0;
            client->sendevent(99410, "No upload token available");
            client->reqtag = creqtag;

            return m_transfer.failed(API_EINTERNAL);
        }
    }

    retrying = false;
    m_transfer.state = TRANSFERSTATE_ACTIVE;

    if (!createconnectionsonce())   // don't use connections, reqs, or asyncIO before this point.
    {
        return;
    }

    dstime backoff = 0;
    m_off_t p = 0;

    if (errorcount > 4)
    {
        LOG_warn << "Failed transfer: too many errors";
        return m_transfer.failed(lasterror);
    }

    for (int i = connections; i--; )
    {
        if (reqs[i])
        {
            unsigned slowestConnection;
            if (m_transfer.type == GET && reqs[i]->contentlength == reqs[i]->size && transferbuf.detectSlowestRaidConnection(i, slowestConnection))
            {
                LOG_debug << "Connection " << slowestConnection << " is the slowest to reply, using the other 5.";
                delete reqs[slowestConnection];
                reqs[slowestConnection] = NULL;
                transferbuf.resetPart(slowestConnection);
                i = connections; 
                continue;
            }

            if (reqs[i]->status == REQ_FAILURE && reqs[i]->httpstatus == 200 && m_transfer.type == GET && transferbuf.isRaid())
            {
                // check if we got some data and the failure occured partway through the part chunk.  If so, best not to waste it, convert to success case with less data
                HttpReqDL *downloadRequest = (HttpReqDL *)reqs[i];
                LOG_debug << "Connection " << i << " received " << downloadRequest->bufpos << " before failing, processing data.";
                if (downloadRequest->contentlength == downloadRequest->size && downloadRequest->bufpos >= RAIDSECTOR)
                {
                    downloadRequest->bufpos -= downloadRequest->bufpos % RAIDSECTOR;  // always on a raidline boundary
                    downloadRequest->size = unsigned(downloadRequest->bufpos);
                    transferbuf.transferPos(i) = downloadRequest->bufpos;
                    downloadRequest->status = REQ_SUCCESS;
                }
            }

            switch (reqs[i]->status)
            {
                case REQ_INFLIGHT:
                    p += reqs[i]->transferred(client);

                    assert(reqs[i]->lastdata != NEVER);
                    if (m_transfer.type == GET && transferbuf.isRaid() &&
                        (Waiter::ds - reqs[i]->lastdata) > (XFERTIMEOUT / 2) &&
                        transferbuf.connectionRaidPeersAreAllPaused(i))
                    {
                        // switch to 5 channel raid to avoid the slow/delayed connection. (or if already switched, try a different 5).  If we already tried too many times then let the usual timeout occur
                        if (tryRaidRecoveryFromHttpGetError(i))
                        {
                            LOG_warn << "Connection " << i << " is slow or stalled, trying the other 5 cloudraid connections";
                            reqs[i]->disconnect();
                            reqs[i]->status = REQ_READY;
                        }
                    }
                    break;

                case REQ_SUCCESS:
                    if (client->orderdownloadedchunks && m_transfer.type == GET && m_transfer.progresscompleted != ((HttpReqDL *)reqs[i])->dlpos)
                    {
                        // postponing unsorted chunk
                        p += reqs[i]->size;
                        break;
                    }

                    lastdata = Waiter::ds;
                    m_transfer.lastaccesstime = m_time();

                    if (!transferbuf.isRaid())
                    {
                        LOG_debug << "Transfer request finished (" << m_transfer.type << ") Position: " << transferbuf.transferPos(i) << " (" << m_transfer.pos << ") Size: " << reqs[i]->size
                            << " Completed: " << (m_transfer.progresscompleted + reqs[i]->size) << " of " << m_transfer.size;
                    }
                    else
                    {
                        LOG_debug << "Transfer request finished (" << m_transfer.type << ") " << " on connection " << i << " part pos: " << transferbuf.transferPos(i) << " of part size " << transferbuf.raidPartSize(i, m_transfer.size)
                            << " Overall Completed: " << (m_transfer.progresscompleted) << " of " << m_transfer.size;
                    }

                    if (m_transfer.type == PUT)
                    {
                        // completed put transfers are signalled through the
                        // return of the upload token
                        if (reqs[i]->in.size())
                        {
                            if (reqs[i]->in.size() == NewNode::UPLOADTOKENLEN)
                            {                                        
                                LOG_debug << "Upload token received";
                                if (!m_transfer.ultoken)
                                {
                                    m_transfer.ultoken = new byte[NewNode::UPLOADTOKENLEN]();
                                }

                                bool tokenOK = true;
                                if (reqs[i]->in.data()[NewNode::UPLOADTOKENLEN - 1] == 1)
                                {
                                    LOG_debug << "New style upload token";
                                    memcpy(m_transfer.ultoken, reqs[i]->in.data(), NewNode::UPLOADTOKENLEN);
                                }
                                else
                                {
                                    LOG_debug << "Old style upload token: " << reqs[i]->in;
                                    tokenOK = (Base64::atob(reqs[i]->in.data(), m_transfer.ultoken, NewNode::UPLOADTOKENLEN)
                                               == NewNode::OLDUPLOADTOKENLEN);
                                }

                                if (tokenOK)
                                {
                                    errorcount = 0;
                                    m_transfer.failcount = 0;

                                    m_off_t startpos = reqs[i]->pos;
                                    m_off_t finalpos = startpos + reqs[i]->size;
                                    while (startpos < finalpos)
                                    {
                                        m_transfer.chunkmacs[startpos].finished = true;
                                        LOG_verbose << "Upload chunk completed: " << startpos;
                                        startpos = ChunkedHash::chunkceil(startpos, finalpos);
                                    }

                                    updatecontiguousprogress();

                                    m_transfer.progresscompleted += reqs[i]->size;
                                    memcpy(m_transfer.filekey, m_transfer.transferkey, sizeof m_transfer.transferkey);
                                    ((int64_t*)m_transfer.filekey)[2] = m_transfer.ctriv;
                                    ((int64_t*)m_transfer.filekey)[3] = macsmac(&m_transfer.chunkmacs);
                                    SymmCipher::xorblock(m_transfer.filekey + SymmCipher::KEYLENGTH, m_transfer.filekey);

                                    client->transfercacheadd(&m_transfer);

                                    if (m_transfer.progresscompleted != progressreported)
                                    {
                                        progressreported = m_transfer.progresscompleted;
                                        lastdata = Waiter::ds;

                                        progress();
                                    }

                                    return m_transfer.complete();
                                }
                                else
                                {
                                    delete [] m_transfer.ultoken;
                                    m_transfer.ultoken = NULL;
                                }
                            }

                            LOG_debug << "Error uploading chunk: " << reqs[i]->in;
                            error e = (error)atoi(reqs[i]->in.c_str());
                            if (e == API_EKEY)
                            {
                                int creqtag = client->reqtag;
                                client->reqtag = 0;
                                client->sendevent(99429, "Integrity check failed in upload");
                                client->reqtag = creqtag;

                                lasterror = e;
                                errorcount++;
                                reqs[i]->status = REQ_PREPARED;
                                break;
                            }

                            if (e == API_ERATELIMIT || (reqs[i]->contenttype.find("text/html") != string::npos
                                    && !memcmp(reqs[i]->posturl.c_str(), "http:", 5)))
                            {
                                client->usehttps = true;
                                client->app->notify_change_to_https();

                                int creqtag = client->reqtag;
                                client->reqtag = 0;
                                if (e == API_ERATELIMIT)
                                {
                                    client->sendevent(99440, "Retry requested by storage server");
                                }
                                else
                                {
                                    LOG_warn << "Invalid Content-Type detected during upload: " << reqs[i]->contenttype;
                                }
                                client->sendevent(99436, "Automatic change to HTTPS");
                                client->reqtag = creqtag;

                                return m_transfer.failed(API_EAGAIN);
                            }

                            // fail with returned error
                            return m_transfer.failed(e);
                        }

                        m_off_t startpos = reqs[i]->pos;
                        m_off_t finalpos = startpos + reqs[i]->size;
                        while (startpos < finalpos)
                        {
                            m_transfer.chunkmacs[startpos].finished = true;
                            LOG_verbose << "Upload chunk completed: " << startpos;
                            startpos = ChunkedHash::chunkceil(startpos, finalpos);
                        }
                        m_transfer.progresscompleted += reqs[i]->size;

                        updatecontiguousprogress();

                        if (m_transfer.progresscompleted == m_transfer.size)
                        {
                            int creqtag = client->reqtag;
                            client->reqtag = 0;
                            client->sendevent(99409, "No upload token received");
                            client->reqtag = creqtag;

                            return m_transfer.failed(API_EINTERNAL);
                        }

                        errorcount = 0;
                        m_transfer.failcount = 0;
                        client->transfercacheadd(&m_transfer);
                        reqs[i]->status = REQ_READY;
                    }
                    else   // GET
                    {
                        HttpReqDL *downloadRequest = (HttpReqDL *)reqs[i];
                        if (reqs[i]->size == reqs[i]->bufpos || downloadRequest->buffer_released)   // downloadRequest->buffer_released being true indicates we're retrying this asyncIO
                        {

                            if (!downloadRequest->buffer_released)
                            {
                                transferbuf.submitBuffer(i, new TransferBufferManager::FilePiece(downloadRequest->dlpos, downloadRequest->release_buf())); // resets size & bufpos.  finalize() is taken care of in the transferbuf
                                downloadRequest->buffer_released = true;
                            }

                            TransferBufferManager::FilePiece* outputPiece = transferbuf.getAsyncOutputBufferPointer(i);
                            if (outputPiece)
                            {

                                if (fa->asyncavailable())
                                {
                                    if (asyncIO[i])
                                    {
                                        LOG_warn << "Retrying failed async write";
                                        delete asyncIO[i];
                                        asyncIO[i] = NULL;
                                    }

                                    p += reqs[i]->size;

                                    LOG_debug << "Writing data asynchronously at " << outputPiece->pos << " to " << (outputPiece->pos + outputPiece->buf.datalen());
                                    asyncIO[i] = fa->asyncfwrite(outputPiece->buf.datastart(), static_cast<unsigned>(outputPiece->buf.datalen()), outputPiece->pos);
                                    reqs[i]->status = REQ_ASYNCIO;
                                }
                                else
                                {
                                    if (fa->fwrite(outputPiece->buf.datastart(), static_cast<unsigned>(outputPiece->buf.datalen()), outputPiece->pos))
                                    {
                                        LOG_verbose << "Sync write succeeded";
                                        transferbuf.bufferWriteCompleted(i);
                                        errorcount = 0;
                                        m_transfer.failcount = 0;
                                        updatecontiguousprogress();
                                    }
                                    else
                                    {
                                        LOG_err << "Error saving finished chunk";
                                        if (!fa->retry)
                                        {
                                            return m_transfer.failed(API_EWRITE);
                                        }
                                        lasterror = API_EWRITE;
                                        backoff = 2;
                                        break;
                                    }

                                    if (m_transfer.progresscompleted == m_transfer.size)
                                    {
                                        if (m_transfer.progresscompleted)
                                        {
                                            m_transfer.currentmetamac = macsmac(&m_transfer.chunkmacs);
                                            m_transfer.hascurrentmetamac = true;
                                        }

                                        // verify meta MAC
                                        if (!m_transfer.progresscompleted
                                            || (m_transfer.currentmetamac == m_transfer.metamac))
                                        {
                                            client->transfercacheadd(&m_transfer);
                                            if (m_transfer.progresscompleted != progressreported)
                                            {
                                                progressreported = m_transfer.progresscompleted;
                                                lastdata = Waiter::ds;

                                                progress();
                                            }

                                            return m_transfer.complete();
                                        }
                                        else
                                        {
                                            int creqtag = client->reqtag;
                                            client->reqtag = 0;
                                            client->sendevent(99431, "MAC verification failed");
                                            client->reqtag = creqtag;

                                            m_transfer.chunkmacs.clear();
                                            return m_transfer.failed(API_EKEY);
                                        }
                                    }
                                    client->transfercacheadd(&m_transfer);
                                    reqs[i]->status = REQ_READY;
                                }
                            }
                            else if (transferbuf.isRaid())
                            {
                                reqs[i]->status = REQ_READY;  // this connection has retrieved a part of the file, but we don't have enough to combine yet for full file output.   This connection can start fetching the next piece of that part.
                            }
                            else
                            {
                                assert(false);  // non-raid, if the request succeeded then we must have a piece to write to file.
                            }
                        }
                        else
                        {
                            if (reqs[i]->contenttype.find("text/html") != string::npos
                                    && !memcmp(reqs[i]->posturl.c_str(), "http:", 5))
                            {
                                LOG_warn << "Invalid Content-Type detected during download: " << reqs[i]->contenttype;
                                client->usehttps = true;
                                client->app->notify_change_to_https();

                                int creqtag = client->reqtag;
                                client->reqtag = 0;
                                client->sendevent(99436, "Automatic change to HTTPS");
                                client->reqtag = creqtag;

                                return m_transfer.failed(API_EAGAIN);
                            }

                            int creqtag = client->reqtag;
                            client->reqtag = 0;
                            client->sendevent(99430, "Invalid chunk size");
                            client->reqtag = creqtag;

                            LOG_warn << "Invalid chunk size: " << reqs[i]->size << " - " << reqs[i]->bufpos;
                            lasterror = API_EREAD;
                            errorcount++;
                            reqs[i]->status = REQ_PREPARED;
                            break;
                        }
                    }
                    break;

                case REQ_ASYNCIO:
                    if (asyncIO[i]->finished)
                    {
                        LOG_verbose << "Processing finished async fs operation";
                        if (!asyncIO[i]->failed)
                        {
                            if (m_transfer.type == PUT)
                            {
                                LOG_verbose << "Async read succeeded";
                                m_off_t npos = asyncIO[i]->pos + asyncIO[i]->len;
                                string finaltempurl = transferbuf.tempURL(i);
                                if (client->usealtupport && !memcmp(finaltempurl.c_str(), "http:", 5))
                                {
                                    size_t index = finaltempurl.find("/", 8);
                                    if(index != string::npos && finaltempurl.find(":", 8) == string::npos)
                                    {
                                        finaltempurl.insert(index, ":8080");
                                    }
                                }

                                reqs[i]->prepare(finaltempurl.c_str(), m_transfer.transfercipher(),
                                         &m_transfer.chunkmacs, m_transfer.ctriv,
                                         asyncIO[i]->pos, npos);

                                reqs[i]->pos = ChunkedHash::chunkfloor(asyncIO[i]->pos);
                                reqs[i]->status = REQ_PREPARED;
                            }
                            else
                            {
                                LOG_verbose << "Async write succeeded";
                                transferbuf.bufferWriteCompleted(i);
                                errorcount = 0;
                                m_transfer.failcount = 0;

                                updatecontiguousprogress();

                                if (m_transfer.progresscompleted == m_transfer.size)
                                {
                                    if (m_transfer.progresscompleted)
                                    {
                                        m_transfer.currentmetamac = macsmac(&m_transfer.chunkmacs);
                                        m_transfer.hascurrentmetamac = true;
                                    }

                                    // verify meta MAC
                                    if (!m_transfer.progresscompleted
                                            || (m_transfer.currentmetamac == m_transfer.metamac))
                                    {
                                        client->transfercacheadd(&m_transfer);
                                        if (m_transfer.progresscompleted != progressreported)
                                        {
                                            progressreported = m_transfer.progresscompleted;
                                            lastdata = Waiter::ds;

                                            progress();
                                        }

                                        return m_transfer.complete();
                                    }
                                    else
                                    {
                                        int creqtag = client->reqtag;
                                        client->reqtag = 0;
                                        client->sendevent(99431, "MAC verification failed");
                                        client->reqtag = creqtag;

                                        m_transfer.chunkmacs.clear();
                                        return m_transfer.failed(API_EKEY);
                                    }
                                }

                                client->transfercacheadd(&m_transfer);
                                reqs[i]->status = REQ_READY;

                                if (client->orderdownloadedchunks)
                                {
                                    // Check connections again looking for postponed chunks
                                    delete asyncIO[i];
                                    asyncIO[i] = NULL;
                                    i = connections;
                                    continue;
                                }
                            }
                            delete asyncIO[i];
                            asyncIO[i] = NULL;
                        }
                        else
                        {
                            LOG_warn << "Async operation failed: " << asyncIO[i]->retry;
                            if (!asyncIO[i]->retry)
                            {
                                delete asyncIO[i];
                                asyncIO[i] = NULL;
                                return m_transfer.failed(m_transfer.type == PUT ? API_EREAD : API_EWRITE);
                            }

                            // retry shortly
                            if (m_transfer.type == PUT)
                            {
                                lasterror = API_EREAD;
                                reqs[i]->status = REQ_READY;
                            }
                            else
                            {
                                lasterror = API_EWRITE;
                                reqs[i]->status = REQ_SUCCESS;
                            }
                            backoff = 2;
                        }
                    }
                    else if (m_transfer.type == GET)
                    {
                        p += asyncIO[i]->len;
                    }
                    break;

                case REQ_FAILURE:
                    LOG_warn << "Failed chunk. HTTP status: " << reqs[i]->httpstatus;
                    if (reqs[i]->httpstatus && reqs[i]->contenttype.find("text/html") != string::npos
                            && !memcmp(reqs[i]->posturl.c_str(), "http:", 5))
                    {
                        LOG_warn << "Invalid Content-Type detected on failed chunk: " << reqs[i]->contenttype;
                        client->usehttps = true;
                        client->app->notify_change_to_https();

                        int creqtag = client->reqtag;
                        client->reqtag = 0;
                        client->sendevent(99436, "Automatic change to HTTPS");
                        client->reqtag = creqtag;

                        return m_transfer.failed(API_EAGAIN);
                    }

                    if (reqs[i]->httpstatus == 509)
                    {
                        if (reqs[i]->timeleft < 0)
                        {
                            int creqtag = client->reqtag;
                            client->reqtag = 0;
                            client->sendevent(99408, "Overquota without timeleft");
                            client->reqtag = creqtag;
                        }

                        LOG_warn << "Bandwidth overquota from storage server";
                        if (reqs[i]->timeleft > 0)
                        {
                            backoff = dstime(reqs[i]->timeleft * 10);
                        }
                        else
                        {
                            // default retry intervals
                            backoff = MegaClient::DEFAULT_BW_OVERQUOTA_BACKOFF_SECS * 10;
                        }

                        return m_transfer.failed(API_EOVERQUOTA, backoff);
                    }
                    else if (reqs[i]->httpstatus == 403 || reqs[i]->httpstatus == 404 || reqs[i]->httpstatus == 0)
                    {
                        if (!tryRaidRecoveryFromHttpGetError(i))
                        {
                            return m_transfer.failed(API_EAGAIN);
                        }
                    }
                    else
                    {
                        if (!failure)
                        {
                            failure = true;
                            bool changeport = false;

                            if (m_transfer.type == GET && client->autodownport && !memcmp(transferbuf.tempURL(i).c_str(), "http:", 5))
                            {
                                LOG_debug << "Automatically changing download port";
                                client->usealtdownport = !client->usealtdownport;
                                changeport = true;
                            }
                            else if (m_transfer.type == PUT && client->autoupport && !memcmp(transferbuf.tempURL(i).c_str(), "http:", 5))
                            {
                                LOG_debug << "Automatically changing upload port";
                                client->usealtupport = !client->usealtupport;
                                changeport = true;
                            }

                            client->app->transfer_failed(&m_transfer, API_EFAILED);
                            client->setchunkfailed(&reqs[i]->posturl);

                            if (changeport)
                            {
                                toggleport(reqs[i]);
                            }
                        }
                        reqs[i]->status = REQ_PREPARED;
                    }

                default:
                    ;
            }
        }

        if (!failure)
        {
            if (!reqs[i] || (reqs[i]->status == REQ_READY))
            {
                bool newInputBufferSupplied = false;
                bool pauseConnectionInputForRaid = false;
                std::pair<m_off_t, m_off_t> posrange = transferbuf.nextNPosForConnection(i, maxRequestSize, connections, newInputBufferSupplied, pauseConnectionInputForRaid);

                // we might have a raid-reassembled block to write, or a previously loaded block, or a skip block to process.
                bool newOutputBufferSupplied = false;
                TransferBufferManager::FilePiece* outputPiece = transferbuf.getAsyncOutputBufferPointer(i);
                if (outputPiece && reqs[i])
                {
                    // set up to do the actual write on the next loop, as if it was a retry
                    reqs[i]->status = REQ_SUCCESS;
                    ((HttpReqDL*)reqs[i])->buffer_released = true;
                    newOutputBufferSupplied = true;
                }

                if (newOutputBufferSupplied || newInputBufferSupplied || pauseConnectionInputForRaid)
                {
                    // process supplied block, or just wait until other connections catch up a bit
                }
                else if (posrange.second > posrange.first || !m_transfer.size || (m_transfer.type == PUT && asyncIO[i]))
                {
                    // download/upload specified range

                    if (!reqs[i])
                    {
                        reqs[i] = m_transfer.type == PUT ? (HttpReqXfer*)new HttpReqUL() : (HttpReqXfer*)new HttpReqDL();
                    }

                    bool prepare = true;
                    if (m_transfer.type == PUT)
                    {
                        m_off_t pos = posrange.first;
                        unsigned size = (unsigned)(posrange.second - pos);

                        if (fa->asyncavailable())
                        {
                            if (asyncIO[i])
                            {
                                LOG_warn << "Retrying a failed read";
                                pos = asyncIO[i]->pos;
                                size = asyncIO[i]->len;
                                posrange.second = pos + size;
                                delete asyncIO[i];
                                asyncIO[i] = NULL;
                            }

                            asyncIO[i] = fa->asyncfread(reqs[i]->out, size, (-(int)size) & (SymmCipher::BLOCKSIZE - 1), pos);
                            reqs[i]->status = REQ_ASYNCIO;
                            prepare = false;
                        }
                        else
                        {
                            if (!fa->fread(reqs[i]->out, size, (-(int)size) & (SymmCipher::BLOCKSIZE - 1), m_transfer.pos))
                            {
                                LOG_warn << "Error preparing transfer: " << fa->retry;
                                if (!fa->retry)
                                {
                                    return m_transfer.failed(API_EREAD);
                                }

                                // retry the read shortly
                                backoff = 2;
                                posrange.second = m_transfer.pos;
                                prepare = false;
                            }
                        }
                    }

                    if (prepare)
                    {
                        string finaltempurl = transferbuf.tempURL(i);
                        if (m_transfer.type == GET && client->usealtdownport
                                && !memcmp(finaltempurl.c_str(), "http:", 5))
                        {
                            size_t index = finaltempurl.find("/", 8);
                            if(index != string::npos && finaltempurl.find(":", 8) == string::npos)
                            {
                                finaltempurl.insert(index, ":8080");
                            }
                        }

                        if (m_transfer.type == PUT && client->usealtupport
                                && !memcmp(finaltempurl.c_str(), "http:", 5))
                        {
                            size_t index = finaltempurl.find("/", 8);
                            if(index != string::npos && finaltempurl.find(":", 8) == string::npos)
                            {
                                finaltempurl.insert(index, ":8080");
                            }
                        }

                        unsigned size = (unsigned)(posrange.second - posrange.first);
                        if (size > 16777216)
                        {
                            int creqtag = client->reqtag;
                            client->reqtag = 0;
                            client->sendevent(99434, "Invalid request size");
                            client->reqtag = creqtag;

                            m_transfer.chunkmacs.clear();
                            return m_transfer.failed(API_EINTERNAL);
                        }

                        reqs[i]->prepare(finaltempurl.c_str(), m_transfer.transfercipher(),
                                                               &m_transfer.chunkmacs, m_transfer.ctriv,
                                                               posrange.first, posrange.second);
                        reqs[i]->pos = ChunkedHash::chunkfloor(posrange.first);
                        reqs[i]->status = REQ_PREPARED;
                    }

                    transferbuf.transferPos(i) = std::max<m_off_t>(transferbuf.transferPos(i), posrange.second);
                }
                else if (reqs[i])
                {
                    reqs[i]->status = REQ_DONE;

                    if (m_transfer.type == GET)
                    {
                        // raid reassembly can have several chunks to complete at the end of the file - keep processing till they are all done
                        TransferBufferManager::FilePiece* outputPiece = transferbuf.getAsyncOutputBufferPointer(i);
                        if (outputPiece)
                        {
                            // set up to do the actual write on the next loop, as if it was a retry
                            reqs[i]->status = REQ_SUCCESS;
                            ((HttpReqDL*)reqs[i])->buffer_released = true;
                        }
                    }
                }
            }

            if (reqs[i] && (reqs[i]->status == REQ_PREPARED))
            {
                reqs[i]->minspeed = true;
                reqs[i]->post(client);
            }
        }
    }

    if (m_transfer.type == GET && transferbuf.isRaid())
    {
        p = transferbuf.progress();
        for (int i = connections; i--; )
        {
            if (reqs[i] && reqs[i]->status == REQ_INFLIGHT)
            {
                p += static_cast<HttpReqDL*>(reqs[i])->bufpos;
            }
        }
    }
    else
    {
        p += m_transfer.progresscompleted;
    }

    if (p != progressreported || (Waiter::ds - lastprogressreport) > PROGRESSTIMEOUT)
    {
        if (p != progressreported)
        {
            m_off_t diff = p - progressreported;
            speed = speedController.calculateSpeed(diff);
            meanSpeed = speedController.getMeanSpeed();
            if (m_transfer.type == PUT)
            {
                client->httpio->updateuploadspeed(diff);
            }
            else
            {
                client->httpio->updatedownloadspeed(diff);
            }

            progressreported = p;
            lastdata = Waiter::ds;
        }
        lastprogressreport = Waiter::ds;

        progress();
    }

    if (Waiter::ds - lastdata >= XFERTIMEOUT && !failure)
    {
        LOG_warn << "Failed chunk due to a timeout";
        failure = true;
        bool changeport = false;

        if (m_transfer.type == GET && client->autodownport && !memcmp(transferbuf.tempURL(0).c_str(), "http:", 5))
        {
            LOG_debug << "Automatically changing download port due to a timeout";
            client->usealtdownport = !client->usealtdownport;
            changeport = true;
        }
        else if (m_transfer.type == PUT && client->autoupport && !memcmp(transferbuf.tempURL(0).c_str(), "http:", 5))
        {
            LOG_debug << "Automatically changing upload port due to a timeout";
            client->usealtupport = !client->usealtupport;
            changeport = true;
        }

        bool chunkfailed = false;
        for (int i = connections; i--; )
        {
            if (reqs[i] && reqs[i]->status == REQ_INFLIGHT)
            {
                chunkfailed = true;
                client->setchunkfailed(&reqs[i]->posturl);
                reqs[i]->disconnect();

                if (changeport)
                {
                    toggleport(reqs[i]);
                }

                reqs[i]->status = REQ_PREPARED;
            }
        }

        if (!chunkfailed)
        {
            LOG_warn << "Transfer failed due to a timeout";
            m_transfer.failed(API_EAGAIN);
        }
        else
        {
            LOG_warn << "Chunk failed due to a timeout";
            client->app->transfer_failed(&m_transfer, API_EFAILED);
        }
    }

    if (!failure)
    {
        if (!backoff && (Waiter::ds - lastdata) < XFERTIMEOUT)
        {
            // no other backoff: check again at XFERMAXFAIL
            backoff = XFERTIMEOUT - (Waiter::ds - lastdata);
        }

        retrybt.backoff(backoff);
    }
}


bool TransferSlot::tryRaidRecoveryFromHttpGetError(unsigned connectionNum)
{
    // If we are downloding a cloudraid file then we may be able to ignore one connection and download from the other 5.
    if (transferbuf.isRaid())
    {
        if (transferbuf.tryRaidHttpGetErrorRecovery(connectionNum))
        {
            // transferbuf is now set up to try a new connection
            reqs[connectionNum]->status = REQ_READY;

            // if the file is nearly complete then some connections might have stopped, but need restarting as they could have skipped portions
            for (unsigned j = connections; j--; )
            {
                if (reqs[j] && reqs[j]->status == REQ_DONE)
                {
                    reqs[j]->status = REQ_READY;
                }
            }
            return true;
        }
        LOG_warn << "Cloudraid transfer failed, too many connection errors";
    }
    return false;
}


// transfer progress notification to app and related files
void TransferSlot::progress()
{
    m_transfer.client->app->transfer_update(&m_transfer);

    for (file_list::iterator it = m_transfer.files.begin(); it != m_transfer.files.end(); it++)
    {
        (*it)->progress();
    }
}

void TransferSlot::updatecontiguousprogress()
{
    chunkmac_map::iterator pcit;
    chunkmac_map &pcchunkmacs = m_transfer.chunkmacs;
    while ((pcit = pcchunkmacs.find(progresscontiguous)) != pcchunkmacs.end()
           && pcit->second.finished)
    {
        progresscontiguous = ChunkedHash::chunkceil(progresscontiguous, m_transfer.size);
    }
    if (!transferbuf.tempUrlVector().empty() && transferbuf.isRaid())
    {
        LOG_debug << "Contiguous progress: " << progresscontiguous;
    }
    else
    {
        LOG_debug << "Contiguous progress: " << progresscontiguous << " (" << (m_transfer.pos - progresscontiguous) << ")";
    }
}

} // namespace
