// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright The Music Player Daemon Project

/**
 * CD-Audio handling (requires libcdio_paranoia)
 */

#include "CdioParanoiaInputPlugin.hxx"
#include "lib/cdio/Paranoia.hxx"
#include "lib/fmt/RuntimeError.hxx"
#include "lib/curl/Init.hxx"
#include "lib/curl/Headers.hxx"
#include "lib/curl/Request.hxx"
#include "lib/curl/StringHandler.hxx"
#include "../InputStream.hxx"
#include "../InputPlugin.hxx"
#include "util/StringCompare.hxx"
#include "util/Domain.hxx"
#include "util/ByteOrder.hxx"
#include "util/NumberParser.hxx"
#include "util/ScopeExit.hxx"
#include "util/StringSplit.hxx"
#include "fs/AllocatedPath.hxx"
#include "Log.hxx"
#include "config/Block.hxx"
#include "input/RemoteTagScanner.hxx"
#include "event/Loop.hxx"
#include <upnp.h> // for IXML_Document

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <vector>
#include <map>

#include <cdio/cd_types.h>

extern "C" {
#include <libavutil/sha.h>
#include <libavutil/base64.h>

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h> /* close() */
#include <string.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#if defined(__linux__)
#include <linux/cdrom.h>
#define cdte_track_address      cdte_addr.lba
#define DEVICE_NAME             "/dev/cdrom"

#elif defined(__GNU__)
/* According to Samuel Thibault <sthibault@debian.org>, cd-discid needs this
 * to compile on Debian GNU/Hurd (i386) */
#include <sys/cdrom.h>
#define cdte_track_address      cdte_addr.lba
#define DEVICE_NAME             "/dev/cd0"

#elif defined(sun) && defined(unix) && defined(__SVR4)
#include <sys/cdio.h>
#define CD_MSF_OFFSET   150
#define CD_FRAMES       75
/* According to David Schweikert <dws@ee.ethz.ch>, cd-discid needs this
 * to compile on Solaris */
#define cdte_track_address      cdte_addr.lba
#define DEVICE_NAME             "/dev/vol/aliases/cdrom0"

/* __FreeBSD_kernel__ is needed for properly compiling on Debian GNU/kFreeBSD
   Look at http://glibc-bsd.alioth.debian.org/porting/PORTING for more info */
#elif defined(__FreeBSD__) || defined(__FreeBSD_kernel__) || defined(__DragonFly__)
#include <sys/cdio.h>
#define CDROM_LBA               CD_LBA_FORMAT    /* first frame is 0 */
#define CD_MSF_OFFSET           150              /* MSF offset of first frame */
#define CD_FRAMES               75               /* per second */
#define CDROM_LEADOUT           0xAA             /* leadout track */
#define CDROMREADTOCHDR         CDIOREADTOCHEADER
#define CDROMREADTOCENTRY       CDIOREADTOCENTRY
#define cdrom_tochdr            ioc_toc_header
#define cdth_trk0               starting_track
#define cdth_trk1               ending_track
#define cdrom_tocentry          ioc_read_toc_single_entry
#define cdte_track              track
#define cdte_format             address_format
#define cdte_track_address      entry.addr.lba
#define DEVICE_NAME             "/dev/cdrom"

#elif defined(__OpenBSD__) || defined(__NetBSD__)
#include <sys/cdio.h>
#define CDROM_LBA               CD_LBA_FORMAT    /* first frame is 0 */
#define CD_MSF_OFFSET           150              /* MSF offset of first frame */
#define CD_FRAMES               75               /* per second */
#define CDROM_LEADOUT           0xAA             /* leadout track */
#define CDROMREADTOCHDR         CDIOREADTOCHEADER
#define cdrom_tochdr            ioc_toc_header
#define cdth_trk0               starting_track
#define cdth_trk1               ending_track
#define cdrom_tocentry          cd_toc_entry
#define cdte_track              track
#define cdte_track_address      addr.lba
#define DEVICE_NAME             "/dev/cd0a"

#elif defined(__APPLE__)
#include <sys/types.h>
#include <IOKit/storage/IOCDTypes.h>
#include <IOKit/storage/IOCDMediaBSDClient.h>
#define CD_FRAMES               75               /* per second */
#define CD_MSF_OFFSET           150              /* MSF offset of first frame */
#define cdrom_tochdr            CDDiscInfo
#define cdth_trk0               numberOfFirstTrack
/* NOTE: Judging by the name here, we might have to do this:
 * hdr.lastTrackNumberInLastSessionMSB << 8 *
 * sizeof(hdr.lastTrackNumberInLastSessionLSB)
 * | hdr.lastTrackNumberInLastSessionLSB; */
#define cdth_trk1               lastTrackNumberInLastSessionLSB
#define cdrom_tocentry          CDTrackInfo
#define cdte_track_address      trackStartAddress
#define DEVICE_NAME             "/dev/rdisk1"

#elif defined(__sgi)
#include <dmedia/cdaudio.h>
#define CD_FRAMES               75               /* per second */
#define CD_MSF_OFFSET           150              /* MSF offset of first frame */
#define cdrom_tochdr            CDSTATUS
#define cdth_trk0               first
#define cdth_trk1               last
#define close                   CDclose
struct cdrom_tocentry
{
	int cdte_track_address;
};
#define DEVICE_NAME             "/dev/scsi/sc0d4l0"
#else
#error "Your OS isn't supported yet."
#endif  /* os selection */
}
using std::string_view_literals::operator""sv;

static constexpr Domain cdio_domain("cdio");

static bool default_reverse_endian;
static unsigned speed = 0;

/* Default to full paranoia, but allow skipping sectors. */
static int mode_flags = PARANOIA_MODE_FULL^PARANOIA_MODE_NEVERSKIP;

class CdioParanoiaInputStream final : public InputStream {
	cdrom_drive_t *const drv;
	CdIo_t *const cdio;
	CdromParanoia para;

	const lsn_t lsn_from;

	char buffer[CDIO_CD_FRAMESIZE_RAW];
	lsn_t buffer_lsn;

 public:
	CdioParanoiaInputStream(std::string_view _uri, Mutex &_mutex,
				cdrom_drive_t *_drv, CdIo_t *_cdio,
				bool reverse_endian,
				lsn_t _lsn_from, lsn_t lsn_to)
		:InputStream(_uri, _mutex),
		 drv(_drv), cdio(_cdio), para(drv),
		 lsn_from(_lsn_from),
		 buffer_lsn(-1)
	{
		para.SetMode(mode_flags);

		/* seek to beginning of the track */
		para.Seek(lsn_from);

		seekable = true;
		size = (lsn_to - lsn_from + 1) * CDIO_CD_FRAMESIZE_RAW;

		/* hack to make MPD select the "pcm" decoder plugin */
		SetMimeType(reverse_endian
			    ? "audio/x-mpd-cdda-pcm-reverse"
			    : "audio/x-mpd-cdda-pcm");
		SetReady();
	}

	~CdioParanoiaInputStream() override {
		para = {};
		cdio_cddap_close_no_free_cdio(drv);
		cdio_destroy(cdio);
	}

	CdioParanoiaInputStream(const CdioParanoiaInputStream &) = delete;
	CdioParanoiaInputStream &operator=(const CdioParanoiaInputStream &) = delete;

	/* virtual methods from InputStream */
	[[nodiscard]] bool IsEOF() const noexcept override;
	size_t Read(std::unique_lock<Mutex> &lock,
		    std::span<std::byte> dest) override;
	void Seek(std::unique_lock<Mutex> &lock, offset_type offset) override;
};

struct CdioUri {
	char device[64];
	int track;
};

static CdioUri
parse_cdio_uri(std::string_view src)
{
	CdioUri dest;

	src = StringAfterPrefixIgnoreCase(src, "cdda://"sv);

	const auto [device, track] = Split(src, '/');
	if (device.size() >= sizeof(dest.device))
		throw std::invalid_argument{"Device name is too long"};

	*std::copy(device.begin(), device.end(), dest.device) = '\0';

	if (!track.empty()) {
		auto value = ParseInteger<uint_least16_t>(track);
		if (!value)
			throw std::invalid_argument{"Bad track number"};

		dest.track = *value;
	} else
		/* play the whole CD */
		dest.track = -1;

	return dest;
}

static AllocatedPath
cdio_detect_device()
{
	char **devices = cdio_get_devices_with_cap(nullptr, CDIO_FS_AUDIO,
						   false);
	if (devices == nullptr)
		return nullptr;

	AtScopeExit(devices) { cdio_free_device_list(devices); };

	if (devices[0] == nullptr)
		return nullptr;

	return AllocatedPath::FromFS(devices[0]);
}

static char*
makeMusicBrainzIdWith(int firstTrack, int lastTrack, int leadIn, std::vector<int> frameOffsets)
{
	struct AVSHA* sha1 = av_sha_alloc();
	const int numBitsSha1 = 160;
	const int digestSize = numBitsSha1 / 8;
	uint8_t digest[digestSize];
	const int tempSize = 32;
	char temp[tempSize];

	av_sha_init(sha1, numBitsSha1);

	snprintf(temp, tempSize, "%02X", firstTrack);
	av_sha_update(sha1, (const uint8_t*)temp, strlen(temp));

	snprintf(temp, tempSize, "%02X", lastTrack);
	av_sha_update(sha1, (const uint8_t*)temp, strlen(temp));

	for (size_t i = 0; i < 100; ++i)
	{
		int offset = 0;

		if (i < frameOffsets.size())
			offset = frameOffsets[i] + leadIn;
		snprintf(temp, tempSize, "%08X", offset);
		av_sha_update(sha1, (const uint8_t*)temp, strlen(temp));
	}
	av_sha_final(sha1, digest);
	free(sha1);

	const int outputSize = 128;
	char *output = new char[outputSize];

	av_base64_encode(output, outputSize, digest, digestSize);

	for (size_t i = 0; i < strlen(output); ++i)
	{
		switch (output[i])
		{
		case '=':
			output[i] = '-';
			break;
		case '/':
			output[i] = '_';
			break;
		case '+':
			output[i] = '.';
			break;
		default:
			break;
		}
	}

	return output;
}

class CDDiscId
{
public:
	static char* getCurrentCDId (std::string_view uri)
	{
		const auto parsed_uri = parse_cdio_uri(uri);

		const AllocatedPath device = parsed_uri.device[0] != 0
			? AllocatedPath::FromFS(parsed_uri.device)
			: cdio_detect_device();

		if (device.IsNull())
			return nullptr;

		int len;
		int i;
		long int cksum = 0;
		//int musicbrainz = 0;
		unsigned char last = 1;
		const char *devicename = device.c_str();
		struct cdrom_tocentry *TocEntry;
#ifndef __sgi
		int drive;
		struct cdrom_tochdr hdr;
#else
		CDPLAYER *drive;
		CDTRACKINFO info;
		cdrom_tochdr hdr;
#endif
		//char *command = argv[0];

#if defined(__OpenBSD__) || defined(__NetBSD__)
		struct ioc_read_toc_entry t;
#elif defined(__APPLE__)
		dk_cd_read_disc_info_t discInfoParams;
#endif

#if defined(__sgi)
		drive = CDopen(devicename, "r");
		if (drive == 0) {
			return nullptr;
		}
#else
		drive = open(devicename, O_RDONLY | O_NONBLOCK);
		if (drive < 0) {
			return nullptr;
		}
#endif

#if defined(__APPLE__)
		memset(&discInfoParams, 0, sizeof(discInfoParams));
		discInfoParams.buffer = &hdr;
		discInfoParams.bufferLength = sizeof(hdr);
		if (ioctl(drive, DKIOCCDREADDISCINFO, &discInfoParams) < 0
				|| discInfoParams.bufferLength != sizeof(hdr)) {
			return nullptr;
		}
#elif defined(__sgi)
		if (CDgetstatus(drive, &hdr) == 0) {
			return nullptr
		}
#else
		if (ioctl(drive, CDROMREADTOCHDR, &hdr) < 0) {
			return nullptr;
		}
#endif

		last = hdr.cdth_trk1;

		len = (last + 1) * sizeof(struct cdrom_tocentry);

		TocEntry = (cdrom_tocentry*)malloc(len);
		if (!TocEntry) {
			return nullptr;
		}

#if defined(__OpenBSD__)
		t.starting_track = 0;
#elif defined(__NetBSD__)
		t.starting_track = 1;
#endif

#if defined(__OpenBSD__) || defined(__NetBSD__)
		t.address_format = CDROM_LBA;
		t.data_len = len;
		t.data = TocEntry;
		memset(TocEntry, 0, len);

		if (ioctl(drive, CDIOREADTOCENTRYS, (char*)&t) < 0) {
			return nullptr;
		}
#elif defined(__APPLE__)
		dk_cd_read_track_info_t trackInfoParams;
		memset(&trackInfoParams, 0, sizeof(trackInfoParams));
		trackInfoParams.addressType = kCDTrackInfoAddressTypeTrackNumber;
		trackInfoParams.bufferLength = sizeof(*TocEntry);

		for (i = 0; i < last; i++) {
			trackInfoParams.address = i + 1;
			trackInfoParams.buffer = &TocEntry[i];

			if (ioctl(drive, DKIOCCDREADTRACKINFO, &trackInfoParams) < 0) {
				return nullptr;
			}
		}

		/* MacOS X on G5-based systems does not report valid info for
		 * TocEntry[last-1].lastRecordedAddress + 1, so we compute the start
		 * of leadout from the start+length of the last track instead
		 */
		TocEntry[last].cdte_track_address = htonl(ntohl(TocEntry[last-1].trackSize) + ntohl(TocEntry[last-1].trackStartAddress));
#elif defined(__sgi)
		for (i = 0; i < last; i++) {
			if (CDgettrackinfo(drive, i + 1, &info) == 0) {
				return nullptr;
			}
			TocEntry[i].cdte_track_address = info.start_min*60*CD_FRAMES + info.start_sec*CD_FRAMES + info.start_frame;
		}
		TocEntry[last].cdte_track_address = TocEntry[last - 1].cdte_track_address + info.total_min*60*CD_FRAMES + info.total_sec*CD_FRAMES + info.total_frame;
#else   /* FreeBSD, Linux, Solaris */
		for (i = 0; i < last; i++) {
			/* tracks start with 1, but I must start with 0 on OpenBSD */
			TocEntry[i].cdte_track = i + 1;
			TocEntry[i].cdte_format = CDROM_LBA;
			if (ioctl(drive, CDROMREADTOCENTRY, &TocEntry[i]) < 0) {
				return nullptr;
			}
		}

		TocEntry[last].cdte_track = CDROM_LEADOUT;
		TocEntry[last].cdte_format = CDROM_LBA;
		if (ioctl(drive, CDROMREADTOCENTRY, &TocEntry[i]) < 0) {
			return nullptr;
		}
#endif

		/* release file handle */
		close(drive);

#if defined(__FreeBSD__) || defined(__DragonFly__) || defined(__APPLE__)
		TocEntry[i].cdte_track_address = ntohl(TocEntry[i].cdte_track_address);
#endif

		for (i = 0; i < last; i++) {
#if defined(__FreeBSD__) || defined(__DragonFly__) || defined(__APPLE__)
			TocEntry[i].cdte_track_address = ntohl(TocEntry[i].cdte_track_address);
#endif
			cksum += cddb_sum((TocEntry[i].cdte_track_address + CD_MSF_OFFSET) / CD_FRAMES);
		}

		/*
		 *totaltime = ((TocEntry[last].cdte_track_address + CD_MSF_OFFSET) / CD_FRAMES) -
		 *    ((TocEntry[0].cdte_track_address + CD_MSF_OFFSET) / CD_FRAMES);
		 */

		/*
		 *[> print discid <]
		 *if (!musicbrainz)
		 *    printf("%08lx ", (cksum % 0xff) << 24 | totaltime << 8 | last);
		 */

		/* print number of tracks */
		//printf("%d", last);
		int numTracks = last;
		int firstTrackNumber = 1;

		std::vector<int> frameOffsets;

		if (last > 0)
			frameOffsets.push_back(TocEntry[last].cdte_track_address);

		/* print frame offsets of all tracks */
		for (i = 0; i < last; i++)
		{
			//printf(" %d", TocEntry[i].cdte_track_address + CD_MSF_OFFSET);
			frameOffsets.push_back(TocEntry[i].cdte_track_address);
		}

		free(TocEntry);

		int leadIn = CDIO_PREGAP_SECTORS;
		int lastTrack = numTracks + firstTrackNumber - 1;

		auto musicId = makeMusicBrainzIdWith(firstTrackNumber, lastTrack, leadIn, frameOffsets);

		FmtDebug(cdio_domain, "music id from cache: {}", musicId);
		return musicId;
	}
private:
	static int cddb_sum(int n)
	{
		/* a number like 2344 becomes 2+3+4+4 (13) */
		int ret = 0;

		while (n > 0) {
			ret = ret + (n % 10);
			n = n / 10;
		}

		return ret;
	}
};

class CDTagsXmlCache
: public StringCurlResponseHandler
{
public:
	CDTagsXmlCache (EventLoop &event_loop)
	: curl(event_loop)
	{
	}

	virtual ~CDTagsXmlCache ()
	{
		deleteAndClearTracks();
	}

public:
	struct TrackInfo
	{
		int trackNum = -99;
		std::string title;
		std::string artist;
		std::string albumTitle;

		std::string toString () const
		{
			return title + ", " + artist + ", " + albumTitle;
		}
	};

public:
	class Listener
	{
	public: // CDTagsXmlCache::Listener
		virtual void setTags (CDTagsXmlCache::TrackInfo& trackInfo) = 0;
	};

public: // CurlResponseHandler
	/* virtual methods from CurlResponseHandler */
	void OnEnd() override
	{
		auto resp = StringCurlResponseHandler::GetResponse();
		std::string body = resp.body;

		makeTrackInfoFromXml(body);
		dataReady = true;

		/*
		 *callListeners();
		 */
	}

	void OnError(std::exception_ptr ) noexcept override
	{
	}

public:
	void requestTags (std::string_view& uri, Listener *listener)
	{
		const std::scoped_lock lock{mutex};

		if (insertedCdChanged(uri))
		{
			deleteAndClearTracks();
			requestMusicBrainzTags();
		}
		FmtDebug(cdio_domain, "requesting uri: {}", uri);
		const char* uriPrefix = "cdda:///";

		if (strlen(uri.data()) > strlen(uriPrefix))
		{
			int trackNum = atoi(uri.data() + strlen(uriPrefix));
			listeners[trackNum].insert(listener);
		}
	}

	void fillTrackInfo (int trackNum, TrackInfo& info)
	{
		const std::scoped_lock lock{mutex};

		auto it = listeners.find(trackNum);

		if (it != listeners.end())
		{
			for (auto listener : it->second)
				listener->setTags(info);
			listeners.erase(it);
		}
	}

	void cancelRequest (Listener* listener)
	{
		const std::scoped_lock lock{mutex};

		for (auto it : listeners)
		{
			auto lit = it.second.find(listener);

			if (lit != it.second.end())
				it.second.erase(lit);
		}
	}

	bool insertedCdChanged (std::string_view uri)
	{
		char *cdId = CDDiscId::getCurrentCDId(uri);

		if (cdId == nullptr)
		{
			FmtDebug(cdio_domain, "no cdid \\o/");
			return true;
		}

		if (lastCdId != nullptr && strcmp(cdId, lastCdId) == 0)
		{
			delete [] cdId;
			return false;
		}
		if (lastCdId != nullptr)
			delete [] lastCdId;
		lastCdId = cdId;
		return true;
	}

	void deleteAndClearTracks ()
	{
		if (request != nullptr)
			request->StopIndirect();
		for (auto track : tracks)
			delete track.second;
		tracks.clear();
	}

	void requestMusicBrainzTags()
	{
		if (lastCdId == nullptr || strlen(lastCdId) == 0)
			return ;

		// generate url
		std::string urlPrefix("https://musicbrainz.org/ws/2/discid/");
		std::string urlArgs("?inc=artist-credits+recordings");
		std::string url = urlPrefix + std::string(lastCdId) + urlArgs;

		// launch curl request
		if (request != nullptr)
			delete request;
		request = new CurlRequest(*curl, url.c_str(), *(StringCurlResponseHandler*)this);
		request->StartIndirect();
	}

	void makeTrackInfoFromXml (std::string body)
	{
		IXML_Document *document = ixmlParseBuffer(body.c_str());
		std::string albumTitle;

		if (document != nullptr)
		{
			IXML_NodeList *releaseNode = ixmlDocument_getElementsByTagName(document, "release");

			if (releaseNode != nullptr && releaseNode->nodeItem != nullptr)
			{
				auto releaseInfoNode = ixmlNode_getChildNodes(releaseNode->nodeItem);

				while (releaseInfoNode != nullptr && releaseInfoNode->nodeItem != nullptr)
				{
					auto nodeName = ixmlNode_getNodeName(releaseInfoNode->nodeItem);

					if (strcmp(nodeName, "title") == 0)
					{
						auto value = ixmlNode_getNodeValue(ixmlNode_getFirstChild(releaseInfoNode->nodeItem));

						if (value == nullptr)
						{
							FmtDebug(cdio_domain, "no value");
							return ;
						}
						albumTitle = value;
						FmtDebug(cdio_domain, "album: {}", albumTitle);
						break;
					}
					releaseInfoNode = releaseInfoNode->next;
				}
			}

			IXML_NodeList *trackListNode = ixmlDocument_getElementsByTagName(document, "track-list");
			
			if (trackListNode != nullptr && trackListNode->nodeItem != nullptr)
			{
				FmtDebug(cdio_domain, "track-list node found");

				IXML_NodeList *tracksNode = ixmlNode_getChildNodes(trackListNode->nodeItem);

				while (tracksNode != nullptr && tracksNode->nodeItem != nullptr)
				{
					TrackInfo *trackInfo = new TrackInfo;
					IXML_NodeList *trackNode = ixmlNode_getChildNodes(tracksNode->nodeItem);

					while (trackNode != nullptr && trackNode->nodeItem != nullptr)
					{
						auto nodeName = ixmlNode_getNodeName(trackNode->nodeItem);

						if (strcmp(nodeName, "recording") == 0)
						{
							auto recordNode = ixmlNode_getChildNodes(trackNode->nodeItem);

							while (recordNode != nullptr && recordNode->nodeItem != nullptr)
							{
								auto childName = ixmlNode_getNodeName(recordNode->nodeItem);

								if (strcmp(childName, "title") == 0)
								{
									auto title = ixmlNode_getNodeValue(ixmlNode_getFirstChild(recordNode->nodeItem));
									trackInfo->title = std::string(title);
								}
								else if (strcmp(childName, "artist-credit") == 0)
								{
									auto nameCredit = ixmlNode_getChildNodes(recordNode->nodeItem);

									if (nameCredit != nullptr && nameCredit->nodeItem != nullptr)
									{
										auto artistNode = ixmlNode_getChildNodes(nameCredit->nodeItem);

										if (artistNode != nullptr && artistNode->nodeItem != nullptr)
										{
											auto artistInfoNode = ixmlNode_getChildNodes(artistNode->nodeItem);

											while (artistInfoNode != nullptr && artistInfoNode->nodeItem != nullptr)
											{
												auto artistInfoName = ixmlNode_getNodeName(artistInfoNode->nodeItem);

												if (strcmp(artistInfoName, "name") == 0)
												{
													auto artist = ixmlNode_getNodeValue(ixmlNode_getFirstChild(artistInfoNode->nodeItem));
													trackInfo->artist = std::string(artist);
												}
												artistInfoNode = artistInfoNode->next;
											}
										}

									}
								}

								recordNode = recordNode->next;
							}
						}
						else if (strcmp(nodeName, "number") == 0)
						{
							auto value = ixmlNode_getNodeValue(ixmlNode_getFirstChild(trackNode->nodeItem));

							trackInfo->trackNum = atoi(value);
						}
						trackNode = trackNode->next;
					}
					if (trackInfo->trackNum != -99)
					{
						trackInfo->albumTitle = albumTitle;
						FmtDebug(cdio_domain, "trackInfo {}, {}", trackInfo->trackNum, trackInfo->toString());
						tracks[trackInfo->trackNum] = trackInfo;
					}
					else
					{
						delete trackInfo;
					}
					
					tracksNode = tracksNode->next;
				}
			}

			ixmlDocument_free(document);
		}
	}

public:
	static void deleteInstance ()
	{
		if (instance != nullptr)
			delete instance;
		instance = nullptr;
	}

	static void createInstance (EventLoop &event_loop)
	{
		instance = new CDTagsXmlCache(event_loop);
	}

	static CDTagsXmlCache* getInstance ()
	{
		return instance;
	}

private:
	const char* lastCdId = nullptr;
	std::map<int, TrackInfo*> tracks;

	static CDTagsXmlCache *instance;

	std::map<int, std::set<Listener*> > listeners;
	Mutex mutex;
	CurlInit curl;
	CurlRequest* request = nullptr;
	bool curlRequested = false;
	bool dataReady = false;
};

CDTagsXmlCache* CDTagsXmlCache::instance = nullptr;

class MusicBrainzTagScanner final
: public RemoteTagScanner
, public CDTagsXmlCache::Listener
{
	RemoteTagHandler &handler;
	std::string_view uri;

public:
	MusicBrainzTagScanner(std::string_view _uri,
			RemoteTagHandler &_handler)
	: handler(_handler)
	, uri(_uri)  
	{
	}

	~MusicBrainzTagScanner() noexcept override
	{
	}

public: // CDTagsXmlCache::Listener
	virtual void setTags (CDTagsXmlCache::TrackInfo& trackInfo) override
	{
		FmtDebug(cdio_domain, "track title: {}", trackInfo.title);
	}

private:
	void Start() noexcept override {
		CDTagsXmlCache::getInstance()->requestTags(uri, this);
	}
};

static void
input_cdio_init(EventLoop &event_loop, const ConfigBlock &block)
{
	const char *value = block.GetBlockValue("default_byte_order");
	if (value != nullptr) {
		if (strcmp(value, "little_endian") == 0)
			default_reverse_endian = IsBigEndian();
		else if (strcmp(value, "big_endian") == 0)
			default_reverse_endian = IsLittleEndian();
		else
			throw FmtRuntimeError("Unrecognized 'default_byte_order' setting: {}",
					      value);
	}
	speed = block.GetBlockValue("speed",0U);

	if (const auto *param = block.GetBlockParam("mode")) {
		param->With([](const char *s){
			if (StringIsEqual(s, "disable"))
				mode_flags = PARANOIA_MODE_DISABLE;
			else if (StringIsEqual(s, "overlap"))
				mode_flags = PARANOIA_MODE_OVERLAP;
			else if (StringIsEqual(s, "full"))
				mode_flags = PARANOIA_MODE_FULL;
			else
				throw std::invalid_argument{"Invalid paranoia mode"};
		});
	}

	if (const auto *param = block.GetBlockParam("skip")) {
		if (param->GetBoolValue())
			mode_flags &= ~PARANOIA_MODE_NEVERSKIP;
		else
			mode_flags |= PARANOIA_MODE_NEVERSKIP;
	}
	CDTagsXmlCache::createInstance(event_loop);
}

static void
input_cdio_finish() noexcept
{
	CDTagsXmlCache::deleteInstance();
}

static InputStreamPtr
input_cdio_open(std::string_view uri,
		Mutex &mutex)
{
	const auto parsed_uri = parse_cdio_uri(uri);

	/* get list of CD's supporting CD-DA */
	const AllocatedPath device = parsed_uri.device[0] != 0
		? AllocatedPath::FromFS(parsed_uri.device)
		: cdio_detect_device();
	if (device.IsNull())
		throw std::runtime_error("Unable find or access a CD-ROM drive with an audio CD in it.");

	/* Found such a CD-ROM with a CD-DA loaded. Use the first drive in the list. */
	const auto cdio = cdio_open(device.c_str(), DRIVER_UNKNOWN);
	if (cdio == nullptr)
		throw std::runtime_error("Failed to open CD drive");

	const auto drv = cdio_cddap_identify_cdio(cdio, 1, nullptr);
	if (drv == nullptr) {
		cdio_destroy(cdio);
		throw std::runtime_error("Unable to identify audio CD disc.");
	}

	cdio_cddap_verbose_set(drv, CDDA_MESSAGE_FORGETIT, CDDA_MESSAGE_FORGETIT);

	if (0 != cdio_cddap_open(drv)) {
		cdio_cddap_close_no_free_cdio(drv);
		cdio_destroy(cdio);
		throw std::runtime_error("Unable to open disc.");
	}

	if (speed > 0) {
		FmtDebug(cdio_domain, "Attempting to set CD speed to {}x",
			 speed);
		/* Negative value indicate error (e.g. -405: not supported) */
		if (cdio_cddap_speed_set(drv,speed) < 0)
			FmtDebug(cdio_domain, "Failed to set CD speed to {}x",
				 speed);
	}

	bool reverse_endian;
	const int be = data_bigendianp(drv);
	switch (be) {
	case -1:
		LogDebug(cdio_domain, "drive returns unknown audio data");
		reverse_endian = default_reverse_endian;
		break;

	case 0:
		LogDebug(cdio_domain, "drive returns audio data Little Endian");
		reverse_endian = IsBigEndian();
		break;

	case 1:
		LogDebug(cdio_domain, "drive returns audio data Big Endian");
		reverse_endian = IsLittleEndian();
		break;

	default:
		cdio_cddap_close_no_free_cdio(drv);
		cdio_destroy(cdio);
		throw FmtRuntimeError("Drive returns unknown data type {}",
				      be);
	}

	lsn_t lsn_from, lsn_to;
	if (parsed_uri.track >= 0) {
		lsn_from = cdio_cddap_track_firstsector(drv, parsed_uri.track);
		lsn_to = cdio_cddap_track_lastsector(drv, parsed_uri.track);
	} else {
		lsn_from = cdio_cddap_disc_firstsector(drv);
		lsn_to = cdio_cddap_disc_lastsector(drv);
	}

	/* LSNs < 0 indicate errors (e.g. -401: Invaid track, -402: no pregap) */
	if(lsn_from < 0 || lsn_to < 0)
		throw FmtRuntimeError("Error {} on track {}",
				      lsn_from < 0 ? lsn_from : lsn_to, parsed_uri.track);

	/* Only check for audio track if not pregap or whole CD */
	if (!cdio_cddap_track_audiop(drv, parsed_uri.track) && parsed_uri.track > 0)
		throw FmtRuntimeError("No audio track: {}",
				      parsed_uri.track);

	return std::make_unique<CdioParanoiaInputStream>(uri, mutex,
							 drv, cdio,
							 reverse_endian,
							 lsn_from, lsn_to);
}

void
CdioParanoiaInputStream::Seek(std::unique_lock<Mutex> &,
			      offset_type new_offset)
{
	if (new_offset > size)
		throw FmtRuntimeError("Invalid offset to seek {} ({})",
				      new_offset, size);

	/* simple case */
	if (new_offset == offset)
		return;

	/* calculate current LSN */
	const lsn_t lsn_relofs = new_offset / CDIO_CD_FRAMESIZE_RAW;

	if (lsn_relofs != buffer_lsn) {
		const ScopeUnlock unlock(mutex);
		para.Seek(lsn_from + lsn_relofs);
	}

	offset = new_offset;
}

size_t
CdioParanoiaInputStream::Read(std::unique_lock<Mutex> &,
			      std::span<std::byte> dest)
{
	/* end of track ? */
	if (IsEOF())
		return 0;

	//current sector was changed ?
	const int16_t *rbuf;

	const lsn_t lsn_relofs = offset / CDIO_CD_FRAMESIZE_RAW;
	const std::size_t diff = offset % CDIO_CD_FRAMESIZE_RAW;

	if (lsn_relofs != buffer_lsn) {
		const ScopeUnlock unlock(mutex);

		try {
			rbuf = para.Read().data();
		} catch (...) {
			char *s_err = cdio_cddap_errors(drv);
			if (s_err) {
				FmtError(cdio_domain,
					 "paranoia_read: {}", s_err);
				cdio_cddap_free_messages(s_err);
			}

			throw;
		}

		//store current buffer
		memcpy(buffer, rbuf, CDIO_CD_FRAMESIZE_RAW);
		buffer_lsn = lsn_relofs;
	} else {
		//use cached sector
		rbuf = (const int16_t *)buffer;
	}

	const size_t maxwrite = CDIO_CD_FRAMESIZE_RAW - diff;  //# of bytes pending in current buffer
	const std::size_t nbytes = std::min(dest.size(), maxwrite);

	//skip diff bytes from this lsn
	memcpy(dest.data(), ((const char *)rbuf) + diff, nbytes);

	//update offset
	offset += nbytes;

	return nbytes;
}

bool
CdioParanoiaInputStream::IsEOF() const noexcept
{
	return offset >= size;
}

static std::unique_ptr<RemoteTagScanner>
musicbrainz_tags (std::string_view uri, RemoteTagHandler &handler)
{
	return std::make_unique<MusicBrainzTagScanner>(uri, handler);
}

static constexpr const char *cdio_paranoia_prefixes[] = {
	"cdda://",
	nullptr
};

const InputPlugin input_plugin_cdio_paranoia = {
	"cdio_paranoia",
	cdio_paranoia_prefixes,
	input_cdio_init,
	input_cdio_finish,
	input_cdio_open,
	nullptr,
	musicbrainz_tags,
};
