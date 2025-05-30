// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright The Music Player Daemon Project

#pragma once

#include "db/Features.hxx" // for ENABLE_DATABASE

#include <cstddef>

class IClient;
class Database;
class Storage;
class DetachedSong;
class Path;
struct LocatedUri;

/**
 * A utility class that loads a #DetachedSong object by its URI.  If
 * the URI is an absolute local file, it applies security checks via
 * Client::AllowFile().  If no #Client pointer was specified, then it
 * is assumed that all local files are allowed.
 */
class SongLoader {
	const IClient *const client;

#ifdef ENABLE_DATABASE
	const Database *const db;
	Storage *const storage;
#endif

public:
#ifdef ENABLE_DATABASE
	explicit SongLoader(const IClient &_client) noexcept;
	SongLoader(const Database *_db, Storage *_storage) noexcept
		:client(nullptr), db(_db), storage(_storage) {}
	SongLoader(const IClient &_client, const Database *_db,
		   Storage *_storage) noexcept
		:client(&_client), db(_db), storage(_storage) {}
#else
	explicit SongLoader(const IClient &_client) noexcept
		:client(&_client) {}
	explicit SongLoader(std::nullptr_t, std::nullptr_t) noexcept
		:client(nullptr) {}
#endif

#ifdef ENABLE_DATABASE
	Storage *GetStorage() const noexcept {
		return storage;
	}
#endif

	DetachedSong LoadSong(const LocatedUri &uri) const;

	/**
	 * Throws #std::runtime_error on error.
	 */
	[[gnu::nonnull]]
	DetachedSong LoadSong(const char *uri_utf8) const;

private:
	[[gnu::nonnull]]
	DetachedSong LoadFromDatabase(const char *uri) const;

	[[gnu::nonnull]]
	DetachedSong LoadFile(const char *path_utf8, Path path_fs) const;
};
