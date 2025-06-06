// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright The Music Player Daemon Project

#include "ConfiguredResampler.hxx"
#include "FallbackResampler.hxx"
#include "pcm/Features.h" // for ENABLE_LIBSAMPLERATE, ENABLE_SOXR
#include "config/Data.hxx"
#include "config/Option.hxx"
#include "config/Block.hxx"
#include "config/Param.hxx"
#include "lib/fmt/RuntimeError.hxx"

#ifdef ENABLE_LIBSAMPLERATE
#include "LibsamplerateResampler.hxx"
#endif

#ifdef ENABLE_SOXR
#include "SoxrResampler.hxx"
#endif

#include <cassert>
#include <utility> // for std::unreachable()

#include <string.h>

enum class SelectedResampler {
	FALLBACK,

#ifdef ENABLE_LIBSAMPLERATE
	LIBSAMPLERATE,
#endif

#ifdef ENABLE_SOXR
	SOXR,
#endif
};

static SelectedResampler selected_resampler = SelectedResampler::FALLBACK;

static const ConfigBlock *
MakeResamplerDefaultConfig(ConfigBlock &block) noexcept
{
	assert(block.IsEmpty());

#ifdef ENABLE_LIBSAMPLERATE
	block.AddBlockParam("plugin", "libsamplerate");
#elif defined(ENABLE_SOXR)
	block.AddBlockParam("plugin", "soxr");
#else
	block.AddBlockParam("plugin", "internal");
#endif
	return &block;
}

/**
 * Convert the old "samplerate_converter" setting to a new-style
 * "resampler" block.
 */
static const ConfigBlock *
MigrateResamplerConfig(const ConfigParam &param, ConfigBlock &block) noexcept
{
	assert(block.IsEmpty());

	block.line = param.line;

	const char *converter = param.value.c_str();
	if (*converter == 0 || strcmp(converter, "internal") == 0) {
		block.AddBlockParam("plugin", "internal");
		return &block;
	}

#ifdef ENABLE_SOXR
	if (strcmp(converter, "soxr") == 0) {
		block.AddBlockParam("plugin", "soxr");
		return &block;
	}

	if (memcmp(converter, "soxr ", 5) == 0) {
		block.AddBlockParam("plugin", "soxr");
		block.AddBlockParam("quality", converter + 5);
		return &block;
	}
#endif

	block.AddBlockParam("plugin", "libsamplerate");
	block.AddBlockParam("type", converter);
	return &block;
}

static const ConfigBlock *
MigrateResamplerConfig(const ConfigParam *param, ConfigBlock &buffer) noexcept
{
	assert(buffer.IsEmpty());

	return param == nullptr
		? MakeResamplerDefaultConfig(buffer)
		: MigrateResamplerConfig(*param, buffer);
}

static const ConfigBlock *
GetResamplerConfig(const ConfigData &config, ConfigBlock &buffer)
{
	const auto *old_param =
		config.GetParam(ConfigOption::SAMPLERATE_CONVERTER);
	const auto *block = config.GetBlock(ConfigBlockOption::RESAMPLER);
	if (block == nullptr)
		return MigrateResamplerConfig(old_param, buffer);

	if (old_param != nullptr)
		throw FmtRuntimeError("Cannot use both 'resampler' (line {}) and 'samplerate_converter' (line {})",
				      block->line, old_param->line);

	block->SetUsed();
	return block;
}

void
pcm_resampler_global_init(const ConfigData &config)
{
	ConfigBlock buffer;
	const auto *block = GetResamplerConfig(config, buffer);

	const char *plugin_name = block->GetBlockValue("plugin");
	if (plugin_name == nullptr)
		throw FmtRuntimeError("'plugin' missing in line {}",
				      block->line);

	if (strcmp(plugin_name, "internal") == 0) {
		selected_resampler = SelectedResampler::FALLBACK;
#ifdef ENABLE_SOXR
	} else if (strcmp(plugin_name, "soxr") == 0) {
		selected_resampler = SelectedResampler::SOXR;
		pcm_resample_soxr_global_init(*block);
#endif
#ifdef ENABLE_LIBSAMPLERATE
	} else if (strcmp(plugin_name, "libsamplerate") == 0) {
		selected_resampler = SelectedResampler::LIBSAMPLERATE;
		pcm_resample_lsr_global_init(*block);
#endif
	} else {
		throw FmtRuntimeError("No such resampler plugin: {}",
				      plugin_name);
	}
}

PcmResampler *
pcm_resampler_create()
{
	switch (selected_resampler) {
	case SelectedResampler::FALLBACK:
		return new FallbackPcmResampler();

#ifdef ENABLE_LIBSAMPLERATE
	case SelectedResampler::LIBSAMPLERATE:
		return new LibsampleratePcmResampler();
#endif

#ifdef ENABLE_SOXR
	case SelectedResampler::SOXR:
		return new SoxrPcmResampler();
#endif
	}

	std::unreachable();
}
