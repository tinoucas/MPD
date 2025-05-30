// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright The Music Player Daemon Project

#include "HwSetup.hxx"
#include "Error.hxx"
#include "Format.hxx"
#include "lib/fmt/AudioFormatFormatter.hxx"
#include "lib/fmt/ToBuffer.hxx"
#include "lib/fmt/RuntimeError.hxx"
#include "util/ByteOrder.hxx"
#include "util/Domain.hxx"
#include "pcm/AudioFormat.hxx"
#include "pcm/Features.h" // for ENABLE_DSD
#include "Log.hxx"

static constexpr Domain alsa_output_domain("alsa_output");

namespace Alsa {

/**
 * Attempts to configure the specified sample format.  On failure,
 * fall back to the packed version.
 */
static int
TryFormatOrPacked(snd_pcm_t *pcm, snd_pcm_hw_params_t *hwparams,
		  snd_pcm_format_t fmt, PcmExport::Params &params)
{
	int err = snd_pcm_hw_params_set_format(pcm, hwparams, fmt);
	if (err == 0)
		params.pack24 = false;

	if (err != -EINVAL)
		return err;

	fmt = PackAlsaPcmFormat(fmt);
	if (fmt == SND_PCM_FORMAT_UNKNOWN)
		return -EINVAL;

	err = snd_pcm_hw_params_set_format(pcm, hwparams, fmt);
	if (err == 0)
		params.pack24 = true;

	return err;
}

/**
 * Attempts to configure the specified sample format, and tries the
 * reversed host byte order if was not supported.
 */
static int
TryFormatOrByteSwap(snd_pcm_t *pcm, snd_pcm_hw_params_t *hwparams,
		    snd_pcm_format_t fmt,
		    PcmExport::Params &params)
{
	int err = TryFormatOrPacked(pcm, hwparams, fmt, params);
	if (err == 0)
		params.reverse_endian = false;

	if (err != -EINVAL)
		return err;

	fmt = ByteSwapAlsaPcmFormat(fmt);
	if (fmt == SND_PCM_FORMAT_UNKNOWN)
		return -EINVAL;

	err = TryFormatOrPacked(pcm, hwparams, fmt, params);
	if (err == 0)
		params.reverse_endian = true;

	return err;
}

/**
 * Attempts to configure the specified sample format.  On DSD_U8
 * failure, attempt to switch to DSD_U32 or DSD_U16.
 */
static int
TryFormatDsd(snd_pcm_t *pcm, snd_pcm_hw_params_t *hwparams,
	     snd_pcm_format_t fmt, PcmExport::Params &params)
{
	int err = TryFormatOrByteSwap(pcm, hwparams, fmt, params);

#ifdef ENABLE_DSD
	if (err == -EINVAL && fmt == SND_PCM_FORMAT_DSD_U8) {
		/* attempt to switch to DSD_U32 */
		fmt = IsLittleEndian()
			? SND_PCM_FORMAT_DSD_U32_LE
			: SND_PCM_FORMAT_DSD_U32_BE;
		err = TryFormatOrByteSwap(pcm, hwparams, fmt, params);
		if (err == 0)
			params.dsd_mode = PcmExport::DsdMode::U32;
		else
			fmt = SND_PCM_FORMAT_DSD_U8;
	}

	if (err == -EINVAL && fmt == SND_PCM_FORMAT_DSD_U8) {
		/* attempt to switch to DSD_U16 */
		fmt = IsLittleEndian()
			? SND_PCM_FORMAT_DSD_U16_LE
			: SND_PCM_FORMAT_DSD_U16_BE;
		err = TryFormatOrByteSwap(pcm, hwparams, fmt, params);
		if (err == 0)
			params.dsd_mode = PcmExport::DsdMode::U16;
		else
			fmt = SND_PCM_FORMAT_DSD_U8;
	}
#endif

	return err;
}

static int
TryFormat(snd_pcm_t *pcm, snd_pcm_hw_params_t *hwparams,
	  SampleFormat sample_format,
	  PcmExport::Params &params)
{
	snd_pcm_format_t alsa_format = ToAlsaPcmFormat(sample_format);
	if (alsa_format == SND_PCM_FORMAT_UNKNOWN)
		return -EINVAL;

	return TryFormatDsd(pcm, hwparams, alsa_format, params);
}

/**
 * Configure a sample format, and probe other formats if that fails.
 */
static int
SetupSampleFormat(snd_pcm_t *pcm, snd_pcm_hw_params_t *hwparams,
		  SampleFormat &sample_format,
		  PcmExport::Params &params)
{
	/* try the input format first */

	int err = TryFormat(pcm, hwparams, sample_format, params);

	/* if unsupported by the hardware, try other formats */

	static constexpr SampleFormat probe_formats[] = {
		SampleFormat::S24_P32,
		SampleFormat::S32,
		SampleFormat::S16,
		SampleFormat::S8,
		SampleFormat::UNDEFINED,
	};

	for (unsigned i = 0;
	     err == -EINVAL && probe_formats[i] != SampleFormat::UNDEFINED;
	     ++i) {
		const SampleFormat mpd_format = probe_formats[i];
		if (mpd_format == sample_format)
			continue;

		err = TryFormat(pcm, hwparams, mpd_format, params);
		if (err == 0)
			sample_format = mpd_format;
	}

	return err;
}

HwResult
SetupHw(snd_pcm_t *pcm,
	unsigned buffer_time, unsigned period_time,
	AudioFormat &audio_format, PcmExport::Params &params)
{
	snd_pcm_hw_params_t *hwparams;
	snd_pcm_hw_params_alloca(&hwparams);

	int err;
	unsigned int period_time_ro = period_time;

	/* configure HW params */
	err = snd_pcm_hw_params_any(pcm, hwparams);
	if (err < 0)
		throw Alsa::MakeError(err, "snd_pcm_hw_params_any() failed");

	err = snd_pcm_hw_params_set_access(pcm, hwparams,
					   SND_PCM_ACCESS_RW_INTERLEAVED);
	if (err < 0)
		throw Alsa::MakeError(err, "snd_pcm_hw_params_set_access() failed");

	err = SetupSampleFormat(pcm, hwparams,
				audio_format.format, params);
	if (err < 0)
		throw Alsa::MakeError(err,
				      FmtBuffer<256>("Failed to configure format {}",
						     audio_format.format));

	unsigned int channels = audio_format.channels;
	err = snd_pcm_hw_params_set_channels_near(pcm, hwparams,
						  &channels);
	if (err < 0)
		throw Alsa::MakeError(err,
				      FmtBuffer<256>("Failed to configure {} channels",
						     audio_format.channels));

	audio_format.channels = (int8_t)channels;

	const unsigned requested_sample_rate =
		params.CalcOutputSampleRate(audio_format.sample_rate);
	unsigned output_sample_rate = requested_sample_rate;

	err = snd_pcm_hw_params_set_rate_near(pcm, hwparams,
					      &output_sample_rate, nullptr);
	if (err < 0)
		throw Alsa::MakeError(err,
				      FmtBuffer<256>("Failed to configure sample rate {} Hz",
						     requested_sample_rate));

	if (output_sample_rate == 0)
		throw FmtRuntimeError("Failed to configure sample rate {} Hz",
				      audio_format.sample_rate);

	if (output_sample_rate != requested_sample_rate)
		audio_format.sample_rate = params.CalcInputSampleRate(output_sample_rate);

	snd_pcm_uframes_t buffer_size_min, buffer_size_max;
	snd_pcm_hw_params_get_buffer_size_min(hwparams, &buffer_size_min);
	snd_pcm_hw_params_get_buffer_size_max(hwparams, &buffer_size_max);
	unsigned buffer_time_min, buffer_time_max;
	snd_pcm_hw_params_get_buffer_time_min(hwparams, &buffer_time_min, nullptr);
	snd_pcm_hw_params_get_buffer_time_max(hwparams, &buffer_time_max, nullptr);
	FmtDebug(alsa_output_domain, "buffer: size={}..{} time={}..{}",
		 buffer_size_min, buffer_size_max,
		 buffer_time_min, buffer_time_max);

	snd_pcm_uframes_t period_size_min, period_size_max;
	snd_pcm_hw_params_get_period_size_min(hwparams, &period_size_min, nullptr);
	snd_pcm_hw_params_get_period_size_max(hwparams, &period_size_max, nullptr);
	unsigned period_time_min, period_time_max;
	snd_pcm_hw_params_get_period_time_min(hwparams, &period_time_min, nullptr);
	snd_pcm_hw_params_get_period_time_max(hwparams, &period_time_max, nullptr);
	FmtDebug(alsa_output_domain, "period: size={}..{} time={}..{}",
		 period_size_min, period_size_max,
		 period_time_min, period_time_max);

	if (buffer_time > 0) {
		err = snd_pcm_hw_params_set_buffer_time_near(pcm, hwparams,
							     &buffer_time, nullptr);
		if (err < 0)
			throw Alsa::MakeError(err, "snd_pcm_hw_params_set_buffer_time_near() failed");
	} else {
		err = snd_pcm_hw_params_get_buffer_time(hwparams, &buffer_time,
							nullptr);
		if (err < 0)
			buffer_time = 0;
	}

	if (period_time_ro == 0 && buffer_time >= 10000) {
		period_time_ro = period_time = buffer_time / 4;

		FmtDebug(alsa_output_domain,
			 "default period_time = buffer_time/4 = {}/4 = {}",
			 buffer_time, period_time);
	}

	if (period_time_ro > 0) {
		period_time = period_time_ro;
		err = snd_pcm_hw_params_set_period_time_near(pcm, hwparams,
							     &period_time, nullptr);
		if (err < 0)
			throw Alsa::MakeError(err, "snd_pcm_hw_params_set_period_time_near() failed");
	}

	err = snd_pcm_hw_params(pcm, hwparams);
	if (err < 0)
		throw Alsa::MakeError(err, "snd_pcm_hw_params() failed");

	HwResult result;

	err = snd_pcm_hw_params_get_format(hwparams, &result.format);
	if (err < 0)
		throw Alsa::MakeError(err, "snd_pcm_hw_params_get_format() failed");

	err = snd_pcm_hw_params_get_buffer_size(hwparams, &result.buffer_size);
	if (err < 0)
		throw Alsa::MakeError(err, "snd_pcm_hw_params_get_buffer_size() failed");

	err = snd_pcm_hw_params_get_period_size(hwparams, &result.period_size,
						nullptr);
	if (err < 0)
		throw Alsa::MakeError(err, "snd_pcm_hw_params_get_period_size() failed");

	return result;
}

} // namespace Alsa
