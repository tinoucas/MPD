// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright The Music Player Daemon Project

#include "PcmChannels.hxx"
#include "ChannelDefs.hxx"
#include "Buffer.hxx"
#include "Silence.hxx"
#include "Traits.hxx"
#include "pcm/Features.h" // for ENABLE_DSD

#include <array>
#include <algorithm>
#include <cassert>

template<typename D, typename S>
static void
MonoToStereo(D dest, S src) noexcept
{
	for (const auto value : src) {
		*dest++ = value;
		*dest++ = value;
	}

}

template<SampleFormat F, ArithmeticSampleTraits Traits=SampleTraits<F>>
static typename Traits::value_type
StereoToMono(typename Traits::value_type _a,
	     typename Traits::value_type _b) noexcept
{
	typename Traits::sum_type a(_a);
	typename Traits::sum_type b(_b);

	return typename Traits::value_type((a + b) / 2);
}

template<SampleFormat F, AnySampleTraits Traits=SampleTraits<F>>
static typename Traits::value_type
StereoToMono(typename Traits::value_type _a,
	     [[maybe_unused]] typename Traits::value_type _b) noexcept
	requires(!ArithmeticSampleTraits<Traits>)
{
	/* this fallback specialization discards the second channel;
	   it is only implemented for DSD, and this static_assert
	   makes sure it's never used for anything else */
	static_assert(F == SampleFormat::DSD);
	return _a;
}

template<SampleFormat F, AnySampleTraits Traits=SampleTraits<F>>
static typename Traits::pointer
StereoToMono(typename Traits::pointer dest,
	     std::span<const typename Traits::value_type> _src) noexcept
{
	for (auto src = _src.begin(), end = _src.end(); src != end;) {
		const auto a = *src++;
		const auto b = *src++;

		*dest++ = StereoToMono<F, Traits>(a, b);
	}

	return dest;
}

template<SampleFormat F, ArithmeticSampleTraits Traits=SampleTraits<F>>
static typename Traits::pointer
NToStereo(typename Traits::pointer dest,
	  unsigned src_channels,
	  std::span<const typename Traits::value_type> _src) noexcept
{
	assert(_src.size() % src_channels == 0);

	for (auto src = _src.begin(), end = _src.end(); src != end;) {
		typename Traits::sum_type sum = *src++;
		for (unsigned c = 1; c < src_channels; ++c)
			sum += *src++;

		typename Traits::value_type value(sum / int(src_channels));

		/* TODO: this is actually only mono ... */
		*dest++ = value;
		*dest++ = value;
	}

	return dest;
}

template<SampleFormat F, AnySampleTraits Traits=SampleTraits<F>>
static typename Traits::pointer
NToStereo(typename Traits::pointer dest,
	  unsigned src_channels,
	  std::span<const typename Traits::value_type> _src) noexcept
	requires(!ArithmeticSampleTraits<Traits>)
{
	/* this fallback specialization discards all but the first two
	   channels; it is only implemented for DSD, and this
	   static_assert makes sure it's never used for anything
	   else */
	static_assert(F == SampleFormat::DSD);

	assert(_src.size() % src_channels == 0);

	for (auto src = _src.begin(), end = _src.end(); src != end;) {
		*dest++ = *src++;
		*dest++ = *src++;
		src += src_channels - 2;
	}

	return dest;
}

/**
 * Convert stereo to N channels (where N > 2).  Left and right map to
 * the first two channels (front left and front right), and the
 * remaining (surround) channels are filled with silence.
 */
template<SampleFormat F, AnySampleTraits Traits=SampleTraits<F>>
static typename Traits::pointer
StereoToN(typename Traits::pointer dest,
	  unsigned dest_channels,
	  std::span<const typename Traits::value_type> _src) noexcept
{
	assert(dest_channels > 2);
	assert(_src.size() % 2 == 0);

	std::array<typename Traits::value_type, MAX_CHANNELS - 2> silence;
	PcmSilence(std::as_writable_bytes(std::span{silence}), F);

	for (auto src = _src.begin(), end = _src.end(); src != end;) {
		/* copy left/right to front-left/front-right, which is
		   the first two channels in all multi-channel
		   configurations **/
		*dest++ = *src++;
		*dest++ = *src++;

		/* all other channels are silent */
		dest = std::copy_n(silence.begin(), dest_channels - 2, dest);
	}

	return dest;
}

template<SampleFormat F, ArithmeticSampleTraits Traits=SampleTraits<F>>
static typename Traits::pointer
NToM(typename Traits::pointer dest,
     unsigned dest_channels,
     unsigned src_channels,
     std::span<const typename Traits::value_type> _src) noexcept
{
	assert(_src.size() % src_channels == 0);

	for (auto src = _src.begin(), end = _src.end(); src != end;) {
		typename Traits::sum_type sum = *src++;
		for (unsigned c = 1; c < src_channels; ++c)
			sum += *src++;

		typename Traits::value_type value(sum / int(src_channels));

		/* TODO: this is actually only mono ... */
		for (unsigned c = 0; c < dest_channels; ++c)
			*dest++ = value;
	}

	return dest;
}

template<SampleFormat F, AnySampleTraits Traits=SampleTraits<F>>
static typename Traits::pointer
NToM(typename Traits::pointer dest,
     unsigned dest_channels,
     unsigned src_channels,
     std::span<const typename Traits::value_type> _src) noexcept
	requires(!ArithmeticSampleTraits<Traits>)
{
	/* this fallback specialization discards does not do any
	   arithmetic; it is only implemented for DSD, and this
	   static_assert makes sure it's never used for anything
	   else */
	static_assert(F == SampleFormat::DSD);

	assert(_src.size() % src_channels == 0);

	if (dest_channels < src_channels) {
		for (auto src = _src.begin(), end = _src.end(); src != end;) {
			dest = std::copy_n(src, dest_channels, dest);
			src += src_channels;
		}
	} else {
		for (auto src = _src.begin(), end = _src.end(); src != end;) {
			dest = std::copy_n(src, src_channels, dest);
			src += src_channels;
			dest = std::fill_n(dest, dest_channels - src_channels, Traits::SILENCE);
		}
	}

	return dest;
}

template<SampleFormat F, AnySampleTraits Traits=SampleTraits<F>>
static std::span<const typename Traits::value_type>
ConvertChannels(PcmBuffer &buffer,
		unsigned dest_channels,
		unsigned src_channels,
		std::span<const typename Traits::value_type> src) noexcept
{
	assert(src.size() % src_channels == 0);

	const size_t dest_size = src.size() / src_channels * dest_channels;
	auto dest = buffer.GetT<typename Traits::value_type>(dest_size);

	if (src_channels == 1 && dest_channels == 2)
		MonoToStereo(dest, src);
	else if (src_channels == 2 && dest_channels == 1)
		StereoToMono<F, Traits>(dest, src);
	else if (dest_channels == 2)
		NToStereo<F, Traits>(dest, src_channels, src);
	else if (src_channels == 2 && dest_channels > 2)
		StereoToN<F, Traits>(dest, dest_channels, src);
	else
		NToM<F, Traits>(dest, dest_channels, src_channels, src);

	return { dest, dest_size };
}

std::span<const int16_t>
pcm_convert_channels_16(PcmBuffer &buffer,
			unsigned dest_channels,
			unsigned src_channels,
			std::span<const int16_t> src) noexcept
{
	return ConvertChannels<SampleFormat::S16>(buffer, dest_channels,
						  src_channels, src);
}

std::span<const int32_t>
pcm_convert_channels_24(PcmBuffer &buffer,
			unsigned dest_channels,
			unsigned src_channels,
			std::span<const int32_t> src) noexcept
{
	return ConvertChannels<SampleFormat::S24_P32>(buffer, dest_channels,
						      src_channels, src);
}

std::span<const int32_t>
pcm_convert_channels_32(PcmBuffer &buffer,
			unsigned dest_channels,
			unsigned src_channels,
			std::span<const int32_t> src) noexcept
{
	return ConvertChannels<SampleFormat::S32>(buffer, dest_channels,
						  src_channels, src);
}

std::span<const float>
pcm_convert_channels_float(PcmBuffer &buffer,
			   unsigned dest_channels,
			   unsigned src_channels,
			   std::span<const float> src) noexcept
{
	return ConvertChannels<SampleFormat::FLOAT>(buffer, dest_channels,
						    src_channels, src);
}

#ifdef ENABLE_DSD

std::span<const std::byte>
pcm_convert_channels_dsd(PcmBuffer &buffer,
			 unsigned dest_channels,
			 unsigned src_channels,
			 std::span<const std::byte> src) noexcept
{
	return ConvertChannels<SampleFormat::DSD>(buffer, dest_channels,
						  src_channels, src);
}

#endif // ENABLE_DSD
