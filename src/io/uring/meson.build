uring_features = configuration_data()

if host_machine.system() != 'linux' or is_android
  # io_uring is a Linux-only feature; on Android, we also disable it
  # because it's forbidden by a seccomp filter
  uring_dep = dependency('', required: false)
  uring_features.set('HAVE_URING', false)
  configure_file(output: 'Features.h', configuration: uring_features)
  subdir_done()
endif

liburing = dependency('liburing',
                      version: '>= 2.3',
                      include_type: 'system',
                      required: get_option('io_uring'))
uring_features.set('HAVE_URING', liburing.found())
configure_file(output: 'Features.h', configuration: uring_features)

if not liburing.found()
  uring_dep = dependency('', required: false)
  subdir_done()
endif

uring = static_library(
  'uring',
  'Ring.cxx',
  'Queue.cxx',
  'Operation.cxx',
  'Close.cxx',
  'ReadOperation.cxx',
  include_directories: inc,
  dependencies: [
    liburing,
  ],
)

uring_dep = declare_dependency(
  link_with: uring,
  dependencies: [
    liburing,
    io_dep,
  ],
)
