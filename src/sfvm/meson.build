sfvm_driver_sources = [
  'sfvm_driver.c',
]

sfvm_driver_assets = [
  'test-screenshot.png',
]

if conf.has('WITH_SFVM')
  sfvm_lib = static_library(
    'virt_sfvm',
    [
      sfvm_driver_sources,
    ],
    dependencies: [
      src_dep,
    ],
    include_directories: [
      conf_inc_dir,
      hypervisor_inc_dir,
    ],
  )

  libvirt_libs += sfvm_lib

  install_data(sfvm_driver_assets, install_dir: pkgdatadir)
endif
