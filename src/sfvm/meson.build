sfvm_driver_sources = [
  'sfvm_conf.c',
  'sfvm_conf.h',
  'sfvm_domain.c',
  'sfvm_domain.h',
  'sfvm_driver.c',
  'sfvm_driver.h',
  'sfvm_monitor.c',
  'sfvm_monitor.h',
  'sfvm_process.c',
  'sfvm_process.h',
]

driver_source_files += files(sfvm_driver_sources)

stateful_driver_source_files += files(sfvm_driver_sources)

if conf.has('WITH_SFVM')
  sfvm_driver_impl = static_library(
    'virt_driver_sfvm_impl',
    [
      sfvm_driver_sources,
    ],
    dependencies: [
      access_dep,
      curl_dep,
      log_dep,
      src_dep,
    ],
    include_directories: [
      conf_inc_dir,
      hypervisor_inc_dir,
    ],
  )

  virt_modules += {
    'name': 'virt_driver_sfvm',
    'link_whole': [
      sfvm_driver_impl,
    ],
    'link_args': [
      libvirt_no_undefined,
    ],
  }

  virt_daemons += {
    'name': 'virtsfvmd',
    'c_args': [
      '-DDAEMON_NAME="virtsfvmd"',
      '-DMODULE_NAME="sfvm"',
    ],
  }

  virt_daemon_confs += {
    'name': 'virtsfvmd',
  }

  virt_daemon_units += {
    'service': 'virtsfvmd',
    'service_in': files('virtsfvmd.service.in'),
    'name': 'Libvirt sfvm',
    'sockprefix': 'virtsfvmd',
    'sockets': [ 'main', 'ro', 'admin' ],
  }

  virt_install_dirs += [
    localstatedir / 'lib' / 'libvirt' / 'sfvm',
    localstatedir / 'log' / 'libvirt' / 'sfvm',
    runstatedir / 'libvirt' / 'sfvm',
  ]
endif
