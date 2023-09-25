/*---------------------------------------------------------------------------
  Copyright 2020-2021, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/
#ifndef WIN32
#include <sys/stat.h>
#include <fcntl.h>
#endif

static kk_std_core__error kk_os_read_text_file_error( kk_string_t path, kk_context_t* ctx ) {
  kk_string_t content;
  const int err = kk_os_read_text_file(path,&content,ctx);
  if (err != 0) return kk_error_from_errno(err,ctx);
           else return kk_error_ok(kk_string_box(content),ctx);
}

static kk_std_core__error kk_os_write_text_file_error( kk_string_t path, kk_string_t content, kk_context_t* ctx ) {
  const int err = kk_os_write_text_file(path,content,ctx);
  if (err != 0) return kk_error_from_errno(err,ctx);
           else return kk_error_ok(kk_unit_box(kk_Unit),ctx);
}

#define nothing(ctx) kk_std_core_types__new_Nothing(ctx)

static kk_std_core__error kk_os_fstat_error(kk_string_t path, kk_context_t* ctx) {
  kk_stat_t st = { 0 };
  kk_file_t f;
  int err = kk_posix_open(path, O_RDONLY, 0, &f, ctx);
  if (err != 0) return kk_error_from_errno(err,ctx);
  err = kk_posix_fstat(f, &st);
  if (err != 0) return kk_error_from_errno(err,ctx);
  kk_std_os_file__fstat fstat;
  #ifndef WIN32
  kk_integer_t size = kk_integer_from_size_t(st.st_size, ctx);
  kk_std_os_file__fmode fmode = kk_std_os_file__new_Fmode((uint16_t)st.st_mode, ctx);
  fstat = kk_std_os_file__new_Fstat(NULL, 0, fmode, size, nothing(ctx), nothing(ctx), nothing(ctx), nothing(ctx), nothing(ctx), ctx);
  #else
  // fstat = kk_std_os_file__new_Fstat(NULL, ctx);
  #endif
  return kk_error_ok(kk_std_os_file__fstat_box(fstat, ctx), ctx);
}

static bool kk_os_fmode_is_dir(kk_std_os_file__fmode fmode, kk_context_t* ctx) {
  #ifndef WIN32
  return S_ISDIR(fmode.os_flags);
  #else
  return _S_IFDIR(fmode.os_flags);
  #endif
}

static bool kk_os_fmode_is_file(kk_std_os_file__fmode fmode, kk_context_t* ctx) {
  #ifndef WIN32
  return S_ISREG(fmode.os_flags);
  #else
  return _S_IFREG(fmode.os_flags);
  #endif
}

static bool kk_os_fmode_is_symlink(kk_std_os_file__fmode fmode, kk_context_t* ctx) {
  #ifndef WIN32
  return S_ISLNK(fmode.os_flags);
  #else
  return false;
  #endif
}