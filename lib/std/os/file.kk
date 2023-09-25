/*---------------------------------------------------------------------------
  Copyright 2020-2021, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

/* File operations.
*/
module std/os/file

import std/os/path
import std/os/dir
import std/time/time

extern import
  c file "file-inline.c"
  js file "file-inline.js"

pub value struct fmode
  os-flags: int32

pub ref struct fstat 
  mode: fmode
  size: int
  uid: maybe<int>
  gid: maybe<int>
  atime: maybe<time>
  mtime: maybe<time>
  ctime: maybe<time>

pub inline extern is-dir(m: fmode): bool
  c "kk_os_fmode_is_dir(#1)"

pub inline extern is-file(m: fmode): bool
  c "kk_os_fmode_is_file(#1)"

pub inline extern is-symlink(m: fmode): bool
  c "kk_os_fmode_is_link(#1)"

pub fun fstat( path : path ) : <fsys,exn> fstat
  match fstat-err(path.string)
    Error(exn)  -> throw-exn(exn.prepend("unable to read text file " ++ path.show))
    Ok(content) -> content

// Read a text file synchronously (using UTF8 encoding)
pub fun read-text-file( path : path ) : <fsys,exn> string
  match read-text-file-err(path.string)
    Error(exn)  -> throw-exn(exn.prepend("unable to read text file " ++ path.show))
    Ok(content) -> content

// Write a text file synchronously (using UTF8 encoding)
pub fun write-text-file( path : path, content : string, create-dir : bool = True ) : <fsys,exn> ()
  if create-dir then ensure-dir(path.nobase)
  match(write-text-file-err(path.string,content))
    Error(exn) -> throw-exn(exn.prepend("unable to write text file " ++ path.show))
    _ -> ()


fun prepend( exn : exception, pre : string ) : exception
  Exception(pre ++ ": " ++ exn.message, exn.info)

extern fstat-err( path : string ) : fsys error<fstat>
  c "kk_os_fstat_error"

extern read-text-file-err( path : string ) : fsys error<string>
  c "kk_os_read_text_file_error"
  js "_read_text_file_error"
  //cs inline "System.IO.File.ReadAllText(#1,System.Text.Encoding.UTF8)"

extern write-text-file-err( path : string, content : string ) : fsys error<()>
  c "kk_os_write_text_file_error"
  js "_write_text_file_error"
  //cs inline "System.IO.File.WriteAllText(#1,#2,System.Text.Encoding.UTF8)"

