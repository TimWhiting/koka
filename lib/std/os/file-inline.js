/*---------------------------------------------------------------------------
  Copyright 2012-2021, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/
var _read_text_file_error;
var _write_text_file_error;

if ($std_core.host()=="node")
{
  // Node
  var fs = await import("fs");

  _read_text_file_error = function( path ) {
    try {
      return $std_core_exn.Ok( fs.readFileSync(path,{encoding: 'utf8'}) );
    }
    catch(exn) {
      return $std_core_exn._error_from_exception(exn);
    }
  };


  _write_text_file_error = function( path, content ) {
    try {
      fs.writeFileSync(path,content,{encoding: 'utf8'});
      return $std_core_exn.Ok( $std_core_types._Unit_ );
    }
    catch(exn) {
      return $std_core_exn._error_from_exception(exn);
    }
  };

}
else {
  // TODO: write to local storage on the browser?
  _read_text_file_error = function( path ) {
    return $std_core.Ok( "" );
  };

  _write_text_file_error = function( path, content ) {
    return $std_core.Ok( $std_core_types._Unit_ );
  }
}
