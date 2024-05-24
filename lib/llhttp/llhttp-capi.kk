/*---------------------------------------------------------------------------
  Copyright 2024 Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

module llhttp-capi
pub import std/num/int32

extern import
  c { vcpkg="llhttp"; library="llhttp" }

extern import
  c file "inline.c"

pub value struct llhttp { internal: intptr_t }
pub value struct llhttp-settings { internal: intptr_t }

pub extern default-settings(): io-event llhttp-settings
  c "kk_llhttp_settings_default"

pub extern init(settings: llhttp-settings, http-type: int32): io-event llhttp
  c "kk_llhttp_parser_init"

pub extern get-type(parser: llhttp): io-event int32
  c inline "llhttp_get_type((llhttp_t*)#1.internal)"

pub extern get-http-major(parser: llhttp): io-event int32
  c inline "llhttp_get_http_major((llhttp_t*)#1.internal)"

pub extern get-http-minor(parser: llhttp): io-event int32
  c inline "llhttp_get_http_minor((llhttp_t*)#1.internal)"

pub extern get-method(parser: llhttp): io-event int32
  c inline "llhttp_get_method((llhttp_t*)#1.internal)"

pub extern get-status-code(parser: llhttp): io-event int32
  c inline "llhttp_get_status_code((llhttp_t*)#1.internal)"

pub extern get-upgrade(parser: llhttp): io-event bool
  c inline "llhttp_get_upgrade((llhttp_t*)#1.internal)"

pub extern reset(parser: llhttp): io-event ()
  c inline "llhttp_reset((llhttp_t*)#1.internal)"

pub extern string/execute(parser: llhttp, data: string): io-event int32
  c "kk_llhttp_execute"

pub extern bytes/execute(parser: llhttp, data: bytes): io-event int32
  c "kk_llhttp_bytes_execute"

// Also deallocates the parser, don't use anymore! TODO: Should we changes this behavior?
pub extern finish(parser: llhttp): io-event int32
  c "kk_llhttp_finish"

pub extern message-needs-eof(parser: llhttp): io-event bool
  c inline "llhttp_message_needs_eof((llhttp_t*)#1.internal)"

pub extern should-keep-alive(parser: llhttp): io-event bool
  c inline "llhttp_should_keep_alive((llhttp_t*)#1.internal)"

pub extern pause(parser: llhttp): io-event ()
  c inline "llhttp_pause((llhttp_t*)#1.internal)"

pub extern resume(parser: llhttp): io-event ()
  c inline "llhttp_resume((llhttp_t*)#1.internal)"

pub extern resume-after-upgrade(parser: llhttp): io-event ()
  c inline "llhttp_resume_after_upgrade((llhttp_t*)#1.internal)"

pub extern get-error(parser: llhttp): io-event int32
  c inline "llhttp_get_errno((llhttp_t*)#1.internal)"

pub extern get-error-reason(parser: llhttp): io-event string
  c inline "kk_string_alloc_from_utf8(llhttp_get_error_reason((llhttp_t*)#1.internal), kk_context())"

pub extern set-error-reason(parser: llhttp, reason: string): io-event ()
  c inline "kk_ssize_t s; llhttp_set_error_reason((llhttp_t*)#1.internal, kk_string_cbuf_borrow(#2, &s, kk_context()))"

pub extern set-on-message-begin(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_message_begin"

pub extern set-on-url(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_url"

pub extern set-on-status(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_status"

pub extern set-on-method(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_method"

pub extern set-on-version(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_version"

pub extern set-on-header-field(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_header_field"

pub extern set-on-header-value(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_header_value"

pub extern set-on-chunk-extension-name(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_chunk_extension_name"

pub extern set-on-chunk-extension-value(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_chunk_extension_value"

pub extern set-on-headers-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_headers_complete"

pub extern set-on-body(parser: llhttp, cb: (string) -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_body"

pub extern set-on-message-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_message_complete"

pub extern set-on-url-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_url_complete"

pub extern set-on-status-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_status_complete"

pub extern set-on-method-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_method_complete"

pub extern set-on-version-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_version_complete"

pub extern set-on-header-field-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_header_field_complete"

pub extern set-on-header-value-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_header_value_complete"

pub extern set-on-chunk-extension-name-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_chunk_extension_name_complete"

pub extern set-on-chunk-extension-value-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_chunk_extension_value_complete"

// When on_chunk_header is called, the current chunk length is stored
// in parser->content_length.
pub extern set-on-chunk-header(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_chunk_header"

pub extern set-on-chunk-complete(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_chunk_complete"

pub extern set-on-reset(parser: llhttp, cb: () -> io-event int32): io-event ()
  c "kk_llhttp_parser_set_on_reset"

pub extern content-length(parser: llhttp): io-event int32
  c inline "((llhttp_t*)#1.internal)->content_length"

pub type llhttp-type
  HTTP_BOTH
  HTTP_REQUEST
  HTTP_RESPONSE

pub fun http-type/int(tp: llhttp-type): int32
  match tp
    HTTP_BOTH -> 0.int32
    HTTP_REQUEST -> 1.int32
    HTTP_RESPONSE -> 2.int32

pub type llhttp-method
  HTTP_DELETE
  HTTP_GET
  HTTP_HEAD
  HTTP_POST
  HTTP_PUT
  HTTP_CONNECT
  HTTP_OPTIONS
  HTTP_TRACE
  HTTP_COPY
  HTTP_LOCK
  HTTP_MKCOL
  HTTP_MOVE
  HTTP_PROPFIND
  HTTP_PROPPATCH
  HTTP_SEARCH
  HTTP_UNLOCK
  HTTP_BIND
  HTTP_REBIND
  HTTP_UNBIND
  HTTP_ACL
  HTTP_REPORT
  HTTP_MKACTIVITY
  HTTP_CHECKOUT
  HTTP_MERGE
  HTTP_MSEARCH
  HTTP_NOTIFY
  HTTP_SUBSCRIBE
  HTTP_UNSUBSCRIBE
  HTTP_PATCH
  HTTP_PURGE
  HTTP_MKCALENDAR
  HTTP_LINK
  HTTP_UNLINK
  HTTP_SOURCE
  HTTP_PRI
  HTTP_DESCRIBE
  HTTP_ANNOUNCE
  HTTP_SETUP
  HTTP_PLAY
  HTTP_PAUSE
  HTTP_TEARDOWN
  HTTP_GET_PARAMETER
  HTTP_SET_PARAMETER
  HTTP_REDIRECT
  HTTP_RECORD
  HTTP_FLUSH

pub fun method/int(m: llhttp-method): int32
  match m
    HTTP_DELETE -> 0.int32
    HTTP_GET -> 1.int32
    HTTP_HEAD -> 2.int32
    HTTP_POST -> 3.int32
    HTTP_PUT -> 4.int32
    HTTP_CONNECT -> 5.int32
    HTTP_OPTIONS -> 6.int32
    HTTP_TRACE -> 7.int32
    HTTP_COPY -> 8.int32
    HTTP_LOCK -> 9.int32
    HTTP_MKCOL -> 10.int32
    HTTP_MOVE -> 11.int32
    HTTP_PROPFIND -> 12.int32
    HTTP_PROPPATCH -> 13.int32
    HTTP_SEARCH -> 14.int32
    HTTP_UNLOCK -> 15.int32
    HTTP_BIND -> 16.int32
    HTTP_REBIND -> 17.int32
    HTTP_UNBIND -> 18.int32
    HTTP_ACL -> 19.int32
    HTTP_REPORT -> 20.int32
    HTTP_MKACTIVITY -> 21.int32
    HTTP_CHECKOUT -> 22.int32
    HTTP_MERGE -> 23.int32
    HTTP_MSEARCH -> 24.int32
    HTTP_NOTIFY -> 25.int32
    HTTP_SUBSCRIBE -> 26.int32
    HTTP_UNSUBSCRIBE -> 27.int32
    HTTP_PATCH -> 28.int32
    HTTP_PURGE -> 29.int32
    HTTP_MKCALENDAR -> 30.int32
    HTTP_LINK -> 31.int32
    HTTP_UNLINK -> 32.int32
    HTTP_SOURCE -> 33.int32
    HTTP_PRI -> 34.int32
    HTTP_DESCRIBE -> 35.int32
    HTTP_ANNOUNCE -> 36.int32
    HTTP_SETUP -> 37.int32
    HTTP_PLAY -> 38.int32
    HTTP_PAUSE -> 39.int32
    HTTP_TEARDOWN -> 40.int32
    HTTP_GET_PARAMETER -> 41.int32
    HTTP_SET_PARAMETER -> 42.int32
    HTTP_REDIRECT -> 43.int32
    HTTP_RECORD -> 44.int32
    HTTP_FLUSH -> 45.int32

pub type llhttp-status
  HTTP_STATUS_CONTINUE
  HTTP_STATUS_SWITCHING_PROTOCOLS
  HTTP_STATUS_PROCESSING
  HTTP_STATUS_EARLY_HINTS
  HTTP_STATUS_RESPONSE_IS_STALE
  HTTP_STATUS_REVALIDATION_FAILED
  HTTP_STATUS_DISCONNECTED_OPERATION
  HTTP_STATUS_HEURISTIC_EXPIRATION
  HTTP_STATUS_MISCELLANEOUS_WARNING
  HTTP_STATUS_OK
  HTTP_STATUS_CREATED
  HTTP_STATUS_ACCEPTED
  HTTP_STATUS_NON_AUTHORITATIVE_INFORMATION
  HTTP_STATUS_NO_CONTENT
  HTTP_STATUS_RESET_CONTENT
  HTTP_STATUS_PARTIAL_CONTENT
  HTTP_STATUS_MULTI_STATUS
  HTTP_STATUS_ALREADY_REPORTED
  HTTP_STATUS_TRANSFORMATION_APPLIED
  HTTP_STATUS_IM_USED
  HTTP_STATUS_MISCELLANEOUS_PERSISTENT_WARNING
  HTTP_STATUS_MULTIPLE_CHOICES
  HTTP_STATUS_MOVED_PERMANENTLY
  HTTP_STATUS_FOUND
  HTTP_STATUS_SEE_OTHER
  HTTP_STATUS_NOT_MODIFIED
  HTTP_STATUS_USE_PROXY
  HTTP_STATUS_SWITCH_PROXY
  HTTP_STATUS_TEMPORARY_REDIRECT
  HTTP_STATUS_PERMANENT_REDIRECT
  HTTP_STATUS_BAD_REQUEST
  HTTP_STATUS_UNAUTHORIZED
  HTTP_STATUS_PAYMENT_REQUIRED
  HTTP_STATUS_FORBIDDEN
  HTTP_STATUS_NOT_FOUND
  HTTP_STATUS_METHOD_NOT_ALLOWED
  HTTP_STATUS_NOT_ACCEPTABLE
  HTTP_STATUS_PROXY_AUTHENTICATION_REQUIRED
  HTTP_STATUS_REQUEST_TIMEOUT
  HTTP_STATUS_CONFLICT
  HTTP_STATUS_GONE
  HTTP_STATUS_LENGTH_REQUIRED
  HTTP_STATUS_PRECONDITION_FAILED
  HTTP_STATUS_PAYLOAD_TOO_LARGE
  HTTP_STATUS_URI_TOO_LONG
  HTTP_STATUS_UNSUPPORTED_MEDIA_TYPE
  HTTP_STATUS_RANGE_NOT_SATISFIABLE
  HTTP_STATUS_EXPECTATION_FAILED
  HTTP_STATUS_IM_A_TEAPOT
  HTTP_STATUS_PAGE_EXPIRED
  HTTP_STATUS_ENHANCE_YOUR_CALM
  HTTP_STATUS_MISDIRECTED_REQUEST
  HTTP_STATUS_UNPROCESSABLE_ENTITY
  HTTP_STATUS_LOCKED
  HTTP_STATUS_FAILED_DEPENDENCY
  HTTP_STATUS_TOO_EARLY
  HTTP_STATUS_UPGRADE_REQUIRED
  HTTP_STATUS_PRECONDITION_REQUIRED
  HTTP_STATUS_TOO_MANY_REQUESTS
  HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE_UNOFFICIAL
  HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE
  HTTP_STATUS_LOGIN_TIMEOUT
  HTTP_STATUS_NO_RESPONSE
  HTTP_STATUS_RETRY_WITH
  HTTP_STATUS_BLOCKED_BY_PARENTAL_CONTROL
  HTTP_STATUS_UNAVAILABLE_FOR_LEGAL_REASONS
  HTTP_STATUS_CLIENT_CLOSED_LOAD_BALANCED_REQUEST
  HTTP_STATUS_INVALID_X_FORWARDED_FOR
  HTTP_STATUS_REQUEST_HEADER_TOO_LARGE
  HTTP_STATUS_SSL_CERTIFICATE_ERROR
  HTTP_STATUS_SSL_CERTIFICATE_REQUIRED
  HTTP_STATUS_HTTP_REQUEST_SENT_TO_HTTPS_PORT
  HTTP_STATUS_INVALID_TOKEN
  HTTP_STATUS_CLIENT_CLOSED_REQUEST
  HTTP_STATUS_INTERNAL_SERVER_ERROR
  HTTP_STATUS_NOT_IMPLEMENTED
  HTTP_STATUS_BAD_GATEWAY
  HTTP_STATUS_SERVICE_UNAVAILABLE
  HTTP_STATUS_GATEWAY_TIMEOUT
  HTTP_STATUS_HTTP_VERSION_NOT_SUPPORTED
  HTTP_STATUS_VARIANT_ALSO_NEGOTIATES
  HTTP_STATUS_INSUFFICIENT_STORAGE
  HTTP_STATUS_LOOP_DETECTED
  HTTP_STATUS_BANDWIDTH_LIMIT_EXCEEDED
  HTTP_STATUS_NOT_EXTENDED
  HTTP_STATUS_NETWORK_AUTHENTICATION_REQUIRED
  HTTP_STATUS_WEB_SERVER_UNKNOWN_ERROR
  HTTP_STATUS_WEB_SERVER_IS_DOWN
  HTTP_STATUS_CONNECTION_TIMEOUT
  HTTP_STATUS_ORIGIN_IS_UNREACHABLE
  HTTP_STATUS_TIMEOUT_OCCURED
  HTTP_STATUS_SSL_HANDSHAKE_FAILED
  HTTP_STATUS_INVALID_SSL_CERTIFICATE
  HTTP_STATUS_RAILGUN_ERROR
  HTTP_STATUS_SITE_IS_OVERLOADED
  HTTP_STATUS_SITE_IS_FROZEN
  HTTP_STATUS_IDENTITY_PROVIDER_AUTHENTICATION_ERROR
  HTTP_STATUS_NETWORK_READ_TIMEOUT
  HTTP_STATUS_NETWORK_CONNECT_TIMEOUT

pub fun status/int(status: llhttp-status): int
  match status
    HTTP_STATUS_CONTINUE -> 100
    HTTP_STATUS_SWITCHING_PROTOCOLS -> 101
    HTTP_STATUS_PROCESSING -> 102
    HTTP_STATUS_EARLY_HINTS -> 103
    HTTP_STATUS_RESPONSE_IS_STALE -> 110
    HTTP_STATUS_REVALIDATION_FAILED -> 111
    HTTP_STATUS_DISCONNECTED_OPERATION -> 112
    HTTP_STATUS_HEURISTIC_EXPIRATION -> 113
    HTTP_STATUS_MISCELLANEOUS_WARNING -> 199
    HTTP_STATUS_OK -> 200
    HTTP_STATUS_CREATED -> 201
    HTTP_STATUS_ACCEPTED -> 202
    HTTP_STATUS_NON_AUTHORITATIVE_INFORMATION -> 203
    HTTP_STATUS_NO_CONTENT -> 204
    HTTP_STATUS_RESET_CONTENT -> 205
    HTTP_STATUS_PARTIAL_CONTENT -> 206
    HTTP_STATUS_MULTI_STATUS -> 207
    HTTP_STATUS_ALREADY_REPORTED -> 208
    HTTP_STATUS_TRANSFORMATION_APPLIED -> 214
    HTTP_STATUS_IM_USED -> 226
    HTTP_STATUS_MISCELLANEOUS_PERSISTENT_WARNING -> 299
    HTTP_STATUS_MULTIPLE_CHOICES -> 300
    HTTP_STATUS_MOVED_PERMANENTLY -> 301
    HTTP_STATUS_FOUND -> 302
    HTTP_STATUS_SEE_OTHER -> 303
    HTTP_STATUS_NOT_MODIFIED -> 304
    HTTP_STATUS_USE_PROXY -> 305
    HTTP_STATUS_SWITCH_PROXY -> 306
    HTTP_STATUS_TEMPORARY_REDIRECT -> 307
    HTTP_STATUS_PERMANENT_REDIRECT -> 308
    HTTP_STATUS_BAD_REQUEST -> 400
    HTTP_STATUS_UNAUTHORIZED -> 401
    HTTP_STATUS_PAYMENT_REQUIRED -> 402
    HTTP_STATUS_FORBIDDEN -> 403
    HTTP_STATUS_NOT_FOUND -> 404
    HTTP_STATUS_METHOD_NOT_ALLOWED -> 405
    HTTP_STATUS_NOT_ACCEPTABLE -> 406
    HTTP_STATUS_PROXY_AUTHENTICATION_REQUIRED -> 407
    HTTP_STATUS_REQUEST_TIMEOUT -> 408
    HTTP_STATUS_CONFLICT -> 409
    HTTP_STATUS_GONE -> 410
    HTTP_STATUS_LENGTH_REQUIRED -> 411
    HTTP_STATUS_PRECONDITION_FAILED -> 412
    HTTP_STATUS_PAYLOAD_TOO_LARGE -> 413
    HTTP_STATUS_URI_TOO_LONG -> 414
    HTTP_STATUS_UNSUPPORTED_MEDIA_TYPE -> 415
    HTTP_STATUS_RANGE_NOT_SATISFIABLE -> 416
    HTTP_STATUS_EXPECTATION_FAILED -> 417
    HTTP_STATUS_IM_A_TEAPOT -> 418
    HTTP_STATUS_PAGE_EXPIRED -> 419
    HTTP_STATUS_ENHANCE_YOUR_CALM -> 420
    HTTP_STATUS_MISDIRECTED_REQUEST -> 421
    HTTP_STATUS_UNPROCESSABLE_ENTITY -> 422
    HTTP_STATUS_LOCKED -> 423
    HTTP_STATUS_FAILED_DEPENDENCY -> 424
    HTTP_STATUS_TOO_EARLY -> 425
    HTTP_STATUS_UPGRADE_REQUIRED -> 426
    HTTP_STATUS_PRECONDITION_REQUIRED -> 428
    HTTP_STATUS_TOO_MANY_REQUESTS -> 429
    HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE_UNOFFICIAL -> 430
    HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE -> 431
    HTTP_STATUS_LOGIN_TIMEOUT -> 440
    HTTP_STATUS_NO_RESPONSE -> 444
    HTTP_STATUS_RETRY_WITH -> 449
    HTTP_STATUS_BLOCKED_BY_PARENTAL_CONTROL -> 450
    HTTP_STATUS_UNAVAILABLE_FOR_LEGAL_REASONS -> 451
    HTTP_STATUS_CLIENT_CLOSED_LOAD_BALANCED_REQUEST -> 460
    HTTP_STATUS_INVALID_X_FORWARDED_FOR -> 463
    HTTP_STATUS_REQUEST_HEADER_TOO_LARGE -> 494
    HTTP_STATUS_SSL_CERTIFICATE_ERROR -> 495
    HTTP_STATUS_SSL_CERTIFICATE_REQUIRED -> 496
    HTTP_STATUS_HTTP_REQUEST_SENT_TO_HTTPS_PORT -> 497
    HTTP_STATUS_INVALID_TOKEN -> 498
    HTTP_STATUS_CLIENT_CLOSED_REQUEST -> 499
    HTTP_STATUS_INTERNAL_SERVER_ERROR -> 500
    HTTP_STATUS_NOT_IMPLEMENTED -> 501
    HTTP_STATUS_BAD_GATEWAY -> 502
    HTTP_STATUS_SERVICE_UNAVAILABLE -> 503
    HTTP_STATUS_GATEWAY_TIMEOUT -> 504
    HTTP_STATUS_HTTP_VERSION_NOT_SUPPORTED -> 505
    HTTP_STATUS_VARIANT_ALSO_NEGOTIATES -> 506
    HTTP_STATUS_INSUFFICIENT_STORAGE -> 507
    HTTP_STATUS_LOOP_DETECTED -> 508
    HTTP_STATUS_BANDWIDTH_LIMIT_EXCEEDED -> 509
    HTTP_STATUS_NOT_EXTENDED -> 510
    HTTP_STATUS_NETWORK_AUTHENTICATION_REQUIRED -> 511
    HTTP_STATUS_WEB_SERVER_UNKNOWN_ERROR -> 520
    HTTP_STATUS_WEB_SERVER_IS_DOWN -> 521
    HTTP_STATUS_CONNECTION_TIMEOUT -> 522
    HTTP_STATUS_ORIGIN_IS_UNREACHABLE -> 523
    HTTP_STATUS_TIMEOUT_OCCURED -> 524
    HTTP_STATUS_SSL_HANDSHAKE_FAILED -> 525
    HTTP_STATUS_INVALID_SSL_CERTIFICATE -> 526
    HTTP_STATUS_RAILGUN_ERROR -> 527
    HTTP_STATUS_SITE_IS_OVERLOADED -> 529
    HTTP_STATUS_SITE_IS_FROZEN -> 530
    HTTP_STATUS_IDENTITY_PROVIDER_AUTHENTICATION_ERROR -> 561
    HTTP_STATUS_NETWORK_READ_TIMEOUT -> 598
    HTTP_STATUS_NETWORK_CONNECT_TIMEOUT -> 599

pub fun int/status(i: int): exn llhttp-status
  match i
    100 -> HTTP_STATUS_CONTINUE
    101 -> HTTP_STATUS_SWITCHING_PROTOCOLS
    102 -> HTTP_STATUS_PROCESSING
    103 -> HTTP_STATUS_EARLY_HINTS
    110 -> HTTP_STATUS_RESPONSE_IS_STALE
    111 -> HTTP_STATUS_REVALIDATION_FAILED
    112 -> HTTP_STATUS_DISCONNECTED_OPERATION
    113 -> HTTP_STATUS_HEURISTIC_EXPIRATION
    199 -> HTTP_STATUS_MISCELLANEOUS_WARNING
    200 -> HTTP_STATUS_OK
    201 -> HTTP_STATUS_CREATED
    202 -> HTTP_STATUS_ACCEPTED
    203 -> HTTP_STATUS_NON_AUTHORITATIVE_INFORMATION
    204 -> HTTP_STATUS_NO_CONTENT
    205 -> HTTP_STATUS_RESET_CONTENT
    206 -> HTTP_STATUS_PARTIAL_CONTENT
    207 -> HTTP_STATUS_MULTI_STATUS
    208 -> HTTP_STATUS_ALREADY_REPORTED
    214 -> HTTP_STATUS_TRANSFORMATION_APPLIED
    226 -> HTTP_STATUS_IM_USED
    299 -> HTTP_STATUS_MISCELLANEOUS_PERSISTENT_WARNING
    300 -> HTTP_STATUS_MULTIPLE_CHOICES
    301 -> HTTP_STATUS_MOVED_PERMANENTLY
    302 -> HTTP_STATUS_FOUND
    303 -> HTTP_STATUS_SEE_OTHER
    304 -> HTTP_STATUS_NOT_MODIFIED
    305 -> HTTP_STATUS_USE_PROXY
    306 -> HTTP_STATUS_SWITCH_PROXY
    307 -> HTTP_STATUS_TEMPORARY_REDIRECT
    308 -> HTTP_STATUS_PERMANENT_REDIRECT
    400 -> HTTP_STATUS_BAD_REQUEST
    401 -> HTTP_STATUS_UNAUTHORIZED
    402 -> HTTP_STATUS_PAYMENT_REQUIRED
    403 -> HTTP_STATUS_FORBIDDEN
    404 -> HTTP_STATUS_NOT_FOUND
    405 -> HTTP_STATUS_METHOD_NOT_ALLOWED
    406 -> HTTP_STATUS_NOT_ACCEPTABLE
    407 -> HTTP_STATUS_PROXY_AUTHENTICATION_REQUIRED
    408 -> HTTP_STATUS_REQUEST_TIMEOUT
    409 -> HTTP_STATUS_CONFLICT
    410 -> HTTP_STATUS_GONE
    411 -> HTTP_STATUS_LENGTH_REQUIRED
    412 -> HTTP_STATUS_PRECONDITION_FAILED
    413 -> HTTP_STATUS_PAYLOAD_TOO_LARGE
    414 -> HTTP_STATUS_URI_TOO_LONG
    415 -> HTTP_STATUS_UNSUPPORTED_MEDIA_TYPE
    416 -> HTTP_STATUS_RANGE_NOT_SATISFIABLE
    417 -> HTTP_STATUS_EXPECTATION_FAILED
    418 -> HTTP_STATUS_IM_A_TEAPOT
    419 -> HTTP_STATUS_PAGE_EXPIRED
    420 -> HTTP_STATUS_ENHANCE_YOUR_CALM
    421 -> HTTP_STATUS_MISDIRECTED_REQUEST
    422 -> HTTP_STATUS_UNPROCESSABLE_ENTITY
    423 -> HTTP_STATUS_LOCKED
    424 -> HTTP_STATUS_FAILED_DEPENDENCY
    425 -> HTTP_STATUS_TOO_EARLY
    426 -> HTTP_STATUS_UPGRADE_REQUIRED
    428 -> HTTP_STATUS_PRECONDITION_REQUIRED
    429 -> HTTP_STATUS_TOO_MANY_REQUESTS
    430 -> HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE_UNOFFICIAL
    431 -> HTTP_STATUS_REQUEST_HEADER_FIELDS_TOO_LARGE
    440 -> HTTP_STATUS_LOGIN_TIMEOUT
    444 -> HTTP_STATUS_NO_RESPONSE
    449 -> HTTP_STATUS_RETRY_WITH
    450 -> HTTP_STATUS_BLOCKED_BY_PARENTAL_CONTROL
    451 -> HTTP_STATUS_UNAVAILABLE_FOR_LEGAL_REASONS
    460 -> HTTP_STATUS_CLIENT_CLOSED_LOAD_BALANCED_REQUEST
    463 -> HTTP_STATUS_INVALID_X_FORWARDED_FOR
    494 -> HTTP_STATUS_REQUEST_HEADER_TOO_LARGE
    495 -> HTTP_STATUS_SSL_CERTIFICATE_ERROR
    496 -> HTTP_STATUS_SSL_CERTIFICATE_REQUIRED
    497 -> HTTP_STATUS_HTTP_REQUEST_SENT_TO_HTTPS_PORT
    498 -> HTTP_STATUS_INVALID_TOKEN
    499 -> HTTP_STATUS_CLIENT_CLOSED_REQUEST
    500 -> HTTP_STATUS_INTERNAL_SERVER_ERROR
    501 -> HTTP_STATUS_NOT_IMPLEMENTED
    502 -> HTTP_STATUS_BAD_GATEWAY
    503 -> HTTP_STATUS_SERVICE_UNAVAILABLE
    504 -> HTTP_STATUS_GATEWAY_TIMEOUT
    505 -> HTTP_STATUS_HTTP_VERSION_NOT_SUPPORTED
    506 -> HTTP_STATUS_VARIANT_ALSO_NEGOTIATES
    507 -> HTTP_STATUS_INSUFFICIENT_STORAGE
    508 -> HTTP_STATUS_LOOP_DETECTED
    509 -> HTTP_STATUS_BANDWIDTH_LIMIT_EXCEEDED
    510 -> HTTP_STATUS_NOT_EXTENDED
    511 -> HTTP_STATUS_NETWORK_AUTHENTICATION_REQUIRED
    520 -> HTTP_STATUS_WEB_SERVER_UNKNOWN_ERROR
    521 -> HTTP_STATUS_WEB_SERVER_IS_DOWN
    522 -> HTTP_STATUS_CONNECTION_TIMEOUT
    523 -> HTTP_STATUS_ORIGIN_IS_UNREACHABLE
    524 -> HTTP_STATUS_TIMEOUT_OCCURED
    525 -> HTTP_STATUS_SSL_HANDSHAKE_FAILED
    526 -> HTTP_STATUS_INVALID_SSL_CERTIFICATE
    527 -> HTTP_STATUS_RAILGUN_ERROR
    529 -> HTTP_STATUS_SITE_IS_OVERLOADED
    530 -> HTTP_STATUS_SITE_IS_FROZEN
    561 -> HTTP_STATUS_IDENTITY_PROVIDER_AUTHENTICATION_ERROR
    598 -> HTTP_STATUS_NETWORK_READ_TIMEOUT
    599 -> HTTP_STATUS_NETWORK_CONNECT_TIMEOUT

pub type llhttp-error
  LLHTTPOK
  INTERNAL
  STRICT
  CR_EXPECTED
  LF_EXPECTED
  UNEXPECTED_CONTENT_LENGTH
  UNEXPECTED_SPACE
  CLOSED_CONNECTION
  INVALID_METHOD
  INVALID_URL
  INVALID_CONSTANT
  INVALID_VERSION
  INVALID_HEADER_TOKEN
  INVALID_CONTENT_LENGTH
  INVALID_CHUNK_SIZE
  INVALID_STATUS
  INVALID_EOF_STATE
  INVALID_TRANSFER_ENCODING
  CB_MESSAGE_BEGIN
  CB_HEADERS_COMPLETE
  CB_MESSAGE_COMPLETE
  CB_CHUNK_HEADER
  CB_CHUNK_COMPLETE
  PAUSED
  PAUSED_UPGRADE
  PAUSED_H2_UPGRADE
  USER
  CB_URL_COMPLETE
  CB_STATUS_COMPLETE
  CB_METHOD_COMPLETE
  CB_VERSION_COMPLETE
  CB_HEADER_FIELD_COMPLETE
  CB_HEADER_VALUE_COMPLETE
  CB_CHUNK_EXTENSION_NAME_COMPLETE
  CB_CHUNK_EXTENSION_VALUE_COMPLETE
  CB_RESET

pub fun error/int(e: llhttp-error): int32
  match e
    LLHTTPOK -> 0.int32
    INTERNAL -> 1.int32
    STRICT -> 2.int32
    CR_EXPECTED -> 25.int32
    LF_EXPECTED -> 3.int32
    UNEXPECTED_CONTENT_LENGTH -> 4.int32
    UNEXPECTED_SPACE -> 30.int32
    CLOSED_CONNECTION -> 5.int32
    INVALID_METHOD -> 6.int32
    INVALID_URL -> 7.int32
    INVALID_CONSTANT -> 8.int32
    INVALID_VERSION -> 9.int32
    INVALID_HEADER_TOKEN -> 10.int32
    INVALID_CONTENT_LENGTH -> 11.int32
    INVALID_CHUNK_SIZE -> 12.int32
    INVALID_STATUS -> 13.int32
    INVALID_EOF_STATE -> 14.int32
    INVALID_TRANSFER_ENCODING -> 15.int32
    CB_MESSAGE_BEGIN -> 16.int32
    CB_HEADERS_COMPLETE -> 17.int32
    CB_MESSAGE_COMPLETE -> 18.int32
    CB_CHUNK_HEADER -> 19.int32
    CB_CHUNK_COMPLETE -> 20.int32
    PAUSED -> 21.int32
    PAUSED_UPGRADE -> 22.int32
    PAUSED_H2_UPGRADE -> 23.int32
    USER -> 24.int32
    CB_URL_COMPLETE -> 26.int32
    CB_STATUS_COMPLETE -> 27.int32
    CB_METHOD_COMPLETE -> 32.int32
    CB_VERSION_COMPLETE -> 33.int32
    CB_HEADER_FIELD_COMPLETE -> 28.int32
    CB_HEADER_VALUE_COMPLETE -> 29.int32
    CB_CHUNK_EXTENSION_NAME_COMPLETE -> 34.int32
    CB_CHUNK_EXTENSION_VALUE_COMPLETE -> 35.int32
    CB_RESET -> 31.int32

pub type llhttp-lenient-flags
  HEADERS
  CHUNKED_LENGTH
  KEEP_ALIVE
  TRANSFER_ENCODING
  VERSION

pub fun lenient-flag/int(f: llhttp-lenient-flags): int32
  match f
    HEADERS -> 1.int32
    CHUNKED_LENGTH -> 2.int32
    KEEP_ALIVE -> 4.int32
    TRANSFER_ENCODING -> 8.int32
    VERSION -> 16.int32

pub fun lenient-flags/int(fs: list<llhttp-lenient-flags>): int32
  fs.foldr(0.int32, fn(f, acc) f.int.or(acc))

pub type llhttp-flags
  F_CONNECTION_KEEP_ALIVE
  F_CONNECTION_CLOSE
  F_CONNECTION_UPGRADE
  F_CHUNKED
  F_UPGRADE
  F_CONTENT_LENGTH
  F_SKIPBODY
  F_TRAILING
  F_TRANSFER_ENCODING

pub fun flag/int(f: llhttp-flags): int32
  match f
    F_CONNECTION_KEEP_ALIVE -> 1.int32
    F_CONNECTION_CLOSE -> 2.int32
    F_CONNECTION_UPGRADE -> 4.int32
    F_CHUNKED -> 8.int32
    F_UPGRADE -> 16.int32
    F_CONTENT_LENGTH -> 32.int32
    F_SKIPBODY -> 64.int32
    F_TRAILING -> 128.int32
    F_TRANSFER_ENCODING -> 512.int32

pub fun flags/int(fs: list<llhttp-flags>): int32
  fs.foldr(0.int32, fn(f, acc) f.int.or(acc))
