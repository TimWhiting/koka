module mbedtls-capi
import std/async
import std/num/int32

extern import
  c { library="mbedtls"; vcpkg="mbedtls" }

extern import
  c file "inline"

pub value struct mbedtls-config { internal: intptr_t }
pub struct mbedtls-stream
  source: channel<bytes>
  stream: channel<bytes>
  ssl-context: intptr_t
  handshaked: bool
  chunck-size: ssize_t

extend type exception-info
  TLSException(i: int32)

pub extern init-tls-client-config(): io-event error<mbedtls-config>
  c "kk_ssl_config_client"

extern external/handshake(ssl: intptr_t): io-event int32
  c inline "mbedtls_ssl_handshake((mbedtls_ssl_context*)#1)"

pub fun tls/handshake(stream: mbedtls-stream): io-event error<mbedtls-stream>
  if stream.handshaked then
    return Ok(stream)
  val result = stream.ssl-context.external/handshake()
  if result == 0.int32 then
    Ok(stream(handshaked=True))
  else
    Error(Exception("Handshake Failed", TLSException(result)))

