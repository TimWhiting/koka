#define mbed_error(msg, err) \
  kk_std_core_exn__new_Error( kk_std_core_exn__new_Exception(msg, kk_ssl_mbedtls_mbedtls_dash_capi__new_TLSException(kk_reuse_null, 0, err, _ctx), _ctx), _ctx )

typedef struct {
  mbedtls_ssl_config        mbedtls_config;
  mbedtls_ctr_drbg_context* drbg;
  mbedtls_entropy_context*  entropy;
  mbedtls_x509_crt*         chain;
  mbedtls_pk_context*       private_key;
} mbedtls_config_t;


void config_free(mbedtls_config_t* config, kk_context_t* _ctx) {
  if (config->chain != NULL) {
    mbedtls_x509_crt_free(config->chain);
    kk_free(config->chain, kk_context());
  }
  if (config->private_key != NULL) {
    mbedtls_pk_free(config->private_key);
    kk_free(config->private_key, kk_context());
  }
  if (config->drbg != NULL) {
    mbedtls_ctr_drbg_free(config->drbg);
    kk_free(config->drbg, kk_context());
  }
  if (config->entropy != NULL) {
    (config->entropy);
    kk_free(config->entropy, kk_context());
  }
  mbedtls_ssl_config_free(&config->mbedtls_config);
  kk_free(config, kk_context());
}

kk_std_core_exn__error kk_ssl_config_server(kk_string_t cert, kk_string_t pk, kk_string_t pssd, kk_context_t* _ctx) {
  mbedtls_config_t* config = kk_malloc(sizeof(mbedtls_config_t), kk_context());
  mbedtls_ssl_config_init(&config->mbedtls_config);
  int res = mbedtls_ssl_config_defaults(&config->mbedtls_config, 
      MBEDTLS_SSL_IS_SERVER, MBEDTLS_SSL_TRANSPORT_STREAM, MBEDTLS_SSL_PRESET_DEFAULT);
  if (res != 0) {
    kk_define_string_literal(static, err, 21, "cannot configure TLS", kk_context());
    kk_free(config, kk_context());
    return mbed_error(err, res);
  }

  // init random numbers
  // mbedtls_ssl_conf_dbg(&config->mbedtls_config, &debug_callback, stderr);
  // mbedtls_debug_set_threshold(1);
  // mbedtls_ctr_drbg_init(config->drbg);
  config->entropy = kk_malloc(sizeof(mbedtls_ctr_drbg_context), kk_context());
  mbedtls_entropy_init(config->entropy);
  config->drbg = kk_malloc(sizeof(mbedtls_entropy_context), kk_context());
  res = mbedtls_ctr_drbg_seed(config->drbg, &mbedtls_entropy_func, config->entropy, "", 0);
  if (res != 0) {
    kk_define_string_literal(static, err, 42, "cannot initialize random number generator", kk_context());
    config_free(config, kk_context());
    return mbed_error(err, res);
  }
  mbedtls_ssl_conf_rng(&config->mbedtls_config, mbedtls_ctr_drbg_random, config->drbg);
  
  // set our own certificate
  config->chain = kk_malloc(sizeof(mbedtls_x509_crt), kk_context());
  mbedtls_x509_crt_init(config->chain);
  kk_ssize_t len;
  const unsigned char* base = kk_string_cbuf_borrow(cert, &len, _ctx);
  res = mbedtls_x509_crt_parse(config->chain, base, len + 1); // include zero byte at end
  if (res != 0) {
    kk_define_string_literal(static, err, 23, "cannot parse certificate", kk_context());
    config_free(config, kk_context());
    return mbed_error(err, res);
  }
  config->private_key = kk_malloc(sizeof(mbedtls_pk_context), kk_context());
  mbedtls_pk_init(config->private_key);
  base = kk_string_cbuf_borrow(pk, &len, _ctx);
  kk_ssize_t ps_len;
  const unsigned char* password = kk_string_cbuf_borrow(pssd, &ps_len, _ctx);
  res = mbedtls_pk_parse_key(config->private_key, base, len + 1, password, ps_len + 1);
  if (res != 0) {
    kk_define_string_literal(static, err, 25, "cannot parse private key", kk_context());
    config_free(config, kk_context());
    return mbed_error(err, res);
  }
  res = mbedtls_ssl_conf_own_cert(&config->mbedtls_config, config->chain, config->private_key);
  if (res != 0) {
    kk_define_string_literal(static, err, 30, "cannot set server certificate", kk_context());
    config_free(config, kk_context());
    return mbed_error(err, res);
  }
  return kk_std_core_exn__new_Ok(kk_ssl_mbedtls_mbedtls_dash_capi__mbedtls_config_box(kk_ssl_mbedtls_mbedtls_dash_capi__new_Mbedtls_config((intptr_t) config, _ctx), _ctx), _ctx);
}



kk_std_core_exn__error kk_ssl_config_client(kk_context_t* _ctx) {
  mbedtls_config_t* config = kk_malloc(sizeof(mbedtls_config_t), kk_context());
  mbedtls_ssl_config_init(&config->mbedtls_config);
  int res = mbedtls_ssl_config_defaults(&config->mbedtls_config, 
      MBEDTLS_SSL_IS_CLIENT, MBEDTLS_SSL_TRANSPORT_STREAM, MBEDTLS_SSL_PRESET_DEFAULT);
  if (res != 0) {
    kk_define_string_literal(static, err, 21, "cannot configure TLS", kk_context());
    kk_free(config, kk_context());
    return mbed_error(err, res);
  }

  // init random numbers
  // mbedtls_ssl_conf_dbg(&config->mbedtls_config, &debug_callback, stderr);
  // mbedtls_debug_set_threshold(1);
  // mbedtls_ctr_drbg_init(config->drbg);
  config->entropy = kk_malloc(sizeof(mbedtls_ctr_drbg_context), kk_context());
  mbedtls_entropy_init(config->entropy);
  config->drbg = kk_malloc(sizeof(mbedtls_entropy_context), kk_context());
  static const char* client_seed = "kk_client";
  res = mbedtls_ctr_drbg_seed(config->drbg, &mbedtls_entropy_func, config->entropy, client_seed, strlen(client_seed));
  if (res != 0) {
    kk_define_string_literal(static, err, 42, "cannot initialize random number generator", kk_context());
    config_free(config, kk_context());
    return mbed_error(err, res);
  }
  mbedtls_ssl_conf_rng(&config->mbedtls_config, mbedtls_ctr_drbg_random, config->drbg);
  
  // initialize certificate chain
  config->chain = kk_malloc(sizeof(mbedtls_x509_crt), kk_context());
  mbedtls_x509_crt_init(config->chain);
  mbedtls_ssl_conf_ca_chain(&config->mbedtls_config, config->chain, NULL);
  return kk_std_core_exn__new_Ok(kk_ssl_mbedtls_mbedtls_dash_capi__mbedtls_config_box(kk_ssl_mbedtls_mbedtls_dash_capi__new_Mbedtls_config((intptr_t) config, _ctx), _ctx), _ctx);
}

kk_std_core_exn__error nodecx_ssl_config_add_ca(kk_ssl_mbedtls_mbedtls_dash_capi__mbedtls_config cfg, kk_string_t cert, kk_context_t* _ctx) {
  kk_ssize_t len;
  mbedtls_config_t* config = (mbedtls_config_t*)cfg.internal;
  const unsigned char* base = kk_string_cbuf_borrow(cert, &len, _ctx);
  int res = mbedtls_x509_crt_parse(config->chain, base, len);
  if (res == 0){
    return kk_std_core_exn__new_Ok(kk_unit_box(kk_Unit), _ctx);
  }
  kk_define_string_literal(static, err, 33, "cannot add certificate authority", kk_context());
  return mbed_error(err, res);
}

void kk_config_free(kk_ssl_mbedtls_mbedtls_dash_capi__mbedtls_config cfg, kk_context_t* _ctx){
  mbedtls_config_t* config = (mbedtls_config_t*)cfg.internal;
  config_free(config, _ctx);
}

void async_ssl_config_add_system_certs(kk_ssl_mbedtls_mbedtls_dash_capi__mbedtls_config config, kk_context_t* _ctx) {
#ifdef _WIN32
#pragma comment(lib, "Crypt32.lib")
  HCERTSTORE store;
  PCCERT_CONTEXT cert;
  if ((store = CertOpenSystemStore(0, L"ROOT")) != NULL) {
    cert = NULL;
    while ((cert = CertEnumCertificatesInStore(store, cert)) != NULL) {
      if (cert->dwCertEncodingType == X509_ASN_ENCODING &&
        cert->pbCertEncoded != NULL && cert->cbCertEncoded > 0)
      {
        kk_string_t certstr = kk_string_alloc_from_utf8n(cert->cbCertEncoded, cert->pbCertEncoded, kk_context());
        nodecx_ssl_config_add_ca(config, certstr, kk_context());
      }
    }
    CertCloseStore(store, 0);
  }
#else
// TODO
#endif
}