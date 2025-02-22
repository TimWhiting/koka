
kk_unit_t kk_manage_string(kk_string_t s, kk_context_t* _ctx) { /* (s : string) -> console/console () */ 
  if (kk_datatype_is_unique(s.bytes, _ctx)) {
    kk_info_message("unique\n");
  } else {
    kk_info_message("not unique\n");
  }
  return kk_Unit;
}