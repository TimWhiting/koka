function kk_bytes_assign(b, i, new_value) {
  const fresh = new Uint8Array(b);
  fresh[i] = new_value;
  return fresh;
}
function kk_bytes_cat(a1, a2) {
  const a1len = a1.length
  const acat = new Uint8Array(a1len + a2.length);
  acat.set(a1, 0);
  acat.set(a2, a1len);
  return acat;
}