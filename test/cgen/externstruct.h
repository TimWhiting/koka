typedef struct silly_s {
  int32_t a1;
  int32_t b1;
} silly;

static inline int32_t foo(int32_t a, int32_t(*b)(silly)){
  silly x = {a, 2};
  return b(x);
}