HALIDE_ALWAYS_INLINE int64_t add(halide_type_t &t, int64_t a, int64_t b) {
    t.lanes |= ((t.bits >= 32) && add_would_overflow(t.bits, a, b)) ? MatcherState::signed_integer_overflow : 0;
    int dead_bits = 64 - t.bits;
    // Drop the high bits then sign-extend them back
    return int64_t((uint64_t(a) + uint64_t(b)) << dead_bits) >> dead_bits;
}

HALIDE_ALWAYS_INLINE void fold_add(halide_scalar_value_t &ret, halide_type_t &t, halide_scalar_value_t &val_a, halide_scalar_value_t &val_b) {
    switch (t.code) {
        case halide_type_int:
            ret.u.i64 = add(t, val_a.u.i64, val_b.u.i64);
            break;
        case halide_type_uint:
            ret.u.u64 = add(t, val_a.u.u64, val_b.u.u64);
            break;
        case halide_type_float:
        case halide_type_bfloat:
            ret.u.f64 = add(t, val_a.u.f64, val_b.u.f64);
            break;
        default:
            // unreachable
            ;
    }
}

HALIDE_ALWAYS_INLINE void fold_eq(halide_scalar_value_t &ret, halide_type_t &t, halide_scalar_value_t &val_a, int b) {
    switch (t.code) {
        case halide_type_int:
            ret.u.u64 = (val_a.u.i64 == (int64_t)b);
            break;
        case halide_type_uint:
            ret.u.u64 = (val_a.u.u64 == (uint64_t)b);
            break;
        case halide_type_float:
        case halide_type_bfloat:
            ret.u.f64 = (val_a.u.f64 == (double)b);
            break;
        default:
            // unreachable
            ;
    }
}

if (is_const_v(a)) {
    if (is_const_v(b)) {
        return fold((a + b));
    }
}

halide_scalar_value_t c0, c1, c2, c3, c4, c5;
halide_type_t t0, t1, t2, t3, t4, t5;

halide_scalar_value_t ret_val;
halide_type_t ret_type;

// fold((c0 + c1) + c2)
halide_scalar_value_t c0;
halide_type_t t0;
if (is_const_v(a, c0, t0)) {
    halide_scalar_value_t c1;
    halide_type_t t1;
    if (is_const_v(b, c1, t1)) {
        halide_scalar_value_t c2;
        halide_type_t t2;
        if (is_const_v(c, c2, t2)) {
            assert(t0 == t1);
            fold_add(ret_val, ret_type, t0, c0, c1);
            fold_add(ret_val, ret_type, t0, ret_val, c2);
            return make_const(ret_type, ret_val);
      }
    }
}

// fold((c0 + c1) + (c2 + c3) * c0)
// fold_add() -> save to ret0
// fold_add() -> save to ret1
// fold_mul() -> save to ret2


if ((r1 = ((const Ramp*)r0)->base.as<Broadcast>())) {
  // if (is_const_v(((const Broadcast*)r1)->lanes)) {
    // if (is_const_v(((const Ramp*)r0)->lanes)) {
      if ((r2 = b.as<Broadcast>())) {
        // if (is_const_v(((const Broadcast*)r2)->lanes)) {
          if ((((const Broadcast*)r2)->lanes == (((const Broadcast*)r1)->lanes * ((const Ramp*)r0)->lanes))) {
            return ramp(broadcast((((const Broadcast*)r1)->value + ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
          }
        // }
      }
    // }
  // }
}

if ((r0 = a.as<Select>())) {
  // ......
  if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
    if (is_const_v(((const Add*)r1)->b)) {
      if (is_const_v(b)) {
        if (evaluate_predicate(fold(((((const Add*)r1)->b + b) == 0)))) {
          return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value + b), ((const Add*)r1)->a);
        }
      }
    }
  }
}

if ((r0 = a.as<Select>())) {
  // ......
  if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
    if (is_const_v(((const Add*)r1)->b, c0, t0)) {
      if (is_const_v(b, c1, t1)) {
        assert(t0 == t1);
        fold_add(ret_val, ret_type, t0, c0, c1);
        fold_eq(ret_val, ret_type, t0, ret_val, 0);
        if (ret_val.u.u64) {
          return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value + b), ((const Add*)r1)->a);
        }
      }
    }
  }
}