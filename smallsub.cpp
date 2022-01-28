#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr Small_Sub(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  if (!(type.is_bool())) {
    halide_scalar_value_t c0;
    halide_type_t t0;
    if (is_const_v(a, c0, t0)) {
      halide_scalar_value_t c1;
      halide_type_t t1;
      if (is_const_v(b, c1, t1)) {
        if (evaluate_predicate(fold((c0 >= c1)))) {
          return fold((c0 - c1));
        }
      }
    }
  }
  if (!(type.is_uint() || type.is_operand_uint() || type.is_operand_float() || type.is_float())) {
    if (equal(a, b)) {
      return 0;
    }
  }
  if (type.is_float()) {
    if ((const Ramp *a0 = a.as<Ramp>())) {
      halide_scalar_value_t c2;
      halide_type_t t2;
      if (is_const_v(a0->lanes, c2, t2)) {
        if ((const Ramp *a1 = b.as<Ramp>())) {
          if (equal(c2, a1->lanes)) {
            return ramp((a0->base - a1->base), (a0->stride - a1->stride), c2);
          }
        }
        if ((const Broadcast *a3 = b.as<Broadcast>())) {
          if (equal(c3, a3->lanes)) {
            return ramp((a0->base - a3->value), a0->stride, c3);
          }
        }
      }
    }
    if ((const Broadcast *a4 = a.as<Broadcast>())) {
      halide_scalar_value_t c4;
      halide_type_t t4;
      if (is_const_v(a4->lanes, c4, t4)) {
        if ((const Ramp *a5 = b.as<Ramp>())) {
          if (equal(c4, a5->lanes)) {
            return ramp((a4->value - a5->base), (0 - a5->stride), c4);
          }
        }
      }
    }
  }
  if (type.is_no_overflow_int() || type.is_no_overflow()) {
    if ((const Broadcast *a6 = a.as<Broadcast>())) {
      halide_scalar_value_t c5;
      halide_type_t t5;
      if (is_const_v(a6->lanes, c5, t5)) {
        if ((const Broadcast *a7 = b.as<Broadcast>())) {
          if (equal(c5, a7->lanes)) {
            return broadcast((a6->value - a7->value), c5);
          }
        }
      }
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
