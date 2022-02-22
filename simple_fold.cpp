#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr simple_fold(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  if (is_const_v(a)) {
    if (is_const_v(b)) {
      return fold((a + b));
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
