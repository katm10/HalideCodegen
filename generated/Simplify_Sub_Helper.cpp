#include "Expr.h"
#include "Type.h"
#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"

namespace Halide {
namespace Internal {
namespace CodeGen {
Expr Simplify_Sub(const Sub *expr, Simplify *simplifier) {
  if (is_const_int(expr->b, 0)) {
    return expr->a;
  }
  if (is_const(expr->a)) {
    if (is_const(expr->b)) {
      return fold((expr->a - expr->b));
    }
    if (const Select *a91 = expr->b.as<Select>()) {
      if (is_const(a91->true_value)) {
        if (is_const(a91->false_value)) {
          return select(a91->condition, fold((expr->a - a91->true_value)), fold((expr->a - a91->false_value)));
        }
      }
    }
  }
  if (!(is_uint(expr))) {
    if (is_const(expr->b)) {
      if (evaluate_predicate(fold(!(overflows((0 - expr->b)))))) {
        return (expr->a + fold((0 - expr->b)));
      }
    }
  }
  if (equal(expr->a, expr->b)) {
    return 0;
  }
  if (const Ramp *a1 = expr->a.as<Ramp>()) {
    if (is_const(a1->lanes)) {
      if (const Ramp *a2 = expr->b.as<Ramp>()) {
        if (equal(a1->lanes, a2->lanes)) {
          return ramp((a1->base - a2->base), (a1->stride - a2->stride), a1->lanes);
        }
      }
      if (const Broadcast *a4 = expr->b.as<Broadcast>()) {
        if (equal(a1->lanes, a4->lanes)) {
          return ramp((a1->base - a4->value), a1->stride, a1->lanes);
        }
      }
    }
    if (const Broadcast *a20 = a1->base.as<Broadcast>()) {
      if (is_const(a20->lanes)) {
        if (is_const(a1->lanes)) {
          if (const Broadcast *a21 = expr->b.as<Broadcast>()) {
            if (is_const(a21->lanes)) {
              if (evaluate_predicate(fold((a21->lanes == (a20->lanes * a1->lanes))))) {
                return ramp(broadcast((a20->value - a21->value), a20->lanes), a1->stride, a1->lanes);
              }
            }
          }
        }
      }
    }
    if (const Ramp *a23 = a1->base.as<Ramp>()) {
      if (is_const(a23->lanes)) {
        if (is_const(a1->lanes)) {
          if (const Broadcast *a24 = expr->b.as<Broadcast>()) {
            if (is_const(a24->lanes)) {
              if (evaluate_predicate(fold((a24->lanes == (a23->lanes * a1->lanes))))) {
                return ramp(ramp((a23->base - a24->value), a23->stride, a23->lanes), a1->stride, a1->lanes);
              }
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a5 = expr->a.as<Broadcast>()) {
    if (is_const(a5->lanes)) {
      if (const Ramp *a6 = expr->b.as<Ramp>()) {
        if (equal(a5->lanes, a6->lanes)) {
          return ramp((a5->value - a6->base), (0 - a6->stride), a5->lanes);
        }
      }
      if (const Broadcast *a8 = expr->b.as<Broadcast>()) {
        if (equal(a5->lanes, a8->lanes)) {
          return broadcast((a5->value - a8->value), a5->lanes);
        }
        if (is_const(a8->lanes)) {
          if (evaluate_predicate(fold(((a8->lanes % a5->lanes) == 0)))) {
            return broadcast((a5->value - broadcast(a8->value, fold((a8->lanes / a5->lanes)))), a5->lanes);
          }
          if (evaluate_predicate(fold(((a5->lanes % a8->lanes) == 0)))) {
            return broadcast((broadcast(a5->value, fold((a5->lanes / a8->lanes))) - a8->value), a8->lanes);
          }
        }
      }
    }
  }
  if (const Sub *a13 = expr->a.as<Sub>()) {
    if (const Broadcast *a14 = a13->b.as<Broadcast>()) {
      if (is_const(a14->lanes)) {
        if (const Broadcast *a15 = expr->b.as<Broadcast>()) {
          if (equal(a14->lanes, a15->lanes)) {
            return (a13->a - broadcast((a14->value + a15->value), a14->lanes));
          }
        }
      }
    }
    if (equal(a13->a, expr->b)) {
      return (0 - a13->b);
    }
    if (const Select *a89 = a13->a.as<Select>()) {
      if (const Select *a90 = expr->b.as<Select>()) {
        if (equal(a89->condition, a90->condition)) {
          return (select(a89->condition, (a89->true_value - a90->true_value), (a89->false_value - a90->false_value)) - a13->b);
        }
      }
    }
    if (is_const(a13->a)) {
      if (const Sub *a99 = expr->b.as<Sub>()) {
        if (is_const(a99->a)) {
          return ((a99->b - a13->b) + fold((a13->a - a99->a)));
        }
      }
      if (const Add *a101 = expr->b.as<Add>()) {
        if (is_const(a101->b)) {
          return (fold((a13->a - a101->b)) - (a13->b + a101->a));
        }
      }
      if (is_const(expr->b)) {
        return (fold((a13->a - expr->b)) - a13->b);
      }
    }
    if (const Mul *a127 = a13->b.as<Mul>()) {
      if (const Mul *a128 = expr->b.as<Mul>()) {
        if (equal(a127->b, a128->b)) {
          return (a13->a - ((a127->a + a128->a) * a127->b));
        }
        if (equal(a127->b, a128->a)) {
          return (a13->a - ((a127->a + a128->b) * a127->b));
        }
        if (equal(a127->a, a128->b)) {
          return (a13->a - (a127->a * (a127->b + a128->a)));
        }
        if (equal(a127->a, a128->a)) {
          return (a13->a - (a127->a * (a127->b + a128->b)));
        }
      }
    }
    if (const Mul *a151 = a13->a.as<Mul>()) {
      if (const Mul *a152 = expr->b.as<Mul>()) {
        if (equal(a151->b, a152->b)) {
          return (((a151->a - a152->a) * a151->b) - a13->b);
        }
        if (equal(a151->b, a152->a)) {
          return (((a151->a - a152->b) * a151->b) - a13->b);
        }
        if (equal(a151->a, a152->b)) {
          return ((a151->a * (a151->b - a152->a)) - a13->b);
        }
        if (equal(a151->a, a152->a)) {
          return ((a151->a * (a151->b - a152->b)) - a13->b);
        }
      }
    }
    if (const Add *a267 = expr->b.as<Add>()) {
      if (equal(a13->a, a267->a)) {
        return ((0 - a13->b) - a267->b);
      }
      if (equal(a13->a, a267->b)) {
        return ((0 - a13->b) - a267->a);
      }
    }
    if (const Add *a271 = a13->a.as<Add>()) {
      if (equal(a271->a, expr->b)) {
        return (a271->b - a13->b);
      }
      if (equal(a271->b, expr->b)) {
        return (a271->a - a13->b);
      }
    }
    if (const Sub *a295 = a13->a.as<Sub>()) {
      if (equal(a295->a, expr->b)) {
        return (0 - (a295->b + a13->b));
      }
    }
  }
  if (const Add *a16 = expr->a.as<Add>()) {
    if (const Broadcast *a17 = a16->b.as<Broadcast>()) {
      if (is_const(a17->lanes)) {
        if (const Broadcast *a18 = expr->b.as<Broadcast>()) {
          if (equal(a17->lanes, a18->lanes)) {
            return (a16->a + broadcast((a17->value - a18->value), a17->lanes));
          }
        }
      }
    }
    if (equal(a16->a, expr->b)) {
      return a16->b;
    }
    if (equal(a16->b, expr->b)) {
      return a16->a;
    }
    if (const Select *a77 = a16->a.as<Select>()) {
      if (const Select *a78 = expr->b.as<Select>()) {
        if (equal(a77->condition, a78->condition)) {
          return (select(a77->condition, (a77->true_value - a78->true_value), (a77->false_value - a78->false_value)) + a16->b);
        }
      }
    }
    if (const Select *a80 = a16->b.as<Select>()) {
      if (const Select *a81 = expr->b.as<Select>()) {
        if (equal(a80->condition, a81->condition)) {
          return (select(a80->condition, (a80->true_value - a81->true_value), (a80->false_value - a81->false_value)) + a16->a);
        }
      }
    }
    if (is_const(a16->b)) {
      if (is_const(expr->b)) {
        return (a16->a + fold((a16->b - expr->b)));
      }
      if (const Sub *a94 = expr->b.as<Sub>()) {
        if (is_const(a94->a)) {
          return ((a16->a + a94->b) + fold((a16->b - a94->a)));
        }
      }
      if (const Add *a96 = expr->b.as<Add>()) {
        if (is_const(a96->b)) {
          return ((a16->a - a96->a) + fold((a16->b - a96->b)));
        }
      }
      return ((a16->a - expr->b) + a16->b);
    }
    if (const Mul *a115 = a16->b.as<Mul>()) {
      if (const Mul *a116 = expr->b.as<Mul>()) {
        if (equal(a115->b, a116->b)) {
          return (a16->a + ((a115->a - a116->a) * a115->b));
        }
        if (equal(a115->b, a116->a)) {
          return (a16->a + ((a115->a - a116->b) * a115->b));
        }
        if (equal(a115->a, a116->b)) {
          return (a16->a + (a115->a * (a115->b - a116->a)));
        }
        if (equal(a115->a, a116->a)) {
          return (a16->a + (a115->a * (a115->b - a116->b)));
        }
      }
    }
    if (const Mul *a139 = a16->a.as<Mul>()) {
      if (const Mul *a140 = expr->b.as<Mul>()) {
        if (equal(a139->b, a140->b)) {
          return (a16->b + ((a139->a - a140->a) * a139->b));
        }
        if (equal(a139->b, a140->a)) {
          return (a16->b + ((a139->a - a140->b) * a139->b));
        }
        if (equal(a139->a, a140->b)) {
          return (a16->b + (a139->a * (a139->b - a140->a)));
        }
        if (equal(a139->a, a140->a)) {
          return (a16->b + (a139->a * (a139->b - a140->b)));
        }
      }
    }
    if (const Add *a211 = expr->b.as<Add>()) {
      if (equal(a16->a, a211->a)) {
        return (a16->b - a211->b);
      }
      if (equal(a16->a, a211->b)) {
        return (a16->b - a211->a);
      }
      if (equal(a16->b, a211->a)) {
        return (a16->a - a211->b);
      }
      if (equal(a16->b, a211->b)) {
        return (a16->a - a211->a);
      }
      if (const Add *a244 = a211->b.as<Add>()) {
        if (equal(a16->a, a244->b)) {
          return (a16->b - (a211->a + a244->a));
        }
        if (equal(a16->b, a244->b)) {
          return (a16->a - (a211->a + a244->a));
        }
        if (equal(a16->a, a244->a)) {
          return (a16->b - (a211->a + a244->b));
        }
        if (equal(a16->b, a244->a)) {
          return (a16->a - (a211->a + a244->b));
        }
      }
      if (const Add *a256 = a211->a.as<Add>()) {
        if (equal(a16->a, a256->a)) {
          return (a16->b - (a256->b + a211->b));
        }
        if (equal(a16->b, a256->a)) {
          return (a16->a - (a256->b + a211->b));
        }
        if (equal(a16->a, a256->b)) {
          return (a16->b - (a256->a + a211->b));
        }
        if (equal(a16->b, a256->b)) {
          return (a16->a - (a256->a + a211->b));
        }
      }
    }
    if (const Add *a219 = a16->a.as<Add>()) {
      if (equal(a219->a, expr->b)) {
        return (a219->b + a16->b);
      }
      if (equal(a219->b, expr->b)) {
        return (a219->a + a16->b);
      }
    }
    if (const Add *a223 = a16->b.as<Add>()) {
      if (equal(a223->a, expr->b)) {
        return (a16->a + a223->b);
      }
      if (equal(a223->b, expr->b)) {
        return (a16->a + a223->a);
      }
    }
    if (const Sub *a231 = a16->b.as<Sub>()) {
      if (equal(a231->a, expr->b)) {
        return (a16->a - a231->b);
      }
    }
    if (const Sub *a233 = a16->a.as<Sub>()) {
      if (equal(a233->a, expr->b)) {
        return (a16->b - a233->b);
      }
    }
    if (const Min *a281 = expr->b.as<Min>()) {
      if (equal(a16->a, a281->a)) {
        if (equal(a16->b, a281->b)) {
          return max(a16->b, a16->a);
        }
      }
      if (equal(a16->b, a281->a)) {
        if (equal(a16->a, a281->b)) {
          return max(a16->b, a16->a);
        }
      }
    }
    if (const Max *a285 = expr->b.as<Max>()) {
      if (equal(a16->a, a285->a)) {
        if (equal(a16->b, a285->b)) {
          return min(a16->b, a16->a);
        }
      }
      if (equal(a16->b, a285->a)) {
        if (equal(a16->a, a285->b)) {
          return min(a16->a, a16->b);
        }
      }
    }
  }
  if (const Select *a25 = expr->a.as<Select>()) {
    if (const Select *a26 = expr->b.as<Select>()) {
      if (equal(a25->condition, a26->condition)) {
        return select(a25->condition, (a25->true_value - a26->true_value), (a25->false_value - a26->false_value));
      }
    }
    if (equal(a25->true_value, expr->b)) {
      return select(a25->condition, 0, (a25->false_value - a25->true_value));
    }
    if (equal(a25->false_value, expr->b)) {
      return select(a25->condition, (a25->true_value - a25->false_value), 0);
    }
    if (const Add *a32 = a25->true_value.as<Add>()) {
      if (equal(a32->a, expr->b)) {
        return select(a25->condition, a32->b, (a25->false_value - a32->a));
      }
      if (equal(a32->b, expr->b)) {
        return select(a25->condition, a32->a, (a25->false_value - a32->b));
      }
      if (const Add *a41 = a32->b.as<Add>()) {
        if (equal(a41->b, expr->b)) {
          return select(a25->condition, (a32->a + a41->a), (a25->false_value - a41->b));
        }
        if (equal(a41->a, expr->b)) {
          return select(a25->condition, (a32->a + a41->b), (a25->false_value - a41->a));
        }
      }
      if (const Add *a47 = a32->a.as<Add>()) {
        if (equal(a47->a, expr->b)) {
          return select(a25->condition, (a32->b + a47->b), (a25->false_value - a47->a));
        }
        if (equal(a47->b, expr->b)) {
          return select(a25->condition, (a32->b + a47->a), (a25->false_value - a47->b));
        }
      }
      if (const Add *a53 = expr->b.as<Add>()) {
        if (equal(a32->a, a53->b)) {
          return (select(a25->condition, a32->b, (a25->false_value - a32->a)) - a53->a);
        }
        if (equal(a32->b, a53->b)) {
          return (select(a25->condition, a32->a, (a25->false_value - a32->b)) - a53->a);
        }
        if (equal(a32->a, a53->a)) {
          return (select(a25->condition, a32->b, (a25->false_value - a32->a)) - a53->b);
        }
        if (equal(a32->b, a53->a)) {
          return (select(a25->condition, a32->a, (a25->false_value - a32->b)) - a53->b);
        }
      }
    }
    if (const Add *a36 = a25->false_value.as<Add>()) {
      if (equal(a36->a, expr->b)) {
        return select(a25->condition, (a25->true_value - a36->a), a36->b);
      }
      if (equal(a36->b, expr->b)) {
        return select(a25->condition, (a25->true_value - a36->b), a36->a);
      }
    }
    if (const Add *a83 = expr->b.as<Add>()) {
      if (const Select *a84 = a83->a.as<Select>()) {
        if (equal(a25->condition, a84->condition)) {
          return (select(a25->condition, (a25->true_value - a84->true_value), (a25->false_value - a84->false_value)) - a83->b);
        }
      }
      if (const Select *a87 = a83->b.as<Select>()) {
        if (equal(a25->condition, a87->condition)) {
          return (select(a25->condition, (a25->true_value - a87->true_value), (a25->false_value - a87->false_value)) - a83->a);
        }
      }
    }
  }
  if (const Select *a29 = expr->b.as<Select>()) {
    if (equal(expr->a, a29->true_value)) {
      return select(a29->condition, 0, (expr->a - a29->false_value));
    }
    if (equal(expr->a, a29->false_value)) {
      return select(a29->condition, (expr->a - a29->true_value), 0);
    }
    if (const Add *a64 = a29->true_value.as<Add>()) {
      if (equal(expr->a, a64->a)) {
        return (0 - select(a29->condition, a64->b, (a29->false_value - expr->a)));
      }
      if (equal(expr->a, a64->b)) {
        return (0 - select(a29->condition, a64->a, (a29->false_value - expr->a)));
      }
    }
    if (const Add *a68 = a29->false_value.as<Add>()) {
      if (equal(expr->a, a68->a)) {
        return (0 - select(a29->condition, (a29->true_value - expr->a), a68->b));
      }
      if (equal(expr->a, a68->b)) {
        return (0 - select(a29->condition, (a29->true_value - expr->a), a68->a));
      }
    }
  }
  if (const Add *a73 = expr->b.as<Add>()) {
    if (equal(expr->a, a73->a)) {
      return (0 - a73->b);
    }
    if (equal(expr->a, a73->b)) {
      return (0 - a73->a);
    }
    if (is_const(a73->b)) {
      return ((expr->a - a73->a) - a73->b);
    }
    if (const Sub *a227 = a73->b.as<Sub>()) {
      if (equal(expr->a, a227->a)) {
        return (a227->b - a73->a);
      }
    }
    if (const Sub *a229 = a73->a.as<Sub>()) {
      if (equal(expr->a, a229->a)) {
        return (a229->b - a73->b);
      }
    }
    if (const Add *a235 = a73->b.as<Add>()) {
      if (equal(expr->a, a235->a)) {
        return (0 - (a73->a + a235->b));
      }
      if (equal(expr->a, a235->b)) {
        return (0 - (a73->a + a235->a));
      }
    }
    if (const Add *a239 = a73->a.as<Add>()) {
      if (equal(expr->a, a239->a)) {
        return (0 - (a239->b + a73->b));
      }
      if (equal(expr->a, a239->b)) {
        return (0 - (a239->a + a73->b));
      }
    }
  }
  if (const Sub *a102 = expr->b.as<Sub>()) {
    return (expr->a + (a102->b - a102->a));
  }
  if (const Mul *a103 = expr->b.as<Mul>()) {
    if (is_const(a103->b)) {
      if (evaluate_predicate(fold(((a103->b < 0) && (0 - (a103->b > 0)))))) {
        return (expr->a + (a103->a * fold((0 - a103->b))));
      }
    }
    if (const Div *a298 = a103->a.as<Div>()) {
      if (const Add *a299 = a298->a.as<Add>()) {
        if (equal(expr->a, a299->a)) {
          if (is_const(a299->b)) {
            if (is_const(a298->b)) {
              if (equal(a298->b, a103->b)) {
                if (evaluate_predicate(fold((a298->b > 0)))) {
                  return (((expr->a + a299->b) % a298->b) - a299->b);
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Mul *a106 = expr->a.as<Mul>()) {
    if (const Mul *a107 = expr->b.as<Mul>()) {
      if (equal(a106->b, a107->b)) {
        return ((a106->a - a107->a) * a106->b);
      }
      if (equal(a106->b, a107->a)) {
        return ((a106->a - a107->b) * a106->b);
      }
      if (equal(a106->a, a107->b)) {
        return (a106->a * (a106->b - a107->a));
      }
      if (equal(a106->a, a107->a)) {
        return (a106->a * (a106->b - a107->b));
      }
    }
    if (const Add *a163 = expr->b.as<Add>()) {
      if (const Mul *a164 = a163->b.as<Mul>()) {
        if (equal(a106->b, a164->b)) {
          return (((a106->a - a164->a) * a106->b) - a163->a);
        }
        if (equal(a106->b, a164->a)) {
          return (((a106->a - a164->b) * a106->b) - a163->a);
        }
        if (equal(a106->a, a164->b)) {
          return ((a106->a * (a106->b - a164->a)) - a163->a);
        }
        if (equal(a106->a, a164->a)) {
          return ((a106->a * (a106->b - a164->b)) - a163->a);
        }
      }
      if (const Mul *a188 = a163->a.as<Mul>()) {
        if (equal(a106->b, a188->b)) {
          return (((a106->a - a188->a) * a106->b) - a163->b);
        }
        if (equal(a106->b, a188->a)) {
          return (((a106->a - a188->b) * a106->b) - a163->b);
        }
        if (equal(a106->a, a188->b)) {
          return ((a106->a * (a106->b - a188->a)) - a163->b);
        }
        if (equal(a106->a, a188->a)) {
          return ((a106->a * (a106->b - a188->b)) - a163->b);
        }
      }
    }
    if (const Sub *a175 = expr->b.as<Sub>()) {
      if (const Mul *a176 = a175->b.as<Mul>()) {
        if (equal(a106->b, a176->b)) {
          return (((a106->a + a176->a) * a106->b) - a175->a);
        }
        if (equal(a106->b, a176->a)) {
          return (((a106->a + a176->b) * a106->b) - a175->a);
        }
        if (equal(a106->a, a176->b)) {
          return ((a106->a * (a106->b + a176->a)) - a175->a);
        }
        if (equal(a106->a, a176->a)) {
          return ((a106->a * (a106->b + a176->b)) - a175->a);
        }
      }
      if (const Mul *a200 = a175->a.as<Mul>()) {
        if (equal(a106->b, a200->b)) {
          return (((a106->a - a200->a) * a106->b) + a175->b);
        }
        if (equal(a106->b, a200->a)) {
          return (((a106->a - a200->b) * a106->b) + a175->b);
        }
        if (equal(a106->a, a200->b)) {
          return ((a106->a * (a106->b - a200->a)) + a175->b);
        }
        if (equal(a106->a, a200->a)) {
          return ((a106->a * (a106->b - a200->b)) + a175->b);
        }
      }
    }
  }
  if (const Min *a274 = expr->b.as<Min>()) {
    if (const Sub *a275 = a274->a.as<Sub>()) {
      if (equal(expr->a, a275->a)) {
        if (is_const_int(a274->b, 0)) {
          return max(expr->a, a275->b);
        }
      }
    }
  }
  if (const Max *a277 = expr->b.as<Max>()) {
    if (const Sub *a278 = a277->a.as<Sub>()) {
      if (equal(expr->a, a278->a)) {
        if (is_const_int(a277->b, 0)) {
          return min(expr->a, a278->b);
        }
      }
    }
  }
  if (is_const_int(expr->a, 0)) {
    if (const Add *a289 = expr->b.as<Add>()) {
      if (const Sub *a290 = a289->b.as<Sub>()) {
        return (a290->b - (a289->a + a290->a));
      }
      if (const Sub *a293 = a289->a.as<Sub>()) {
        return (a293->b - (a293->a + a289->b));
      }
    }
  }
  if (const Mod *a296 = expr->b.as<Mod>()) {
    if (equal(expr->a, a296->a)) {
      if (is_const(a296->b)) {
        return ((expr->a / a296->b) * a296->b);
      }
    }
  }
  if (is_no_overflow(expr)) {
    if (const Max *a300 = expr->a.as<Max>()) {
      if (equal(a300->a, expr->b)) {
        return max((a300->b - a300->a), 0);
      }
      if (equal(a300->b, expr->b)) {
        return max((a300->a - a300->b), 0);
      }
      if (const Sub *a320 = a300->a.as<Sub>()) {
        if (is_const_int(a300->b, 0)) {
          if (equal(a320->a, expr->b)) {
            return (0 - min(a320->a, a320->b));
          }
        }
      }
      if (const Add *a327 = expr->b.as<Add>()) {
        if (equal(a300->a, a327->a)) {
          if (equal(a300->b, a327->b)) {
            return (0 - min(a300->a, a300->b));
          }
        }
        if (equal(a300->b, a327->a)) {
          if (equal(a300->a, a327->b)) {
            return (0 - min(a300->b, a300->a));
          }
        }
      }
      if (const Add *a451 = a300->a.as<Add>()) {
        if (equal(a451->a, expr->b)) {
          return max((a300->b - a451->a), a451->b);
        }
        if (equal(a451->b, expr->b)) {
          return max((a300->b - a451->b), a451->a);
        }
        if (const Add *a472 = a451->b.as<Add>()) {
          if (equal(a472->b, expr->b)) {
            return max((a300->b - a472->b), (a451->a + a472->a));
          }
          if (equal(a472->a, expr->b)) {
            return max((a300->b - a472->a), (a451->a + a472->b));
          }
        }
        if (const Add *a478 = a451->a.as<Add>()) {
          if (equal(a478->b, expr->b)) {
            return max((a300->b - a478->b), (a478->a + a451->b));
          }
          if (equal(a478->a, expr->b)) {
            return max((a300->b - a478->a), (a478->b + a451->b));
          }
        }
        if (is_const(a451->b)) {
          if (const Max *a590 = expr->b.as<Max>()) {
            if (equal(a451->a, a590->a)) {
              if (evaluate_predicate(fold(can_prove((a300->b >= (a590->b + a451->b)), simplifier)))) {
                return max((a300->b - max(a451->a, a590->b)), a451->b);
              }
              if (evaluate_predicate(fold(can_prove((a300->b <= (a590->b + a451->b)), simplifier)))) {
                return min((max((a451->a + a451->b), a300->b) - a590->b), a451->b);
              }
            }
            if (const Add *a603 = a590->a.as<Add>()) {
              if (equal(a451->a, a603->a)) {
                if (is_const(a603->b)) {
                  if (evaluate_predicate(fold(can_prove(((a300->b + a603->b) >= (a590->b + a451->b)), simplifier)))) {
                    return max((a300->b - max((a451->a + a603->b), a590->b)), fold((a451->b - a603->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a300->b + a603->b) <= (a590->b + a451->b)), simplifier)))) {
                    return min((max((a451->a + a451->b), a300->b) - a590->b), fold((a451->b - a603->b)));
                  }
                }
              }
            }
            if (equal(a451->a, a590->b)) {
              if (evaluate_predicate(fold(can_prove((a300->b >= (a590->a + a451->b)), simplifier)))) {
                return max((a300->b - max(a451->a, a590->a)), a451->b);
              }
              if (evaluate_predicate(fold(can_prove((a300->b <= (a590->a + a451->b)), simplifier)))) {
                return min((max((a451->a + a451->b), a300->b) - a590->a), a451->b);
              }
            }
            if (const Add *a651 = a590->b.as<Add>()) {
              if (equal(a451->a, a651->a)) {
                if (is_const(a651->b)) {
                  if (evaluate_predicate(fold(can_prove(((a300->b + a651->b) >= (a590->a + a451->b)), simplifier)))) {
                    return max((a300->b - max((a451->a + a651->b), a590->a)), fold((a451->b - a651->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a300->b + a651->b) <= (a590->a + a451->b)), simplifier)))) {
                    return min((max((a451->a + a451->b), a300->b) - a590->a), fold((a451->b - a651->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a455 = a300->b.as<Add>()) {
        if (equal(a455->a, expr->b)) {
          return max((a300->a - a455->a), a455->b);
        }
        if (equal(a455->b, expr->b)) {
          return max((a300->a - a455->b), a455->a);
        }
        if (const Add *a460 = a455->b.as<Add>()) {
          if (equal(a460->b, expr->b)) {
            return max((a300->a - a460->b), (a455->a + a460->a));
          }
          if (equal(a460->a, expr->b)) {
            return max((a300->a - a460->a), (a455->a + a460->b));
          }
        }
        if (const Add *a466 = a455->a.as<Add>()) {
          if (equal(a466->b, expr->b)) {
            return max((a300->a - a466->b), (a466->a + a455->b));
          }
          if (equal(a466->a, expr->b)) {
            return max((a300->a - a466->a), (a466->b + a455->b));
          }
        }
        if (is_const(a455->b)) {
          if (const Max *a614 = expr->b.as<Max>()) {
            if (equal(a455->a, a614->b)) {
              if (evaluate_predicate(fold(can_prove((a300->a >= (a614->a + a455->b)), simplifier)))) {
                return max((a300->a - max(a455->a, a614->a)), a455->b);
              }
              if (evaluate_predicate(fold(can_prove((a300->a <= (a614->a + a455->b)), simplifier)))) {
                return min((max((a455->a + a455->b), a300->a) - a614->a), a455->b);
              }
            }
            if (const Add *a627 = a614->b.as<Add>()) {
              if (equal(a455->a, a627->a)) {
                if (is_const(a627->b)) {
                  if (evaluate_predicate(fold(can_prove(((a300->a + a627->b) >= (a614->a + a455->b)), simplifier)))) {
                    return max((a300->a - max((a455->a + a627->b), a614->a)), fold((a455->b - a627->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a300->a + a627->b) <= (a614->a + a455->b)), simplifier)))) {
                    return min((max((a455->a + a455->b), a300->a) - a614->a), fold((a455->b - a627->b)));
                  }
                }
              }
            }
            if (equal(a455->a, a614->a)) {
              if (evaluate_predicate(fold(can_prove((a300->a >= (a614->b + a455->b)), simplifier)))) {
                return max((a300->a - max(a455->a, a614->b)), a455->b);
              }
              if (evaluate_predicate(fold(can_prove((a300->a <= (a614->b + a455->b)), simplifier)))) {
                return min((max((a455->a + a455->b), a300->a) - a614->b), a455->b);
              }
            }
            if (const Add *a675 = a614->a.as<Add>()) {
              if (equal(a455->a, a675->a)) {
                if (is_const(a675->b)) {
                  if (evaluate_predicate(fold(can_prove(((a300->a + a675->b) >= (a614->b + a455->b)), simplifier)))) {
                    return max((a300->a - max((a455->a + a675->b), a614->b)), fold((a455->b - a675->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a300->a + a675->b) <= (a614->b + a455->b)), simplifier)))) {
                    return min((max((a455->a + a455->b), a300->a) - a614->b), fold((a455->b - a675->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Max *a483 = expr->b.as<Max>()) {
        if (equal(a300->b, a483->a)) {
          if (equal(a300->a, a483->b)) {
            return 0;
          }
          if (evaluate_predicate(fold(can_prove((a300->a >= a483->b), simplifier)))) {
            return max((a300->a - max(a300->b, a483->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a300->a <= a483->b), simplifier)))) {
            return min((max(a300->b, a300->a) - a483->b), 0);
          }
        }
        if (evaluate_predicate(fold(can_prove(((a300->a - a300->b) == (a483->a - a483->b)), simplifier)))) {
          return (a300->b - a483->b);
        }
        if (evaluate_predicate(fold(can_prove(((a300->a - a300->b) == (a483->b - a483->a)), simplifier)))) {
          return (a300->b - a483->a);
        }
        if (equal(a300->a, a483->a)) {
          if (evaluate_predicate(fold(can_prove((a300->b >= a483->b), simplifier)))) {
            return max((a300->b - max(a300->a, a483->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a300->b <= a483->b), simplifier)))) {
            return min((max(a300->a, a300->b) - a483->b), 0);
          }
        }
        if (const Add *a596 = a483->a.as<Add>()) {
          if (equal(a300->a, a596->a)) {
            if (is_const(a596->b)) {
              if (evaluate_predicate(fold(can_prove(((a300->b + a596->b) >= a483->b), simplifier)))) {
                return max((a300->b - max((a300->a + a596->b), a483->b)), fold((0 - a596->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a300->b + a596->b) <= a483->b), simplifier)))) {
                return min((max(a300->a, a300->b) - a483->b), fold((0 - a596->b)));
              }
            }
          }
          if (equal(a300->b, a596->a)) {
            if (is_const(a596->b)) {
              if (evaluate_predicate(fold(can_prove(((a300->a + a596->b) >= a483->b), simplifier)))) {
                return max((a300->a - max((a300->b + a596->b), a483->b)), fold((0 - a596->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a300->a + a596->b) <= a483->b), simplifier)))) {
                return min((max(a300->b, a300->a) - a483->b), fold((0 - a596->b)));
              }
            }
          }
        }
        if (equal(a300->b, a483->b)) {
          if (evaluate_predicate(fold(can_prove((a300->a >= a483->a), simplifier)))) {
            return max((a300->a - max(a300->b, a483->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a300->a <= a483->a), simplifier)))) {
            return min((max(a300->b, a300->a) - a483->a), 0);
          }
        }
        if (const Add *a620 = a483->b.as<Add>()) {
          if (equal(a300->b, a620->a)) {
            if (is_const(a620->b)) {
              if (evaluate_predicate(fold(can_prove(((a300->a + a620->b) >= a483->a), simplifier)))) {
                return max((a300->a - max((a300->b + a620->b), a483->a)), fold((0 - a620->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a300->a + a620->b) <= a483->a), simplifier)))) {
                return min((max(a300->b, a300->a) - a483->a), fold((0 - a620->b)));
              }
            }
          }
          if (equal(a300->a, a620->a)) {
            if (is_const(a620->b)) {
              if (evaluate_predicate(fold(can_prove(((a300->b + a620->b) >= a483->a), simplifier)))) {
                return max((a300->b - max((a300->a + a620->b), a483->a)), fold((0 - a620->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a300->b + a620->b) <= a483->a), simplifier)))) {
                return min((max(a300->a, a300->b) - a483->a), fold((0 - a620->b)));
              }
            }
          }
        }
        if (equal(a300->a, a483->b)) {
          if (evaluate_predicate(fold(can_prove((a300->b >= a483->a), simplifier)))) {
            return max((a300->b - max(a300->a, a483->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a300->b <= a483->a), simplifier)))) {
            return min((max(a300->a, a300->b) - a483->a), 0);
          }
        }
      }
    }
    if (const Min *a301 = expr->a.as<Min>()) {
      if (equal(a301->a, expr->b)) {
        return min((a301->b - a301->a), 0);
      }
      if (equal(a301->b, expr->b)) {
        return min((a301->a - a301->b), 0);
      }
      if (const Sub *a317 = a301->a.as<Sub>()) {
        if (is_const_int(a301->b, 0)) {
          if (equal(a317->a, expr->b)) {
            return (0 - max(a317->a, a317->b));
          }
        }
      }
      if (const Add *a323 = expr->b.as<Add>()) {
        if (equal(a301->a, a323->a)) {
          if (equal(a301->b, a323->b)) {
            return (0 - max(a301->b, a301->a));
          }
        }
        if (equal(a301->b, a323->a)) {
          if (equal(a301->a, a323->b)) {
            return (0 - max(a301->a, a301->b));
          }
        }
      }
      if (const Add *a377 = a301->a.as<Add>()) {
        if (equal(a377->a, expr->b)) {
          return min((a301->b - a377->a), a377->b);
        }
        if (equal(a377->b, expr->b)) {
          return min((a301->b - a377->b), a377->a);
        }
        if (const Add *a398 = a377->b.as<Add>()) {
          if (equal(a398->b, expr->b)) {
            return min((a301->b - a398->b), (a377->a + a398->a));
          }
          if (equal(a398->a, expr->b)) {
            return min((a301->b - a398->a), (a377->a + a398->b));
          }
        }
        if (const Add *a404 = a377->a.as<Add>()) {
          if (equal(a404->b, expr->b)) {
            return min((a301->b - a404->b), (a404->a + a377->b));
          }
          if (equal(a404->a, expr->b)) {
            return min((a301->b - a404->a), (a404->b + a377->b));
          }
        }
        if (is_const(a377->b)) {
          if (const Min *a494 = expr->b.as<Min>()) {
            if (equal(a377->a, a494->a)) {
              if (evaluate_predicate(fold(can_prove((a301->b <= (a494->b + a377->b)), simplifier)))) {
                return min((a301->b - min(a377->a, a494->b)), a377->b);
              }
              if (evaluate_predicate(fold(can_prove((a301->b >= (a494->b + a377->b)), simplifier)))) {
                return max((min((a377->a + a377->b), a301->b) - a494->b), a377->b);
              }
            }
            if (const Add *a507 = a494->a.as<Add>()) {
              if (equal(a377->a, a507->a)) {
                if (is_const(a507->b)) {
                  if (evaluate_predicate(fold(can_prove(((a301->b + a507->b) <= (a494->b + a377->b)), simplifier)))) {
                    return min((a301->b - min((a377->a + a507->b), a494->b)), fold((a377->b - a507->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a301->b + a507->b) >= (a494->b + a377->b)), simplifier)))) {
                    return max((min((a377->a + a377->b), a301->b) - a494->b), fold((a377->b - a507->b)));
                  }
                }
              }
            }
            if (equal(a377->a, a494->b)) {
              if (evaluate_predicate(fold(can_prove((a301->b <= (a494->a + a377->b)), simplifier)))) {
                return min((a301->b - min(a377->a, a494->a)), a377->b);
              }
              if (evaluate_predicate(fold(can_prove((a301->b >= (a494->a + a377->b)), simplifier)))) {
                return max((min((a377->a + a377->b), a301->b) - a494->a), a377->b);
              }
            }
            if (const Add *a555 = a494->b.as<Add>()) {
              if (equal(a377->a, a555->a)) {
                if (is_const(a555->b)) {
                  if (evaluate_predicate(fold(can_prove(((a301->b + a555->b) <= (a494->a + a377->b)), simplifier)))) {
                    return min((a301->b - min((a377->a + a555->b), a494->a)), fold((a377->b - a555->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a301->b + a555->b) >= (a494->a + a377->b)), simplifier)))) {
                    return max((min((a377->a + a377->b), a301->b) - a494->a), fold((a377->b - a555->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a381 = a301->b.as<Add>()) {
        if (equal(a381->a, expr->b)) {
          return min((a301->a - a381->a), a381->b);
        }
        if (equal(a381->b, expr->b)) {
          return min((a301->a - a381->b), a381->a);
        }
        if (const Add *a386 = a381->b.as<Add>()) {
          if (equal(a386->b, expr->b)) {
            return min((a301->a - a386->b), (a381->a + a386->a));
          }
          if (equal(a386->a, expr->b)) {
            return min((a301->a - a386->a), (a381->a + a386->b));
          }
        }
        if (const Add *a392 = a381->a.as<Add>()) {
          if (equal(a392->b, expr->b)) {
            return min((a301->a - a392->b), (a392->a + a381->b));
          }
          if (equal(a392->a, expr->b)) {
            return min((a301->a - a392->a), (a392->b + a381->b));
          }
        }
        if (is_const(a381->b)) {
          if (const Min *a518 = expr->b.as<Min>()) {
            if (equal(a381->a, a518->b)) {
              if (evaluate_predicate(fold(can_prove((a301->a <= (a518->a + a381->b)), simplifier)))) {
                return min((a301->a - min(a381->a, a518->a)), a381->b);
              }
              if (evaluate_predicate(fold(can_prove((a301->a >= (a518->a + a381->b)), simplifier)))) {
                return max((min((a381->a + a381->b), a301->a) - a518->a), a381->b);
              }
            }
            if (const Add *a531 = a518->b.as<Add>()) {
              if (equal(a381->a, a531->a)) {
                if (is_const(a531->b)) {
                  if (evaluate_predicate(fold(can_prove(((a301->a + a531->b) <= (a518->a + a381->b)), simplifier)))) {
                    return min((a301->a - min((a381->a + a531->b), a518->a)), fold((a381->b - a531->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a301->a + a531->b) >= (a518->a + a381->b)), simplifier)))) {
                    return max((min((a381->a + a381->b), a301->a) - a518->a), fold((a381->b - a531->b)));
                  }
                }
              }
            }
            if (equal(a381->a, a518->a)) {
              if (evaluate_predicate(fold(can_prove((a301->a <= (a518->b + a381->b)), simplifier)))) {
                return min((a301->a - min(a381->a, a518->b)), a381->b);
              }
              if (evaluate_predicate(fold(can_prove((a301->a >= (a518->b + a381->b)), simplifier)))) {
                return max((min((a381->a + a381->b), a301->a) - a518->b), a381->b);
              }
            }
            if (const Add *a579 = a518->a.as<Add>()) {
              if (equal(a381->a, a579->a)) {
                if (is_const(a579->b)) {
                  if (evaluate_predicate(fold(can_prove(((a301->a + a579->b) <= (a518->b + a381->b)), simplifier)))) {
                    return min((a301->a - min((a381->a + a579->b), a518->b)), fold((a381->b - a579->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((a301->a + a579->b) >= (a518->b + a381->b)), simplifier)))) {
                    return max((min((a381->a + a381->b), a301->a) - a518->b), fold((a381->b - a579->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a409 = expr->b.as<Min>()) {
        if (equal(a301->b, a409->a)) {
          if (equal(a301->a, a409->b)) {
            return 0;
          }
          if (evaluate_predicate(fold(can_prove((a301->a <= a409->b), simplifier)))) {
            return min((a301->a - min(a301->b, a409->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a301->a >= a409->b), simplifier)))) {
            return max((min(a301->b, a301->a) - a409->b), 0);
          }
        }
        if (evaluate_predicate(fold(can_prove(((a301->a - a301->b) == (a409->a - a409->b)), simplifier)))) {
          return (a301->b - a409->b);
        }
        if (evaluate_predicate(fold(can_prove(((a301->a - a301->b) == (a409->b - a409->a)), simplifier)))) {
          return (a301->b - a409->a);
        }
        if (equal(a301->a, a409->a)) {
          if (evaluate_predicate(fold(can_prove((a301->b <= a409->b), simplifier)))) {
            return min((a301->b - min(a301->a, a409->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a301->b >= a409->b), simplifier)))) {
            return max((min(a301->a, a301->b) - a409->b), 0);
          }
        }
        if (const Add *a500 = a409->a.as<Add>()) {
          if (equal(a301->a, a500->a)) {
            if (is_const(a500->b)) {
              if (evaluate_predicate(fold(can_prove(((a301->b + a500->b) <= a409->b), simplifier)))) {
                return min((a301->b - min((a301->a + a500->b), a409->b)), fold((0 - a500->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a301->b + a500->b) >= a409->b), simplifier)))) {
                return max((min(a301->a, a301->b) - a409->b), fold((0 - a500->b)));
              }
            }
          }
          if (equal(a301->b, a500->a)) {
            if (is_const(a500->b)) {
              if (evaluate_predicate(fold(can_prove(((a301->a + a500->b) <= a409->b), simplifier)))) {
                return min((a301->a - min((a301->b + a500->b), a409->b)), fold((0 - a500->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a301->a + a500->b) >= a409->b), simplifier)))) {
                return max((min(a301->b, a301->a) - a409->b), fold((0 - a500->b)));
              }
            }
          }
        }
        if (equal(a301->b, a409->b)) {
          if (evaluate_predicate(fold(can_prove((a301->a <= a409->a), simplifier)))) {
            return min((a301->a - min(a301->b, a409->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a301->a >= a409->a), simplifier)))) {
            return max((min(a301->b, a301->a) - a409->a), 0);
          }
        }
        if (const Add *a524 = a409->b.as<Add>()) {
          if (equal(a301->b, a524->a)) {
            if (is_const(a524->b)) {
              if (evaluate_predicate(fold(can_prove(((a301->a + a524->b) <= a409->a), simplifier)))) {
                return min((a301->a - min((a301->b + a524->b), a409->a)), fold((0 - a524->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a301->a + a524->b) >= a409->a), simplifier)))) {
                return max((min(a301->b, a301->a) - a409->a), fold((0 - a524->b)));
              }
            }
          }
          if (equal(a301->a, a524->a)) {
            if (is_const(a524->b)) {
              if (evaluate_predicate(fold(can_prove(((a301->b + a524->b) <= a409->a), simplifier)))) {
                return min((a301->b - min((a301->a + a524->b), a409->a)), fold((0 - a524->b)));
              }
              if (evaluate_predicate(fold(can_prove(((a301->b + a524->b) >= a409->a), simplifier)))) {
                return max((min(a301->a, a301->b) - a409->a), fold((0 - a524->b)));
              }
            }
          }
        }
        if (equal(a301->a, a409->b)) {
          if (evaluate_predicate(fold(can_prove((a301->b <= a409->a), simplifier)))) {
            return min((a301->b - min(a301->a, a409->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((a301->b >= a409->a), simplifier)))) {
            return max((min(a301->a, a301->b) - a409->a), 0);
          }
        }
      }
      if (const Mul *a415 = a301->a.as<Mul>()) {
        if (is_const(a415->b)) {
          if (is_const(a301->b)) {
            if (const Mul *a416 = expr->b.as<Mul>()) {
              if (const Min *a417 = a416->a.as<Min>()) {
                if (equal(a415->a, a417->a)) {
                  if (is_const(a417->b)) {
                    if (equal(a415->b, a416->b)) {
                      if (evaluate_predicate(fold(((a415->b > 0) && (a301->b <= (a417->b * a415->b)))))) {
                        return min((a301->b - (min(a415->a, a417->b) * a415->b)), 0);
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    if (const Max *a304 = expr->b.as<Max>()) {
      if (equal(expr->a, a304->a)) {
        if (evaluate_predicate(fold(!(is_const(expr->a))))) {
          return min((expr->a - a304->b), 0);
        }
      }
      if (equal(expr->a, a304->b)) {
        if (evaluate_predicate(fold(!(is_const(expr->a))))) {
          return min((expr->a - a304->a), 0);
        }
      }
      if (const Sub *a313 = a304->b.as<Sub>()) {
        if (equal(expr->a, a313->a)) {
          return min((expr->a - a304->a), a313->b);
        }
      }
      if (const Sub *a315 = a304->a.as<Sub>()) {
        if (equal(expr->a, a315->a)) {
          return min(a315->b, (expr->a - a304->b));
        }
        if (is_const(a304->b)) {
          return (expr->a + min((a315->b - a315->a), fold((0 - a304->b))));
        }
      }
      if (const Min *a335 = a304->a.as<Min>()) {
        if (const Sub *a336 = a335->a.as<Sub>()) {
          if (is_const(a335->b)) {
            if (is_const(a304->b)) {
              return (expr->a + min(max((a336->b - a336->a), fold((0 - a335->b))), fold((0 - a304->b))));
            }
          }
        }
      }
      if (const Add *a419 = a304->b.as<Add>()) {
        if (equal(expr->a, a419->a)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - max((a304->a - expr->a), a419->b));
          }
        }
        if (equal(expr->a, a419->b)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - max((a304->a - expr->a), a419->a));
          }
        }
        if (const Add *a428 = a419->b.as<Add>()) {
          if (equal(expr->a, a428->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->a - expr->a), (a419->a + a428->b)));
            }
          }
          if (equal(expr->a, a428->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->a - expr->a), (a428->a + a419->a)));
            }
          }
        }
        if (const Add *a434 = a419->a.as<Add>()) {
          if (equal(expr->a, a434->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->a - expr->a), (a434->b + a419->b)));
            }
          }
          if (equal(expr->a, a434->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->a - expr->a), (a434->a + a419->b)));
            }
          }
        }
      }
      if (const Add *a423 = a304->a.as<Add>()) {
        if (equal(expr->a, a423->a)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - max((a304->b - expr->a), a423->b));
          }
        }
        if (equal(expr->a, a423->b)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - max((a304->b - expr->a), a423->a));
          }
        }
        if (const Add *a440 = a423->b.as<Add>()) {
          if (equal(expr->a, a440->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->b - expr->a), (a423->a + a440->b)));
            }
          }
          if (equal(expr->a, a440->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->b - expr->a), (a440->a + a423->a)));
            }
          }
        }
        if (const Add *a446 = a423->a.as<Add>()) {
          if (equal(expr->a, a446->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->b - expr->a), (a423->b + a446->b)));
            }
          }
          if (equal(expr->a, a446->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - max((a304->b - expr->a), (a423->b + a446->a)));
            }
          }
        }
      }
    }
    if (const Min *a305 = expr->b.as<Min>()) {
      if (equal(expr->a, a305->a)) {
        if (evaluate_predicate(fold(!(is_const(expr->a))))) {
          return max((expr->a - a305->b), 0);
        }
      }
      if (equal(expr->a, a305->b)) {
        if (evaluate_predicate(fold(!(is_const(expr->a))))) {
          return max((expr->a - a305->a), 0);
        }
      }
      if (const Sub *a309 = a305->b.as<Sub>()) {
        if (equal(expr->a, a309->a)) {
          return max((expr->a - a305->a), a309->b);
        }
      }
      if (const Sub *a311 = a305->a.as<Sub>()) {
        if (equal(expr->a, a311->a)) {
          return max(a311->b, (expr->a - a305->b));
        }
        if (is_const(a305->b)) {
          return (expr->a + max((a311->b - a311->a), fold((0 - a305->b))));
        }
      }
      if (const Max *a338 = a305->a.as<Max>()) {
        if (const Sub *a339 = a338->a.as<Sub>()) {
          if (is_const(a338->b)) {
            if (is_const(a305->b)) {
              return (expr->a + max(min((a339->b - a339->a), fold((0 - a338->b))), fold((0 - a305->b))));
            }
          }
        }
      }
      if (const Add *a345 = a305->b.as<Add>()) {
        if (equal(expr->a, a345->a)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - min((a305->a - expr->a), a345->b));
          }
        }
        if (equal(expr->a, a345->b)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - min((a305->a - expr->a), a345->a));
          }
        }
        if (const Add *a354 = a345->b.as<Add>()) {
          if (equal(expr->a, a354->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->a - expr->a), (a345->a + a354->b)));
            }
          }
          if (equal(expr->a, a354->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->a - expr->a), (a354->a + a345->a)));
            }
          }
        }
        if (const Add *a360 = a345->a.as<Add>()) {
          if (equal(expr->a, a360->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->a - expr->a), (a360->b + a345->b)));
            }
          }
          if (equal(expr->a, a360->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->a - expr->a), (a360->a + a345->b)));
            }
          }
        }
      }
      if (const Add *a349 = a305->a.as<Add>()) {
        if (equal(expr->a, a349->a)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - min((a305->b - expr->a), a349->b));
          }
        }
        if (equal(expr->a, a349->b)) {
          if (evaluate_predicate(fold(!(is_const(expr->a))))) {
            return (0 - min((a305->b - expr->a), a349->a));
          }
        }
        if (const Add *a366 = a349->b.as<Add>()) {
          if (equal(expr->a, a366->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->b - expr->a), (a349->a + a366->b)));
            }
          }
          if (equal(expr->a, a366->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->b - expr->a), (a366->a + a349->a)));
            }
          }
        }
        if (const Add *a372 = a349->a.as<Add>()) {
          if (equal(expr->a, a372->a)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->b - expr->a), (a349->b + a372->b)));
            }
          }
          if (equal(expr->a, a372->b)) {
            if (evaluate_predicate(fold(!(is_const(expr->a))))) {
              return (0 - min((a305->b - expr->a), (a349->b + a372->a)));
            }
          }
        }
      }
    }
    if (const Mul *a340 = expr->a.as<Mul>()) {
      if (equal(a340->a, expr->b)) {
        return (a340->a * (a340->b - 1));
      }
      if (equal(a340->b, expr->b)) {
        return ((a340->a - 1) * a340->b);
      }
    }
    if (const Mul *a342 = expr->b.as<Mul>()) {
      if (equal(expr->a, a342->a)) {
        return (expr->a * (1 - a342->b));
      }
      if (equal(expr->a, a342->b)) {
        return ((1 - a342->a) * expr->a);
      }
    }
  }
  if (is_no_overflow_int(expr)) {
    if (is_const(expr->a)) {
      if (const Div *a680 = expr->b.as<Div>()) {
        if (const Sub *a681 = a680->a.as<Sub>()) {
          if (is_const(a681->a)) {
            if (is_const(a680->b)) {
              if (evaluate_predicate(fold((a680->b > 0)))) {
                return ((fold(((((expr->a * a680->b) - a681->a) + a680->b) - 1)) + a681->b) / a680->b);
              }
            }
          }
        }
        if (const Add *a683 = a680->a.as<Add>()) {
          if (is_const(a683->b)) {
            if (is_const(a680->b)) {
              if (evaluate_predicate(fold((a680->b > 0)))) {
                return ((fold(((((expr->a * a680->b) - a683->b) + a680->b) - 1)) - a683->a) / a680->b);
              }
            }
          }
        }
      }
    }
    if (const Div *a684 = expr->b.as<Div>()) {
      if (const Add *a685 = a684->a.as<Add>()) {
        if (equal(expr->a, a685->a)) {
          if (is_const(a684->b)) {
            if (evaluate_predicate(fold((a684->b > 0)))) {
              return ((((expr->a * fold((a684->b - 1))) - a685->b) + fold((a684->b - 1))) / a684->b);
            }
          }
        }
        if (equal(expr->a, a685->b)) {
          if (is_const(a684->b)) {
            if (evaluate_predicate(fold((a684->b > 0)))) {
              return ((((expr->a * fold((a684->b - 1))) - a685->a) + fold((a684->b - 1))) / a684->b);
            }
          }
        }
      }
      if (const Sub *a687 = a684->a.as<Sub>()) {
        if (equal(expr->a, a687->a)) {
          if (is_const(a684->b)) {
            if (evaluate_predicate(fold((a684->b > 0)))) {
              return ((((expr->a * fold((a684->b - 1))) + a687->b) + fold((a684->b - 1))) / a684->b);
            }
          }
        }
        if (equal(expr->a, a687->b)) {
          if (is_const(a684->b)) {
            if (evaluate_predicate(fold((a684->b > 0)))) {
              return ((((expr->a * fold((a684->b + 1))) - a687->a) + fold((a684->b - 1))) / a684->b);
            }
          }
        }
      }
    }
    if (const Div *a692 = expr->a.as<Div>()) {
      if (const Add *a693 = a692->a.as<Add>()) {
        if (is_const(a692->b)) {
          if (equal(a693->a, expr->b)) {
            return (((a693->a * fold((1 - a692->b))) + a693->b) / a692->b);
          }
          if (equal(a693->b, expr->b)) {
            return ((a693->a + (a693->b * fold((1 - a692->b)))) / a692->b);
          }
          if (const Div *a722 = expr->b.as<Div>()) {
            if (const Add *a723 = a722->a.as<Add>()) {
              if (equal(a693->b, a723->a)) {
                if (equal(a693->a, a723->b)) {
                  if (equal(a692->b, a722->b)) {
                    if (evaluate_predicate(fold((a692->b != 0)))) {
                      return 0;
                    }
                  }
                }
              }
              if (equal(a693->a, a723->a)) {
                if (is_const(a723->b)) {
                  if (equal(a692->b, a722->b)) {
                    if (evaluate_predicate(fold((a692->b > 0)))) {
                      return ((((a693->a + fold((a723->b % a692->b))) % a692->b) + (a693->b - a723->b)) / a692->b);
                    }
                  }
                }
              }
            }
            if (equal(a693->a, a722->a)) {
              if (equal(a692->b, a722->b)) {
                if (evaluate_predicate(fold((a692->b > 0)))) {
                  return (((a693->a % a692->b) + a693->b) / a692->b);
                }
              }
            }
          }
        }
        if (const Add *a716 = a693->a.as<Add>()) {
          if (is_const(a692->b)) {
            if (const Div *a717 = expr->b.as<Div>()) {
              if (const Add *a718 = a717->a.as<Add>()) {
                if (const Add *a719 = a718->a.as<Add>()) {
                  if (equal(a716->b, a719->a)) {
                    if (equal(a716->a, a719->b)) {
                      if (equal(a692->b, a717->b)) {
                        if (evaluate_predicate(fold((a692->b > 0)))) {
                          return ((((a716->a + a716->b) + a693->b) / a692->b) - (((a716->a + a716->b) + a718->b) / a692->b));
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const(a693->b)) {
          if (is_const(a692->b)) {
            if (const Div *a730 = expr->b.as<Div>()) {
              if (const Add *a731 = a730->a.as<Add>()) {
                if (equal(a693->a, a731->a)) {
                  if (equal(a692->b, a730->b)) {
                    if (evaluate_predicate(fold((a692->b > 0)))) {
                      return (((fold(((a692->b + a693->b) - 1)) - a731->b) - ((a693->a + fold((a693->b % a692->b))) % a692->b)) / a692->b);
                    }
                  }
                }
              }
              if (const Sub *a739 = a730->a.as<Sub>()) {
                if (equal(a693->a, a739->a)) {
                  if (equal(a692->b, a730->b)) {
                    if (evaluate_predicate(fold((a692->b > 0)))) {
                      return (((a739->b + fold(((a692->b + a693->b) - 1))) - ((a693->a + fold((a693->b % a692->b))) % a692->b)) / a692->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a786 = a693->a.as<Min>()) {
          if (const Add *a787 = a786->a.as<Add>()) {
            if (const Mul *a788 = a787->a.as<Mul>()) {
              if (is_const(a788->b)) {
                if (is_const(a692->b)) {
                  if (const Mul *a789 = expr->b.as<Mul>()) {
                    if (equal(a788->a, a789->a)) {
                      if (is_const(a789->b)) {
                        if (evaluate_predicate(fold((a788->b == (a692->b * a789->b))))) {
                          return ((min(a787->b, (a786->b - (a788->a * a788->b))) + a693->b) / a692->b);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Add *a793 = a786->b.as<Add>()) {
            if (const Mul *a794 = a793->a.as<Mul>()) {
              if (is_const(a794->b)) {
                if (is_const(a692->b)) {
                  if (const Mul *a795 = expr->b.as<Mul>()) {
                    if (equal(a794->a, a795->a)) {
                      if (is_const(a795->b)) {
                        if (evaluate_predicate(fold((a794->b == (a692->b * a795->b))))) {
                          return ((min((a786->a - (a794->a * a794->b)), a793->b) + a693->b) / a692->b);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Sub *a697 = a692->a.as<Sub>()) {
        if (is_const(a692->b)) {
          if (equal(a697->a, expr->b)) {
            return (((a697->a * fold((1 - a692->b))) - a697->b) / a692->b);
          }
          if (equal(a697->b, expr->b)) {
            return ((a697->a - (a697->b * fold((1 + a692->b)))) / a692->b);
          }
          if (const Div *a734 = expr->b.as<Div>()) {
            if (const Add *a735 = a734->a.as<Add>()) {
              if (equal(a697->a, a735->a)) {
                if (is_const(a735->b)) {
                  if (equal(a692->b, a734->b)) {
                    if (evaluate_predicate(fold((a692->b > 0)))) {
                      return (((((a697->a + fold((a735->b % a692->b))) % a692->b) - a697->b) - a735->b) / a692->b);
                    }
                  }
                }
              }
            }
            if (equal(a697->a, a734->a)) {
              if (equal(a692->b, a734->b)) {
                if (evaluate_predicate(fold((a692->b > 0)))) {
                  return (((a697->a % a692->b) - a697->b) / a692->b);
                }
              }
            }
          }
        }
      }
      if (is_const(a692->b)) {
        if (const Div *a741 = expr->b.as<Div>()) {
          if (const Add *a742 = a741->a.as<Add>()) {
            if (equal(a692->a, a742->a)) {
              if (equal(a692->b, a741->b)) {
                if (evaluate_predicate(fold((a692->b > 0)))) {
                  return (((fold((a692->b - 1)) - a742->b) - (a692->a % a692->b)) / a692->b);
                }
              }
            }
          }
          if (const Sub *a748 = a741->a.as<Sub>()) {
            if (equal(a692->a, a748->a)) {
              if (equal(a692->b, a741->b)) {
                if (evaluate_predicate(fold((a692->b > 0)))) {
                  return (((a748->b + fold((a692->b - 1))) - (a692->a % a692->b)) / a692->b);
                }
              }
            }
          }
        }
      }
      if (const Min *a775 = a692->a.as<Min>()) {
        if (const Add *a776 = a775->a.as<Add>()) {
          if (const Mul *a777 = a776->a.as<Mul>()) {
            if (is_const(a777->b)) {
              if (is_const(a692->b)) {
                if (const Mul *a778 = expr->b.as<Mul>()) {
                  if (equal(a777->a, a778->a)) {
                    if (is_const(a778->b)) {
                      if (evaluate_predicate(fold((a777->b == (a692->b * a778->b))))) {
                        return (min(a776->b, (a775->b - (a777->a * a777->b))) / a692->b);
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a781 = a775->b.as<Add>()) {
          if (const Mul *a782 = a781->a.as<Mul>()) {
            if (is_const(a782->b)) {
              if (is_const(a692->b)) {
                if (const Mul *a783 = expr->b.as<Mul>()) {
                  if (equal(a782->a, a783->a)) {
                    if (is_const(a783->b)) {
                      if (evaluate_predicate(fold((a782->b == (a692->b * a783->b))))) {
                        return (min(a781->b, (a775->a - (a782->a * a782->b))) / a692->b);
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    if (const Mul *a700 = expr->a.as<Mul>()) {
      if (const Div *a701 = a700->a.as<Div>()) {
        if (is_const(a701->b)) {
          if (equal(a701->b, a700->b)) {
            if (equal(a701->a, expr->b)) {
              if (evaluate_predicate(fold((a701->b > 0)))) {
                return (0 - (a701->a % a701->b));
              }
            }
          }
        }
        if (const Add *a706 = a701->a.as<Add>()) {
          if (is_const(a706->b)) {
            if (is_const(a701->b)) {
              if (equal(a701->b, a700->b)) {
                if (equal(a706->a, expr->b)) {
                  if (evaluate_predicate(fold(((a701->b > 0) && ((a706->b + 1) == a701->b))))) {
                    return ((0 - a706->a) % a701->b);
                  }
                }
              }
            }
          }
        }
      }
      if (is_const(a700->b)) {
        if (const Mul *a711 = expr->b.as<Mul>()) {
          if (is_const(a711->b)) {
            if (evaluate_predicate(fold(((a700->b % a711->b) == 0)))) {
              return (((a700->a * fold((a700->b / a711->b))) - a711->a) * a711->b);
            }
            if (evaluate_predicate(fold(((a711->b % a700->b) == 0)))) {
              return ((a700->a - (a711->a * fold((a711->b / a700->b)))) * a700->b);
            }
          }
        }
      }
    }
    if (const Mul *a702 = expr->b.as<Mul>()) {
      if (const Div *a703 = a702->a.as<Div>()) {
        if (equal(expr->a, a703->a)) {
          if (is_const(a703->b)) {
            if (equal(a703->b, a702->b)) {
              if (evaluate_predicate(fold((a703->b > 0)))) {
                return (expr->a % a703->b);
              }
            }
          }
        }
        if (const Add *a709 = a703->a.as<Add>()) {
          if (equal(expr->a, a709->a)) {
            if (is_const(a709->b)) {
              if (is_const(a703->b)) {
                if (equal(a703->b, a702->b)) {
                  if (evaluate_predicate(fold(((a703->b > 0) && ((a709->b + 1) == a703->b))))) {
                    return (((expr->a + a709->b) % a703->b) + fold((0 - a709->b)));
                  }
                }
              }
            }
          }
        }
      }
    }
    if (const Add *a752 = expr->a.as<Add>()) {
      if (const Min *a753 = a752->a.as<Min>()) {
        if (const Add *a754 = a753->a.as<Add>()) {
          if (equal(a754->a, expr->b)) {
            return (min((a753->b - a754->a), a754->b) + a752->b);
          }
        }
      }
    }
    if (const Min *a755 = expr->a.as<Min>()) {
      if (const Add *a756 = a755->a.as<Add>()) {
        if (const Add *a757 = a756->a.as<Add>()) {
          if (equal(a757->a, expr->b)) {
            return min((a755->b - a757->a), (a757->b + a756->b));
          }
        }
        if (const Mul *a766 = a756->a.as<Mul>()) {
          if (const Add *a767 = a766->a.as<Add>()) {
            if (const Mul *a768 = expr->b.as<Mul>()) {
              if (equal(a767->a, a768->a)) {
                if (equal(a766->b, a768->b)) {
                  return min((a755->b - (a767->a * a766->b)), ((a767->b * a766->b) + a756->b));
                }
              }
              if (equal(a767->b, a768->a)) {
                if (equal(a766->b, a768->b)) {
                  return min((a755->b - (a767->b * a766->b)), ((a767->a * a766->b) + a756->b));
                }
              }
            }
          }
        }
      }
      if (const Min *a759 = a755->a.as<Min>()) {
        if (const Add *a760 = a759->a.as<Add>()) {
          if (equal(a760->a, expr->b)) {
            return min((min(a759->b, a755->b) - a760->a), a760->b);
          }
        }
        if (const Add *a763 = a759->b.as<Add>()) {
          if (equal(a763->a, expr->b)) {
            return min((min(a759->a, a755->b) - a763->a), a763->b);
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
