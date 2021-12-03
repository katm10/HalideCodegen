#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_Sub(const Sub *expr, Simplify *simplifier) {
  if (is_const_int(expr->b, 0)) {
    return expr->a;
  }
  if (is_const_v(expr->a)) {
    if (is_const_v(expr->b)) {
      return fold((expr->a - expr->b));
    }
    if (const Select *a91 = expr->b.as<Select>()) {
      if (is_const_v(a91->true_value)) {
        if (is_const_v(a91->false_value)) {
          return select(a91->condition, fold((expr->a - a91->true_value)), fold((expr->a - a91->false_value)));
        }
      }
    }
  }
  if (!(expr->is_uint())) {
    if (const Sub *a0 = expr.as<Sub>()) {
      if (is_const_v(a0->b)) {
        if (evaluate_predicate(fold(!(overflows((0 - a0->b)))))) {
          return (a0->a + fold((0 - a0->b)));
        }
      }
    }
  }
  if (equal(expr->a, expr->b)) {
    return 0;
  }
  if (const Ramp *a1 = expr->a.as<Ramp>()) {
    if (is_const_v(a1->lanes)) {
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
      if (is_const_v(a20->lanes)) {
        if (is_const_v(a1->lanes)) {
          if (const Broadcast *a21 = expr->b.as<Broadcast>()) {
            if (is_const_v(a21->lanes)) {
              if (evaluate_predicate(fold((a21->lanes == (a20->lanes * a1->lanes))))) {
                return ramp(broadcast((a20->value - a21->value), a20->lanes), a1->stride, a1->lanes);
              }
            }
          }
        }
      }
    }
    if (const Ramp *a23 = a1->base.as<Ramp>()) {
      if (is_const_v(a23->lanes)) {
        if (is_const_v(a1->lanes)) {
          if (const Broadcast *a24 = expr->b.as<Broadcast>()) {
            if (is_const_v(a24->lanes)) {
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
    if (is_const_v(a5->lanes)) {
      if (const Ramp *a6 = expr->b.as<Ramp>()) {
        if (equal(a5->lanes, a6->lanes)) {
          return ramp((a5->value - a6->base), (0 - a6->stride), a5->lanes);
        }
      }
      if (const Broadcast *a8 = expr->b.as<Broadcast>()) {
        if (equal(a5->lanes, a8->lanes)) {
          return broadcast((a5->value - a8->value), a5->lanes);
        }
        if (is_const_v(a8->lanes)) {
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
      if (is_const_v(a14->lanes)) {
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
    if (is_const_v(a13->a)) {
      if (const Sub *a99 = expr->b.as<Sub>()) {
        if (is_const_v(a99->a)) {
          return ((a99->b - a13->b) + fold((a13->a - a99->a)));
        }
      }
      if (const Add *a101 = expr->b.as<Add>()) {
        if (is_const_v(a101->b)) {
          return (fold((a13->a - a101->b)) - (a13->b + a101->a));
        }
      }
      if (is_const_v(expr->b)) {
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
    if (const Sub *a291 = a13->a.as<Sub>()) {
      if (equal(a291->a, expr->b)) {
        return (0 - (a291->b + a13->b));
      }
    }
  }
  if (const Add *a16 = expr->a.as<Add>()) {
    if (const Broadcast *a17 = a16->b.as<Broadcast>()) {
      if (is_const_v(a17->lanes)) {
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
    if (is_const_v(a16->b)) {
      if (is_const_v(expr->b)) {
        return (a16->a + fold((a16->b - expr->b)));
      }
      if (const Sub *a94 = expr->b.as<Sub>()) {
        if (is_const_v(a94->a)) {
          return ((a16->a + a94->b) + fold((a16->b - a94->a)));
        }
      }
      if (const Add *a96 = expr->b.as<Add>()) {
        if (is_const_v(a96->b)) {
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
    if (const Min *a279 = expr->b.as<Min>()) {
      if (equal(a16->a, a279->a)) {
        if (equal(a16->b, a279->b)) {
          return min(a16->b, a16->a);
        }
      }
      if (equal(a16->b, a279->a)) {
        if (equal(a16->a, a279->b)) {
          return min(a16->b, a16->a);
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
    if (is_const_v(a73->b)) {
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
    if (is_const_v(a103->b)) {
      if (evaluate_predicate(fold(((a103->b < 0) && (0 - (a103->b > 0)))))) {
        return (expr->a + (a103->a * fold((0 - a103->b))));
      }
    }
    if (const Div *a294 = a103->a.as<Div>()) {
      if (const Add *a295 = a294->a.as<Add>()) {
        if (equal(expr->a, a295->a)) {
          if (is_const_v(a295->b)) {
            if (is_const_v(a294->b)) {
              if (equal(a294->b, a103->b)) {
                if (evaluate_predicate(fold((a294->b > 0)))) {
                  return (((expr->a + a295->b) % a294->b) - a295->b);
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
          return min(expr->a, a275->b);
        }
      }
    }
  }
  if (is_const_int(expr->a, 0)) {
    if (const Add *a286 = expr->b.as<Add>()) {
      if (const Sub *a287 = a286->b.as<Sub>()) {
        return (a287->b - (a286->a + a287->a));
      }
      if (const Sub *a289 = a286->a.as<Sub>()) {
        return (a289->b - (a289->a + a286->b));
      }
    }
  }
  if (const Mod *a292 = expr->b.as<Mod>()) {
    if (equal(expr->a, a292->a)) {
      if (is_const_v(a292->b)) {
        return ((expr->a / a292->b) * a292->b);
      }
    }
  }
  if (expr->is_no_overflow()) {
    if (const Sub *a296 = expr.as<Sub>()) {
      if (const Min *a297 = a296->a.as<Min>()) {
        if (equal(a297->a, a296->b)) {
          return min((a297->b - a297->a), 0);
        }
        if (equal(a297->b, a296->b)) {
          return min((a297->a - a297->b), 0);
        }
        if (const Sub *a326 = a297->a.as<Sub>()) {
          if (is_const_int(a297->b, 0)) {
            if (equal(a326->a, a296->b)) {
              return (0 - min(a326->a, a326->b));
            }
          }
        }
        if (const Add *a332 = a296->b.as<Add>()) {
          if (equal(a297->a, a332->a)) {
            if (equal(a297->b, a332->b)) {
              return (0 - min(a297->b, a297->a));
              return (0 - min(a297->a, a297->b));
            }
          }
          if (equal(a297->b, a332->a)) {
            if (equal(a297->a, a332->b)) {
              return (0 - min(a297->a, a297->b));
              return (0 - min(a297->b, a297->a));
            }
          }
        }
        if (const Add *a410 = a297->a.as<Add>()) {
          if (equal(a410->a, a296->b)) {
            return min((a297->b - a410->a), a410->b);
          }
          if (equal(a410->b, a296->b)) {
            return min((a297->b - a410->b), a410->a);
          }
          if (const Add *a439 = a410->b.as<Add>()) {
            if (equal(a439->b, a296->b)) {
              return min((a297->b - a439->b), (a410->a + a439->a));
            }
            if (equal(a439->a, a296->b)) {
              return min((a297->b - a439->a), (a410->a + a439->b));
            }
          }
          if (const Add *a447 = a410->a.as<Add>()) {
            if (equal(a447->b, a296->b)) {
              return min((a297->b - a447->b), (a447->a + a410->b));
            }
            if (equal(a447->a, a296->b)) {
              return min((a297->b - a447->a), (a447->b + a410->b));
            }
          }
          if (is_const_v(a410->b)) {
            if (const Min *a572 = a296->b.as<Min>()) {
              if (equal(a410->a, a572->a)) {
                if (evaluate_predicate(fold(can_prove((a297->b <= (a572->b + a410->b)), simplifier)))) {
                  return min((a297->b - min(a410->a, a572->b)), a410->b);
                  return min((min((a410->a + a410->b), a297->b) - a572->b), a410->b);
                }
                if (evaluate_predicate(fold(can_prove((a297->b >= (a572->b + a410->b)), simplifier)))) {
                  return min((min((a410->a + a410->b), a297->b) - a572->b), a410->b);
                  return min((a297->b - min(a410->a, a572->b)), a410->b);
                }
              }
              if (const Add *a589 = a572->a.as<Add>()) {
                if (equal(a410->a, a589->a)) {
                  if (is_const_v(a589->b)) {
                    if (evaluate_predicate(fold(can_prove(((a297->b + a589->b) <= (a572->b + a410->b)), simplifier)))) {
                      return min((a297->b - min((a410->a + a589->b), a572->b)), fold((a410->b - a589->b)));
                      return min((min((a410->a + a410->b), a297->b) - a572->b), fold((a410->b - a589->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a297->b + a589->b) >= (a572->b + a410->b)), simplifier)))) {
                      return min((min((a410->a + a410->b), a297->b) - a572->b), fold((a410->b - a589->b)));
                      return min((a297->b - min((a410->a + a589->b), a572->b)), fold((a410->b - a589->b)));
                    }
                  }
                }
              }
              if (equal(a410->a, a572->b)) {
                if (evaluate_predicate(fold(can_prove((a297->b <= (a572->a + a410->b)), simplifier)))) {
                  return min((a297->b - min(a410->a, a572->a)), a410->b);
                  return min((min((a410->a + a410->b), a297->b) - a572->a), a410->b);
                }
                if (evaluate_predicate(fold(can_prove((a297->b >= (a572->a + a410->b)), simplifier)))) {
                  return min((min((a410->a + a410->b), a297->b) - a572->a), a410->b);
                  return min((a297->b - min(a410->a, a572->a)), a410->b);
                }
              }
              if (const Add *a653 = a572->b.as<Add>()) {
                if (equal(a410->a, a653->a)) {
                  if (is_const_v(a653->b)) {
                    if (evaluate_predicate(fold(can_prove(((a297->b + a653->b) <= (a572->a + a410->b)), simplifier)))) {
                      return min((a297->b - min((a410->a + a653->b), a572->a)), fold((a410->b - a653->b)));
                      return min((min((a410->a + a410->b), a297->b) - a572->a), fold((a410->b - a653->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a297->b + a653->b) >= (a572->a + a410->b)), simplifier)))) {
                      return min((min((a410->a + a410->b), a297->b) - a572->a), fold((a410->b - a653->b)));
                      return min((a297->b - min((a410->a + a653->b), a572->a)), fold((a410->b - a653->b)));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a416 = a297->b.as<Add>()) {
          if (equal(a416->a, a296->b)) {
            return min((a297->a - a416->a), a416->b);
          }
          if (equal(a416->b, a296->b)) {
            return min((a297->a - a416->b), a416->a);
          }
          if (const Add *a423 = a416->b.as<Add>()) {
            if (equal(a423->b, a296->b)) {
              return min((a297->a - a423->b), (a416->a + a423->a));
            }
            if (equal(a423->a, a296->b)) {
              return min((a297->a - a423->a), (a416->a + a423->b));
            }
          }
          if (const Add *a431 = a416->a.as<Add>()) {
            if (equal(a431->b, a296->b)) {
              return min((a297->a - a431->b), (a431->a + a416->b));
            }
            if (equal(a431->a, a296->b)) {
              return min((a297->a - a431->a), (a431->b + a416->b));
            }
          }
          if (is_const_v(a416->b)) {
            if (const Min *a604 = a296->b.as<Min>()) {
              if (equal(a416->a, a604->b)) {
                if (evaluate_predicate(fold(can_prove((a297->a <= (a604->a + a416->b)), simplifier)))) {
                  return min((a297->a - min(a416->a, a604->a)), a416->b);
                  return min((min((a416->a + a416->b), a297->a) - a604->a), a416->b);
                }
                if (evaluate_predicate(fold(can_prove((a297->a >= (a604->a + a416->b)), simplifier)))) {
                  return min((min((a416->a + a416->b), a297->a) - a604->a), a416->b);
                  return min((a297->a - min(a416->a, a604->a)), a416->b);
                }
              }
              if (const Add *a621 = a604->b.as<Add>()) {
                if (equal(a416->a, a621->a)) {
                  if (is_const_v(a621->b)) {
                    if (evaluate_predicate(fold(can_prove(((a297->a + a621->b) <= (a604->a + a416->b)), simplifier)))) {
                      return min((a297->a - min((a416->a + a621->b), a604->a)), fold((a416->b - a621->b)));
                      return min((min((a416->a + a416->b), a297->a) - a604->a), fold((a416->b - a621->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a297->a + a621->b) >= (a604->a + a416->b)), simplifier)))) {
                      return min((min((a416->a + a416->b), a297->a) - a604->a), fold((a416->b - a621->b)));
                      return min((a297->a - min((a416->a + a621->b), a604->a)), fold((a416->b - a621->b)));
                    }
                  }
                }
              }
              if (equal(a416->a, a604->a)) {
                if (evaluate_predicate(fold(can_prove((a297->a <= (a604->b + a416->b)), simplifier)))) {
                  return min((a297->a - min(a416->a, a604->b)), a416->b);
                  return min((min((a416->a + a416->b), a297->a) - a604->b), a416->b);
                }
                if (evaluate_predicate(fold(can_prove((a297->a >= (a604->b + a416->b)), simplifier)))) {
                  return min((min((a416->a + a416->b), a297->a) - a604->b), a416->b);
                  return min((a297->a - min(a416->a, a604->b)), a416->b);
                }
              }
              if (const Add *a685 = a604->a.as<Add>()) {
                if (equal(a416->a, a685->a)) {
                  if (is_const_v(a685->b)) {
                    if (evaluate_predicate(fold(can_prove(((a297->a + a685->b) <= (a604->b + a416->b)), simplifier)))) {
                      return min((a297->a - min((a416->a + a685->b), a604->b)), fold((a416->b - a685->b)));
                      return min((min((a416->a + a416->b), a297->a) - a604->b), fold((a416->b - a685->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a297->a + a685->b) >= (a604->b + a416->b)), simplifier)))) {
                      return min((min((a416->a + a416->b), a297->a) - a604->b), fold((a416->b - a685->b)));
                      return min((a297->a - min((a416->a + a685->b), a604->b)), fold((a416->b - a685->b)));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a454 = a296->b.as<Min>()) {
          if (equal(a297->b, a454->a)) {
            if (equal(a297->a, a454->b)) {
              return 0;
            }
            if (evaluate_predicate(fold(can_prove((a297->a <= a454->b), simplifier)))) {
              return min((a297->a - min(a297->b, a454->b)), 0);
              return min((min(a297->b, a297->a) - a454->b), 0);
            }
            if (evaluate_predicate(fold(can_prove((a297->a >= a454->b), simplifier)))) {
              return min((min(a297->b, a297->a) - a454->b), 0);
              return min((a297->a - min(a297->b, a454->b)), 0);
            }
          }
          if (evaluate_predicate(fold(can_prove(((a297->a - a297->b) == (a454->a - a454->b)), simplifier)))) {
            return (a297->b - a454->b);
          }
          if (evaluate_predicate(fold(can_prove(((a297->a - a297->b) == (a454->b - a454->a)), simplifier)))) {
            return (a297->b - a454->a);
          }
          if (equal(a297->a, a454->a)) {
            if (evaluate_predicate(fold(can_prove((a297->b <= a454->b), simplifier)))) {
              return min((a297->b - min(a297->a, a454->b)), 0);
              return min((min(a297->a, a297->b) - a454->b), 0);
            }
            if (evaluate_predicate(fold(can_prove((a297->b >= a454->b), simplifier)))) {
              return min((min(a297->a, a297->b) - a454->b), 0);
              return min((a297->b - min(a297->a, a454->b)), 0);
            }
          }
          if (const Add *a580 = a454->a.as<Add>()) {
            if (equal(a297->a, a580->a)) {
              if (is_const_v(a580->b)) {
                if (evaluate_predicate(fold(can_prove(((a297->b + a580->b) <= a454->b), simplifier)))) {
                  return min((a297->b - min((a297->a + a580->b), a454->b)), fold((0 - a580->b)));
                  return min((min(a297->a, a297->b) - a454->b), fold((0 - a580->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a297->b + a580->b) >= a454->b), simplifier)))) {
                  return min((min(a297->a, a297->b) - a454->b), fold((0 - a580->b)));
                  return min((a297->b - min((a297->a + a580->b), a454->b)), fold((0 - a580->b)));
                }
              }
            }
            if (equal(a297->b, a580->a)) {
              if (is_const_v(a580->b)) {
                if (evaluate_predicate(fold(can_prove(((a297->a + a580->b) <= a454->b), simplifier)))) {
                  return min((a297->a - min((a297->b + a580->b), a454->b)), fold((0 - a580->b)));
                  return min((min(a297->b, a297->a) - a454->b), fold((0 - a580->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a297->a + a580->b) >= a454->b), simplifier)))) {
                  return min((min(a297->b, a297->a) - a454->b), fold((0 - a580->b)));
                  return min((a297->a - min((a297->b + a580->b), a454->b)), fold((0 - a580->b)));
                }
              }
            }
          }
          if (equal(a297->b, a454->b)) {
            if (evaluate_predicate(fold(can_prove((a297->a <= a454->a), simplifier)))) {
              return min((a297->a - min(a297->b, a454->a)), 0);
              return min((min(a297->b, a297->a) - a454->a), 0);
            }
            if (evaluate_predicate(fold(can_prove((a297->a >= a454->a), simplifier)))) {
              return min((min(a297->b, a297->a) - a454->a), 0);
              return min((a297->a - min(a297->b, a454->a)), 0);
            }
          }
          if (const Add *a612 = a454->b.as<Add>()) {
            if (equal(a297->b, a612->a)) {
              if (is_const_v(a612->b)) {
                if (evaluate_predicate(fold(can_prove(((a297->a + a612->b) <= a454->a), simplifier)))) {
                  return min((a297->a - min((a297->b + a612->b), a454->a)), fold((0 - a612->b)));
                  return min((min(a297->b, a297->a) - a454->a), fold((0 - a612->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a297->a + a612->b) >= a454->a), simplifier)))) {
                  return min((min(a297->b, a297->a) - a454->a), fold((0 - a612->b)));
                  return min((a297->a - min((a297->b + a612->b), a454->a)), fold((0 - a612->b)));
                }
              }
            }
            if (equal(a297->a, a612->a)) {
              if (is_const_v(a612->b)) {
                if (evaluate_predicate(fold(can_prove(((a297->b + a612->b) <= a454->a), simplifier)))) {
                  return min((a297->b - min((a297->a + a612->b), a454->a)), fold((0 - a612->b)));
                  return min((min(a297->a, a297->b) - a454->a), fold((0 - a612->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a297->b + a612->b) >= a454->a), simplifier)))) {
                  return min((min(a297->a, a297->b) - a454->a), fold((0 - a612->b)));
                  return min((a297->b - min((a297->a + a612->b), a454->a)), fold((0 - a612->b)));
                }
              }
            }
          }
          if (equal(a297->a, a454->b)) {
            if (evaluate_predicate(fold(can_prove((a297->b <= a454->a), simplifier)))) {
              return min((a297->b - min(a297->a, a454->a)), 0);
              return min((min(a297->a, a297->b) - a454->a), 0);
            }
            if (evaluate_predicate(fold(can_prove((a297->b >= a454->a), simplifier)))) {
              return min((min(a297->a, a297->b) - a454->a), 0);
              return min((a297->b - min(a297->a, a454->a)), 0);
            }
          }
        }
        if (const Mul *a463 = a297->a.as<Mul>()) {
          if (is_const_v(a463->b)) {
            if (is_const_v(a297->b)) {
              if (const Mul *a464 = a296->b.as<Mul>()) {
                if (const Min *a465 = a464->a.as<Min>()) {
                  if (equal(a463->a, a465->a)) {
                    if (is_const_v(a465->b)) {
                      if (equal(a463->b, a464->b)) {
                        if (evaluate_predicate(fold(((a463->b > 0) && (a297->b <= (a465->b * a463->b)))))) {
                          return min((a297->b - (min(a463->a, a465->b) * a463->b)), 0);
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
      if (const Min *a305 = a296->b.as<Min>()) {
        if (equal(a296->a, a305->a)) {
          if (evaluate_predicate(fold(!(is_const(a296->a))))) {
            return min((a296->a - a305->b), 0);
          }
        }
        if (equal(a296->a, a305->b)) {
          if (evaluate_predicate(fold(!(is_const(a296->a))))) {
            return min((a296->a - a305->a), 0);
          }
        }
        if (const Sub *a314 = a305->b.as<Sub>()) {
          if (equal(a296->a, a314->a)) {
            return min((a296->a - a305->a), a314->b);
          }
        }
        if (const Sub *a317 = a305->a.as<Sub>()) {
          if (equal(a296->a, a317->a)) {
            return min(a317->b, (a296->a - a305->b));
          }
          if (is_const_v(a305->b)) {
            return (a296->a + min((a317->b - a317->a), fold((0 - a305->b))));
          }
        }
        if (const Min *a350 = a305->a.as<Min>()) {
          if (const Sub *a351 = a350->a.as<Sub>()) {
            if (is_const_v(a350->b)) {
              if (is_const_v(a305->b)) {
                return (a296->a + min(min((a351->b - a351->a), fold((0 - a350->b))), fold((0 - a305->b))));
              }
            }
          }
        }
        if (const Add *a366 = a305->b.as<Add>()) {
          if (equal(a296->a, a366->a)) {
            if (evaluate_predicate(fold(!(is_const(a296->a))))) {
              return (0 - min((a305->a - a296->a), a366->b));
            }
          }
          if (equal(a296->a, a366->b)) {
            if (evaluate_predicate(fold(!(is_const(a296->a))))) {
              return (0 - min((a305->a - a296->a), a366->a));
            }
          }
          if (const Add *a379 = a366->b.as<Add>()) {
            if (equal(a296->a, a379->a)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->a - a296->a), (a366->a + a379->b)));
              }
            }
            if (equal(a296->a, a379->b)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->a - a296->a), (a379->a + a366->a)));
              }
            }
          }
          if (const Add *a387 = a366->a.as<Add>()) {
            if (equal(a296->a, a387->a)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->a - a296->a), (a387->b + a366->b)));
              }
            }
            if (equal(a296->a, a387->b)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->a - a296->a), (a387->a + a366->b)));
              }
            }
          }
        }
        if (const Add *a372 = a305->a.as<Add>()) {
          if (equal(a296->a, a372->a)) {
            if (evaluate_predicate(fold(!(is_const(a296->a))))) {
              return (0 - min((a305->b - a296->a), a372->b));
            }
          }
          if (equal(a296->a, a372->b)) {
            if (evaluate_predicate(fold(!(is_const(a296->a))))) {
              return (0 - min((a305->b - a296->a), a372->a));
            }
          }
          if (const Add *a395 = a372->b.as<Add>()) {
            if (equal(a296->a, a395->a)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->b - a296->a), (a372->a + a395->b)));
              }
            }
            if (equal(a296->a, a395->b)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->b - a296->a), (a395->a + a372->a)));
              }
            }
          }
          if (const Add *a403 = a372->a.as<Add>()) {
            if (equal(a296->a, a403->a)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->b - a296->a), (a372->b + a403->b)));
              }
            }
            if (equal(a296->a, a403->b)) {
              if (evaluate_predicate(fold(!(is_const(a296->a))))) {
                return (0 - min((a305->b - a296->a), (a372->b + a403->a)));
              }
            }
          }
        }
      }
      if (const Mul *a357 = a296->a.as<Mul>()) {
        if (equal(a357->a, a296->b)) {
          return (a357->a * (a357->b - 1));
        }
        if (equal(a357->b, a296->b)) {
          return ((a357->a - 1) * a357->b);
        }
      }
      if (const Mul *a361 = a296->b.as<Mul>()) {
        if (equal(a296->a, a361->a)) {
          return (a296->a * (1 - a361->b));
        }
        if (equal(a296->a, a361->b)) {
          return ((1 - a361->a) * a296->a);
        }
      }
    }
  }
  if (expr->is_no_overflow_int()) {
    if (const Sub *a819 = expr.as<Sub>()) {
      if (is_const_v(a819->a)) {
        if (const Div *a820 = a819->b.as<Div>()) {
          if (const Sub *a821 = a820->a.as<Sub>()) {
            if (is_const_v(a821->a)) {
              if (is_const_v(a820->b)) {
                if (evaluate_predicate(fold((a820->b > 0)))) {
                  return ((fold(((((a819->a * a820->b) - a821->a) + a820->b) - 1)) + a821->b) / a820->b);
                }
              }
            }
          }
          if (const Add *a824 = a820->a.as<Add>()) {
            if (is_const_v(a824->b)) {
              if (is_const_v(a820->b)) {
                if (evaluate_predicate(fold((a820->b > 0)))) {
                  return ((fold(((((a819->a * a820->b) - a824->b) + a820->b) - 1)) - a824->a) / a820->b);
                }
              }
            }
          }
        }
      }
      if (const Div *a826 = a819->b.as<Div>()) {
        if (const Add *a827 = a826->a.as<Add>()) {
          if (equal(a819->a, a827->a)) {
            if (is_const_v(a826->b)) {
              if (evaluate_predicate(fold((a826->b > 0)))) {
                return ((((a819->a * fold((a826->b - 1))) - a827->b) + fold((a826->b - 1))) / a826->b);
              }
            }
          }
          if (equal(a819->a, a827->b)) {
            if (is_const_v(a826->b)) {
              if (evaluate_predicate(fold((a826->b > 0)))) {
                return ((((a819->a * fold((a826->b - 1))) - a827->a) + fold((a826->b - 1))) / a826->b);
              }
            }
          }
        }
        if (const Sub *a830 = a826->a.as<Sub>()) {
          if (equal(a819->a, a830->a)) {
            if (is_const_v(a826->b)) {
              if (evaluate_predicate(fold((a826->b > 0)))) {
                return ((((a819->a * fold((a826->b - 1))) + a830->b) + fold((a826->b - 1))) / a826->b);
              }
            }
          }
          if (equal(a819->a, a830->b)) {
            if (is_const_v(a826->b)) {
              if (evaluate_predicate(fold((a826->b > 0)))) {
                return ((((a819->a * fold((a826->b + 1))) - a830->a) + fold((a826->b - 1))) / a826->b);
              }
            }
          }
        }
      }
      if (const Div *a838 = a819->a.as<Div>()) {
        if (const Add *a839 = a838->a.as<Add>()) {
          if (is_const_v(a838->b)) {
            if (equal(a839->a, a819->b)) {
              return (((a839->a * fold((1 - a838->b))) + a839->b) / a838->b);
            }
            if (equal(a839->b, a819->b)) {
              return ((a839->a + (a839->b * fold((1 - a838->b)))) / a838->b);
            }
            if (const Div *a879 = a819->b.as<Div>()) {
              if (const Add *a880 = a879->a.as<Add>()) {
                if (equal(a839->b, a880->a)) {
                  if (equal(a839->a, a880->b)) {
                    if (equal(a838->b, a879->b)) {
                      if (evaluate_predicate(fold((a838->b != 0)))) {
                        return 0;
                      }
                    }
                  }
                }
                if (equal(a839->a, a880->a)) {
                  if (is_const_v(a880->b)) {
                    if (equal(a838->b, a879->b)) {
                      if (evaluate_predicate(fold((a838->b > 0)))) {
                        return ((((a839->a + fold((a880->b % a838->b))) % a838->b) + (a839->b - a880->b)) / a838->b);
                      }
                    }
                  }
                }
              }
              if (equal(a839->a, a879->a)) {
                if (equal(a838->b, a879->b)) {
                  if (evaluate_predicate(fold((a838->b > 0)))) {
                    return (((a839->a % a838->b) + a839->b) / a838->b);
                  }
                }
              }
            }
          }
          if (const Add *a872 = a839->a.as<Add>()) {
            if (is_const_v(a838->b)) {
              if (const Div *a873 = a819->b.as<Div>()) {
                if (const Add *a874 = a873->a.as<Add>()) {
                  if (const Add *a875 = a874->a.as<Add>()) {
                    if (equal(a872->b, a875->a)) {
                      if (equal(a872->a, a875->b)) {
                        if (equal(a838->b, a873->b)) {
                          if (evaluate_predicate(fold((a838->b > 0)))) {
                            return ((((a872->a + a872->b) + a839->b) / a838->b) - (((a872->a + a872->b) + a874->b) / a838->b));
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(a839->b)) {
            if (is_const_v(a838->b)) {
              if (const Div *a889 = a819->b.as<Div>()) {
                if (const Add *a890 = a889->a.as<Add>()) {
                  if (equal(a839->a, a890->a)) {
                    if (equal(a838->b, a889->b)) {
                      if (evaluate_predicate(fold((a838->b > 0)))) {
                        return (((fold(((a838->b + a839->b) - 1)) - a890->b) - ((a839->a + fold((a839->b % a838->b))) % a838->b)) / a838->b);
                      }
                    }
                  }
                }
                if (const Sub *a900 = a889->a.as<Sub>()) {
                  if (equal(a839->a, a900->a)) {
                    if (equal(a838->b, a889->b)) {
                      if (evaluate_predicate(fold((a838->b > 0)))) {
                        return (((a900->b + fold(((a838->b + a839->b) - 1))) - ((a839->a + fold((a839->b % a838->b))) % a838->b)) / a838->b);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Min *a960 = a839->a.as<Min>()) {
            if (const Add *a961 = a960->a.as<Add>()) {
              if (const Mul *a962 = a961->a.as<Mul>()) {
                if (is_const_v(a962->b)) {
                  if (is_const_v(a838->b)) {
                    if (const Mul *a963 = a819->b.as<Mul>()) {
                      if (equal(a962->a, a963->a)) {
                        if (is_const_v(a963->b)) {
                          if (evaluate_predicate(fold((a962->b == (a838->b * a963->b))))) {
                            return ((min(a961->b, (a960->b - (a962->a * a962->b))) + a839->b) / a838->b);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (const Add *a968 = a960->b.as<Add>()) {
              if (const Mul *a969 = a968->a.as<Mul>()) {
                if (is_const_v(a969->b)) {
                  if (is_const_v(a838->b)) {
                    if (const Mul *a970 = a819->b.as<Mul>()) {
                      if (equal(a969->a, a970->a)) {
                        if (is_const_v(a970->b)) {
                          if (evaluate_predicate(fold((a969->b == (a838->b * a970->b))))) {
                            return ((min((a960->a - (a969->a * a969->b)), a968->b) + a839->b) / a838->b);
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
        if (const Sub *a845 = a838->a.as<Sub>()) {
          if (is_const_v(a838->b)) {
            if (equal(a845->a, a819->b)) {
              return (((a845->a * fold((1 - a838->b))) - a845->b) / a838->b);
            }
            if (equal(a845->b, a819->b)) {
              return ((a845->a - (a845->b * fold((1 + a838->b)))) / a838->b);
            }
            if (const Div *a894 = a819->b.as<Div>()) {
              if (const Add *a895 = a894->a.as<Add>()) {
                if (equal(a845->a, a895->a)) {
                  if (is_const_v(a895->b)) {
                    if (equal(a838->b, a894->b)) {
                      if (evaluate_predicate(fold((a838->b > 0)))) {
                        return (((((a845->a + fold((a895->b % a838->b))) % a838->b) - a845->b) - a895->b) / a838->b);
                      }
                    }
                  }
                }
              }
              if (equal(a845->a, a894->a)) {
                if (equal(a838->b, a894->b)) {
                  if (evaluate_predicate(fold((a838->b > 0)))) {
                    return (((a845->a % a838->b) - a845->b) / a838->b);
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a838->b)) {
          if (const Div *a903 = a819->b.as<Div>()) {
            if (const Add *a904 = a903->a.as<Add>()) {
              if (equal(a838->a, a904->a)) {
                if (equal(a838->b, a903->b)) {
                  if (evaluate_predicate(fold((a838->b > 0)))) {
                    return (((fold((a838->b - 1)) - a904->b) - (a838->a % a838->b)) / a838->b);
                  }
                }
              }
            }
            if (const Sub *a912 = a903->a.as<Sub>()) {
              if (equal(a838->a, a912->a)) {
                if (equal(a838->b, a903->b)) {
                  if (evaluate_predicate(fold((a838->b > 0)))) {
                    return (((a912->b + fold((a838->b - 1))) - (a838->a % a838->b)) / a838->b);
                  }
                }
              }
            }
          }
        }
        if (const Min *a947 = a838->a.as<Min>()) {
          if (const Add *a948 = a947->a.as<Add>()) {
            if (const Mul *a949 = a948->a.as<Mul>()) {
              if (is_const_v(a949->b)) {
                if (is_const_v(a838->b)) {
                  if (const Mul *a950 = a819->b.as<Mul>()) {
                    if (equal(a949->a, a950->a)) {
                      if (is_const_v(a950->b)) {
                        if (evaluate_predicate(fold((a949->b == (a838->b * a950->b))))) {
                          return (min(a948->b, (a947->b - (a949->a * a949->b))) / a838->b);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Add *a954 = a947->b.as<Add>()) {
            if (const Mul *a955 = a954->a.as<Mul>()) {
              if (is_const_v(a955->b)) {
                if (is_const_v(a838->b)) {
                  if (const Mul *a956 = a819->b.as<Mul>()) {
                    if (equal(a955->a, a956->a)) {
                      if (is_const_v(a956->b)) {
                        if (evaluate_predicate(fold((a955->b == (a838->b * a956->b))))) {
                          return (min(a954->b, (a947->a - (a955->a * a955->b))) / a838->b);
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
      if (const Mul *a850 = a819->a.as<Mul>()) {
        if (const Div *a851 = a850->a.as<Div>()) {
          if (is_const_v(a851->b)) {
            if (equal(a851->b, a850->b)) {
              if (equal(a851->a, a819->b)) {
                if (evaluate_predicate(fold((a851->b > 0)))) {
                  return (0 - (a851->a % a851->b));
                }
              }
            }
          }
          if (const Add *a858 = a851->a.as<Add>()) {
            if (is_const_v(a858->b)) {
              if (is_const_v(a851->b)) {
                if (equal(a851->b, a850->b)) {
                  if (equal(a858->a, a819->b)) {
                    if (evaluate_predicate(fold(((a851->b > 0) && ((a858->b + 1) == a851->b))))) {
                      return ((0 - a858->a) % a851->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a850->b)) {
          if (const Mul *a865 = a819->b.as<Mul>()) {
            if (is_const_v(a865->b)) {
              if (evaluate_predicate(fold(((a850->b % a865->b) == 0)))) {
                return (((a850->a * fold((a850->b / a865->b))) - a865->a) * a865->b);
              }
              if (evaluate_predicate(fold(((a865->b % a850->b) == 0)))) {
                return ((a850->a - (a865->a * fold((a865->b / a850->b)))) * a850->b);
              }
            }
          }
        }
      }
      if (const Mul *a853 = a819->b.as<Mul>()) {
        if (const Div *a854 = a853->a.as<Div>()) {
          if (equal(a819->a, a854->a)) {
            if (is_const_v(a854->b)) {
              if (equal(a854->b, a853->b)) {
                if (evaluate_predicate(fold((a854->b > 0)))) {
                  return (a819->a % a854->b);
                }
              }
            }
          }
          if (const Add *a862 = a854->a.as<Add>()) {
            if (equal(a819->a, a862->a)) {
              if (is_const_v(a862->b)) {
                if (is_const_v(a854->b)) {
                  if (equal(a854->b, a853->b)) {
                    if (evaluate_predicate(fold(((a854->b > 0) && ((a862->b + 1) == a854->b))))) {
                      return (((a819->a + a862->b) % a854->b) + fold((0 - a862->b)));
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a918 = a819->a.as<Add>()) {
        if (const Min *a919 = a918->a.as<Min>()) {
          if (const Add *a920 = a919->a.as<Add>()) {
            if (equal(a920->a, a819->b)) {
              return (min((a919->b - a920->a), a920->b) + a918->b);
            }
          }
        }
      }
      if (const Min *a922 = a819->a.as<Min>()) {
        if (const Add *a923 = a922->a.as<Add>()) {
          if (const Add *a924 = a923->a.as<Add>()) {
            if (equal(a924->a, a819->b)) {
              return min((a922->b - a924->a), (a924->b + a923->b));
            }
          }
          if (const Mul *a936 = a923->a.as<Mul>()) {
            if (const Add *a937 = a936->a.as<Add>()) {
              if (const Mul *a938 = a819->b.as<Mul>()) {
                if (equal(a937->a, a938->a)) {
                  if (equal(a936->b, a938->b)) {
                    return min((a922->b - (a937->a * a936->b)), ((a937->b * a936->b) + a923->b));
                  }
                }
                if (equal(a937->b, a938->a)) {
                  if (equal(a936->b, a938->b)) {
                    return min((a922->b - (a937->b * a936->b)), ((a937->a * a936->b) + a923->b));
                  }
                }
              }
            }
          }
        }
        if (const Min *a927 = a922->a.as<Min>()) {
          if (const Add *a928 = a927->a.as<Add>()) {
            if (equal(a928->a, a819->b)) {
              return min((min(a927->b, a922->b) - a928->a), a928->b);
            }
          }
          if (const Add *a932 = a927->b.as<Add>()) {
            if (equal(a932->a, a819->b)) {
              return min((min(a927->a, a922->b) - a932->a), a932->b);
            }
          }
        }
      }
    }
  }
  return expr;
}
