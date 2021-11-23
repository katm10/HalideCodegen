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
    if (const Select *a92 = expr->b->as<Select>()) {
      if (is_const_v(a92->a)) {
        if (is_const_v(a92->b)) {
          return select(a92->cond, fold((expr->a - a92->a)), fold((expr->a - a92->b)));
        }
      }
    }
  }
  if (!(expr->is_uint())) {
    if (const Sub *a1 = expr->as<Sub>()) {
      if (is_const_v(a1->b)) {
        if (evaluate_predicate(fold(!(overflows((0 - a1->b)))))) {
          return (a1->a + fold((0 - a1->b)));
        }
      }
    }
  }
  if (equal(expr->a, expr->b)) {
    return 0;
  }
  if (const Ramp *a2 = expr->a->as<Ramp>()) {
    if (is_const_v(a2->lanes)) {
      if (const Ramp *a3 = expr->b->as<Ramp>()) {
        if (equal(a2->lanes, a3->lanes)) {
          return ramp((a2->base - a3->base), (a2->stride - a3->stride), a2->lanes);
        }
      }
      if (const Broadcast *a5 = expr->b->as<Broadcast>()) {
        if (equal(a2->lanes, a5->lanes)) {
          return ramp((a2->base - a5->value), a2->stride, a2->lanes);
        }
      }
    }
    if (const Broadcast *a21 = a2->base->as<Broadcast>()) {
      if (is_const_v(a21->lanes)) {
        if (is_const_v(a2->lanes)) {
          if (const Broadcast *a22 = expr->b->as<Broadcast>()) {
            if (is_const_v(a22->lanes)) {
              if (evaluate_predicate(fold((a22->lanes == (a21->lanes * a2->lanes))))) {
                return ramp(broadcast((a21->value - a22->value), a21->lanes), a2->stride, a2->lanes);
              }
            }
          }
        }
      }
    }
    if (const Ramp *a24 = a2->base->as<Ramp>()) {
      if (is_const_v(a24->lanes)) {
        if (is_const_v(a2->lanes)) {
          if (const Broadcast *a25 = expr->b->as<Broadcast>()) {
            if (is_const_v(a25->lanes)) {
              if (evaluate_predicate(fold((a25->lanes == (a24->lanes * a2->lanes))))) {
                return ramp(ramp((a24->base - a25->value), a24->stride, a24->lanes), a2->stride, a2->lanes);
              }
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a6 = expr->a->as<Broadcast>()) {
    if (is_const_v(a6->lanes)) {
      if (const Ramp *a7 = expr->b->as<Ramp>()) {
        if (equal(a6->lanes, a7->lanes)) {
          return ramp((a6->value - a7->base), (0 - a7->stride), a6->lanes);
        }
      }
      if (const Broadcast *a9 = expr->b->as<Broadcast>()) {
        if (equal(a6->lanes, a9->lanes)) {
          return broadcast((a6->value - a9->value), a6->lanes);
        }
        if (is_const_v(a9->lanes)) {
          if (evaluate_predicate(fold(((a9->lanes % a6->lanes) == 0)))) {
            return broadcast((a6->value - broadcast(a9->value, fold((a9->lanes / a6->lanes)))), a6->lanes);
          }
          if (evaluate_predicate(fold(((a6->lanes % a9->lanes) == 0)))) {
            return broadcast((broadcast(a6->value, fold((a6->lanes / a9->lanes))) - a9->value), a9->lanes);
          }
        }
      }
    }
  }
  if (const Sub *a14 = expr->a->as<Sub>()) {
    if (const Broadcast *a15 = a14->b->as<Broadcast>()) {
      if (is_const_v(a15->lanes)) {
        if (const Broadcast *a16 = expr->b->as<Broadcast>()) {
          if (equal(a15->lanes, a16->lanes)) {
            return (a14->a - broadcast((a15->value + a16->value), a15->lanes));
          }
        }
      }
    }
    if (equal(a14->a, expr->b)) {
      return (0 - a14->b);
    }
    if (const Select *a90 = a14->a->as<Select>()) {
      if (const Select *a91 = expr->b->as<Select>()) {
        if (equal(a90->cond, a91->cond)) {
          return (select(a90->cond, (a90->a - a91->a), (a90->b - a91->b)) - a14->b);
        }
      }
    }
    if (is_const_v(a14->a)) {
      if (const Sub *a100 = expr->b->as<Sub>()) {
        if (is_const_v(a100->a)) {
          return ((a100->b - a14->b) + fold((a14->a - a100->a)));
        }
      }
      if (const Add *a102 = expr->b->as<Add>()) {
        if (is_const_v(a102->b)) {
          return (fold((a14->a - a102->b)) - (a14->b + a102->a));
        }
      }
      if (is_const_v(expr->b)) {
        return (fold((a14->a - expr->b)) - a14->b);
      }
    }
    if (const Mul *a128 = a14->b->as<Mul>()) {
      if (const Mul *a129 = expr->b->as<Mul>()) {
        if (equal(a128->b, a129->b)) {
          return (a14->a - ((a128->a + a129->a) * a128->b));
        }
        if (equal(a128->b, a129->a)) {
          return (a14->a - ((a128->a + a129->b) * a128->b));
        }
        if (equal(a128->a, a129->b)) {
          return (a14->a - (a128->a * (a128->b + a129->a)));
        }
        if (equal(a128->a, a129->a)) {
          return (a14->a - (a128->a * (a128->b + a129->b)));
        }
      }
    }
    if (const Mul *a152 = a14->a->as<Mul>()) {
      if (const Mul *a153 = expr->b->as<Mul>()) {
        if (equal(a152->b, a153->b)) {
          return (((a152->a - a153->a) * a152->b) - a14->b);
        }
        if (equal(a152->b, a153->a)) {
          return (((a152->a - a153->b) * a152->b) - a14->b);
        }
        if (equal(a152->a, a153->b)) {
          return ((a152->a * (a152->b - a153->a)) - a14->b);
        }
        if (equal(a152->a, a153->a)) {
          return ((a152->a * (a152->b - a153->b)) - a14->b);
        }
      }
    }
    if (const Add *a268 = expr->b->as<Add>()) {
      if (equal(a14->a, a268->a)) {
        return ((0 - a14->b) - a268->b);
      }
      if (equal(a14->a, a268->b)) {
        return ((0 - a14->b) - a268->a);
      }
    }
    if (const Add *a272 = a14->a->as<Add>()) {
      if (equal(a272->a, expr->b)) {
        return (a272->b - a14->b);
      }
      if (equal(a272->b, expr->b)) {
        return (a272->a - a14->b);
      }
    }
    if (const Sub *a296 = a14->a->as<Sub>()) {
      if (equal(a296->a, expr->b)) {
        return (0 - (a296->b + a14->b));
      }
    }
  }
  if (const Add *a17 = expr->a->as<Add>()) {
    if (const Broadcast *a18 = a17->b->as<Broadcast>()) {
      if (is_const_v(a18->lanes)) {
        if (const Broadcast *a19 = expr->b->as<Broadcast>()) {
          if (equal(a18->lanes, a19->lanes)) {
            return (a17->a + broadcast((a18->value - a19->value), a18->lanes));
          }
        }
      }
    }
    if (equal(a17->a, expr->b)) {
      return a17->b;
    }
    if (equal(a17->b, expr->b)) {
      return a17->a;
    }
    if (const Select *a78 = a17->a->as<Select>()) {
      if (const Select *a79 = expr->b->as<Select>()) {
        if (equal(a78->cond, a79->cond)) {
          return (select(a78->cond, (a78->a - a79->a), (a78->b - a79->b)) + a17->b);
        }
      }
    }
    if (const Select *a81 = a17->b->as<Select>()) {
      if (const Select *a82 = expr->b->as<Select>()) {
        if (equal(a81->cond, a82->cond)) {
          return (select(a81->cond, (a81->a - a82->a), (a81->b - a82->b)) + a17->a);
        }
      }
    }
    if (is_const_v(a17->b)) {
      if (is_const_v(expr->b)) {
        return (a17->a + fold((a17->b - expr->b)));
      }
      if (const Sub *a95 = expr->b->as<Sub>()) {
        if (is_const_v(a95->a)) {
          return ((a17->a + a95->b) + fold((a17->b - a95->a)));
        }
      }
      if (const Add *a97 = expr->b->as<Add>()) {
        if (is_const_v(a97->b)) {
          return ((a17->a - a97->a) + fold((a17->b - a97->b)));
        }
      }
      return ((a17->a - expr->b) + a17->b);
    }
    if (const Mul *a116 = a17->b->as<Mul>()) {
      if (const Mul *a117 = expr->b->as<Mul>()) {
        if (equal(a116->b, a117->b)) {
          return (a17->a + ((a116->a - a117->a) * a116->b));
        }
        if (equal(a116->b, a117->a)) {
          return (a17->a + ((a116->a - a117->b) * a116->b));
        }
        if (equal(a116->a, a117->b)) {
          return (a17->a + (a116->a * (a116->b - a117->a)));
        }
        if (equal(a116->a, a117->a)) {
          return (a17->a + (a116->a * (a116->b - a117->b)));
        }
      }
    }
    if (const Mul *a140 = a17->a->as<Mul>()) {
      if (const Mul *a141 = expr->b->as<Mul>()) {
        if (equal(a140->b, a141->b)) {
          return (a17->b + ((a140->a - a141->a) * a140->b));
        }
        if (equal(a140->b, a141->a)) {
          return (a17->b + ((a140->a - a141->b) * a140->b));
        }
        if (equal(a140->a, a141->b)) {
          return (a17->b + (a140->a * (a140->b - a141->a)));
        }
        if (equal(a140->a, a141->a)) {
          return (a17->b + (a140->a * (a140->b - a141->b)));
        }
      }
    }
    if (const Add *a212 = expr->b->as<Add>()) {
      if (equal(a17->a, a212->a)) {
        return (a17->b - a212->b);
      }
      if (equal(a17->a, a212->b)) {
        return (a17->b - a212->a);
      }
      if (equal(a17->b, a212->a)) {
        return (a17->a - a212->b);
      }
      if (equal(a17->b, a212->b)) {
        return (a17->a - a212->a);
      }
      if (const Add *a245 = a212->b->as<Add>()) {
        if (equal(a17->a, a245->b)) {
          return (a17->b - (a212->a + a245->a));
        }
        if (equal(a17->b, a245->b)) {
          return (a17->a - (a212->a + a245->a));
        }
        if (equal(a17->a, a245->a)) {
          return (a17->b - (a212->a + a245->b));
        }
        if (equal(a17->b, a245->a)) {
          return (a17->a - (a212->a + a245->b));
        }
      }
      if (const Add *a257 = a212->a->as<Add>()) {
        if (equal(a17->a, a257->a)) {
          return (a17->b - (a257->b + a212->b));
        }
        if (equal(a17->b, a257->a)) {
          return (a17->a - (a257->b + a212->b));
        }
        if (equal(a17->a, a257->b)) {
          return (a17->b - (a257->a + a212->b));
        }
        if (equal(a17->b, a257->b)) {
          return (a17->a - (a257->a + a212->b));
        }
      }
    }
    if (const Add *a220 = a17->a->as<Add>()) {
      if (equal(a220->a, expr->b)) {
        return (a220->b + a17->b);
      }
      if (equal(a220->b, expr->b)) {
        return (a220->a + a17->b);
      }
    }
    if (const Add *a224 = a17->b->as<Add>()) {
      if (equal(a224->a, expr->b)) {
        return (a17->a + a224->b);
      }
      if (equal(a224->b, expr->b)) {
        return (a17->a + a224->a);
      }
    }
    if (const Sub *a232 = a17->b->as<Sub>()) {
      if (equal(a232->a, expr->b)) {
        return (a17->a - a232->b);
      }
    }
    if (const Sub *a234 = a17->a->as<Sub>()) {
      if (equal(a234->a, expr->b)) {
        return (a17->b - a234->b);
      }
    }
    if (const Min *a282 = expr->b->as<Min>()) {
      if (equal(a17->a, a282->a)) {
        if (equal(a17->b, a282->b)) {
          return min(a17->b, a17->a);
        }
      }
      if (equal(a17->b, a282->a)) {
        if (equal(a17->a, a282->b)) {
          return min(a17->b, a17->a);
          return min(a17->a, a17->b);
        }
      }
    }
  }
  if (const Select *a26 = expr->a->as<Select>()) {
    if (const Select *a27 = expr->b->as<Select>()) {
      if (equal(a26->cond, a27->cond)) {
        return select(a26->cond, (a26->a - a27->a), (a26->b - a27->b));
      }
    }
    if (equal(a26->a, expr->b)) {
      return select(a26->cond, 0, (a26->b - a26->a));
    }
    if (equal(a26->b, expr->b)) {
      return select(a26->cond, (a26->a - a26->b), 0);
    }
    if (const Add *a33 = a26->a->as<Add>()) {
      if (equal(a33->a, expr->b)) {
        return select(a26->cond, a33->b, (a26->b - a33->a));
      }
      if (equal(a33->b, expr->b)) {
        return select(a26->cond, a33->a, (a26->b - a33->b));
      }
      if (const Add *a42 = a33->b->as<Add>()) {
        if (equal(a42->b, expr->b)) {
          return select(a26->cond, (a33->a + a42->a), (a26->b - a42->b));
        }
        if (equal(a42->a, expr->b)) {
          return select(a26->cond, (a33->a + a42->b), (a26->b - a42->a));
        }
      }
      if (const Add *a48 = a33->a->as<Add>()) {
        if (equal(a48->a, expr->b)) {
          return select(a26->cond, (a33->b + a48->b), (a26->b - a48->a));
        }
        if (equal(a48->b, expr->b)) {
          return select(a26->cond, (a33->b + a48->a), (a26->b - a48->b));
        }
      }
      if (const Add *a54 = expr->b->as<Add>()) {
        if (equal(a33->a, a54->b)) {
          return (select(a26->cond, a33->b, (a26->b - a33->a)) - a54->a);
        }
        if (equal(a33->b, a54->b)) {
          return (select(a26->cond, a33->a, (a26->b - a33->b)) - a54->a);
        }
        if (equal(a33->a, a54->a)) {
          return (select(a26->cond, a33->b, (a26->b - a33->a)) - a54->b);
        }
        if (equal(a33->b, a54->a)) {
          return (select(a26->cond, a33->a, (a26->b - a33->b)) - a54->b);
        }
      }
    }
    if (const Add *a37 = a26->b->as<Add>()) {
      if (equal(a37->a, expr->b)) {
        return select(a26->cond, (a26->a - a37->a), a37->b);
      }
      if (equal(a37->b, expr->b)) {
        return select(a26->cond, (a26->a - a37->b), a37->a);
      }
    }
    if (const Add *a84 = expr->b->as<Add>()) {
      if (const Select *a85 = a84->a->as<Select>()) {
        if (equal(a26->cond, a85->cond)) {
          return (select(a26->cond, (a26->a - a85->a), (a26->b - a85->b)) - a84->b);
        }
      }
      if (const Select *a88 = a84->b->as<Select>()) {
        if (equal(a26->cond, a88->cond)) {
          return (select(a26->cond, (a26->a - a88->a), (a26->b - a88->b)) - a84->a);
        }
      }
    }
  }
  if (const Select *a30 = expr->b->as<Select>()) {
    if (equal(expr->a, a30->a)) {
      return select(a30->cond, 0, (expr->a - a30->b));
    }
    if (equal(expr->a, a30->b)) {
      return select(a30->cond, (expr->a - a30->a), 0);
    }
    if (const Add *a65 = a30->a->as<Add>()) {
      if (equal(expr->a, a65->a)) {
        return (0 - select(a30->cond, a65->b, (a30->b - expr->a)));
      }
      if (equal(expr->a, a65->b)) {
        return (0 - select(a30->cond, a65->a, (a30->b - expr->a)));
      }
    }
    if (const Add *a69 = a30->b->as<Add>()) {
      if (equal(expr->a, a69->a)) {
        return (0 - select(a30->cond, (a30->a - expr->a), a69->b));
      }
      if (equal(expr->a, a69->b)) {
        return (0 - select(a30->cond, (a30->a - expr->a), a69->a));
      }
    }
  }
  if (const Add *a74 = expr->b->as<Add>()) {
    if (equal(expr->a, a74->a)) {
      return (0 - a74->b);
    }
    if (equal(expr->a, a74->b)) {
      return (0 - a74->a);
    }
    if (is_const_v(a74->b)) {
      return ((expr->a - a74->a) - a74->b);
    }
    if (const Sub *a228 = a74->b->as<Sub>()) {
      if (equal(expr->a, a228->a)) {
        return (a228->b - a74->a);
      }
    }
    if (const Sub *a230 = a74->a->as<Sub>()) {
      if (equal(expr->a, a230->a)) {
        return (a230->b - a74->b);
      }
    }
    if (const Add *a236 = a74->b->as<Add>()) {
      if (equal(expr->a, a236->a)) {
        return (0 - (a74->a + a236->b));
      }
      if (equal(expr->a, a236->b)) {
        return (0 - (a74->a + a236->a));
      }
    }
    if (const Add *a240 = a74->a->as<Add>()) {
      if (equal(expr->a, a240->a)) {
        return (0 - (a240->b + a74->b));
      }
      if (equal(expr->a, a240->b)) {
        return (0 - (a240->a + a74->b));
      }
    }
  }
  if (const Sub *a103 = expr->b->as<Sub>()) {
    return (expr->a + (a103->b - a103->a));
  }
  if (const Mul *a104 = expr->b->as<Mul>()) {
    if (is_const_v(a104->b)) {
      if (evaluate_predicate(fold(((a104->b < 0) && (0 - (a104->b > 0)))))) {
        return (expr->a + (a104->a * fold((0 - a104->b))));
      }
    }
    if (const Div *a299 = a104->a->as<Div>()) {
      if (const Add *a300 = a299->a->as<Add>()) {
        if (equal(expr->a, a300->a)) {
          if (is_const_v(a300->b)) {
            if (is_const_v(a299->b)) {
              if (equal(a299->b, a104->b)) {
                if (evaluate_predicate(fold((a299->b > 0)))) {
                  return (((expr->a + a300->b) % a299->b) - a300->b);
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Mul *a107 = expr->a->as<Mul>()) {
    if (const Mul *a108 = expr->b->as<Mul>()) {
      if (equal(a107->b, a108->b)) {
        return ((a107->a - a108->a) * a107->b);
      }
      if (equal(a107->b, a108->a)) {
        return ((a107->a - a108->b) * a107->b);
      }
      if (equal(a107->a, a108->b)) {
        return (a107->a * (a107->b - a108->a));
      }
      if (equal(a107->a, a108->a)) {
        return (a107->a * (a107->b - a108->b));
      }
    }
    if (const Add *a164 = expr->b->as<Add>()) {
      if (const Mul *a165 = a164->b->as<Mul>()) {
        if (equal(a107->b, a165->b)) {
          return (((a107->a - a165->a) * a107->b) - a164->a);
        }
        if (equal(a107->b, a165->a)) {
          return (((a107->a - a165->b) * a107->b) - a164->a);
        }
        if (equal(a107->a, a165->b)) {
          return ((a107->a * (a107->b - a165->a)) - a164->a);
        }
        if (equal(a107->a, a165->a)) {
          return ((a107->a * (a107->b - a165->b)) - a164->a);
        }
      }
      if (const Mul *a189 = a164->a->as<Mul>()) {
        if (equal(a107->b, a189->b)) {
          return (((a107->a - a189->a) * a107->b) - a164->b);
        }
        if (equal(a107->b, a189->a)) {
          return (((a107->a - a189->b) * a107->b) - a164->b);
        }
        if (equal(a107->a, a189->b)) {
          return ((a107->a * (a107->b - a189->a)) - a164->b);
        }
        if (equal(a107->a, a189->a)) {
          return ((a107->a * (a107->b - a189->b)) - a164->b);
        }
      }
    }
    if (const Sub *a176 = expr->b->as<Sub>()) {
      if (const Mul *a177 = a176->b->as<Mul>()) {
        if (equal(a107->b, a177->b)) {
          return (((a107->a + a177->a) * a107->b) - a176->a);
        }
        if (equal(a107->b, a177->a)) {
          return (((a107->a + a177->b) * a107->b) - a176->a);
        }
        if (equal(a107->a, a177->b)) {
          return ((a107->a * (a107->b + a177->a)) - a176->a);
        }
        if (equal(a107->a, a177->a)) {
          return ((a107->a * (a107->b + a177->b)) - a176->a);
        }
      }
      if (const Mul *a201 = a176->a->as<Mul>()) {
        if (equal(a107->b, a201->b)) {
          return (((a107->a - a201->a) * a107->b) + a176->b);
        }
        if (equal(a107->b, a201->a)) {
          return (((a107->a - a201->b) * a107->b) + a176->b);
        }
        if (equal(a107->a, a201->b)) {
          return ((a107->a * (a107->b - a201->a)) + a176->b);
        }
        if (equal(a107->a, a201->a)) {
          return ((a107->a * (a107->b - a201->b)) + a176->b);
        }
      }
    }
  }
  if (const Min *a275 = expr->b->as<Min>()) {
    if (const Sub *a276 = a275->a->as<Sub>()) {
      if (equal(expr->a, a276->a)) {
        if (is_const_int(a275->b, 0)) {
          return min(expr->a, a276->b);
        }
      }
    }
  }
  if (is_const_int(expr->a, 0)) {
    if (const Add *a290 = expr->b->as<Add>()) {
      if (const Sub *a291 = a290->b->as<Sub>()) {
        return (a291->b - (a290->a + a291->a));
      }
      if (const Sub *a294 = a290->a->as<Sub>()) {
        return (a294->b - (a294->a + a290->b));
      }
    }
  }
  if (const Mod *a297 = expr->b->as<Mod>()) {
    if (equal(expr->a, a297->a)) {
      if (is_const_v(a297->b)) {
        return ((expr->a / a297->b) * a297->b);
      }
    }
  }
  if (expr->is_no_overflow()) {
    if (const Sub *a301 = expr->as<Sub>()) {
      if (const Min *a302 = a301->a->as<Min>()) {
        if (equal(a302->a, a301->b)) {
          return min((a302->b - a302->a), 0);
        }
        if (equal(a302->b, a301->b)) {
          return min((a302->a - a302->b), 0);
        }
        if (const Sub *a331 = a302->a->as<Sub>()) {
          if (is_const_int(a302->b, 0)) {
            if (equal(a331->a, a301->b)) {
              return (0 - min(a331->a, a331->b));
            }
          }
        }
        if (const Add *a339 = a301->b->as<Add>()) {
          if (equal(a302->a, a339->a)) {
            if (equal(a302->b, a339->b)) {
              return (0 - min(a302->b, a302->a));
              return (0 - min(a302->a, a302->b));
            }
          }
          if (equal(a302->b, a339->a)) {
            if (equal(a302->a, a339->b)) {
              return (0 - min(a302->a, a302->b));
              return (0 - min(a302->b, a302->a));
            }
          }
        }
        if (const Add *a417 = a302->a->as<Add>()) {
          if (equal(a417->a, a301->b)) {
            return min((a302->b - a417->a), a417->b);
          }
          if (equal(a417->b, a301->b)) {
            return min((a302->b - a417->b), a417->a);
          }
          if (const Add *a446 = a417->b->as<Add>()) {
            if (equal(a446->b, a301->b)) {
              return min((a302->b - a446->b), (a417->a + a446->a));
            }
            if (equal(a446->a, a301->b)) {
              return min((a302->b - a446->a), (a417->a + a446->b));
            }
          }
          if (const Add *a454 = a417->a->as<Add>()) {
            if (equal(a454->b, a301->b)) {
              return min((a302->b - a454->b), (a454->a + a417->b));
            }
            if (equal(a454->a, a301->b)) {
              return min((a302->b - a454->a), (a454->b + a417->b));
            }
          }
          if (is_const_v(a417->b)) {
            if (const Min *a579 = a301->b->as<Min>()) {
              if (equal(a417->a, a579->a)) {
                if (evaluate_predicate(fold(can_prove((a302->b <= (a579->b + a417->b)), simplifier)))) {
                  return min((a302->b - min(a417->a, a579->b)), a417->b);
                  return min((min((a417->a + a417->b), a302->b) - a579->b), a417->b);
                }
                if (evaluate_predicate(fold(can_prove((a302->b >= (a579->b + a417->b)), simplifier)))) {
                  return min((min((a417->a + a417->b), a302->b) - a579->b), a417->b);
                  return min((a302->b - min(a417->a, a579->b)), a417->b);
                }
              }
              if (const Add *a596 = a579->a->as<Add>()) {
                if (equal(a417->a, a596->a)) {
                  if (is_const_v(a596->b)) {
                    if (evaluate_predicate(fold(can_prove(((a302->b + a596->b) <= (a579->b + a417->b)), simplifier)))) {
                      return min((a302->b - min((a417->a + a596->b), a579->b)), fold((a417->b - a596->b)));
                      return min((min((a417->a + a417->b), a302->b) - a579->b), fold((a417->b - a596->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a302->b + a596->b) >= (a579->b + a417->b)), simplifier)))) {
                      return min((min((a417->a + a417->b), a302->b) - a579->b), fold((a417->b - a596->b)));
                      return min((a302->b - min((a417->a + a596->b), a579->b)), fold((a417->b - a596->b)));
                    }
                  }
                }
              }
              if (equal(a417->a, a579->b)) {
                if (evaluate_predicate(fold(can_prove((a302->b <= (a579->a + a417->b)), simplifier)))) {
                  return min((a302->b - min(a417->a, a579->a)), a417->b);
                  return min((min((a417->a + a417->b), a302->b) - a579->a), a417->b);
                }
                if (evaluate_predicate(fold(can_prove((a302->b >= (a579->a + a417->b)), simplifier)))) {
                  return min((min((a417->a + a417->b), a302->b) - a579->a), a417->b);
                  return min((a302->b - min(a417->a, a579->a)), a417->b);
                }
              }
              if (const Add *a660 = a579->b->as<Add>()) {
                if (equal(a417->a, a660->a)) {
                  if (is_const_v(a660->b)) {
                    if (evaluate_predicate(fold(can_prove(((a302->b + a660->b) <= (a579->a + a417->b)), simplifier)))) {
                      return min((a302->b - min((a417->a + a660->b), a579->a)), fold((a417->b - a660->b)));
                      return min((min((a417->a + a417->b), a302->b) - a579->a), fold((a417->b - a660->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a302->b + a660->b) >= (a579->a + a417->b)), simplifier)))) {
                      return min((min((a417->a + a417->b), a302->b) - a579->a), fold((a417->b - a660->b)));
                      return min((a302->b - min((a417->a + a660->b), a579->a)), fold((a417->b - a660->b)));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a423 = a302->b->as<Add>()) {
          if (equal(a423->a, a301->b)) {
            return min((a302->a - a423->a), a423->b);
          }
          if (equal(a423->b, a301->b)) {
            return min((a302->a - a423->b), a423->a);
          }
          if (const Add *a430 = a423->b->as<Add>()) {
            if (equal(a430->b, a301->b)) {
              return min((a302->a - a430->b), (a423->a + a430->a));
            }
            if (equal(a430->a, a301->b)) {
              return min((a302->a - a430->a), (a423->a + a430->b));
            }
          }
          if (const Add *a438 = a423->a->as<Add>()) {
            if (equal(a438->b, a301->b)) {
              return min((a302->a - a438->b), (a438->a + a423->b));
            }
            if (equal(a438->a, a301->b)) {
              return min((a302->a - a438->a), (a438->b + a423->b));
            }
          }
          if (is_const_v(a423->b)) {
            if (const Min *a611 = a301->b->as<Min>()) {
              if (equal(a423->a, a611->b)) {
                if (evaluate_predicate(fold(can_prove((a302->a <= (a611->a + a423->b)), simplifier)))) {
                  return min((a302->a - min(a423->a, a611->a)), a423->b);
                  return min((min((a423->a + a423->b), a302->a) - a611->a), a423->b);
                }
                if (evaluate_predicate(fold(can_prove((a302->a >= (a611->a + a423->b)), simplifier)))) {
                  return min((min((a423->a + a423->b), a302->a) - a611->a), a423->b);
                  return min((a302->a - min(a423->a, a611->a)), a423->b);
                }
              }
              if (const Add *a628 = a611->b->as<Add>()) {
                if (equal(a423->a, a628->a)) {
                  if (is_const_v(a628->b)) {
                    if (evaluate_predicate(fold(can_prove(((a302->a + a628->b) <= (a611->a + a423->b)), simplifier)))) {
                      return min((a302->a - min((a423->a + a628->b), a611->a)), fold((a423->b - a628->b)));
                      return min((min((a423->a + a423->b), a302->a) - a611->a), fold((a423->b - a628->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a302->a + a628->b) >= (a611->a + a423->b)), simplifier)))) {
                      return min((min((a423->a + a423->b), a302->a) - a611->a), fold((a423->b - a628->b)));
                      return min((a302->a - min((a423->a + a628->b), a611->a)), fold((a423->b - a628->b)));
                    }
                  }
                }
              }
              if (equal(a423->a, a611->a)) {
                if (evaluate_predicate(fold(can_prove((a302->a <= (a611->b + a423->b)), simplifier)))) {
                  return min((a302->a - min(a423->a, a611->b)), a423->b);
                  return min((min((a423->a + a423->b), a302->a) - a611->b), a423->b);
                }
                if (evaluate_predicate(fold(can_prove((a302->a >= (a611->b + a423->b)), simplifier)))) {
                  return min((min((a423->a + a423->b), a302->a) - a611->b), a423->b);
                  return min((a302->a - min(a423->a, a611->b)), a423->b);
                }
              }
              if (const Add *a692 = a611->a->as<Add>()) {
                if (equal(a423->a, a692->a)) {
                  if (is_const_v(a692->b)) {
                    if (evaluate_predicate(fold(can_prove(((a302->a + a692->b) <= (a611->b + a423->b)), simplifier)))) {
                      return min((a302->a - min((a423->a + a692->b), a611->b)), fold((a423->b - a692->b)));
                      return min((min((a423->a + a423->b), a302->a) - a611->b), fold((a423->b - a692->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a302->a + a692->b) >= (a611->b + a423->b)), simplifier)))) {
                      return min((min((a423->a + a423->b), a302->a) - a611->b), fold((a423->b - a692->b)));
                      return min((a302->a - min((a423->a + a692->b), a611->b)), fold((a423->b - a692->b)));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a461 = a301->b->as<Min>()) {
          if (equal(a302->b, a461->a)) {
            if (equal(a302->a, a461->b)) {
              return 0;
            }
            if (evaluate_predicate(fold(can_prove((a302->a <= a461->b), simplifier)))) {
              return min((a302->a - min(a302->b, a461->b)), 0);
              return min((min(a302->b, a302->a) - a461->b), 0);
            }
            if (evaluate_predicate(fold(can_prove((a302->a >= a461->b), simplifier)))) {
              return min((min(a302->b, a302->a) - a461->b), 0);
              return min((a302->a - min(a302->b, a461->b)), 0);
            }
          }
          if (evaluate_predicate(fold(can_prove(((a302->a - a302->b) == (a461->a - a461->b)), simplifier)))) {
            return (a302->b - a461->b);
          }
          if (evaluate_predicate(fold(can_prove(((a302->a - a302->b) == (a461->b - a461->a)), simplifier)))) {
            return (a302->b - a461->a);
          }
          if (equal(a302->a, a461->a)) {
            if (evaluate_predicate(fold(can_prove((a302->b <= a461->b), simplifier)))) {
              return min((a302->b - min(a302->a, a461->b)), 0);
              return min((min(a302->a, a302->b) - a461->b), 0);
            }
            if (evaluate_predicate(fold(can_prove((a302->b >= a461->b), simplifier)))) {
              return min((min(a302->a, a302->b) - a461->b), 0);
              return min((a302->b - min(a302->a, a461->b)), 0);
            }
          }
          if (const Add *a587 = a461->a->as<Add>()) {
            if (equal(a302->a, a587->a)) {
              if (is_const_v(a587->b)) {
                if (evaluate_predicate(fold(can_prove(((a302->b + a587->b) <= a461->b), simplifier)))) {
                  return min((a302->b - min((a302->a + a587->b), a461->b)), fold((0 - a587->b)));
                  return min((min(a302->a, a302->b) - a461->b), fold((0 - a587->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a302->b + a587->b) >= a461->b), simplifier)))) {
                  return min((min(a302->a, a302->b) - a461->b), fold((0 - a587->b)));
                  return min((a302->b - min((a302->a + a587->b), a461->b)), fold((0 - a587->b)));
                }
              }
            }
            if (equal(a302->b, a587->a)) {
              if (is_const_v(a587->b)) {
                if (evaluate_predicate(fold(can_prove(((a302->a + a587->b) <= a461->b), simplifier)))) {
                  return min((a302->a - min((a302->b + a587->b), a461->b)), fold((0 - a587->b)));
                  return min((min(a302->b, a302->a) - a461->b), fold((0 - a587->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a302->a + a587->b) >= a461->b), simplifier)))) {
                  return min((min(a302->b, a302->a) - a461->b), fold((0 - a587->b)));
                  return min((a302->a - min((a302->b + a587->b), a461->b)), fold((0 - a587->b)));
                }
              }
            }
          }
          if (equal(a302->b, a461->b)) {
            if (evaluate_predicate(fold(can_prove((a302->a <= a461->a), simplifier)))) {
              return min((a302->a - min(a302->b, a461->a)), 0);
              return min((min(a302->b, a302->a) - a461->a), 0);
            }
            if (evaluate_predicate(fold(can_prove((a302->a >= a461->a), simplifier)))) {
              return min((min(a302->b, a302->a) - a461->a), 0);
              return min((a302->a - min(a302->b, a461->a)), 0);
            }
          }
          if (const Add *a619 = a461->b->as<Add>()) {
            if (equal(a302->b, a619->a)) {
              if (is_const_v(a619->b)) {
                if (evaluate_predicate(fold(can_prove(((a302->a + a619->b) <= a461->a), simplifier)))) {
                  return min((a302->a - min((a302->b + a619->b), a461->a)), fold((0 - a619->b)));
                  return min((min(a302->b, a302->a) - a461->a), fold((0 - a619->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a302->a + a619->b) >= a461->a), simplifier)))) {
                  return min((min(a302->b, a302->a) - a461->a), fold((0 - a619->b)));
                  return min((a302->a - min((a302->b + a619->b), a461->a)), fold((0 - a619->b)));
                }
              }
            }
            if (equal(a302->a, a619->a)) {
              if (is_const_v(a619->b)) {
                if (evaluate_predicate(fold(can_prove(((a302->b + a619->b) <= a461->a), simplifier)))) {
                  return min((a302->b - min((a302->a + a619->b), a461->a)), fold((0 - a619->b)));
                  return min((min(a302->a, a302->b) - a461->a), fold((0 - a619->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a302->b + a619->b) >= a461->a), simplifier)))) {
                  return min((min(a302->a, a302->b) - a461->a), fold((0 - a619->b)));
                  return min((a302->b - min((a302->a + a619->b), a461->a)), fold((0 - a619->b)));
                }
              }
            }
          }
          if (equal(a302->a, a461->b)) {
            if (evaluate_predicate(fold(can_prove((a302->b <= a461->a), simplifier)))) {
              return min((a302->b - min(a302->a, a461->a)), 0);
              return min((min(a302->a, a302->b) - a461->a), 0);
            }
            if (evaluate_predicate(fold(can_prove((a302->b >= a461->a), simplifier)))) {
              return min((min(a302->a, a302->b) - a461->a), 0);
              return min((a302->b - min(a302->a, a461->a)), 0);
            }
          }
        }
        if (const Mul *a470 = a302->a->as<Mul>()) {
          if (is_const_v(a470->b)) {
            if (is_const_v(a302->b)) {
              if (const Mul *a471 = a301->b->as<Mul>()) {
                if (const Min *a472 = a471->a->as<Min>()) {
                  if (equal(a470->a, a472->a)) {
                    if (is_const_v(a472->b)) {
                      if (equal(a470->b, a471->b)) {
                        if (evaluate_predicate(fold(((a470->b > 0) && (a302->b <= (a472->b * a470->b)))))) {
                          return min((a302->b - (min(a470->a, a472->b) * a470->b)), 0);
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
      if (const Min *a310 = a301->b->as<Min>()) {
        if (equal(a301->a, a310->a)) {
          if (evaluate_predicate(fold(!(is_const(a301->a))))) {
            return min((a301->a - a310->b), 0);
          }
        }
        if (equal(a301->a, a310->b)) {
          if (evaluate_predicate(fold(!(is_const(a301->a))))) {
            return min((a301->a - a310->a), 0);
          }
        }
        if (const Sub *a319 = a310->b->as<Sub>()) {
          if (equal(a301->a, a319->a)) {
            return min((a301->a - a310->a), a319->b);
          }
        }
        if (const Sub *a322 = a310->a->as<Sub>()) {
          if (equal(a301->a, a322->a)) {
            return min(a322->b, (a301->a - a310->b));
          }
          if (is_const_v(a310->b)) {
            return (a301->a + min((a322->b - a322->a), fold((0 - a310->b))));
          }
        }
        if (const Min *a357 = a310->a->as<Min>()) {
          if (const Sub *a358 = a357->a->as<Sub>()) {
            if (is_const_v(a357->b)) {
              if (is_const_v(a310->b)) {
                return (a301->a + min(min((a358->b - a358->a), fold((0 - a357->b))), fold((0 - a310->b))));
              }
            }
          }
        }
        if (const Add *a373 = a310->b->as<Add>()) {
          if (equal(a301->a, a373->a)) {
            if (evaluate_predicate(fold(!(is_const(a301->a))))) {
              return (0 - min((a310->a - a301->a), a373->b));
            }
          }
          if (equal(a301->a, a373->b)) {
            if (evaluate_predicate(fold(!(is_const(a301->a))))) {
              return (0 - min((a310->a - a301->a), a373->a));
            }
          }
          if (const Add *a386 = a373->b->as<Add>()) {
            if (equal(a301->a, a386->a)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->a - a301->a), (a373->a + a386->b)));
              }
            }
            if (equal(a301->a, a386->b)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->a - a301->a), (a386->a + a373->a)));
              }
            }
          }
          if (const Add *a394 = a373->a->as<Add>()) {
            if (equal(a301->a, a394->a)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->a - a301->a), (a394->b + a373->b)));
              }
            }
            if (equal(a301->a, a394->b)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->a - a301->a), (a394->a + a373->b)));
              }
            }
          }
        }
        if (const Add *a379 = a310->a->as<Add>()) {
          if (equal(a301->a, a379->a)) {
            if (evaluate_predicate(fold(!(is_const(a301->a))))) {
              return (0 - min((a310->b - a301->a), a379->b));
            }
          }
          if (equal(a301->a, a379->b)) {
            if (evaluate_predicate(fold(!(is_const(a301->a))))) {
              return (0 - min((a310->b - a301->a), a379->a));
            }
          }
          if (const Add *a402 = a379->b->as<Add>()) {
            if (equal(a301->a, a402->a)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->b - a301->a), (a379->a + a402->b)));
              }
            }
            if (equal(a301->a, a402->b)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->b - a301->a), (a402->a + a379->a)));
              }
            }
          }
          if (const Add *a410 = a379->a->as<Add>()) {
            if (equal(a301->a, a410->a)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->b - a301->a), (a379->b + a410->b)));
              }
            }
            if (equal(a301->a, a410->b)) {
              if (evaluate_predicate(fold(!(is_const(a301->a))))) {
                return (0 - min((a310->b - a301->a), (a379->b + a410->a)));
              }
            }
          }
        }
      }
      if (const Mul *a364 = a301->a->as<Mul>()) {
        if (equal(a364->a, a301->b)) {
          return (a364->a * (a364->b - 1));
        }
        if (equal(a364->b, a301->b)) {
          return ((a364->a - 1) * a364->b);
        }
      }
      if (const Mul *a368 = a301->b->as<Mul>()) {
        if (equal(a301->a, a368->a)) {
          return (a301->a * (1 - a368->b));
        }
        if (equal(a301->a, a368->b)) {
          return ((1 - a368->a) * a301->a);
        }
      }
    }
  }
  if (expr->is_no_overflow_int()) {
    if (const Sub *a826 = expr->as<Sub>()) {
      if (is_const_v(a826->a)) {
        if (const Div *a827 = a826->b->as<Div>()) {
          if (const Sub *a828 = a827->a->as<Sub>()) {
            if (is_const_v(a828->a)) {
              if (is_const_v(a827->b)) {
                if (evaluate_predicate(fold((a827->b > 0)))) {
                  return ((fold(((((a826->a * a827->b) - a828->a) + a827->b) - 1)) + a828->b) / a827->b);
                }
              }
            }
          }
          if (const Add *a831 = a827->a->as<Add>()) {
            if (is_const_v(a831->b)) {
              if (is_const_v(a827->b)) {
                if (evaluate_predicate(fold((a827->b > 0)))) {
                  return ((fold(((((a826->a * a827->b) - a831->b) + a827->b) - 1)) - a831->a) / a827->b);
                }
              }
            }
          }
        }
      }
      if (const Div *a833 = a826->b->as<Div>()) {
        if (const Add *a834 = a833->a->as<Add>()) {
          if (equal(a826->a, a834->a)) {
            if (is_const_v(a833->b)) {
              if (evaluate_predicate(fold((a833->b > 0)))) {
                return ((((a826->a * fold((a833->b - 1))) - a834->b) + fold((a833->b - 1))) / a833->b);
              }
            }
          }
          if (equal(a826->a, a834->b)) {
            if (is_const_v(a833->b)) {
              if (evaluate_predicate(fold((a833->b > 0)))) {
                return ((((a826->a * fold((a833->b - 1))) - a834->a) + fold((a833->b - 1))) / a833->b);
              }
            }
          }
        }
        if (const Sub *a837 = a833->a->as<Sub>()) {
          if (equal(a826->a, a837->a)) {
            if (is_const_v(a833->b)) {
              if (evaluate_predicate(fold((a833->b > 0)))) {
                return ((((a826->a * fold((a833->b - 1))) + a837->b) + fold((a833->b - 1))) / a833->b);
              }
            }
          }
          if (equal(a826->a, a837->b)) {
            if (is_const_v(a833->b)) {
              if (evaluate_predicate(fold((a833->b > 0)))) {
                return ((((a826->a * fold((a833->b + 1))) - a837->a) + fold((a833->b - 1))) / a833->b);
              }
            }
          }
        }
      }
      if (const Div *a845 = a826->a->as<Div>()) {
        if (const Add *a846 = a845->a->as<Add>()) {
          if (is_const_v(a845->b)) {
            if (equal(a846->a, a826->b)) {
              return (((a846->a * fold((1 - a845->b))) + a846->b) / a845->b);
            }
            if (equal(a846->b, a826->b)) {
              return ((a846->a + (a846->b * fold((1 - a845->b)))) / a845->b);
            }
            if (const Div *a886 = a826->b->as<Div>()) {
              if (const Add *a887 = a886->a->as<Add>()) {
                if (equal(a846->b, a887->a)) {
                  if (equal(a846->a, a887->b)) {
                    if (equal(a845->b, a886->b)) {
                      if (evaluate_predicate(fold((a845->b != 0)))) {
                        return 0;
                      }
                    }
                  }
                }
                if (equal(a846->a, a887->a)) {
                  if (is_const_v(a887->b)) {
                    if (equal(a845->b, a886->b)) {
                      if (evaluate_predicate(fold((a845->b > 0)))) {
                        return ((((a846->a + fold((a887->b % a845->b))) % a845->b) + (a846->b - a887->b)) / a845->b);
                      }
                    }
                  }
                }
              }
              if (equal(a846->a, a886->a)) {
                if (equal(a845->b, a886->b)) {
                  if (evaluate_predicate(fold((a845->b > 0)))) {
                    return (((a846->a % a845->b) + a846->b) / a845->b);
                  }
                }
              }
            }
          }
          if (const Add *a879 = a846->a->as<Add>()) {
            if (is_const_v(a845->b)) {
              if (const Div *a880 = a826->b->as<Div>()) {
                if (const Add *a881 = a880->a->as<Add>()) {
                  if (const Add *a882 = a881->a->as<Add>()) {
                    if (equal(a879->b, a882->a)) {
                      if (equal(a879->a, a882->b)) {
                        if (equal(a845->b, a880->b)) {
                          if (evaluate_predicate(fold((a845->b > 0)))) {
                            return ((((a879->a + a879->b) + a846->b) / a845->b) - (((a879->a + a879->b) + a881->b) / a845->b));
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(a846->b)) {
            if (is_const_v(a845->b)) {
              if (const Div *a896 = a826->b->as<Div>()) {
                if (const Add *a897 = a896->a->as<Add>()) {
                  if (equal(a846->a, a897->a)) {
                    if (equal(a845->b, a896->b)) {
                      if (evaluate_predicate(fold((a845->b > 0)))) {
                        return (((fold(((a845->b + a846->b) - 1)) - a897->b) - ((a846->a + fold((a846->b % a845->b))) % a845->b)) / a845->b);
                      }
                    }
                  }
                }
                if (const Sub *a907 = a896->a->as<Sub>()) {
                  if (equal(a846->a, a907->a)) {
                    if (equal(a845->b, a896->b)) {
                      if (evaluate_predicate(fold((a845->b > 0)))) {
                        return (((a907->b + fold(((a845->b + a846->b) - 1))) - ((a846->a + fold((a846->b % a845->b))) % a845->b)) / a845->b);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Min *a967 = a846->a->as<Min>()) {
            if (const Add *a968 = a967->a->as<Add>()) {
              if (const Mul *a969 = a968->a->as<Mul>()) {
                if (is_const_v(a969->b)) {
                  if (is_const_v(a845->b)) {
                    if (const Mul *a970 = a826->b->as<Mul>()) {
                      if (equal(a969->a, a970->a)) {
                        if (is_const_v(a970->b)) {
                          if (evaluate_predicate(fold((a969->b == (a845->b * a970->b))))) {
                            return ((min(a968->b, (a967->b - (a969->a * a969->b))) + a846->b) / a845->b);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (const Add *a975 = a967->b->as<Add>()) {
              if (const Mul *a976 = a975->a->as<Mul>()) {
                if (is_const_v(a976->b)) {
                  if (is_const_v(a845->b)) {
                    if (const Mul *a977 = a826->b->as<Mul>()) {
                      if (equal(a976->a, a977->a)) {
                        if (is_const_v(a977->b)) {
                          if (evaluate_predicate(fold((a976->b == (a845->b * a977->b))))) {
                            return ((min((a967->a - (a976->a * a976->b)), a975->b) + a846->b) / a845->b);
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
        if (const Sub *a852 = a845->a->as<Sub>()) {
          if (is_const_v(a845->b)) {
            if (equal(a852->a, a826->b)) {
              return (((a852->a * fold((1 - a845->b))) - a852->b) / a845->b);
            }
            if (equal(a852->b, a826->b)) {
              return ((a852->a - (a852->b * fold((1 + a845->b)))) / a845->b);
            }
            if (const Div *a901 = a826->b->as<Div>()) {
              if (const Add *a902 = a901->a->as<Add>()) {
                if (equal(a852->a, a902->a)) {
                  if (is_const_v(a902->b)) {
                    if (equal(a845->b, a901->b)) {
                      if (evaluate_predicate(fold((a845->b > 0)))) {
                        return (((((a852->a + fold((a902->b % a845->b))) % a845->b) - a852->b) - a902->b) / a845->b);
                      }
                    }
                  }
                }
              }
              if (equal(a852->a, a901->a)) {
                if (equal(a845->b, a901->b)) {
                  if (evaluate_predicate(fold((a845->b > 0)))) {
                    return (((a852->a % a845->b) - a852->b) / a845->b);
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a845->b)) {
          if (const Div *a910 = a826->b->as<Div>()) {
            if (const Add *a911 = a910->a->as<Add>()) {
              if (equal(a845->a, a911->a)) {
                if (equal(a845->b, a910->b)) {
                  if (evaluate_predicate(fold((a845->b > 0)))) {
                    return (((fold((a845->b - 1)) - a911->b) - (a845->a % a845->b)) / a845->b);
                  }
                }
              }
            }
            if (const Sub *a919 = a910->a->as<Sub>()) {
              if (equal(a845->a, a919->a)) {
                if (equal(a845->b, a910->b)) {
                  if (evaluate_predicate(fold((a845->b > 0)))) {
                    return (((a919->b + fold((a845->b - 1))) - (a845->a % a845->b)) / a845->b);
                  }
                }
              }
            }
          }
        }
        if (const Min *a954 = a845->a->as<Min>()) {
          if (const Add *a955 = a954->a->as<Add>()) {
            if (const Mul *a956 = a955->a->as<Mul>()) {
              if (is_const_v(a956->b)) {
                if (is_const_v(a845->b)) {
                  if (const Mul *a957 = a826->b->as<Mul>()) {
                    if (equal(a956->a, a957->a)) {
                      if (is_const_v(a957->b)) {
                        if (evaluate_predicate(fold((a956->b == (a845->b * a957->b))))) {
                          return (min(a955->b, (a954->b - (a956->a * a956->b))) / a845->b);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Add *a961 = a954->b->as<Add>()) {
            if (const Mul *a962 = a961->a->as<Mul>()) {
              if (is_const_v(a962->b)) {
                if (is_const_v(a845->b)) {
                  if (const Mul *a963 = a826->b->as<Mul>()) {
                    if (equal(a962->a, a963->a)) {
                      if (is_const_v(a963->b)) {
                        if (evaluate_predicate(fold((a962->b == (a845->b * a963->b))))) {
                          return (min(a961->b, (a954->a - (a962->a * a962->b))) / a845->b);
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
      if (const Mul *a857 = a826->a->as<Mul>()) {
        if (const Div *a858 = a857->a->as<Div>()) {
          if (is_const_v(a858->b)) {
            if (equal(a858->b, a857->b)) {
              if (equal(a858->a, a826->b)) {
                if (evaluate_predicate(fold((a858->b > 0)))) {
                  return (0 - (a858->a % a858->b));
                }
              }
            }
          }
          if (const Add *a865 = a858->a->as<Add>()) {
            if (is_const_v(a865->b)) {
              if (is_const_v(a858->b)) {
                if (equal(a858->b, a857->b)) {
                  if (equal(a865->a, a826->b)) {
                    if (evaluate_predicate(fold(((a858->b > 0) && ((a865->b + 1) == a858->b))))) {
                      return ((0 - a865->a) % a858->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a857->b)) {
          if (const Mul *a872 = a826->b->as<Mul>()) {
            if (is_const_v(a872->b)) {
              if (evaluate_predicate(fold(((a857->b % a872->b) == 0)))) {
                return (((a857->a * fold((a857->b / a872->b))) - a872->a) * a872->b);
              }
              if (evaluate_predicate(fold(((a872->b % a857->b) == 0)))) {
                return ((a857->a - (a872->a * fold((a872->b / a857->b)))) * a857->b);
              }
            }
          }
        }
      }
      if (const Mul *a860 = a826->b->as<Mul>()) {
        if (const Div *a861 = a860->a->as<Div>()) {
          if (equal(a826->a, a861->a)) {
            if (is_const_v(a861->b)) {
              if (equal(a861->b, a860->b)) {
                if (evaluate_predicate(fold((a861->b > 0)))) {
                  return (a826->a % a861->b);
                }
              }
            }
          }
          if (const Add *a869 = a861->a->as<Add>()) {
            if (equal(a826->a, a869->a)) {
              if (is_const_v(a869->b)) {
                if (is_const_v(a861->b)) {
                  if (equal(a861->b, a860->b)) {
                    if (evaluate_predicate(fold(((a861->b > 0) && ((a869->b + 1) == a861->b))))) {
                      return (((a826->a + a869->b) % a861->b) + fold((0 - a869->b)));
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a925 = a826->a->as<Add>()) {
        if (const Min *a926 = a925->a->as<Min>()) {
          if (const Add *a927 = a926->a->as<Add>()) {
            if (equal(a927->a, a826->b)) {
              return (min((a926->b - a927->a), a927->b) + a925->b);
            }
          }
        }
      }
      if (const Min *a929 = a826->a->as<Min>()) {
        if (const Add *a930 = a929->a->as<Add>()) {
          if (const Add *a931 = a930->a->as<Add>()) {
            if (equal(a931->a, a826->b)) {
              return min((a929->b - a931->a), (a931->b + a930->b));
            }
          }
          if (const Mul *a943 = a930->a->as<Mul>()) {
            if (const Add *a944 = a943->a->as<Add>()) {
              if (const Mul *a945 = a826->b->as<Mul>()) {
                if (equal(a944->a, a945->a)) {
                  if (equal(a943->b, a945->b)) {
                    return min((a929->b - (a944->a * a943->b)), ((a944->b * a943->b) + a930->b));
                  }
                }
                if (equal(a944->b, a945->a)) {
                  if (equal(a943->b, a945->b)) {
                    return min((a929->b - (a944->b * a943->b)), ((a944->a * a943->b) + a930->b));
                  }
                }
              }
            }
          }
        }
        if (const Min *a934 = a929->a->as<Min>()) {
          if (const Add *a935 = a934->a->as<Add>()) {
            if (equal(a935->a, a826->b)) {
              return min((min(a934->b, a929->b) - a935->a), a935->b);
            }
          }
          if (const Add *a939 = a934->b->as<Add>()) {
            if (equal(a939->a, a826->b)) {
              return min((min(a934->a, a929->b) - a939->a), a939->b);
            }
          }
        }
      }
    }
  }
  return expr;
}
