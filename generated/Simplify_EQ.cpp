#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_EQ(const EQ *expr, Simplify *simplifier) {
  if (const Broadcast *a0 = expr->a.as<Broadcast>()) {
    if (is_const(a0->lanes)) {
      if (is_const_int(expr->b, 0)) {
        return broadcast((a0->value == 0), a0->lanes);
      }
    }
  }
  if (expr->is_operand_no_overflow()) {
    if (const EQ *a2 = expr.as<EQ>()) {
      if (const Mul *a3 = a2->a.as<Mul>()) {
        if (is_const_int(a2->b, 0)) {
          return ((a3->a == 0) || (a3->b == 0));
        }
      }
      if (const Add *a6 = a2->a.as<Add>()) {
        if (const Mul *a7 = a6->a.as<Mul>()) {
          if (is_const(a7->b)) {
            if (is_const(a6->b)) {
              if (is_const_int(a2->b, 0)) {
                if (evaluate_predicate(fold(((a6->b % a7->b) == 0)))) {
                  return (a7->a == fold(((0 - a6->b) / a7->b)));
                }
              }
            }
          }
        }
        if (const Min *a57 = a6->a.as<Min>()) {
          if (is_const(a57->b)) {
            if (is_const(a6->b)) {
              if (is_const_int(a2->b, 0)) {
                if (evaluate_predicate(fold(((a57->b + a6->b) < 0)))) {
                  return (a57->a == fold((0 - a6->b)));
                  return false;
                }
                if (evaluate_predicate(fold(((a57->b + a6->b) > 0)))) {
                  return (a57->a == fold((0 - a6->b)));
                  return false;
                }
                if (evaluate_predicate(fold(((a57->b + a6->b) == 0)))) {
                  return (a57->a <= a57->b);
                  return (a57->b <= a57->a);
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Select *a9 = expr->a.as<Select>()) {
    if (is_const_int(a9->true_value, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (a9->cond || (a9->false_value == 0));
      }
    }
    if (is_const(a9->true_value)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a9->true_value != 0)))) {
          return (!(a9->cond) && (a9->false_value == 0));
        }
      }
    }
    if (is_const_int(a9->false_value, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (!(a9->cond) || (a9->true_value == 0));
      }
    }
    if (is_const(a9->false_value)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a9->false_value != 0)))) {
          return (a9->cond && (a9->true_value == 0));
        }
      }
    }
  }
  if (const Add *a19 = expr->a.as<Add>()) {
    if (const Select *a20 = a19->a.as<Select>()) {
      if (is_const(a20->true_value)) {
        if (is_const(a19->b)) {
          if (is_const_int(expr->b, 0)) {
            if (evaluate_predicate(fold(((a20->true_value + a19->b) == 0)))) {
              return (a20->cond || (a20->false_value == fold((0 - a19->b))));
            }
            if (evaluate_predicate(fold(((a20->true_value + a19->b) != 0)))) {
              return (!(a20->cond) && (a20->false_value == fold((0 - a19->b))));
            }
          }
        }
      }
      if (is_const(a20->false_value)) {
        if (is_const(a19->b)) {
          if (is_const_int(expr->b, 0)) {
            if (evaluate_predicate(fold(((a20->false_value + a19->b) == 0)))) {
              return (!(a20->cond) || (a20->true_value == fold((0 - a19->b))));
            }
            if (evaluate_predicate(fold(((a20->false_value + a19->b) != 0)))) {
              return (a20->cond && (a20->true_value == fold((0 - a19->b))));
            }
          }
        }
      }
    }
  }
  if (const Sub *a31 = expr->a.as<Sub>()) {
    if (const Min *a32 = a31->a.as<Min>()) {
      if (equal(a32->b, a31->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a32->a <= a32->b);
          return (a32->b <= a32->a);
        }
      }
      if (equal(a32->a, a31->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a32->b <= a32->a);
          return (a32->a <= a32->b);
        }
      }
    }
    if (const Min *a44 = a31->b.as<Min>()) {
      if (equal(a31->a, a44->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a44->a <= a31->a);
          return (a31->a <= a44->a);
        }
      }
      if (equal(a31->a, a44->a)) {
        if (is_const_int(expr->b, 0)) {
          return (a44->b <= a31->a);
          return (a31->a <= a44->b);
        }
      }
    }
  }
  if (const Min *a79 = expr->a.as<Min>()) {
    if (is_const(a79->b)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a79->b < 0)))) {
          return (a79->a == 0);
          return false;
        }
        if (evaluate_predicate(fold((a79->b > 0)))) {
          return (a79->a == 0);
          return false;
        }
      }
    }
    if (is_const_int(a79->b, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (a79->a <= 0);
        return (0 <= a79->a);
      }
    }
  }
  if (is_const(expr->a)) {
    if (is_const_int(expr->b, 0)) {
      return fold((expr->a == 0));
    }
  }
  return expr;
}
