#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_EQ(const EQ *expr, Simplify *simplifier) {
  if (const Broadcast *a0 = expr->a.as<Broadcast>()) {
    if (is_const_v(a0->lanes)) {
      if (is_const_int(expr->b, 0)) {
        return broadcast((a0->value == 0), a0->lanes);
      }
    }
  }
  if (expr->is_operand_no_overflow()) {
    if (const EQ *a1 = expr.as<EQ>()) {
      if (const Mul *a2 = a1->a.as<Mul>()) {
        if (is_const_int(a1->b, 0)) {
          return ((a2->a == 0) || (a2->b == 0));
        }
      }
      if (const Add *a4 = a1->a.as<Add>()) {
        if (const Mul *a5 = a4->a.as<Mul>()) {
          if (is_const_v(a5->b)) {
            if (is_const_v(a4->b)) {
              if (is_const_int(a1->b, 0)) {
                if (evaluate_predicate(fold(((a4->b % a5->b) == 0)))) {
                  return (a5->a == fold(((0 - a4->b) / a5->b)));
                }
              }
            }
          }
        }
        if (const Min *a36 = a4->a.as<Min>()) {
          if (is_const_v(a36->b)) {
            if (is_const_v(a4->b)) {
              if (is_const_int(a1->b, 0)) {
                if (evaluate_predicate(fold(((a36->b + a4->b) < 0)))) {
                  return (a36->a == fold((0 - a4->b)));
                  return false;
                }
                if (evaluate_predicate(fold(((a36->b + a4->b) > 0)))) {
                  return (a36->a == fold((0 - a4->b)));
                  return false;
                }
                if (evaluate_predicate(fold(((a36->b + a4->b) == 0)))) {
                  return (a36->a <= a36->b);
                  return (a36->b <= a36->a);
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Select *a6 = expr->a.as<Select>()) {
    if (is_const_int(a6->true_value, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (a6->condition || (a6->false_value == 0));
      }
    }
    if (is_const_v(a6->true_value)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a6->true_value != 0)))) {
          return (!(a6->condition) && (a6->false_value == 0));
        }
      }
    }
    if (is_const_int(a6->false_value, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (!(a6->condition) || (a6->true_value == 0));
      }
    }
    if (is_const_v(a6->false_value)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a6->false_value != 0)))) {
          return (a6->condition && (a6->true_value == 0));
        }
      }
    }
  }
  if (const Add *a10 = expr->a.as<Add>()) {
    if (const Select *a11 = a10->a.as<Select>()) {
      if (is_const_v(a11->true_value)) {
        if (is_const_v(a10->b)) {
          if (is_const_int(expr->b, 0)) {
            if (evaluate_predicate(fold(((a11->true_value + a10->b) == 0)))) {
              return (a11->condition || (a11->false_value == fold((0 - a10->b))));
            }
            if (evaluate_predicate(fold(((a11->true_value + a10->b) != 0)))) {
              return (!(a11->condition) && (a11->false_value == fold((0 - a10->b))));
            }
          }
        }
      }
      if (is_const_v(a11->false_value)) {
        if (is_const_v(a10->b)) {
          if (is_const_int(expr->b, 0)) {
            if (evaluate_predicate(fold(((a11->false_value + a10->b) == 0)))) {
              return (!(a11->condition) || (a11->true_value == fold((0 - a10->b))));
            }
            if (evaluate_predicate(fold(((a11->false_value + a10->b) != 0)))) {
              return (a11->condition && (a11->true_value == fold((0 - a10->b))));
            }
          }
        }
      }
    }
  }
  if (const Sub *a18 = expr->a.as<Sub>()) {
    if (const Min *a19 = a18->a.as<Min>()) {
      if (equal(a19->b, a18->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a19->a <= a19->b);
          return (a19->b <= a19->a);
        }
      }
      if (equal(a19->a, a18->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a19->b <= a19->a);
          return (a19->a <= a19->b);
        }
      }
    }
    if (const Min *a27 = a18->b.as<Min>()) {
      if (equal(a18->a, a27->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a27->a <= a18->a);
          return (a18->a <= a27->a);
        }
      }
      if (equal(a18->a, a27->a)) {
        if (is_const_int(expr->b, 0)) {
          return (a27->b <= a18->a);
          return (a18->a <= a27->b);
        }
      }
    }
  }
  if (const Min *a52 = expr->a.as<Min>()) {
    if (is_const_v(a52->b)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a52->b < 0)))) {
          return (a52->a == 0);
          return false;
        }
        if (evaluate_predicate(fold((a52->b > 0)))) {
          return (a52->a == 0);
          return false;
        }
      }
    }
    if (is_const_int(a52->b, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (a52->a <= 0);
        return (0 <= a52->a);
      }
    }
  }
  if (is_const_v(expr->a)) {
    if (is_const_int(expr->b, 0)) {
      return fold((expr->a == 0));
    }
  }
  return expr;
}
