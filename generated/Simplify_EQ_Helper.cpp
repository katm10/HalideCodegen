#include "Expr.h"
#include "Type.h"
#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"

namespace Halide {
namespace Internal {
namespace CodeGen {
Expr Simplify_EQ(const EQ *expr, Simplify *simplifier) {
  if (const Broadcast *a0 = expr->a.as<Broadcast>()) {
    if (is_const(a0->lanes)) {
      if (is_const_int(expr->b, 0)) {
        return broadcast((a0->value == 0), a0->lanes);
      }
    }
  }
  if (is_operand_no_overflow(expr)) {
    if (const Mul *a2 = expr->a.as<Mul>()) {
      if (is_const_int(expr->b, 0)) {
        return ((a2->a == 0) || (a2->b == 0));
      }
    }
    if (const Add *a4 = expr->a.as<Add>()) {
      if (const Mul *a5 = a4->a.as<Mul>()) {
        if (is_const(a5->b)) {
          if (is_const(a4->b)) {
            if (is_const_int(expr->b, 0)) {
              if (evaluate_predicate(fold(((a4->b % a5->b) == 0)))) {
                return (a5->a == fold(((0 - a4->b) / a5->b)));
              }
            }
          }
        }
      }
      if (const Max *a54 = a4->a.as<Max>()) {
        if (is_const(a54->b)) {
          if (is_const(a4->b)) {
            if (is_const_int(expr->b, 0)) {
              if (evaluate_predicate(fold(((a54->b + a4->b) < 0)))) {
                return (a54->a == fold((0 - a4->b)));
              }
              if (evaluate_predicate(fold(((a54->b + a4->b) > 0)))) {
                return false;
              }
              if (evaluate_predicate(fold(((a54->b + a4->b) == 0)))) {
                return (a54->a <= a54->b);
              }
            }
          }
        }
      }
      if (const Min *a57 = a4->a.as<Min>()) {
        if (is_const(a57->b)) {
          if (is_const(a4->b)) {
            if (is_const_int(expr->b, 0)) {
              if (evaluate_predicate(fold(((a57->b + a4->b) > 0)))) {
                return (a57->a == fold((0 - a4->b)));
              }
              if (evaluate_predicate(fold(((a57->b + a4->b) < 0)))) {
                return false;
              }
              if (evaluate_predicate(fold(((a57->b + a4->b) == 0)))) {
                return (a57->b <= a57->a);
              }
            }
          }
        }
      }
    }
  }
  if (const Select *a7 = expr->a.as<Select>()) {
    if (is_const_int(a7->true_value, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (a7->condition || (a7->false_value == 0));
      }
    }
    if (is_const(a7->true_value)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a7->true_value != 0)))) {
          return (!(a7->condition) && (a7->false_value == 0));
        }
      }
    }
    if (is_const_int(a7->false_value, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (!(a7->condition) || (a7->true_value == 0));
      }
    }
    if (is_const(a7->false_value)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a7->false_value != 0)))) {
          return (a7->condition && (a7->true_value == 0));
        }
      }
    }
  }
  if (const Add *a17 = expr->a.as<Add>()) {
    if (const Select *a18 = a17->a.as<Select>()) {
      if (is_const(a18->true_value)) {
        if (is_const(a17->b)) {
          if (is_const_int(expr->b, 0)) {
            if (evaluate_predicate(fold(((a18->true_value + a17->b) == 0)))) {
              return (a18->condition || (a18->false_value == fold((0 - a17->b))));
            }
            if (evaluate_predicate(fold(((a18->true_value + a17->b) != 0)))) {
              return (!(a18->condition) && (a18->false_value == fold((0 - a17->b))));
            }
          }
        }
      }
      if (is_const(a18->false_value)) {
        if (is_const(a17->b)) {
          if (is_const_int(expr->b, 0)) {
            if (evaluate_predicate(fold(((a18->false_value + a17->b) == 0)))) {
              return (!(a18->condition) || (a18->true_value == fold((0 - a17->b))));
            }
            if (evaluate_predicate(fold(((a18->false_value + a17->b) != 0)))) {
              return (a18->condition && (a18->true_value == fold((0 - a17->b))));
            }
          }
        }
      }
    }
  }
  if (const Sub *a29 = expr->a.as<Sub>()) {
    if (const Max *a30 = a29->a.as<Max>()) {
      if (equal(a30->b, a29->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a30->a <= a30->b);
        }
      }
      if (equal(a30->a, a29->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a30->b <= a30->a);
        }
      }
    }
    if (const Min *a33 = a29->a.as<Min>()) {
      if (equal(a33->b, a29->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a33->b <= a33->a);
        }
      }
      if (equal(a33->a, a29->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a33->a <= a33->b);
        }
      }
    }
    if (const Max *a42 = a29->b.as<Max>()) {
      if (equal(a29->a, a42->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a42->a <= a29->a);
        }
      }
      if (equal(a29->a, a42->a)) {
        if (is_const_int(expr->b, 0)) {
          return (a42->b <= a29->a);
        }
      }
    }
    if (const Min *a45 = a29->b.as<Min>()) {
      if (equal(a29->a, a45->b)) {
        if (is_const_int(expr->b, 0)) {
          return (a29->a <= a45->a);
        }
      }
      if (equal(a29->a, a45->a)) {
        if (is_const_int(expr->b, 0)) {
          return (a29->a <= a45->b);
        }
      }
    }
  }
  if (const Max *a71 = expr->a.as<Max>()) {
    if (is_const(a71->b)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a71->b < 0)))) {
          return (a71->a == 0);
        }
        if (evaluate_predicate(fold((a71->b > 0)))) {
          return false;
        }
      }
    }
    if (is_const_int(a71->b, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (a71->a <= 0);
      }
    }
  }
  if (const Min *a73 = expr->a.as<Min>()) {
    if (is_const(a73->b)) {
      if (is_const_int(expr->b, 0)) {
        if (evaluate_predicate(fold((a73->b > 0)))) {
          return (a73->a == 0);
        }
        if (evaluate_predicate(fold((a73->b < 0)))) {
          return false;
        }
      }
    }
    if (is_const_int(a73->b, 0)) {
      if (is_const_int(expr->b, 0)) {
        return (0 <= a73->a);
      }
    }
  }
  if (is_const(expr->a)) {
    if (is_const_int(expr->b, 0)) {
      return fold((expr->a == 0));
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
