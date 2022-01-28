#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr Simplify_EQ(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  const BaseExprNode *r0 = nullptr;
  const BaseExprNode *r1 = nullptr;
  const BaseExprNode *r2 = nullptr;
  if ((r0 = a.as<Broadcast>())) {
    if (is_const_v(((const Broadcast*)r0)->lanes)) {
      if (is_const_int(b, 0)) {
        return broadcast((((const Broadcast*)r0)->value == 0), ((const Broadcast*)r0)->lanes);
      }
    }
  }
  if (type.is_operand_no_overflow()) {
    if ((r0 = a.as<Mul>())) {
      if (is_const_int(b, 0)) {
        return ((((const Mul*)r0)->a == 0) || (((const Mul*)r0)->b == 0));
      }
    }
    if ((r0 = a.as<Add>())) {
      if ((r1 = ((const Add*)r0)->a.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if (is_const_int(b, 0)) {
              if (evaluate_predicate(fold(((((const Add*)r0)->b % ((const Mul*)r1)->b) == 0)))) {
                return (((const Mul*)r1)->a == fold(((0 - ((const Add*)r0)->b) / ((const Mul*)r1)->b)));
              }
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Max>())) {
        if (is_const_v(((const Max*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if (is_const_int(b, 0)) {
              if (evaluate_predicate(fold(((((const Max*)r1)->b + ((const Add*)r0)->b) < 0)))) {
                return (((const Max*)r1)->a == fold((0 - ((const Add*)r0)->b)));
              }
              if (evaluate_predicate(fold(((((const Max*)r1)->b + ((const Add*)r0)->b) > 0)))) {
                return false;
              }
              if (evaluate_predicate(fold(((((const Max*)r1)->b + ((const Add*)r0)->b) == 0)))) {
                return (((const Max*)r1)->a <= ((const Max*)r1)->b);
              }
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Min>())) {
        if (is_const_v(((const Min*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if (is_const_int(b, 0)) {
              if (evaluate_predicate(fold(((((const Min*)r1)->b + ((const Add*)r0)->b) > 0)))) {
                return (((const Min*)r1)->a == fold((0 - ((const Add*)r0)->b)));
              }
              if (evaluate_predicate(fold(((((const Min*)r1)->b + ((const Add*)r0)->b) < 0)))) {
                return false;
              }
              if (evaluate_predicate(fold(((((const Min*)r1)->b + ((const Add*)r0)->b) == 0)))) {
                return (((const Min*)r1)->b <= ((const Min*)r1)->a);
              }
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<Select>())) {
    if (is_const_int(((const Select*)r0)->true_value, 0)) {
      if (is_const_int(b, 0)) {
        return (((const Select*)r0)->condition || (((const Select*)r0)->false_value == 0));
      }
    }
    if (is_const_v(((const Select*)r0)->true_value)) {
      if (is_const_int(b, 0)) {
        if (evaluate_predicate(fold((((const Select*)r0)->true_value != 0)))) {
          return (!(((const Select*)r0)->condition) && (((const Select*)r0)->false_value == 0));
        }
      }
    }
    if (is_const_int(((const Select*)r0)->false_value, 0)) {
      if (is_const_int(b, 0)) {
        return (!(((const Select*)r0)->condition) || (((const Select*)r0)->true_value == 0));
      }
    }
    if (is_const_v(((const Select*)r0)->false_value)) {
      if (is_const_int(b, 0)) {
        if (evaluate_predicate(fold((((const Select*)r0)->false_value != 0)))) {
          return (((const Select*)r0)->condition && (((const Select*)r0)->true_value == 0));
        }
      }
    }
  }
  if ((r0 = a.as<Add>())) {
    if ((r1 = ((const Add*)r0)->a.as<Select>())) {
      if (is_const_v(((const Select*)r1)->true_value)) {
        if (is_const_v(((const Add*)r0)->b)) {
          if (is_const_int(b, 0)) {
            if (evaluate_predicate(fold(((((const Select*)r1)->true_value + ((const Add*)r0)->b) == 0)))) {
              return (((const Select*)r1)->condition || (((const Select*)r1)->false_value == fold((0 - ((const Add*)r0)->b))));
            }
            if (evaluate_predicate(fold(((((const Select*)r1)->true_value + ((const Add*)r0)->b) != 0)))) {
              return (!(((const Select*)r1)->condition) && (((const Select*)r1)->false_value == fold((0 - ((const Add*)r0)->b))));
            }
          }
        }
      }
      if (is_const_v(((const Select*)r1)->false_value)) {
        if (is_const_v(((const Add*)r0)->b)) {
          if (is_const_int(b, 0)) {
            if (evaluate_predicate(fold(((((const Select*)r1)->false_value + ((const Add*)r0)->b) == 0)))) {
              return (!(((const Select*)r1)->condition) || (((const Select*)r1)->true_value == fold((0 - ((const Add*)r0)->b))));
            }
            if (evaluate_predicate(fold(((((const Select*)r1)->false_value + ((const Add*)r0)->b) != 0)))) {
              return (((const Select*)r1)->condition && (((const Select*)r1)->true_value == fold((0 - ((const Add*)r0)->b))));
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<Sub>())) {
    if ((r1 = ((const Sub*)r0)->a.as<Max>())) {
      if (equal(((const Max*)r1)->b, ((const Sub*)r0)->b)) {
        if (is_const_int(b, 0)) {
          return (((const Max*)r1)->a <= ((const Max*)r1)->b);
        }
      }
      if (equal(((const Max*)r1)->a, ((const Sub*)r0)->b)) {
        if (is_const_int(b, 0)) {
          return (((const Max*)r1)->b <= ((const Max*)r1)->a);
        }
      }
    }
    if ((r1 = ((const Sub*)r0)->a.as<Min>())) {
      if (equal(((const Min*)r1)->b, ((const Sub*)r0)->b)) {
        if (is_const_int(b, 0)) {
          return (((const Min*)r1)->b <= ((const Min*)r1)->a);
        }
      }
      if (equal(((const Min*)r1)->a, ((const Sub*)r0)->b)) {
        if (is_const_int(b, 0)) {
          return (((const Min*)r1)->a <= ((const Min*)r1)->b);
        }
      }
    }
    if ((r1 = ((const Sub*)r0)->b.as<Max>())) {
      if (equal(((const Sub*)r0)->a, ((const Max*)r1)->b)) {
        if (is_const_int(b, 0)) {
          return (((const Max*)r1)->a <= ((const Sub*)r0)->a);
        }
      }
      if (equal(((const Sub*)r0)->a, ((const Max*)r1)->a)) {
        if (is_const_int(b, 0)) {
          return (((const Max*)r1)->b <= ((const Sub*)r0)->a);
        }
      }
    }
    if ((r1 = ((const Sub*)r0)->b.as<Min>())) {
      if (equal(((const Sub*)r0)->a, ((const Min*)r1)->b)) {
        if (is_const_int(b, 0)) {
          return (((const Sub*)r0)->a <= ((const Min*)r1)->a);
        }
      }
      if (equal(((const Sub*)r0)->a, ((const Min*)r1)->a)) {
        if (is_const_int(b, 0)) {
          return (((const Sub*)r0)->a <= ((const Min*)r1)->b);
        }
      }
    }
  }
  if ((r0 = a.as<Max>())) {
    if (is_const_v(((const Max*)r0)->b)) {
      if (is_const_int(b, 0)) {
        if (evaluate_predicate(fold((((const Max*)r0)->b < 0)))) {
          return (((const Max*)r0)->a == 0);
        }
        if (evaluate_predicate(fold((((const Max*)r0)->b > 0)))) {
          return false;
        }
      }
    }
    if (is_const_int(((const Max*)r0)->b, 0)) {
      if (is_const_int(b, 0)) {
        return (((const Max*)r0)->a <= 0);
      }
    }
  }
  if ((r0 = a.as<Min>())) {
    if (is_const_v(((const Min*)r0)->b)) {
      if (is_const_int(b, 0)) {
        if (evaluate_predicate(fold((((const Min*)r0)->b > 0)))) {
          return (((const Min*)r0)->a == 0);
        }
        if (evaluate_predicate(fold((((const Min*)r0)->b < 0)))) {
          return false;
        }
      }
    }
    if (is_const_int(((const Min*)r0)->b, 0)) {
      if (is_const_int(b, 0)) {
        return (0 <= ((const Min*)r0)->a);
      }
    }
  }
  if (is_const_v(a)) {
    if (is_const_int(b, 0)) {
      return fold((a == 0));
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
