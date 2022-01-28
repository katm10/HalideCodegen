#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr Simplify_Sub(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  const BaseExprNode *r0 = nullptr;
  const BaseExprNode *r1 = nullptr;
  const BaseExprNode *r2 = nullptr;
  const BaseExprNode *r3 = nullptr;
  const BaseExprNode *r4 = nullptr;
  const BaseExprNode *r5 = nullptr;
  if (is_const_int(b, 0)) {
    return a;
  }
  if (is_const_v(a)) {
    if (is_const_v(b)) {
      return fold((a - b));
    }
    if ((r0 = b.as<Select>())) {
      if (is_const_v(((const Select*)r0)->true_value)) {
        if (is_const_v(((const Select*)r0)->false_value)) {
          return select(((const Select*)r0)->condition, fold((a - ((const Select*)r0)->true_value)), fold((a - ((const Select*)r0)->false_value)));
        }
      }
    }
  }
  if (!(type.is_uint())) {
    if (is_const_v(b)) {
      if (evaluate_predicate(fold(!(overflows((0 - b)))))) {
        return (a + fold((0 - b)));
      }
    }
  }
  if (equal(a, b)) {
    return 0;
  }
  if ((r0 = a.as<Ramp>())) {
    if (is_const_v(((const Ramp*)r0)->lanes)) {
      if ((r1 = b.as<Ramp>())) {
        if (equal(((const Ramp*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
          return ramp((((const Ramp*)r0)->base - ((const Ramp*)r1)->base), (((const Ramp*)r0)->stride - ((const Ramp*)r1)->stride), ((const Ramp*)r0)->lanes);
        }
      }
      if ((r1 = b.as<Broadcast>())) {
        if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
          return ramp((((const Ramp*)r0)->base - ((const Broadcast*)r1)->value), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
        }
      }
    }
    if ((r1 = ((const Ramp*)r0)->base.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if (is_const_v(((const Ramp*)r0)->lanes)) {
          if ((r2 = b.as<Broadcast>())) {
            if (is_const_v(((const Broadcast*)r2)->lanes)) {
              if (evaluate_predicate(fold((((const Broadcast*)r2)->lanes == (((const Broadcast*)r1)->lanes * ((const Ramp*)r0)->lanes))))) {
                return ramp(broadcast((((const Broadcast*)r1)->value - ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
              }
            }
          }
        }
      }
    }
    if ((r1 = ((const Ramp*)r0)->base.as<Ramp>())) {
      if (is_const_v(((const Ramp*)r1)->lanes)) {
        if (is_const_v(((const Ramp*)r0)->lanes)) {
          if ((r2 = b.as<Broadcast>())) {
            if (is_const_v(((const Broadcast*)r2)->lanes)) {
              if (evaluate_predicate(fold((((const Broadcast*)r2)->lanes == (((const Ramp*)r1)->lanes * ((const Ramp*)r0)->lanes))))) {
                return ramp(ramp((((const Ramp*)r1)->base - ((const Broadcast*)r2)->value), ((const Ramp*)r1)->stride, ((const Ramp*)r1)->lanes), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
              }
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<Broadcast>())) {
    if (is_const_v(((const Broadcast*)r0)->lanes)) {
      if ((r1 = b.as<Ramp>())) {
        if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
          return ramp((((const Broadcast*)r0)->value - ((const Ramp*)r1)->base), (0 - ((const Ramp*)r1)->stride), ((const Broadcast*)r0)->lanes);
        }
      }
      if ((r1 = b.as<Broadcast>())) {
        if (equal(((const Broadcast*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
          return broadcast((((const Broadcast*)r0)->value - ((const Broadcast*)r1)->value), ((const Broadcast*)r0)->lanes);
        }
        if (is_const_v(((const Broadcast*)r1)->lanes)) {
          if (evaluate_predicate(fold(((((const Broadcast*)r1)->lanes % ((const Broadcast*)r0)->lanes) == 0)))) {
            return broadcast((((const Broadcast*)r0)->value - broadcast(((const Broadcast*)r1)->value, fold((((const Broadcast*)r1)->lanes / ((const Broadcast*)r0)->lanes)))), ((const Broadcast*)r0)->lanes);
          }
          if (evaluate_predicate(fold(((((const Broadcast*)r0)->lanes % ((const Broadcast*)r1)->lanes) == 0)))) {
            return broadcast((broadcast(((const Broadcast*)r0)->value, fold((((const Broadcast*)r0)->lanes / ((const Broadcast*)r1)->lanes))) - ((const Broadcast*)r1)->value), ((const Broadcast*)r1)->lanes);
          }
        }
      }
    }
  }
  if ((r0 = a.as<Sub>())) {
    if ((r1 = ((const Sub*)r0)->b.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (equal(((const Broadcast*)r1)->lanes, ((const Broadcast*)r2)->lanes)) {
            return (((const Sub*)r0)->a - broadcast((((const Broadcast*)r1)->value + ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes));
          }
        }
      }
    }
    if (equal(((const Sub*)r0)->a, b)) {
      return (0 - ((const Sub*)r0)->b);
    }
    if ((r1 = ((const Sub*)r0)->a.as<Select>())) {
      if ((r2 = b.as<Select>())) {
        if (equal(((const Select*)r1)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r1)->condition, (((const Select*)r1)->true_value - ((const Select*)r2)->true_value), (((const Select*)r1)->false_value - ((const Select*)r2)->false_value)) - ((const Sub*)r0)->b);
        }
      }
    }
    if (is_const_v(((const Sub*)r0)->a)) {
      if ((r1 = b.as<Sub>())) {
        if (is_const_v(((const Sub*)r1)->a)) {
          return ((((const Sub*)r1)->b - ((const Sub*)r0)->b) + fold((((const Sub*)r0)->a - ((const Sub*)r1)->a)));
        }
      }
      if ((r1 = b.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          return (fold((((const Sub*)r0)->a - ((const Add*)r1)->b)) - (((const Sub*)r0)->b + ((const Add*)r1)->a));
        }
      }
      if (is_const_v(b)) {
        return (fold((((const Sub*)r0)->a - b)) - ((const Sub*)r0)->b);
      }
    }
    if ((r1 = ((const Sub*)r0)->b.as<Mul>())) {
      if ((r2 = b.as<Mul>())) {
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->b)) {
          return (((const Sub*)r0)->a - ((((const Mul*)r1)->a + ((const Mul*)r2)->a) * ((const Mul*)r1)->b));
        }
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->a)) {
          return (((const Sub*)r0)->a - ((((const Mul*)r1)->a + ((const Mul*)r2)->b) * ((const Mul*)r1)->b));
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->b)) {
          return (((const Sub*)r0)->a - (((const Mul*)r1)->a * (((const Mul*)r1)->b + ((const Mul*)r2)->a)));
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
          return (((const Sub*)r0)->a - (((const Mul*)r1)->a * (((const Mul*)r1)->b + ((const Mul*)r2)->b)));
        }
      }
    }
    if ((r1 = ((const Sub*)r0)->a.as<Mul>())) {
      if ((r2 = b.as<Mul>())) {
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->b)) {
          return (((((const Mul*)r1)->a - ((const Mul*)r2)->a) * ((const Mul*)r1)->b) - ((const Sub*)r0)->b);
        }
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->a)) {
          return (((((const Mul*)r1)->a - ((const Mul*)r2)->b) * ((const Mul*)r1)->b) - ((const Sub*)r0)->b);
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->b)) {
          return ((((const Mul*)r1)->a * (((const Mul*)r1)->b - ((const Mul*)r2)->a)) - ((const Sub*)r0)->b);
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
          return ((((const Mul*)r1)->a * (((const Mul*)r1)->b - ((const Mul*)r2)->b)) - ((const Sub*)r0)->b);
        }
      }
    }
    if ((r1 = b.as<Add>())) {
      if (equal(((const Sub*)r0)->a, ((const Add*)r1)->a)) {
        return ((0 - ((const Sub*)r0)->b) - ((const Add*)r1)->b);
      }
      if (equal(((const Sub*)r0)->a, ((const Add*)r1)->b)) {
        return ((0 - ((const Sub*)r0)->b) - ((const Add*)r1)->a);
      }
    }
    if ((r1 = ((const Sub*)r0)->a.as<Add>())) {
      if (equal(((const Add*)r1)->a, b)) {
        return (((const Add*)r1)->b - ((const Sub*)r0)->b);
      }
      if (equal(((const Add*)r1)->b, b)) {
        return (((const Add*)r1)->a - ((const Sub*)r0)->b);
      }
    }
    if ((r1 = ((const Sub*)r0)->a.as<Sub>())) {
      if (equal(((const Sub*)r1)->a, b)) {
        return (0 - (((const Sub*)r1)->b + ((const Sub*)r0)->b));
      }
    }
  }
  if ((r0 = a.as<Add>())) {
    if ((r1 = ((const Add*)r0)->b.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (equal(((const Broadcast*)r1)->lanes, ((const Broadcast*)r2)->lanes)) {
            return (((const Add*)r0)->a + broadcast((((const Broadcast*)r1)->value - ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes));
          }
        }
      }
    }
    if (equal(((const Add*)r0)->a, b)) {
      return ((const Add*)r0)->b;
    }
    if (equal(((const Add*)r0)->b, b)) {
      return ((const Add*)r0)->a;
    }
    if ((r1 = ((const Add*)r0)->a.as<Select>())) {
      if ((r2 = b.as<Select>())) {
        if (equal(((const Select*)r1)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r1)->condition, (((const Select*)r1)->true_value - ((const Select*)r2)->true_value), (((const Select*)r1)->false_value - ((const Select*)r2)->false_value)) + ((const Add*)r0)->b);
        }
      }
    }
    if ((r1 = ((const Add*)r0)->b.as<Select>())) {
      if ((r2 = b.as<Select>())) {
        if (equal(((const Select*)r1)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r1)->condition, (((const Select*)r1)->true_value - ((const Select*)r2)->true_value), (((const Select*)r1)->false_value - ((const Select*)r2)->false_value)) + ((const Add*)r0)->a);
        }
      }
    }
    if (is_const_v(((const Add*)r0)->b)) {
      if (is_const_v(b)) {
        return (((const Add*)r0)->a + fold((((const Add*)r0)->b - b)));
      }
      if ((r1 = b.as<Sub>())) {
        if (is_const_v(((const Sub*)r1)->a)) {
          return ((((const Add*)r0)->a + ((const Sub*)r1)->b) + fold((((const Add*)r0)->b - ((const Sub*)r1)->a)));
        }
      }
      if ((r1 = b.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          return ((((const Add*)r0)->a - ((const Add*)r1)->a) + fold((((const Add*)r0)->b - ((const Add*)r1)->b)));
        }
      }
      return ((((const Add*)r0)->a - b) + ((const Add*)r0)->b);
    }
    if ((r1 = ((const Add*)r0)->b.as<Mul>())) {
      if ((r2 = b.as<Mul>())) {
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->b)) {
          return (((const Add*)r0)->a + ((((const Mul*)r1)->a - ((const Mul*)r2)->a) * ((const Mul*)r1)->b));
        }
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->a)) {
          return (((const Add*)r0)->a + ((((const Mul*)r1)->a - ((const Mul*)r2)->b) * ((const Mul*)r1)->b));
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->b)) {
          return (((const Add*)r0)->a + (((const Mul*)r1)->a * (((const Mul*)r1)->b - ((const Mul*)r2)->a)));
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
          return (((const Add*)r0)->a + (((const Mul*)r1)->a * (((const Mul*)r1)->b - ((const Mul*)r2)->b)));
        }
      }
    }
    if ((r1 = ((const Add*)r0)->a.as<Mul>())) {
      if ((r2 = b.as<Mul>())) {
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->b)) {
          return (((const Add*)r0)->b + ((((const Mul*)r1)->a - ((const Mul*)r2)->a) * ((const Mul*)r1)->b));
        }
        if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->a)) {
          return (((const Add*)r0)->b + ((((const Mul*)r1)->a - ((const Mul*)r2)->b) * ((const Mul*)r1)->b));
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->b)) {
          return (((const Add*)r0)->b + (((const Mul*)r1)->a * (((const Mul*)r1)->b - ((const Mul*)r2)->a)));
        }
        if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
          return (((const Add*)r0)->b + (((const Mul*)r1)->a * (((const Mul*)r1)->b - ((const Mul*)r2)->b)));
        }
      }
    }
    if ((r1 = b.as<Add>())) {
      if (equal(((const Add*)r0)->a, ((const Add*)r1)->a)) {
        return (((const Add*)r0)->b - ((const Add*)r1)->b);
      }
      if (equal(((const Add*)r0)->a, ((const Add*)r1)->b)) {
        return (((const Add*)r0)->b - ((const Add*)r1)->a);
      }
      if (equal(((const Add*)r0)->b, ((const Add*)r1)->a)) {
        return (((const Add*)r0)->a - ((const Add*)r1)->b);
      }
      if (equal(((const Add*)r0)->b, ((const Add*)r1)->b)) {
        return (((const Add*)r0)->a - ((const Add*)r1)->a);
      }
      if ((r2 = ((const Add*)r1)->b.as<Add>())) {
        if (equal(((const Add*)r0)->a, ((const Add*)r2)->b)) {
          return (((const Add*)r0)->b - (((const Add*)r1)->a + ((const Add*)r2)->a));
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r2)->b)) {
          return (((const Add*)r0)->a - (((const Add*)r1)->a + ((const Add*)r2)->a));
        }
        if (equal(((const Add*)r0)->a, ((const Add*)r2)->a)) {
          return (((const Add*)r0)->b - (((const Add*)r1)->a + ((const Add*)r2)->b));
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r2)->a)) {
          return (((const Add*)r0)->a - (((const Add*)r1)->a + ((const Add*)r2)->b));
        }
      }
      if ((r2 = ((const Add*)r1)->a.as<Add>())) {
        if (equal(((const Add*)r0)->a, ((const Add*)r2)->a)) {
          return (((const Add*)r0)->b - (((const Add*)r2)->b + ((const Add*)r1)->b));
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r2)->a)) {
          return (((const Add*)r0)->a - (((const Add*)r2)->b + ((const Add*)r1)->b));
        }
        if (equal(((const Add*)r0)->a, ((const Add*)r2)->b)) {
          return (((const Add*)r0)->b - (((const Add*)r2)->a + ((const Add*)r1)->b));
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r2)->b)) {
          return (((const Add*)r0)->a - (((const Add*)r2)->a + ((const Add*)r1)->b));
        }
      }
    }
    if ((r1 = ((const Add*)r0)->a.as<Add>())) {
      if (equal(((const Add*)r1)->a, b)) {
        return (((const Add*)r1)->b + ((const Add*)r0)->b);
      }
      if (equal(((const Add*)r1)->b, b)) {
        return (((const Add*)r1)->a + ((const Add*)r0)->b);
      }
    }
    if ((r1 = ((const Add*)r0)->b.as<Add>())) {
      if (equal(((const Add*)r1)->a, b)) {
        return (((const Add*)r0)->a + ((const Add*)r1)->b);
      }
      if (equal(((const Add*)r1)->b, b)) {
        return (((const Add*)r0)->a + ((const Add*)r1)->a);
      }
    }
    if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
      if (equal(((const Sub*)r1)->a, b)) {
        return (((const Add*)r0)->a - ((const Sub*)r1)->b);
      }
    }
    if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
      if (equal(((const Sub*)r1)->a, b)) {
        return (((const Add*)r0)->b - ((const Sub*)r1)->b);
      }
    }
    if ((r1 = b.as<Min>())) {
      if (equal(((const Add*)r0)->a, ((const Min*)r1)->a)) {
        if (equal(((const Add*)r0)->b, ((const Min*)r1)->b)) {
          return max(((const Add*)r0)->b, ((const Add*)r0)->a);
        }
      }
      if (equal(((const Add*)r0)->b, ((const Min*)r1)->a)) {
        if (equal(((const Add*)r0)->a, ((const Min*)r1)->b)) {
          return max(((const Add*)r0)->b, ((const Add*)r0)->a);
        }
      }
    }
    if ((r1 = b.as<Max>())) {
      if (equal(((const Add*)r0)->a, ((const Max*)r1)->a)) {
        if (equal(((const Add*)r0)->b, ((const Max*)r1)->b)) {
          return min(((const Add*)r0)->b, ((const Add*)r0)->a);
        }
      }
      if (equal(((const Add*)r0)->b, ((const Max*)r1)->a)) {
        if (equal(((const Add*)r0)->a, ((const Max*)r1)->b)) {
          return min(((const Add*)r0)->a, ((const Add*)r0)->b);
        }
      }
    }
  }
  if ((r0 = a.as<Select>())) {
    if ((r1 = b.as<Select>())) {
      if (equal(((const Select*)r0)->condition, ((const Select*)r1)->condition)) {
        return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - ((const Select*)r1)->true_value), (((const Select*)r0)->false_value - ((const Select*)r1)->false_value));
      }
    }
    if (equal(((const Select*)r0)->true_value, b)) {
      return select(((const Select*)r0)->condition, 0, (((const Select*)r0)->false_value - ((const Select*)r0)->true_value));
    }
    if (equal(((const Select*)r0)->false_value, b)) {
      return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - ((const Select*)r0)->false_value), 0);
    }
    if ((r1 = ((const Select*)r0)->true_value.as<Add>())) {
      if (equal(((const Add*)r1)->a, b)) {
        return select(((const Select*)r0)->condition, ((const Add*)r1)->b, (((const Select*)r0)->false_value - ((const Add*)r1)->a));
      }
      if (equal(((const Add*)r1)->b, b)) {
        return select(((const Select*)r0)->condition, ((const Add*)r1)->a, (((const Select*)r0)->false_value - ((const Add*)r1)->b));
      }
      if ((r2 = ((const Add*)r1)->b.as<Add>())) {
        if (equal(((const Add*)r2)->b, b)) {
          return select(((const Select*)r0)->condition, (((const Add*)r1)->a + ((const Add*)r2)->a), (((const Select*)r0)->false_value - ((const Add*)r2)->b));
        }
        if (equal(((const Add*)r2)->a, b)) {
          return select(((const Select*)r0)->condition, (((const Add*)r1)->a + ((const Add*)r2)->b), (((const Select*)r0)->false_value - ((const Add*)r2)->a));
        }
      }
      if ((r2 = ((const Add*)r1)->a.as<Add>())) {
        if (equal(((const Add*)r2)->a, b)) {
          return select(((const Select*)r0)->condition, (((const Add*)r1)->b + ((const Add*)r2)->b), (((const Select*)r0)->false_value - ((const Add*)r2)->a));
        }
        if (equal(((const Add*)r2)->b, b)) {
          return select(((const Select*)r0)->condition, (((const Add*)r1)->b + ((const Add*)r2)->a), (((const Select*)r0)->false_value - ((const Add*)r2)->b));
        }
      }
      if ((r2 = b.as<Add>())) {
        if (equal(((const Add*)r1)->a, ((const Add*)r2)->b)) {
          return (select(((const Select*)r0)->condition, ((const Add*)r1)->b, (((const Select*)r0)->false_value - ((const Add*)r1)->a)) - ((const Add*)r2)->a);
        }
        if (equal(((const Add*)r1)->b, ((const Add*)r2)->b)) {
          return (select(((const Select*)r0)->condition, ((const Add*)r1)->a, (((const Select*)r0)->false_value - ((const Add*)r1)->b)) - ((const Add*)r2)->a);
        }
        if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
          return (select(((const Select*)r0)->condition, ((const Add*)r1)->b, (((const Select*)r0)->false_value - ((const Add*)r1)->a)) - ((const Add*)r2)->b);
        }
        if (equal(((const Add*)r1)->b, ((const Add*)r2)->a)) {
          return (select(((const Select*)r0)->condition, ((const Add*)r1)->a, (((const Select*)r0)->false_value - ((const Add*)r1)->b)) - ((const Add*)r2)->b);
        }
      }
    }
    if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
      if (equal(((const Add*)r1)->a, b)) {
        return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - ((const Add*)r1)->a), ((const Add*)r1)->b);
      }
      if (equal(((const Add*)r1)->b, b)) {
        return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - ((const Add*)r1)->b), ((const Add*)r1)->a);
      }
    }
    if ((r1 = b.as<Add>())) {
      if ((r2 = ((const Add*)r1)->a.as<Select>())) {
        if (equal(((const Select*)r0)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - ((const Select*)r2)->true_value), (((const Select*)r0)->false_value - ((const Select*)r2)->false_value)) - ((const Add*)r1)->b);
        }
      }
      if ((r2 = ((const Add*)r1)->b.as<Select>())) {
        if (equal(((const Select*)r0)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - ((const Select*)r2)->true_value), (((const Select*)r0)->false_value - ((const Select*)r2)->false_value)) - ((const Add*)r1)->a);
        }
      }
    }
  }
  if ((r0 = b.as<Select>())) {
    if (equal(a, ((const Select*)r0)->true_value)) {
      return select(((const Select*)r0)->condition, 0, (a - ((const Select*)r0)->false_value));
    }
    if (equal(a, ((const Select*)r0)->false_value)) {
      return select(((const Select*)r0)->condition, (a - ((const Select*)r0)->true_value), 0);
    }
    if ((r1 = ((const Select*)r0)->true_value.as<Add>())) {
      if (equal(a, ((const Add*)r1)->a)) {
        return (0 - select(((const Select*)r0)->condition, ((const Add*)r1)->b, (((const Select*)r0)->false_value - a)));
      }
      if (equal(a, ((const Add*)r1)->b)) {
        return (0 - select(((const Select*)r0)->condition, ((const Add*)r1)->a, (((const Select*)r0)->false_value - a)));
      }
    }
    if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
      if (equal(a, ((const Add*)r1)->a)) {
        return (0 - select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - a), ((const Add*)r1)->b));
      }
      if (equal(a, ((const Add*)r1)->b)) {
        return (0 - select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - a), ((const Add*)r1)->a));
      }
    }
  }
  if ((r0 = b.as<Add>())) {
    if (equal(a, ((const Add*)r0)->a)) {
      return (0 - ((const Add*)r0)->b);
    }
    if (equal(a, ((const Add*)r0)->b)) {
      return (0 - ((const Add*)r0)->a);
    }
    if (is_const_v(((const Add*)r0)->b)) {
      return ((a - ((const Add*)r0)->a) - ((const Add*)r0)->b);
    }
    if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->a)) {
        return (((const Sub*)r1)->b - ((const Add*)r0)->a);
      }
    }
    if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->a)) {
        return (((const Sub*)r1)->b - ((const Add*)r0)->b);
      }
    }
    if ((r1 = ((const Add*)r0)->b.as<Add>())) {
      if (equal(a, ((const Add*)r1)->a)) {
        return (0 - (((const Add*)r0)->a + ((const Add*)r1)->b));
      }
      if (equal(a, ((const Add*)r1)->b)) {
        return (0 - (((const Add*)r0)->a + ((const Add*)r1)->a));
      }
    }
    if ((r1 = ((const Add*)r0)->a.as<Add>())) {
      if (equal(a, ((const Add*)r1)->a)) {
        return (0 - (((const Add*)r1)->b + ((const Add*)r0)->b));
      }
      if (equal(a, ((const Add*)r1)->b)) {
        return (0 - (((const Add*)r1)->a + ((const Add*)r0)->b));
      }
    }
  }
  if ((r0 = b.as<Sub>())) {
    return (a + (((const Sub*)r0)->b - ((const Sub*)r0)->a));
  }
  if ((r0 = b.as<Mul>())) {
    if (is_const_v(((const Mul*)r0)->b)) {
      if (evaluate_predicate(fold(((((const Mul*)r0)->b < 0) && (0 - (((const Mul*)r0)->b > 0)))))) {
        return (a + (((const Mul*)r0)->a * fold((0 - ((const Mul*)r0)->b))));
      }
    }
    if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
      if ((r2 = ((const Div*)r1)->a.as<Add>())) {
        if (equal(a, ((const Add*)r2)->a)) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
                if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                  return (((a + ((const Add*)r2)->b) % ((const Div*)r1)->b) - ((const Add*)r2)->b);
                }
              }
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<Mul>())) {
    if ((r1 = b.as<Mul>())) {
      if (equal(((const Mul*)r0)->b, ((const Mul*)r1)->b)) {
        return ((((const Mul*)r0)->a - ((const Mul*)r1)->a) * ((const Mul*)r0)->b);
      }
      if (equal(((const Mul*)r0)->b, ((const Mul*)r1)->a)) {
        return ((((const Mul*)r0)->a - ((const Mul*)r1)->b) * ((const Mul*)r0)->b);
      }
      if (equal(((const Mul*)r0)->a, ((const Mul*)r1)->b)) {
        return (((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r1)->a));
      }
      if (equal(((const Mul*)r0)->a, ((const Mul*)r1)->a)) {
        return (((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r1)->b));
      }
    }
    if ((r1 = b.as<Add>())) {
      if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->b)) {
          return (((((const Mul*)r0)->a - ((const Mul*)r2)->a) * ((const Mul*)r0)->b) - ((const Add*)r1)->a);
        }
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->a)) {
          return (((((const Mul*)r0)->a - ((const Mul*)r2)->b) * ((const Mul*)r0)->b) - ((const Add*)r1)->a);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->b)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r2)->a)) - ((const Add*)r1)->a);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->a)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r2)->b)) - ((const Add*)r1)->a);
        }
      }
      if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->b)) {
          return (((((const Mul*)r0)->a - ((const Mul*)r2)->a) * ((const Mul*)r0)->b) - ((const Add*)r1)->b);
        }
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->a)) {
          return (((((const Mul*)r0)->a - ((const Mul*)r2)->b) * ((const Mul*)r0)->b) - ((const Add*)r1)->b);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->b)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r2)->a)) - ((const Add*)r1)->b);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->a)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r2)->b)) - ((const Add*)r1)->b);
        }
      }
    }
    if ((r1 = b.as<Sub>())) {
      if ((r2 = ((const Sub*)r1)->b.as<Mul>())) {
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->b)) {
          return (((((const Mul*)r0)->a + ((const Mul*)r2)->a) * ((const Mul*)r0)->b) - ((const Sub*)r1)->a);
        }
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->a)) {
          return (((((const Mul*)r0)->a + ((const Mul*)r2)->b) * ((const Mul*)r0)->b) - ((const Sub*)r1)->a);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->b)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b + ((const Mul*)r2)->a)) - ((const Sub*)r1)->a);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->a)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b + ((const Mul*)r2)->b)) - ((const Sub*)r1)->a);
        }
      }
      if ((r2 = ((const Sub*)r1)->a.as<Mul>())) {
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->b)) {
          return (((((const Mul*)r0)->a - ((const Mul*)r2)->a) * ((const Mul*)r0)->b) + ((const Sub*)r1)->b);
        }
        if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->a)) {
          return (((((const Mul*)r0)->a - ((const Mul*)r2)->b) * ((const Mul*)r0)->b) + ((const Sub*)r1)->b);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->b)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r2)->a)) + ((const Sub*)r1)->b);
        }
        if (equal(((const Mul*)r0)->a, ((const Mul*)r2)->a)) {
          return ((((const Mul*)r0)->a * (((const Mul*)r0)->b - ((const Mul*)r2)->b)) + ((const Sub*)r1)->b);
        }
      }
    }
  }
  if ((r0 = b.as<Min>())) {
    if ((r1 = ((const Min*)r0)->a.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->a)) {
        if (is_const_int(((const Min*)r0)->b, 0)) {
          return max(a, ((const Sub*)r1)->b);
        }
      }
    }
  }
  if ((r0 = b.as<Max>())) {
    if ((r1 = ((const Max*)r0)->a.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->a)) {
        if (is_const_int(((const Max*)r0)->b, 0)) {
          return min(a, ((const Sub*)r1)->b);
        }
      }
    }
  }
  if (is_const_int(a, 0)) {
    if ((r0 = b.as<Add>())) {
      if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
        return (((const Sub*)r1)->b - (((const Add*)r0)->a + ((const Sub*)r1)->a));
      }
      if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
        return (((const Sub*)r1)->b - (((const Sub*)r1)->a + ((const Add*)r0)->b));
      }
    }
  }
  if ((r0 = b.as<Mod>())) {
    if (equal(a, ((const Mod*)r0)->a)) {
      if (is_const_v(((const Mod*)r0)->b)) {
        return ((a / ((const Mod*)r0)->b) * ((const Mod*)r0)->b);
      }
    }
  }
  if (type.is_no_overflow()) {
    if ((r0 = a.as<Max>())) {
      if (equal(((const Max*)r0)->a, b)) {
        return max((((const Max*)r0)->b - ((const Max*)r0)->a), 0);
      }
      if (equal(((const Max*)r0)->b, b)) {
        return max((((const Max*)r0)->a - ((const Max*)r0)->b), 0);
      }
      if ((r1 = ((const Max*)r0)->a.as<Sub>())) {
        if (is_const_int(((const Max*)r0)->b, 0)) {
          if (equal(((const Sub*)r1)->a, b)) {
            return (0 - min(((const Sub*)r1)->a, ((const Sub*)r1)->b));
          }
        }
      }
      if ((r1 = b.as<Add>())) {
        if (equal(((const Max*)r0)->a, ((const Add*)r1)->a)) {
          if (equal(((const Max*)r0)->b, ((const Add*)r1)->b)) {
            return (0 - min(((const Max*)r0)->a, ((const Max*)r0)->b));
          }
        }
        if (equal(((const Max*)r0)->b, ((const Add*)r1)->a)) {
          if (equal(((const Max*)r0)->a, ((const Add*)r1)->b)) {
            return (0 - min(((const Max*)r0)->b, ((const Max*)r0)->a));
          }
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Add>())) {
        if (equal(((const Add*)r1)->a, b)) {
          return max((((const Max*)r0)->b - ((const Add*)r1)->a), ((const Add*)r1)->b);
        }
        if (equal(((const Add*)r1)->b, b)) {
          return max((((const Max*)r0)->b - ((const Add*)r1)->b), ((const Add*)r1)->a);
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return max((((const Max*)r0)->b - ((const Add*)r2)->b), (((const Add*)r1)->a + ((const Add*)r2)->a));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return max((((const Max*)r0)->b - ((const Add*)r2)->a), (((const Add*)r1)->a + ((const Add*)r2)->b));
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return max((((const Max*)r0)->b - ((const Add*)r2)->b), (((const Add*)r2)->a + ((const Add*)r1)->b));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return max((((const Max*)r0)->b - ((const Add*)r2)->a), (((const Add*)r2)->b + ((const Add*)r1)->b));
          }
        }
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Max>())) {
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->a)) {
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b >= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return max((((const Max*)r0)->b - max(((const Add*)r1)->a, ((const Max*)r2)->b)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b <= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->b) - ((const Max*)r2)->b), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Max*)r2)->a.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r3)->b) >= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return max((((const Max*)r0)->b - max((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Max*)r2)->b)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r3)->b) <= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->b) - ((const Max*)r2)->b), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b >= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return max((((const Max*)r0)->b - max(((const Add*)r1)->a, ((const Max*)r2)->a)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b <= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->b) - ((const Max*)r2)->a), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Max*)r2)->b.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r3)->b) >= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return max((((const Max*)r0)->b - max((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Max*)r2)->a)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r3)->b) <= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->b) - ((const Max*)r2)->a), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Add>())) {
        if (equal(((const Add*)r1)->a, b)) {
          return max((((const Max*)r0)->a - ((const Add*)r1)->a), ((const Add*)r1)->b);
        }
        if (equal(((const Add*)r1)->b, b)) {
          return max((((const Max*)r0)->a - ((const Add*)r1)->b), ((const Add*)r1)->a);
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return max((((const Max*)r0)->a - ((const Add*)r2)->b), (((const Add*)r1)->a + ((const Add*)r2)->a));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return max((((const Max*)r0)->a - ((const Add*)r2)->a), (((const Add*)r1)->a + ((const Add*)r2)->b));
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return max((((const Max*)r0)->a - ((const Add*)r2)->b), (((const Add*)r2)->a + ((const Add*)r1)->b));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return max((((const Max*)r0)->a - ((const Add*)r2)->a), (((const Add*)r2)->b + ((const Add*)r1)->b));
          }
        }
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Max>())) {
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a >= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return max((((const Max*)r0)->a - max(((const Add*)r1)->a, ((const Max*)r2)->a)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a <= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->a) - ((const Max*)r2)->a), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Max*)r2)->b.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r3)->b) >= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return max((((const Max*)r0)->a - max((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Max*)r2)->a)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r3)->b) <= (((const Max*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->a) - ((const Max*)r2)->a), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->a)) {
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a >= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return max((((const Max*)r0)->a - max(((const Add*)r1)->a, ((const Max*)r2)->b)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a <= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->a) - ((const Max*)r2)->b), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Max*)r2)->a.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r3)->b) >= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return max((((const Max*)r0)->a - max((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Max*)r2)->b)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r3)->b) <= (((const Max*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return min((max((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Max*)r0)->a) - ((const Max*)r2)->b), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = b.as<Max>())) {
        if (equal(((const Max*)r0)->b, ((const Max*)r1)->a)) {
          if (equal(((const Max*)r0)->a, ((const Max*)r1)->b)) {
            return 0;
          }
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a >= ((const Max*)r1)->b), simplifier)))) {
            return max((((const Max*)r0)->a - max(((const Max*)r0)->b, ((const Max*)r1)->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a <= ((const Max*)r1)->b), simplifier)))) {
            return min((max(((const Max*)r0)->b, ((const Max*)r0)->a) - ((const Max*)r1)->b), 0);
          }
        }
        if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a - ((const Max*)r0)->b) == (((const Max*)r1)->a - ((const Max*)r1)->b)), simplifier)))) {
          return (((const Max*)r0)->b - ((const Max*)r1)->b);
        }
        if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a - ((const Max*)r0)->b) == (((const Max*)r1)->b - ((const Max*)r1)->a)), simplifier)))) {
          return (((const Max*)r0)->b - ((const Max*)r1)->a);
        }
        if (equal(((const Max*)r0)->a, ((const Max*)r1)->a)) {
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b >= ((const Max*)r1)->b), simplifier)))) {
            return max((((const Max*)r0)->b - max(((const Max*)r0)->a, ((const Max*)r1)->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b <= ((const Max*)r1)->b), simplifier)))) {
            return min((max(((const Max*)r0)->a, ((const Max*)r0)->b) - ((const Max*)r1)->b), 0);
          }
        }
        if ((r2 = ((const Max*)r1)->a.as<Add>())) {
          if (equal(((const Max*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r2)->b) >= ((const Max*)r1)->b), simplifier)))) {
                return max((((const Max*)r0)->b - max((((const Max*)r0)->a + ((const Add*)r2)->b), ((const Max*)r1)->b)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r2)->b) <= ((const Max*)r1)->b), simplifier)))) {
                return min((max(((const Max*)r0)->a, ((const Max*)r0)->b) - ((const Max*)r1)->b), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Max*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r2)->b) >= ((const Max*)r1)->b), simplifier)))) {
                return max((((const Max*)r0)->a - max((((const Max*)r0)->b + ((const Add*)r2)->b), ((const Max*)r1)->b)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r2)->b) <= ((const Max*)r1)->b), simplifier)))) {
                return min((max(((const Max*)r0)->b, ((const Max*)r0)->a) - ((const Max*)r1)->b), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
        }
        if (equal(((const Max*)r0)->b, ((const Max*)r1)->b)) {
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a >= ((const Max*)r1)->a), simplifier)))) {
            return max((((const Max*)r0)->a - max(((const Max*)r0)->b, ((const Max*)r1)->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->a <= ((const Max*)r1)->a), simplifier)))) {
            return min((max(((const Max*)r0)->b, ((const Max*)r0)->a) - ((const Max*)r1)->a), 0);
          }
        }
        if ((r2 = ((const Max*)r1)->b.as<Add>())) {
          if (equal(((const Max*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r2)->b) >= ((const Max*)r1)->a), simplifier)))) {
                return max((((const Max*)r0)->a - max((((const Max*)r0)->b + ((const Add*)r2)->b), ((const Max*)r1)->a)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->a + ((const Add*)r2)->b) <= ((const Max*)r1)->a), simplifier)))) {
                return min((max(((const Max*)r0)->b, ((const Max*)r0)->a) - ((const Max*)r1)->a), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Max*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r2)->b) >= ((const Max*)r1)->a), simplifier)))) {
                return max((((const Max*)r0)->b - max((((const Max*)r0)->a + ((const Add*)r2)->b), ((const Max*)r1)->a)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Max*)r0)->b + ((const Add*)r2)->b) <= ((const Max*)r1)->a), simplifier)))) {
                return min((max(((const Max*)r0)->a, ((const Max*)r0)->b) - ((const Max*)r1)->a), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
        }
        if (equal(((const Max*)r0)->a, ((const Max*)r1)->b)) {
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b >= ((const Max*)r1)->a), simplifier)))) {
            return max((((const Max*)r0)->b - max(((const Max*)r0)->a, ((const Max*)r1)->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Max*)r0)->b <= ((const Max*)r1)->a), simplifier)))) {
            return min((max(((const Max*)r0)->a, ((const Max*)r0)->b) - ((const Max*)r1)->a), 0);
          }
        }
      }
    }
    if ((r0 = a.as<Min>())) {
      if (equal(((const Min*)r0)->a, b)) {
        return min((((const Min*)r0)->b - ((const Min*)r0)->a), 0);
      }
      if (equal(((const Min*)r0)->b, b)) {
        return min((((const Min*)r0)->a - ((const Min*)r0)->b), 0);
      }
      if ((r1 = ((const Min*)r0)->a.as<Sub>())) {
        if (is_const_int(((const Min*)r0)->b, 0)) {
          if (equal(((const Sub*)r1)->a, b)) {
            return (0 - max(((const Sub*)r1)->a, ((const Sub*)r1)->b));
          }
        }
      }
      if ((r1 = b.as<Add>())) {
        if (equal(((const Min*)r0)->a, ((const Add*)r1)->a)) {
          if (equal(((const Min*)r0)->b, ((const Add*)r1)->b)) {
            return (0 - max(((const Min*)r0)->b, ((const Min*)r0)->a));
          }
        }
        if (equal(((const Min*)r0)->b, ((const Add*)r1)->a)) {
          if (equal(((const Min*)r0)->a, ((const Add*)r1)->b)) {
            return (0 - max(((const Min*)r0)->a, ((const Min*)r0)->b));
          }
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Add>())) {
        if (equal(((const Add*)r1)->a, b)) {
          return min((((const Min*)r0)->b - ((const Add*)r1)->a), ((const Add*)r1)->b);
        }
        if (equal(((const Add*)r1)->b, b)) {
          return min((((const Min*)r0)->b - ((const Add*)r1)->b), ((const Add*)r1)->a);
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return min((((const Min*)r0)->b - ((const Add*)r2)->b), (((const Add*)r1)->a + ((const Add*)r2)->a));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return min((((const Min*)r0)->b - ((const Add*)r2)->a), (((const Add*)r1)->a + ((const Add*)r2)->b));
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return min((((const Min*)r0)->b - ((const Add*)r2)->b), (((const Add*)r2)->a + ((const Add*)r1)->b));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return min((((const Min*)r0)->b - ((const Add*)r2)->a), (((const Add*)r2)->b + ((const Add*)r1)->b));
          }
        }
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Min>())) {
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->a)) {
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b <= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return min((((const Min*)r0)->b - min(((const Add*)r1)->a, ((const Min*)r2)->b)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b >= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->b) - ((const Min*)r2)->b), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Min*)r2)->a.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r3)->b) <= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return min((((const Min*)r0)->b - min((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Min*)r2)->b)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r3)->b) >= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->b) - ((const Min*)r2)->b), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b <= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return min((((const Min*)r0)->b - min(((const Add*)r1)->a, ((const Min*)r2)->a)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b >= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->b) - ((const Min*)r2)->a), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Min*)r2)->b.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r3)->b) <= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return min((((const Min*)r0)->b - min((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Min*)r2)->a)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r3)->b) >= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->b) - ((const Min*)r2)->a), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Add>())) {
        if (equal(((const Add*)r1)->a, b)) {
          return min((((const Min*)r0)->a - ((const Add*)r1)->a), ((const Add*)r1)->b);
        }
        if (equal(((const Add*)r1)->b, b)) {
          return min((((const Min*)r0)->a - ((const Add*)r1)->b), ((const Add*)r1)->a);
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return min((((const Min*)r0)->a - ((const Add*)r2)->b), (((const Add*)r1)->a + ((const Add*)r2)->a));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return min((((const Min*)r0)->a - ((const Add*)r2)->a), (((const Add*)r1)->a + ((const Add*)r2)->b));
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->b, b)) {
            return min((((const Min*)r0)->a - ((const Add*)r2)->b), (((const Add*)r2)->a + ((const Add*)r1)->b));
          }
          if (equal(((const Add*)r2)->a, b)) {
            return min((((const Min*)r0)->a - ((const Add*)r2)->a), (((const Add*)r2)->b + ((const Add*)r1)->b));
          }
        }
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Min>())) {
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a <= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return min((((const Min*)r0)->a - min(((const Add*)r1)->a, ((const Min*)r2)->a)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a >= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->a) - ((const Min*)r2)->a), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Min*)r2)->b.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r3)->b) <= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return min((((const Min*)r0)->a - min((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Min*)r2)->a)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r3)->b) >= (((const Min*)r2)->a + ((const Add*)r1)->b)), simplifier)))) {
                    return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->a) - ((const Min*)r2)->a), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->a)) {
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a <= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return min((((const Min*)r0)->a - min(((const Add*)r1)->a, ((const Min*)r2)->b)), ((const Add*)r1)->b);
              }
              if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a >= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->a) - ((const Min*)r2)->b), ((const Add*)r1)->b);
              }
            }
            if ((r3 = ((const Min*)r2)->a.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r3)->b) <= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return min((((const Min*)r0)->a - min((((const Add*)r1)->a + ((const Add*)r3)->b), ((const Min*)r2)->b)), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                  if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r3)->b) >= (((const Min*)r2)->b + ((const Add*)r1)->b)), simplifier)))) {
                    return max((min((((const Add*)r1)->a + ((const Add*)r1)->b), ((const Min*)r0)->a) - ((const Min*)r2)->b), fold((((const Add*)r1)->b - ((const Add*)r3)->b)));
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = b.as<Min>())) {
        if (equal(((const Min*)r0)->b, ((const Min*)r1)->a)) {
          if (equal(((const Min*)r0)->a, ((const Min*)r1)->b)) {
            return 0;
          }
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a <= ((const Min*)r1)->b), simplifier)))) {
            return min((((const Min*)r0)->a - min(((const Min*)r0)->b, ((const Min*)r1)->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a >= ((const Min*)r1)->b), simplifier)))) {
            return max((min(((const Min*)r0)->b, ((const Min*)r0)->a) - ((const Min*)r1)->b), 0);
          }
        }
        if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a - ((const Min*)r0)->b) == (((const Min*)r1)->a - ((const Min*)r1)->b)), simplifier)))) {
          return (((const Min*)r0)->b - ((const Min*)r1)->b);
        }
        if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a - ((const Min*)r0)->b) == (((const Min*)r1)->b - ((const Min*)r1)->a)), simplifier)))) {
          return (((const Min*)r0)->b - ((const Min*)r1)->a);
        }
        if (equal(((const Min*)r0)->a, ((const Min*)r1)->a)) {
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b <= ((const Min*)r1)->b), simplifier)))) {
            return min((((const Min*)r0)->b - min(((const Min*)r0)->a, ((const Min*)r1)->b)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b >= ((const Min*)r1)->b), simplifier)))) {
            return max((min(((const Min*)r0)->a, ((const Min*)r0)->b) - ((const Min*)r1)->b), 0);
          }
        }
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if (equal(((const Min*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r2)->b) <= ((const Min*)r1)->b), simplifier)))) {
                return min((((const Min*)r0)->b - min((((const Min*)r0)->a + ((const Add*)r2)->b), ((const Min*)r1)->b)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r2)->b) >= ((const Min*)r1)->b), simplifier)))) {
                return max((min(((const Min*)r0)->a, ((const Min*)r0)->b) - ((const Min*)r1)->b), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Min*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r2)->b) <= ((const Min*)r1)->b), simplifier)))) {
                return min((((const Min*)r0)->a - min((((const Min*)r0)->b + ((const Add*)r2)->b), ((const Min*)r1)->b)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r2)->b) >= ((const Min*)r1)->b), simplifier)))) {
                return max((min(((const Min*)r0)->b, ((const Min*)r0)->a) - ((const Min*)r1)->b), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
        }
        if (equal(((const Min*)r0)->b, ((const Min*)r1)->b)) {
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a <= ((const Min*)r1)->a), simplifier)))) {
            return min((((const Min*)r0)->a - min(((const Min*)r0)->b, ((const Min*)r1)->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->a >= ((const Min*)r1)->a), simplifier)))) {
            return max((min(((const Min*)r0)->b, ((const Min*)r0)->a) - ((const Min*)r1)->a), 0);
          }
        }
        if ((r2 = ((const Min*)r1)->b.as<Add>())) {
          if (equal(((const Min*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r2)->b) <= ((const Min*)r1)->a), simplifier)))) {
                return min((((const Min*)r0)->a - min((((const Min*)r0)->b + ((const Add*)r2)->b), ((const Min*)r1)->a)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->a + ((const Add*)r2)->b) >= ((const Min*)r1)->a), simplifier)))) {
                return max((min(((const Min*)r0)->b, ((const Min*)r0)->a) - ((const Min*)r1)->a), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Min*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r2)->b) <= ((const Min*)r1)->a), simplifier)))) {
                return min((((const Min*)r0)->b - min((((const Min*)r0)->a + ((const Add*)r2)->b), ((const Min*)r1)->a)), fold((0 - ((const Add*)r2)->b)));
              }
              if (evaluate_predicate(fold(can_prove(((((const Min*)r0)->b + ((const Add*)r2)->b) >= ((const Min*)r1)->a), simplifier)))) {
                return max((min(((const Min*)r0)->a, ((const Min*)r0)->b) - ((const Min*)r1)->a), fold((0 - ((const Add*)r2)->b)));
              }
            }
          }
        }
        if (equal(((const Min*)r0)->a, ((const Min*)r1)->b)) {
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b <= ((const Min*)r1)->a), simplifier)))) {
            return min((((const Min*)r0)->b - min(((const Min*)r0)->a, ((const Min*)r1)->a)), 0);
          }
          if (evaluate_predicate(fold(can_prove((((const Min*)r0)->b >= ((const Min*)r1)->a), simplifier)))) {
            return max((min(((const Min*)r0)->a, ((const Min*)r0)->b) - ((const Min*)r1)->a), 0);
          }
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if (is_const_v(((const Min*)r0)->b)) {
            if ((r2 = b.as<Mul>())) {
              if ((r3 = ((const Mul*)r2)->a.as<Min>())) {
                if (equal(((const Mul*)r1)->a, ((const Min*)r3)->a)) {
                  if (is_const_v(((const Min*)r3)->b)) {
                    if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->b)) {
                      if (evaluate_predicate(fold(((((const Mul*)r1)->b > 0) && (((const Min*)r0)->b <= (((const Min*)r3)->b * ((const Mul*)r1)->b)))))) {
                        return min((((const Min*)r0)->b - (min(((const Mul*)r1)->a, ((const Min*)r3)->b) * ((const Mul*)r1)->b)), 0);
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
    if ((r0 = b.as<Max>())) {
      if (equal(a, ((const Max*)r0)->a)) {
        if (evaluate_predicate(fold(!(is_const(a))))) {
          return min((a - ((const Max*)r0)->b), 0);
        }
      }
      if (equal(a, ((const Max*)r0)->b)) {
        if (evaluate_predicate(fold(!(is_const(a))))) {
          return min((a - ((const Max*)r0)->a), 0);
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return min((a - ((const Max*)r0)->a), ((const Sub*)r1)->b);
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return min(((const Sub*)r1)->b, (a - ((const Max*)r0)->b));
        }
        if (is_const_v(((const Max*)r0)->b)) {
          return (a + min((((const Sub*)r1)->b - ((const Sub*)r1)->a), fold((0 - ((const Max*)r0)->b))));
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Min>())) {
        if ((r2 = ((const Min*)r1)->a.as<Sub>())) {
          if (is_const_v(((const Min*)r1)->b)) {
            if (is_const_v(((const Max*)r0)->b)) {
              return (a + min(max((((const Sub*)r2)->b - ((const Sub*)r2)->a), fold((0 - ((const Min*)r1)->b))), fold((0 - ((const Max*)r0)->b))));
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - max((((const Max*)r0)->a - a), ((const Add*)r1)->b));
          }
        }
        if (equal(a, ((const Add*)r1)->b)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - max((((const Max*)r0)->a - a), ((const Add*)r1)->a));
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->a - a), (((const Add*)r1)->a + ((const Add*)r2)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->a - a), (((const Add*)r2)->a + ((const Add*)r1)->a)));
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->a - a), (((const Add*)r2)->b + ((const Add*)r1)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->a - a), (((const Add*)r2)->a + ((const Add*)r1)->b)));
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - max((((const Max*)r0)->b - a), ((const Add*)r1)->b));
          }
        }
        if (equal(a, ((const Add*)r1)->b)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - max((((const Max*)r0)->b - a), ((const Add*)r1)->a));
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->b - a), (((const Add*)r1)->a + ((const Add*)r2)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->b - a), (((const Add*)r2)->a + ((const Add*)r1)->a)));
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->b - a), (((const Add*)r1)->b + ((const Add*)r2)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - max((((const Max*)r0)->b - a), (((const Add*)r1)->b + ((const Add*)r2)->a)));
            }
          }
        }
      }
    }
    if ((r0 = b.as<Min>())) {
      if (equal(a, ((const Min*)r0)->a)) {
        if (evaluate_predicate(fold(!(is_const(a))))) {
          return max((a - ((const Min*)r0)->b), 0);
        }
      }
      if (equal(a, ((const Min*)r0)->b)) {
        if (evaluate_predicate(fold(!(is_const(a))))) {
          return max((a - ((const Min*)r0)->a), 0);
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return max((a - ((const Min*)r0)->a), ((const Sub*)r1)->b);
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return max(((const Sub*)r1)->b, (a - ((const Min*)r0)->b));
        }
        if (is_const_v(((const Min*)r0)->b)) {
          return (a + max((((const Sub*)r1)->b - ((const Sub*)r1)->a), fold((0 - ((const Min*)r0)->b))));
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Max>())) {
        if ((r2 = ((const Max*)r1)->a.as<Sub>())) {
          if (is_const_v(((const Max*)r1)->b)) {
            if (is_const_v(((const Min*)r0)->b)) {
              return (a + max(min((((const Sub*)r2)->b - ((const Sub*)r2)->a), fold((0 - ((const Max*)r1)->b))), fold((0 - ((const Min*)r0)->b))));
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - min((((const Min*)r0)->a - a), ((const Add*)r1)->b));
          }
        }
        if (equal(a, ((const Add*)r1)->b)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - min((((const Min*)r0)->a - a), ((const Add*)r1)->a));
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->a - a), (((const Add*)r1)->a + ((const Add*)r2)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->a - a), (((const Add*)r2)->a + ((const Add*)r1)->a)));
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->a - a), (((const Add*)r2)->b + ((const Add*)r1)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->a - a), (((const Add*)r2)->a + ((const Add*)r1)->b)));
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - min((((const Min*)r0)->b - a), ((const Add*)r1)->b));
          }
        }
        if (equal(a, ((const Add*)r1)->b)) {
          if (evaluate_predicate(fold(!(is_const(a))))) {
            return (0 - min((((const Min*)r0)->b - a), ((const Add*)r1)->a));
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->b - a), (((const Add*)r1)->a + ((const Add*)r2)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->b - a), (((const Add*)r2)->a + ((const Add*)r1)->a)));
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->b - a), (((const Add*)r1)->b + ((const Add*)r2)->b)));
            }
          }
          if (equal(a, ((const Add*)r2)->b)) {
            if (evaluate_predicate(fold(!(is_const(a))))) {
              return (0 - min((((const Min*)r0)->b - a), (((const Add*)r1)->b + ((const Add*)r2)->a)));
            }
          }
        }
      }
    }
    if ((r0 = a.as<Mul>())) {
      if (equal(((const Mul*)r0)->a, b)) {
        return (((const Mul*)r0)->a * (((const Mul*)r0)->b - 1));
      }
      if (equal(((const Mul*)r0)->b, b)) {
        return ((((const Mul*)r0)->a - 1) * ((const Mul*)r0)->b);
      }
    }
    if ((r0 = b.as<Mul>())) {
      if (equal(a, ((const Mul*)r0)->a)) {
        return (a * (1 - ((const Mul*)r0)->b));
      }
      if (equal(a, ((const Mul*)r0)->b)) {
        return ((1 - ((const Mul*)r0)->a) * a);
      }
    }
  }
  if (type.is_no_overflow_int()) {
    if (is_const_v(a)) {
      if ((r0 = b.as<Div>())) {
        if ((r1 = ((const Div*)r0)->a.as<Sub>())) {
          if (is_const_v(((const Sub*)r1)->a)) {
            if (is_const_v(((const Div*)r0)->b)) {
              if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                return ((fold(((((a * ((const Div*)r0)->b) - ((const Sub*)r1)->a) + ((const Div*)r0)->b) - 1)) + ((const Sub*)r1)->b) / ((const Div*)r0)->b);
              }
            }
          }
        }
        if ((r1 = ((const Div*)r0)->a.as<Add>())) {
          if (is_const_v(((const Add*)r1)->b)) {
            if (is_const_v(((const Div*)r0)->b)) {
              if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                return ((fold(((((a * ((const Div*)r0)->b) - ((const Add*)r1)->b) + ((const Div*)r0)->b) - 1)) - ((const Add*)r1)->a) / ((const Div*)r0)->b);
              }
            }
          }
        }
      }
    }
    if ((r0 = b.as<Div>())) {
      if ((r1 = ((const Div*)r0)->a.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
              return ((((a * fold((((const Div*)r0)->b - 1))) - ((const Add*)r1)->b) + fold((((const Div*)r0)->b - 1))) / ((const Div*)r0)->b);
            }
          }
        }
        if (equal(a, ((const Add*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
              return ((((a * fold((((const Div*)r0)->b - 1))) - ((const Add*)r1)->a) + fold((((const Div*)r0)->b - 1))) / ((const Div*)r0)->b);
            }
          }
        }
      }
      if ((r1 = ((const Div*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
              return ((((a * fold((((const Div*)r0)->b - 1))) + ((const Sub*)r1)->b) + fold((((const Div*)r0)->b - 1))) / ((const Div*)r0)->b);
            }
          }
        }
        if (equal(a, ((const Sub*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
              return ((((a * fold((((const Div*)r0)->b + 1))) - ((const Sub*)r1)->a) + fold((((const Div*)r0)->b - 1))) / ((const Div*)r0)->b);
            }
          }
        }
      }
    }
    if ((r0 = a.as<Div>())) {
      if ((r1 = ((const Div*)r0)->a.as<Add>())) {
        if (is_const_v(((const Div*)r0)->b)) {
          if (equal(((const Add*)r1)->a, b)) {
            return (((((const Add*)r1)->a * fold((1 - ((const Div*)r0)->b))) + ((const Add*)r1)->b) / ((const Div*)r0)->b);
          }
          if (equal(((const Add*)r1)->b, b)) {
            return ((((const Add*)r1)->a + (((const Add*)r1)->b * fold((1 - ((const Div*)r0)->b)))) / ((const Div*)r0)->b);
          }
          if ((r2 = b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Add*)r1)->b, ((const Add*)r3)->a)) {
                if (equal(((const Add*)r1)->a, ((const Add*)r3)->b)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
                      return 0;
                    }
                  }
                }
              }
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                      return ((((((const Add*)r1)->a + fold((((const Add*)r3)->b % ((const Div*)r0)->b))) % ((const Div*)r0)->b) + (((const Add*)r1)->b - ((const Add*)r3)->b)) / ((const Div*)r0)->b);
                    }
                  }
                }
              }
            }
            if (equal(((const Add*)r1)->a, ((const Div*)r2)->a)) {
              if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                  return (((((const Add*)r1)->a % ((const Div*)r0)->b) + ((const Add*)r1)->b) / ((const Div*)r0)->b);
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (is_const_v(((const Div*)r0)->b)) {
            if ((r3 = b.as<Div>())) {
              if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                if ((r5 = ((const Add*)r4)->a.as<Add>())) {
                  if (equal(((const Add*)r2)->b, ((const Add*)r5)->a)) {
                    if (equal(((const Add*)r2)->a, ((const Add*)r5)->b)) {
                      if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                          return ((((((const Add*)r2)->a + ((const Add*)r2)->b) + ((const Add*)r1)->b) / ((const Div*)r0)->b) - (((((const Add*)r2)->a + ((const Add*)r2)->b) + ((const Add*)r4)->b) / ((const Div*)r0)->b));
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if ((r2 = b.as<Div>())) {
              if ((r3 = ((const Div*)r2)->a.as<Add>())) {
                if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                      return (((fold(((((const Div*)r0)->b + ((const Add*)r1)->b) - 1)) - ((const Add*)r3)->b) - ((((const Add*)r1)->a + fold((((const Add*)r1)->b % ((const Div*)r0)->b))) % ((const Div*)r0)->b)) / ((const Div*)r0)->b);
                    }
                  }
                }
              }
              if ((r3 = ((const Div*)r2)->a.as<Sub>())) {
                if (equal(((const Add*)r1)->a, ((const Sub*)r3)->a)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                      return (((((const Sub*)r3)->b + fold(((((const Div*)r0)->b + ((const Add*)r1)->b) - 1))) - ((((const Add*)r1)->a + fold((((const Add*)r1)->b % ((const Div*)r0)->b))) % ((const Div*)r0)->b)) / ((const Div*)r0)->b);
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Min>())) {
          if ((r3 = ((const Min*)r2)->a.as<Add>())) {
            if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
              if (is_const_v(((const Mul*)r4)->b)) {
                if (is_const_v(((const Div*)r0)->b)) {
                  if ((r5 = b.as<Mul>())) {
                    if (equal(((const Mul*)r4)->a, ((const Mul*)r5)->a)) {
                      if (is_const_v(((const Mul*)r5)->b)) {
                        if (evaluate_predicate(fold((((const Mul*)r4)->b == (((const Div*)r0)->b * ((const Mul*)r5)->b))))) {
                          return ((min(((const Add*)r3)->b, (((const Min*)r2)->b - (((const Mul*)r4)->a * ((const Mul*)r4)->b))) + ((const Add*)r1)->b) / ((const Div*)r0)->b);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if ((r3 = ((const Min*)r2)->b.as<Add>())) {
            if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
              if (is_const_v(((const Mul*)r4)->b)) {
                if (is_const_v(((const Div*)r0)->b)) {
                  if ((r5 = b.as<Mul>())) {
                    if (equal(((const Mul*)r4)->a, ((const Mul*)r5)->a)) {
                      if (is_const_v(((const Mul*)r5)->b)) {
                        if (evaluate_predicate(fold((((const Mul*)r4)->b == (((const Div*)r0)->b * ((const Mul*)r5)->b))))) {
                          return ((min((((const Min*)r2)->a - (((const Mul*)r4)->a * ((const Mul*)r4)->b)), ((const Add*)r3)->b) + ((const Add*)r1)->b) / ((const Div*)r0)->b);
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
      if ((r1 = ((const Div*)r0)->a.as<Sub>())) {
        if (is_const_v(((const Div*)r0)->b)) {
          if (equal(((const Sub*)r1)->a, b)) {
            return (((((const Sub*)r1)->a * fold((1 - ((const Div*)r0)->b))) - ((const Sub*)r1)->b) / ((const Div*)r0)->b);
          }
          if (equal(((const Sub*)r1)->b, b)) {
            return ((((const Sub*)r1)->a - (((const Sub*)r1)->b * fold((1 + ((const Div*)r0)->b)))) / ((const Div*)r0)->b);
          }
          if ((r2 = b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Sub*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                      return (((((((const Sub*)r1)->a + fold((((const Add*)r3)->b % ((const Div*)r0)->b))) % ((const Div*)r0)->b) - ((const Sub*)r1)->b) - ((const Add*)r3)->b) / ((const Div*)r0)->b);
                    }
                  }
                }
              }
            }
            if (equal(((const Sub*)r1)->a, ((const Div*)r2)->a)) {
              if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                  return (((((const Sub*)r1)->a % ((const Div*)r0)->b) - ((const Sub*)r1)->b) / ((const Div*)r0)->b);
                }
              }
            }
          }
        }
      }
      if (is_const_v(((const Div*)r0)->b)) {
        if ((r1 = b.as<Div>())) {
          if ((r2 = ((const Div*)r1)->a.as<Add>())) {
            if (equal(((const Div*)r0)->a, ((const Add*)r2)->a)) {
              if (equal(((const Div*)r0)->b, ((const Div*)r1)->b)) {
                if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                  return (((fold((((const Div*)r0)->b - 1)) - ((const Add*)r2)->b) - (((const Div*)r0)->a % ((const Div*)r0)->b)) / ((const Div*)r0)->b);
                }
              }
            }
          }
          if ((r2 = ((const Div*)r1)->a.as<Sub>())) {
            if (equal(((const Div*)r0)->a, ((const Sub*)r2)->a)) {
              if (equal(((const Div*)r0)->b, ((const Div*)r1)->b)) {
                if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
                  return (((((const Sub*)r2)->b + fold((((const Div*)r0)->b - 1))) - (((const Div*)r0)->a % ((const Div*)r0)->b)) / ((const Div*)r0)->b);
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Div*)r0)->a.as<Min>())) {
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if ((r3 = ((const Add*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Div*)r0)->b)) {
                if ((r4 = b.as<Mul>())) {
                  if (equal(((const Mul*)r3)->a, ((const Mul*)r4)->a)) {
                    if (is_const_v(((const Mul*)r4)->b)) {
                      if (evaluate_predicate(fold((((const Mul*)r3)->b == (((const Div*)r0)->b * ((const Mul*)r4)->b))))) {
                        return (min(((const Add*)r2)->b, (((const Min*)r1)->b - (((const Mul*)r3)->a * ((const Mul*)r3)->b))) / ((const Div*)r0)->b);
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Min*)r1)->b.as<Add>())) {
          if ((r3 = ((const Add*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Div*)r0)->b)) {
                if ((r4 = b.as<Mul>())) {
                  if (equal(((const Mul*)r3)->a, ((const Mul*)r4)->a)) {
                    if (is_const_v(((const Mul*)r4)->b)) {
                      if (evaluate_predicate(fold((((const Mul*)r3)->b == (((const Div*)r0)->b * ((const Mul*)r4)->b))))) {
                        return (min(((const Add*)r2)->b, (((const Min*)r1)->a - (((const Mul*)r3)->a * ((const Mul*)r3)->b))) / ((const Div*)r0)->b);
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
    if ((r0 = a.as<Mul>())) {
      if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
        if (is_const_v(((const Div*)r1)->b)) {
          if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
            if (equal(((const Div*)r1)->a, b)) {
              if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                return (0 - (((const Div*)r1)->a % ((const Div*)r1)->b));
              }
            }
          }
        }
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
                if (equal(((const Add*)r2)->a, b)) {
                  if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && ((((const Add*)r2)->b + 1) == ((const Div*)r1)->b))))) {
                    return ((0 - ((const Add*)r2)->a) % ((const Div*)r1)->b);
                  }
                }
              }
            }
          }
        }
      }
      if (is_const_v(((const Mul*)r0)->b)) {
        if ((r1 = b.as<Mul>())) {
          if (is_const_v(((const Mul*)r1)->b)) {
            if (evaluate_predicate(fold(((((const Mul*)r0)->b % ((const Mul*)r1)->b) == 0)))) {
              return (((((const Mul*)r0)->a * fold((((const Mul*)r0)->b / ((const Mul*)r1)->b))) - ((const Mul*)r1)->a) * ((const Mul*)r1)->b);
            }
            if (evaluate_predicate(fold(((((const Mul*)r1)->b % ((const Mul*)r0)->b) == 0)))) {
              return ((((const Mul*)r0)->a - (((const Mul*)r1)->a * fold((((const Mul*)r1)->b / ((const Mul*)r0)->b)))) * ((const Mul*)r0)->b);
            }
          }
        }
      }
    }
    if ((r0 = b.as<Mul>())) {
      if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
        if (equal(a, ((const Div*)r1)->a)) {
          if (is_const_v(((const Div*)r1)->b)) {
            if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
              if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                return (a % ((const Div*)r1)->b);
              }
            }
          }
        }
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Div*)r1)->b)) {
                if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
                  if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && ((((const Add*)r2)->b + 1) == ((const Div*)r1)->b))))) {
                    return (((a + ((const Add*)r2)->b) % ((const Div*)r1)->b) + fold((0 - ((const Add*)r2)->b)));
                  }
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Add>())) {
      if ((r1 = ((const Add*)r0)->a.as<Min>())) {
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->a, b)) {
            return (min((((const Min*)r1)->b - ((const Add*)r2)->a), ((const Add*)r2)->b) + ((const Add*)r0)->b);
          }
        }
      }
    }
    if ((r0 = a.as<Min>())) {
      if ((r1 = ((const Min*)r0)->a.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->a, b)) {
            return min((((const Min*)r0)->b - ((const Add*)r2)->a), (((const Add*)r2)->b + ((const Add*)r1)->b));
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if ((r3 = ((const Mul*)r2)->a.as<Add>())) {
            if ((r4 = b.as<Mul>())) {
              if (equal(((const Add*)r3)->a, ((const Mul*)r4)->a)) {
                if (equal(((const Mul*)r2)->b, ((const Mul*)r4)->b)) {
                  return min((((const Min*)r0)->b - (((const Add*)r3)->a * ((const Mul*)r2)->b)), ((((const Add*)r3)->b * ((const Mul*)r2)->b) + ((const Add*)r1)->b));
                }
              }
              if (equal(((const Add*)r3)->b, ((const Mul*)r4)->a)) {
                if (equal(((const Mul*)r2)->b, ((const Mul*)r4)->b)) {
                  return min((((const Min*)r0)->b - (((const Add*)r3)->b * ((const Mul*)r2)->b)), ((((const Add*)r3)->a * ((const Mul*)r2)->b) + ((const Add*)r1)->b));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Min>())) {
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->a, b)) {
            return min((min(((const Min*)r1)->b, ((const Min*)r0)->b) - ((const Add*)r2)->a), ((const Add*)r2)->b);
          }
        }
        if ((r2 = ((const Min*)r1)->b.as<Add>())) {
          if (equal(((const Add*)r2)->a, b)) {
            return min((min(((const Min*)r1)->a, ((const Min*)r0)->b) - ((const Add*)r2)->a), ((const Add*)r2)->b);
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
