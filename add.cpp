#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr Simplify_Add(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  const BaseExprNode *r0 = nullptr;
  const BaseExprNode *r1 = nullptr;
  const BaseExprNode *r2 = nullptr;
  const BaseExprNode *r3 = nullptr;
  const BaseExprNode *r4 = nullptr;
  if (is_const_int(b, 0)) {
    return a;
  }
  if (is_const_int(a, 0)) {
    return b;
  }
  if (is_const_v(a)) {
    if (is_const_v(b)) {
      return fold((a + b));
    }
  }
  if (equal(a, b)) {
    return (a * 2);
  }
  if ((r0 = a.as<Ramp>())) {
    if (is_const_v(((const Ramp*)r0)->lanes)) {
      if ((r1 = b.as<Ramp>())) {
        if (equal(((const Ramp*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
          return ramp((((const Ramp*)r0)->base + ((const Ramp*)r1)->base), (((const Ramp*)r0)->stride + ((const Ramp*)r1)->stride), ((const Ramp*)r0)->lanes);
        }
      }
      if ((r1 = b.as<Broadcast>())) {
        if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
          return ramp((((const Ramp*)r0)->base + ((const Broadcast*)r1)->value), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
        }
      }
    }
    if ((r1 = ((const Ramp*)r0)->base.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if (is_const_v(((const Ramp*)r0)->lanes)) {
          if ((r2 = b.as<Broadcast>())) {
            if (is_const_v(((const Broadcast*)r2)->lanes)) {
              if (evaluate_predicate(fold((((const Broadcast*)r2)->lanes == (((const Broadcast*)r1)->lanes * ((const Ramp*)r0)->lanes))))) {
                return ramp(broadcast((((const Broadcast*)r1)->value + ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
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
                return ramp(ramp((((const Ramp*)r1)->base + ((const Broadcast*)r2)->value), ((const Ramp*)r1)->stride, ((const Ramp*)r1)->lanes), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
              }
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<Broadcast>())) {
    if (is_const_v(((const Broadcast*)r0)->lanes)) {
      if ((r1 = b.as<Broadcast>())) {
        if (is_const_v(((const Broadcast*)r1)->lanes)) {
          if (evaluate_predicate(fold(((((const Broadcast*)r1)->lanes % ((const Broadcast*)r0)->lanes) == 0)))) {
            return broadcast((((const Broadcast*)r0)->value + broadcast(((const Broadcast*)r1)->value, fold((((const Broadcast*)r1)->lanes / ((const Broadcast*)r0)->lanes)))), ((const Broadcast*)r0)->lanes);
          }
          if (evaluate_predicate(fold(((((const Broadcast*)r0)->lanes % ((const Broadcast*)r1)->lanes) == 0)))) {
            return broadcast((((const Broadcast*)r1)->value + broadcast(((const Broadcast*)r0)->value, fold((((const Broadcast*)r0)->lanes / ((const Broadcast*)r1)->lanes)))), ((const Broadcast*)r1)->lanes);
          }
        }
      }
    }
  }
  if ((r0 = a.as<Add>())) {
    if ((r1 = ((const Add*)r0)->b.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (is_const_v(((const Broadcast*)r2)->lanes)) {
            if (evaluate_predicate(fold(((((const Broadcast*)r2)->lanes % ((const Broadcast*)r1)->lanes) == 0)))) {
              return (((const Add*)r0)->a + broadcast((((const Broadcast*)r1)->value + broadcast(((const Broadcast*)r2)->value, fold((((const Broadcast*)r2)->lanes / ((const Broadcast*)r1)->lanes)))), ((const Broadcast*)r1)->lanes));
            }
            if (evaluate_predicate(fold(((((const Broadcast*)r1)->lanes % ((const Broadcast*)r2)->lanes) == 0)))) {
              return (((const Add*)r0)->a + broadcast((((const Broadcast*)r2)->value + broadcast(((const Broadcast*)r1)->value, fold((((const Broadcast*)r1)->lanes / ((const Broadcast*)r2)->lanes)))), ((const Broadcast*)r2)->lanes));
            }
          }
        }
      }
    }
    if ((r1 = ((const Add*)r0)->a.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (is_const_v(((const Broadcast*)r2)->lanes)) {
            if (evaluate_predicate(fold(((((const Broadcast*)r2)->lanes % ((const Broadcast*)r1)->lanes) == 0)))) {
              return (((const Add*)r0)->b + broadcast((((const Broadcast*)r1)->value + broadcast(((const Broadcast*)r2)->value, fold((((const Broadcast*)r2)->lanes / ((const Broadcast*)r1)->lanes)))), ((const Broadcast*)r1)->lanes));
            }
            if (evaluate_predicate(fold(((((const Broadcast*)r1)->lanes % ((const Broadcast*)r2)->lanes) == 0)))) {
              return (((const Add*)r0)->b + broadcast((((const Broadcast*)r2)->value + broadcast(((const Broadcast*)r1)->value, fold((((const Broadcast*)r1)->lanes / ((const Broadcast*)r2)->lanes)))), ((const Broadcast*)r2)->lanes));
            }
          }
        }
      }
    }
    if (is_const_v(((const Add*)r0)->b)) {
      if (is_const_v(b)) {
        return (((const Add*)r0)->a + fold((((const Add*)r0)->b + b)));
      }
      return ((((const Add*)r0)->a + b) + ((const Add*)r0)->b);
    }
    if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
      if (equal(((const Sub*)r1)->b, b)) {
        return (((const Sub*)r1)->a + ((const Add*)r0)->b);
      }
    }
    if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
      if (equal(((const Sub*)r1)->b, b)) {
        return (((const Add*)r0)->a + ((const Sub*)r1)->a);
      }
    }
  }
  if ((r0 = a.as<Sub>())) {
    if ((r1 = ((const Sub*)r0)->b.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (is_const_v(((const Broadcast*)r2)->lanes)) {
            if (evaluate_predicate(fold(((((const Broadcast*)r2)->lanes % ((const Broadcast*)r1)->lanes) == 0)))) {
              return (((const Sub*)r0)->a + broadcast((broadcast(((const Broadcast*)r2)->value, fold((((const Broadcast*)r2)->lanes / ((const Broadcast*)r1)->lanes))) - ((const Broadcast*)r1)->value), ((const Broadcast*)r1)->lanes));
            }
            if (evaluate_predicate(fold(((((const Broadcast*)r1)->lanes % ((const Broadcast*)r2)->lanes) == 0)))) {
              return (((const Sub*)r0)->a + broadcast((((const Broadcast*)r2)->value - broadcast(((const Broadcast*)r1)->value, fold((((const Broadcast*)r1)->lanes / ((const Broadcast*)r2)->lanes)))), ((const Broadcast*)r2)->lanes));
            }
          }
        }
      }
    }
    if ((r1 = ((const Sub*)r0)->a.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (is_const_v(((const Broadcast*)r2)->lanes)) {
            if (evaluate_predicate(fold(((((const Broadcast*)r2)->lanes % ((const Broadcast*)r1)->lanes) == 0)))) {
              return (broadcast((((const Broadcast*)r1)->value + broadcast(((const Broadcast*)r2)->value, fold((((const Broadcast*)r2)->lanes / ((const Broadcast*)r1)->lanes)))), ((const Broadcast*)r1)->lanes) - ((const Sub*)r0)->b);
            }
            if (evaluate_predicate(fold(((((const Broadcast*)r1)->lanes % ((const Broadcast*)r2)->lanes) == 0)))) {
              return (broadcast((((const Broadcast*)r2)->value + broadcast(((const Broadcast*)r1)->value, fold((((const Broadcast*)r1)->lanes / ((const Broadcast*)r2)->lanes)))), ((const Broadcast*)r2)->lanes) - ((const Sub*)r0)->b);
            }
          }
        }
      }
    }
    if (is_const_v(((const Sub*)r0)->a)) {
      if (is_const_v(b)) {
        return (fold((((const Sub*)r0)->a + b)) - ((const Sub*)r0)->b);
      }
      return ((b - ((const Sub*)r0)->b) + ((const Sub*)r0)->a);
    }
    if (equal(((const Sub*)r0)->b, b)) {
      return ((const Sub*)r0)->a;
    }
    if ((r1 = b.as<Sub>())) {
      if (equal(((const Sub*)r0)->b, ((const Sub*)r1)->a)) {
        return (((const Sub*)r0)->a - ((const Sub*)r1)->b);
      }
      if (equal(((const Sub*)r0)->a, ((const Sub*)r1)->b)) {
        return (((const Sub*)r1)->a - ((const Sub*)r0)->b);
      }
    }
    if ((r1 = b.as<Add>())) {
      if (equal(((const Sub*)r0)->b, ((const Add*)r1)->a)) {
        return (((const Sub*)r0)->a + ((const Add*)r1)->b);
      }
      if (equal(((const Sub*)r0)->b, ((const Add*)r1)->b)) {
        return (((const Sub*)r0)->a + ((const Add*)r1)->a);
      }
    }
    if ((r1 = ((const Sub*)r0)->a.as<Sub>())) {
      if (equal(((const Sub*)r1)->b, b)) {
        return (((const Sub*)r1)->a - ((const Sub*)r0)->b);
      }
      if (is_const_int(((const Sub*)r1)->a, 0)) {
        return (b - (((const Sub*)r1)->b + ((const Sub*)r0)->b));
      }
      if (is_const_v(((const Sub*)r1)->a)) {
        if (is_const_v(b)) {
          return ((fold((((const Sub*)r1)->a + b)) - ((const Sub*)r0)->b) - ((const Sub*)r1)->b);
        }
      }
    }
    if ((r1 = ((const Sub*)r0)->b.as<Add>())) {
      if (equal(((const Add*)r1)->a, b)) {
        return (((const Sub*)r0)->a - ((const Add*)r1)->b);
      }
      if (equal(((const Add*)r1)->b, b)) {
        return (((const Sub*)r0)->a - ((const Add*)r1)->a);
      }
    }
  }
  if ((r0 = a.as<Select>())) {
    if ((r1 = b.as<Select>())) {
      if (equal(((const Select*)r0)->condition, ((const Select*)r1)->condition)) {
        return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value + ((const Select*)r1)->true_value), (((const Select*)r0)->false_value + ((const Select*)r1)->false_value));
      }
    }
    if (is_const_v(((const Select*)r0)->true_value)) {
      if (is_const_v(((const Select*)r0)->false_value)) {
        if (is_const_v(b)) {
          return select(((const Select*)r0)->condition, fold((((const Select*)r0)->true_value + b)), fold((((const Select*)r0)->false_value + b)));
        }
      }
      if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(b)) {
            return select(((const Select*)r0)->condition, fold((((const Select*)r0)->true_value + b)), (((const Add*)r1)->a + fold((((const Add*)r1)->b + b))));
          }
        }
      }
    }
    if ((r1 = ((const Select*)r0)->true_value.as<Add>())) {
      if (is_const_v(((const Add*)r1)->b)) {
        if (is_const_v(((const Select*)r0)->false_value)) {
          if (is_const_v(b)) {
            return select(((const Select*)r0)->condition, (((const Add*)r1)->a + fold((((const Add*)r1)->b + b))), fold((((const Select*)r0)->false_value + b)));
          }
        }
        if ((r2 = ((const Select*)r0)->false_value.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(b)) {
              return select(((const Select*)r0)->condition, (((const Add*)r1)->a + fold((((const Add*)r1)->b + b))), (((const Add*)r2)->a + fold((((const Add*)r2)->b + b))));
            }
          }
        }
      }
    }
    if ((r1 = b.as<Add>())) {
      if ((r2 = ((const Add*)r1)->a.as<Select>())) {
        if (equal(((const Select*)r0)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r0)->condition, (((const Select*)r0)->true_value + ((const Select*)r2)->true_value), (((const Select*)r0)->false_value + ((const Select*)r2)->false_value)) + ((const Add*)r1)->b);
        }
      }
      if ((r2 = ((const Add*)r1)->b.as<Select>())) {
        if (equal(((const Select*)r0)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r0)->condition, (((const Select*)r0)->true_value + ((const Select*)r2)->true_value), (((const Select*)r0)->false_value + ((const Select*)r2)->false_value)) + ((const Add*)r1)->a);
        }
      }
    }
    if ((r1 = b.as<Sub>())) {
      if ((r2 = ((const Sub*)r1)->a.as<Select>())) {
        if (equal(((const Select*)r0)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r0)->condition, (((const Select*)r0)->true_value + ((const Select*)r2)->true_value), (((const Select*)r0)->false_value + ((const Select*)r2)->false_value)) - ((const Sub*)r1)->b);
        }
      }
      if ((r2 = ((const Sub*)r1)->b.as<Select>())) {
        if (equal(((const Select*)r0)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r0)->condition, (((const Select*)r0)->true_value - ((const Select*)r2)->true_value), (((const Select*)r0)->false_value - ((const Select*)r2)->false_value)) + ((const Sub*)r1)->a);
        }
      }
    }
    if ((r1 = ((const Select*)r0)->true_value.as<Sub>())) {
      if (is_const_v(((const Sub*)r1)->a)) {
        if (is_const_v(((const Select*)r0)->false_value)) {
          if (is_const_v(b)) {
            return select(((const Select*)r0)->condition, (fold((((const Sub*)r1)->a + b)) - ((const Sub*)r1)->b), fold((((const Select*)r0)->false_value + b)));
            return (fold((((const Sub*)r1)->a + b)) - select(((const Select*)r0)->condition, ((const Sub*)r1)->b, fold((((const Sub*)r1)->a - ((const Select*)r0)->false_value))));
          }
        }
      }
    }
    if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
      if (is_const_v(((const Add*)r1)->b)) {
        if (is_const_v(b)) {
          if (evaluate_predicate(fold(((((const Add*)r1)->b + b) == 0)))) {
            return select(((const Select*)r0)->condition, (((const Select*)r0)->true_value + b), ((const Add*)r1)->a);
          }
        }
      }
    }
  }
  if ((r0 = b.as<Mul>())) {
    if ((r1 = ((const Mul*)r0)->b.as<Sub>())) {
      if (is_const_int(((const Sub*)r1)->a, 0)) {
        if (is_const_int(((const Sub*)r1)->b, 1)) {
          return (a - ((const Mul*)r0)->a);
        }
      }
    }
  }
  if ((r0 = a.as<Mul>())) {
    if ((r1 = ((const Mul*)r0)->b.as<Sub>())) {
      if (is_const_int(((const Sub*)r1)->a, 0)) {
        if (is_const_int(((const Sub*)r1)->b, 1)) {
          return (b - ((const Mul*)r0)->a);
        }
      }
    }
    if ((r1 = b.as<Mul>())) {
      if (equal(((const Mul*)r0)->b, ((const Mul*)r1)->b)) {
        return ((((const Mul*)r0)->a + ((const Mul*)r1)->a) * ((const Mul*)r0)->b);
      }
      if (equal(((const Mul*)r0)->b, ((const Mul*)r1)->a)) {
        return ((((const Mul*)r0)->a + ((const Mul*)r1)->b) * ((const Mul*)r0)->b);
      }
      if (equal(((const Mul*)r0)->a, ((const Mul*)r1)->b)) {
        return (((const Mul*)r0)->a * (((const Mul*)r0)->b + ((const Mul*)r1)->a));
      }
      if (equal(((const Mul*)r0)->a, ((const Mul*)r1)->a)) {
        return (((const Mul*)r0)->a * (((const Mul*)r0)->b + ((const Mul*)r1)->b));
      }
    }
    if (is_const_v(((const Mul*)r0)->b)) {
      if ((r1 = b.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if (evaluate_predicate(fold(((((const Mul*)r1)->b % ((const Mul*)r0)->b) == 0)))) {
            return ((((const Mul*)r0)->a + (((const Mul*)r1)->a * fold((((const Mul*)r1)->b / ((const Mul*)r0)->b)))) * ((const Mul*)r0)->b);
          }
          if (evaluate_predicate(fold(((((const Mul*)r0)->b % ((const Mul*)r1)->b) == 0)))) {
            return (((((const Mul*)r0)->a * fold((((const Mul*)r0)->b / ((const Mul*)r1)->b))) + ((const Mul*)r1)->a) * ((const Mul*)r1)->b);
          }
        }
      }
    }
  }
  if ((r0 = b.as<Add>())) {
    if (is_const_v(((const Add*)r0)->b)) {
      return ((a + ((const Add*)r0)->a) + ((const Add*)r0)->b);
    }
    if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->b)) {
        return (((const Sub*)r1)->a + ((const Add*)r0)->b);
      }
    }
    if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->b)) {
        return (((const Add*)r0)->a + ((const Sub*)r1)->a);
      }
    }
  }
  if ((r0 = a.as<Max>())) {
    if ((r1 = ((const Max*)r0)->b.as<Add>())) {
      if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
        if (is_const_v(((const Mul*)r2)->b)) {
          if ((r3 = b.as<Mul>())) {
            if ((r4 = ((const Mul*)r3)->a.as<Sub>())) {
              if (equal(((const Mul*)r2)->a, ((const Sub*)r4)->b)) {
                if (equal(((const Mul*)r2)->b, ((const Mul*)r3)->b)) {
                  return (max((((const Max*)r0)->a - (((const Mul*)r2)->a * ((const Mul*)r2)->b)), ((const Add*)r1)->b) + (((const Sub*)r4)->a * ((const Mul*)r2)->b));
                }
              }
            }
          }
        }
      }
    }
  }
  if ((r0 = b.as<Sub>())) {
    if (equal(a, ((const Sub*)r0)->b)) {
      return ((const Sub*)r0)->a;
    }
    if (is_const_v(((const Sub*)r0)->a)) {
      return ((a - ((const Sub*)r0)->b) + ((const Sub*)r0)->a);
    }
    if ((r1 = ((const Sub*)r0)->a.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->b)) {
        return (((const Sub*)r1)->a - ((const Sub*)r0)->b);
      }
      if (is_const_int(((const Sub*)r1)->a, 0)) {
        return (a - (((const Sub*)r1)->b + ((const Sub*)r0)->b));
      }
    }
    if ((r1 = ((const Sub*)r0)->b.as<Add>())) {
      if (equal(a, ((const Add*)r1)->a)) {
        return (((const Sub*)r0)->a - ((const Add*)r1)->b);
      }
      if (equal(a, ((const Add*)r1)->b)) {
        return (((const Sub*)r0)->a - ((const Add*)r1)->a);
      }
    }
  }
  if (type.is_no_overflow()) {
    if ((r0 = b.as<Mul>())) {
      if (equal(a, ((const Mul*)r0)->a)) {
        return (a * (((const Mul*)r0)->b + 1));
      }
      if (equal(a, ((const Mul*)r0)->b)) {
        return ((((const Mul*)r0)->a + 1) * a);
      }
    }
    if ((r0 = a.as<Mul>())) {
      if (equal(((const Mul*)r0)->a, b)) {
        return (((const Mul*)r0)->a * (((const Mul*)r0)->b + 1));
      }
      if (equal(((const Mul*)r0)->b, b)) {
        if (evaluate_predicate(fold(!(is_const(((const Mul*)r0)->b))))) {
          return ((((const Mul*)r0)->a + 1) * ((const Mul*)r0)->b);
        }
      }
    }
    if ((r0 = a.as<Div>())) {
      if ((r1 = ((const Div*)r0)->a.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (is_const_v(b)) {
              if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
                return ((((const Add*)r1)->a + fold((((const Add*)r1)->b + (((const Div*)r0)->b * b)))) / ((const Div*)r0)->b);
              }
            }
          }
        }
        if (is_const_v(((const Div*)r0)->b)) {
          if (equal(((const Add*)r1)->a, b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return (((fold((((const Div*)r0)->b + 1)) * ((const Add*)r1)->a) + ((const Add*)r1)->b) / ((const Div*)r0)->b);
            }
          }
          if (equal(((const Add*)r1)->b, b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return ((((const Add*)r1)->a + (fold((((const Div*)r0)->b + 1)) * ((const Add*)r1)->b)) / ((const Div*)r0)->b);
            }
          }
        }
      }
      if ((r1 = ((const Div*)r0)->a.as<Sub>())) {
        if (is_const_v(((const Sub*)r1)->a)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (is_const_v(b)) {
              if (evaluate_predicate(fold(((((const Sub*)r1)->a != 0) && (((const Div*)r0)->b != 0))))) {
                return ((fold((((const Sub*)r1)->a + (((const Div*)r0)->b * b))) - ((const Sub*)r1)->b) / ((const Div*)r0)->b);
              }
            }
          }
        }
        if (is_const_v(((const Div*)r0)->b)) {
          if (equal(((const Sub*)r1)->a, b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return (((fold((((const Div*)r0)->b + 1)) * ((const Sub*)r1)->a) - ((const Sub*)r1)->b) / ((const Div*)r0)->b);
            }
          }
          if (equal(((const Sub*)r1)->b, b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return ((((const Sub*)r1)->a + (fold((((const Div*)r0)->b - 1)) * ((const Sub*)r1)->b)) / ((const Div*)r0)->b);
            }
          }
        }
      }
    }
    if ((r0 = a.as<Add>())) {
      if ((r1 = ((const Add*)r0)->b.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if (is_const_v(b)) {
                if (evaluate_predicate(fold((((const Div*)r1)->b != 0)))) {
                  return (((const Add*)r0)->a + ((((const Add*)r2)->a + fold((((const Add*)r2)->b + (((const Div*)r1)->b * b)))) / ((const Div*)r1)->b));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if (is_const_v(b)) {
                if (evaluate_predicate(fold((((const Div*)r1)->b != 0)))) {
                  return (((const Add*)r0)->b + ((((const Add*)r2)->a + fold((((const Add*)r2)->b + (((const Div*)r1)->b * b)))) / ((const Div*)r1)->b));
                }
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
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return (((fold((((const Div*)r0)->b + 1)) * a) + ((const Add*)r1)->b) / ((const Div*)r0)->b);
            }
          }
        }
        if (equal(a, ((const Add*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return (((fold((((const Div*)r0)->b + 1)) * a) + ((const Add*)r1)->a) / ((const Div*)r0)->b);
            }
          }
        }
      }
      if ((r1 = ((const Div*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return (((fold((((const Div*)r0)->b - 1)) * a) + ((const Sub*)r1)->a) / ((const Div*)r0)->b);
            }
          }
        }
        if (equal(a, ((const Sub*)r1)->a)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b != 0)))) {
              return (((fold((((const Div*)r0)->b + 1)) * a) - ((const Sub*)r1)->b) / ((const Div*)r0)->b);
            }
          }
        }
      }
    }
    if ((r0 = a.as<Min>())) {
      if ((r1 = ((const Min*)r0)->b.as<Sub>())) {
        if (equal(((const Sub*)r1)->b, b)) {
          return min((((const Min*)r0)->a + ((const Sub*)r1)->b), ((const Sub*)r1)->a);
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Sub>())) {
        if (equal(((const Sub*)r1)->b, b)) {
          return min(((const Sub*)r1)->a, (((const Min*)r0)->b + ((const Sub*)r1)->b));
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(b)) {
            if (evaluate_predicate(fold(((((const Add*)r1)->b + b) == 0)))) {
              return min((((const Min*)r0)->a + b), ((const Add*)r1)->a);
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return min((((const Min*)r0)->a + (((const Mul*)r2)->a * ((const Mul*)r3)->b)), ((const Add*)r1)->a);
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return min((((const Min*)r0)->a + (((const Mul*)r2)->a * ((const Mul*)r3)->b)), ((const Add*)r1)->b);
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(b)) {
            if (evaluate_predicate(fold(((((const Add*)r1)->b + b) == 0)))) {
              return min(((const Add*)r1)->a, (((const Min*)r0)->b + b));
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return min(((((const Mul*)r2)->a * ((const Mul*)r3)->b) + ((const Min*)r0)->b), ((const Add*)r1)->a);
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return min(((const Add*)r1)->b, ((((const Mul*)r2)->a * ((const Mul*)r3)->b) + ((const Min*)r0)->b));
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if ((r2 = b.as<Mul>())) {
            if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
              if (is_const_v(((const Mul*)r2)->b)) {
                if (evaluate_predicate(fold(((((const Mul*)r1)->b + ((const Mul*)r2)->b) == 0)))) {
                  return min((((const Min*)r0)->a + (((const Mul*)r1)->a * ((const Mul*)r2)->b)), 0);
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if ((r2 = b.as<Mul>())) {
            if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
              if (is_const_v(((const Mul*)r2)->b)) {
                if (evaluate_predicate(fold(((((const Mul*)r1)->b + ((const Mul*)r2)->b) == 0)))) {
                  return min(((((const Mul*)r1)->a * ((const Mul*)r2)->b) + ((const Min*)r0)->b), 0);
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = b.as<Min>())) {
      if ((r1 = ((const Min*)r0)->b.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->b)) {
          return min((a + ((const Min*)r0)->a), ((const Sub*)r1)->a);
        }
      }
      if ((r1 = ((const Min*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->b)) {
          return min(((const Sub*)r1)->a, (a + ((const Min*)r0)->b));
        }
      }
    }
    if ((r0 = b.as<Max>())) {
      if ((r1 = ((const Max*)r0)->b.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->b)) {
          return max((a + ((const Max*)r0)->a), ((const Sub*)r1)->a);
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->b)) {
          return max(((const Sub*)r1)->a, (a + ((const Max*)r0)->b));
        }
      }
    }
    if ((r0 = a.as<Max>())) {
      if ((r1 = ((const Max*)r0)->b.as<Sub>())) {
        if (equal(((const Sub*)r1)->b, b)) {
          return max((((const Max*)r0)->a + ((const Sub*)r1)->b), ((const Sub*)r1)->a);
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Sub>())) {
        if (equal(((const Sub*)r1)->b, b)) {
          return max(((const Sub*)r1)->a, (((const Max*)r0)->b + ((const Sub*)r1)->b));
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(b)) {
            if (evaluate_predicate(fold(((((const Add*)r1)->b + b) == 0)))) {
              return max((((const Max*)r0)->a + b), ((const Add*)r1)->a);
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return max((((const Max*)r0)->a + (((const Mul*)r2)->a * ((const Mul*)r3)->b)), ((const Add*)r1)->a);
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return max((((const Max*)r0)->a + (((const Mul*)r2)->a * ((const Mul*)r3)->b)), ((const Add*)r1)->b);
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(b)) {
            if (evaluate_predicate(fold(((((const Add*)r1)->b + b) == 0)))) {
              return max(((const Add*)r1)->a, (((const Max*)r0)->b + b));
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return max(((const Add*)r1)->a, ((((const Mul*)r2)->a * ((const Mul*)r3)->b) + ((const Max*)r0)->b));
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if ((r3 = b.as<Mul>())) {
              if (equal(((const Mul*)r2)->a, ((const Mul*)r3)->a)) {
                if (is_const_v(((const Mul*)r3)->b)) {
                  if (evaluate_predicate(fold(((((const Mul*)r2)->b + ((const Mul*)r3)->b) == 0)))) {
                    return max(((((const Mul*)r2)->a * ((const Mul*)r3)->b) + ((const Max*)r0)->b), ((const Add*)r1)->b);
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = b.as<Min>())) {
        if (equal(((const Max*)r0)->a, ((const Min*)r1)->a)) {
          if (equal(((const Max*)r0)->b, ((const Min*)r1)->b)) {
            return (((const Max*)r0)->a + ((const Max*)r0)->b);
          }
        }
        if (equal(((const Max*)r0)->b, ((const Min*)r1)->a)) {
          if (equal(((const Max*)r0)->a, ((const Min*)r1)->b)) {
            return (((const Max*)r0)->a + ((const Max*)r0)->b);
          }
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if ((r2 = b.as<Mul>())) {
            if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
              if (is_const_v(((const Mul*)r2)->b)) {
                if (evaluate_predicate(fold(((((const Mul*)r1)->b + ((const Mul*)r2)->b) == 0)))) {
                  return max((((const Max*)r0)->a + (((const Mul*)r1)->a * ((const Mul*)r2)->b)), 0);
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if ((r2 = b.as<Mul>())) {
            if (equal(((const Mul*)r1)->a, ((const Mul*)r2)->a)) {
              if (is_const_v(((const Mul*)r2)->b)) {
                if (evaluate_predicate(fold(((((const Mul*)r1)->b + ((const Mul*)r2)->b) == 0)))) {
                  return max(((((const Mul*)r1)->a * ((const Mul*)r2)->b) + ((const Max*)r0)->b), 0);
                }
              }
            }
          }
        }
      }
    }
  }
  if (type.is_no_overflow_int()) {
    if ((r0 = a.as<Mul>())) {
      if ((r1 = ((const Mul*)r0)->b.as<Div>())) {
        if (equal(((const Mul*)r0)->a, ((const Div*)r1)->b)) {
          if ((r2 = b.as<Mod>())) {
            if (equal(((const Div*)r1)->a, ((const Mod*)r2)->a)) {
              if (equal(((const Mul*)r0)->a, ((const Mod*)r2)->b)) {
                return select((((const Mul*)r0)->a == 0), 0, ((const Div*)r1)->a);
              }
            }
          }
          if ((r2 = b.as<Add>())) {
            if ((r3 = ((const Add*)r2)->a.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Mul*)r0)->a, ((const Mod*)r3)->b)) {
                  return (select((((const Mul*)r0)->a == 0), 0, ((const Div*)r1)->a) + ((const Add*)r2)->b);
                }
              }
            }
            if ((r3 = ((const Add*)r2)->b.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Mul*)r0)->a, ((const Mod*)r3)->b)) {
                  return (select((((const Mul*)r0)->a == 0), 0, ((const Div*)r1)->a) + ((const Add*)r2)->a);
                }
              }
            }
          }
          if ((r2 = b.as<Sub>())) {
            if ((r3 = ((const Sub*)r2)->a.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Mul*)r0)->a, ((const Mod*)r3)->b)) {
                  return (select((((const Mul*)r0)->a == 0), 0, ((const Div*)r1)->a) - ((const Sub*)r2)->b);
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
        if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
          if ((r2 = b.as<Mod>())) {
            if (equal(((const Div*)r1)->a, ((const Mod*)r2)->a)) {
              if (equal(((const Div*)r1)->b, ((const Mod*)r2)->b)) {
                return select((((const Div*)r1)->b == 0), 0, ((const Div*)r1)->a);
              }
            }
          }
          if ((r2 = b.as<Add>())) {
            if ((r3 = ((const Add*)r2)->a.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Div*)r1)->b, ((const Mod*)r3)->b)) {
                  return (select((((const Div*)r1)->b == 0), 0, ((const Div*)r1)->a) + ((const Add*)r2)->b);
                }
              }
            }
            if ((r3 = ((const Add*)r2)->b.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Div*)r1)->b, ((const Mod*)r3)->b)) {
                  return (select((((const Div*)r1)->b == 0), 0, ((const Div*)r1)->a) + ((const Add*)r2)->a);
                }
              }
            }
          }
          if ((r2 = b.as<Sub>())) {
            if ((r3 = ((const Sub*)r2)->a.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Div*)r1)->b, ((const Mod*)r3)->b)) {
                  return (select((((const Div*)r1)->b == 0), 0, ((const Div*)r1)->a) - ((const Sub*)r2)->b);
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Mul*)r0)->b.as<Add>())) {
        if ((r2 = ((const Add*)r1)->b.as<Div>())) {
          if (equal(((const Mul*)r0)->a, ((const Div*)r2)->b)) {
            if ((r3 = b.as<Mod>())) {
              if (equal(((const Div*)r2)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Mul*)r0)->a, ((const Mod*)r3)->b)) {
                  return select((((const Mul*)r0)->a == 0), 0, ((((const Add*)r1)->a * ((const Mul*)r0)->a) + ((const Div*)r2)->a));
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Div>())) {
          if (equal(((const Mul*)r0)->a, ((const Div*)r2)->b)) {
            if ((r3 = b.as<Mod>())) {
              if (equal(((const Div*)r2)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Mul*)r0)->a, ((const Mod*)r3)->b)) {
                  return select((((const Mul*)r0)->a == 0), 0, (((const Div*)r2)->a + (((const Add*)r1)->b * ((const Mul*)r0)->a)));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Mul*)r0)->a.as<Add>())) {
        if ((r2 = ((const Add*)r1)->b.as<Div>())) {
          if (equal(((const Div*)r2)->b, ((const Mul*)r0)->b)) {
            if ((r3 = b.as<Mod>())) {
              if (equal(((const Div*)r2)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Div*)r2)->b, ((const Mod*)r3)->b)) {
                  return select((((const Div*)r2)->b == 0), 0, ((((const Add*)r1)->a * ((const Div*)r2)->b) + ((const Div*)r2)->a));
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Div>())) {
          if (equal(((const Div*)r2)->b, ((const Mul*)r0)->b)) {
            if ((r3 = b.as<Mod>())) {
              if (equal(((const Div*)r2)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Div*)r2)->b, ((const Mod*)r3)->b)) {
                  return select((((const Div*)r2)->b == 0), 0, (((const Div*)r2)->a + (((const Add*)r1)->b * ((const Div*)r2)->b)));
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Mod>())) {
      if ((r1 = b.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->a)) {
            if ((r3 = ((const Mul*)r2)->b.as<Div>())) {
              if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
                if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) + ((const Add*)r1)->b);
                }
              }
            }
          }
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
              if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) + ((const Add*)r1)->b);
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->a)) {
            if ((r3 = ((const Mul*)r2)->b.as<Div>())) {
              if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
                if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) + ((const Add*)r1)->a);
                }
              }
            }
          }
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
              if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) + ((const Add*)r1)->a);
                }
              }
            }
          }
        }
      }
      if ((r1 = b.as<Sub>())) {
        if ((r2 = ((const Sub*)r1)->a.as<Mul>())) {
          if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->a)) {
            if ((r3 = ((const Mul*)r2)->b.as<Div>())) {
              if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
                if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) - ((const Sub*)r1)->b);
                }
              }
            }
          }
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
              if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) - ((const Sub*)r1)->b);
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Div>())) {
      if (is_const_int(((const Div*)r0)->b, 2)) {
        if ((r1 = b.as<Mod>())) {
          if (equal(((const Div*)r0)->a, ((const Mod*)r1)->a)) {
            if (is_const_int(((const Mod*)r1)->b, 2)) {
              return ((((const Div*)r0)->a + 1) / 2);
            }
          }
        }
      }
    }
    if ((r0 = b.as<Mul>())) {
      if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Sub>())) {
          if (is_const_v(((const Sub*)r2)->a)) {
            if (equal(a, ((const Sub*)r2)->b)) {
              if (is_const_v(((const Div*)r1)->b)) {
                if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
                  if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                    return (((const Sub*)r2)->a - ((((const Sub*)r2)->a - a) % ((const Div*)r1)->b));
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Mul*)r0)->a.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Sub>())) {
            if (is_const_v(((const Sub*)r3)->a)) {
              if (equal(a, ((const Sub*)r3)->b)) {
                if (is_const_v(((const Div*)r2)->b)) {
                  if (equal(((const Div*)r2)->b, ((const Mul*)r0)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return (((((const Add*)r1)->b * ((const Div*)r2)->b) - ((((const Sub*)r3)->a - a) % ((const Div*)r2)->b)) + ((const Sub*)r3)->a);
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Sub>())) {
            if (is_const_v(((const Sub*)r3)->a)) {
              if (equal(a, ((const Sub*)r3)->b)) {
                if (is_const_v(((const Div*)r2)->b)) {
                  if (equal(((const Div*)r2)->b, ((const Mul*)r0)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return (((((const Add*)r1)->a * ((const Div*)r2)->b) - ((((const Sub*)r3)->a - a) % ((const Div*)r2)->b)) + ((const Sub*)r3)->a);
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
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
