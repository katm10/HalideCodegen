#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr Simplify_Max(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  const BaseExprNode *r0 = nullptr;
  const BaseExprNode *r1 = nullptr;
  const BaseExprNode *r2 = nullptr;
  const BaseExprNode *r3 = nullptr;
  const BaseExprNode *r4 = nullptr;
  if (equal(a, b)) {
    return a;
  }
  if (is_const_v(a)) {
    if (is_const_v(b)) {
      return fold(max(a, b));
    }
  }
  if ((r0 = a.as<Mul>())) {
    if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
      if (is_const_v(((const Div*)r1)->b)) {
        if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
          if (equal(((const Div*)r1)->a, b)) {
            if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
              return ((const Div*)r1)->a;
            }
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
              return a;
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<Max>())) {
    if (equal(((const Max*)r0)->a, b)) {
      return max(((const Max*)r0)->a, ((const Max*)r0)->b);
    }
    if (equal(((const Max*)r0)->b, b)) {
      return max(((const Max*)r0)->a, ((const Max*)r0)->b);
    }
    if ((r1 = ((const Max*)r0)->a.as<Max>())) {
      if (equal(((const Max*)r1)->a, b)) {
        return max(max(((const Max*)r1)->a, ((const Max*)r1)->b), ((const Max*)r0)->b);
      }
      if (equal(((const Max*)r1)->b, b)) {
        return max(max(((const Max*)r1)->a, ((const Max*)r1)->b), ((const Max*)r0)->b);
      }
      if ((r2 = ((const Max*)r1)->a.as<Max>())) {
        if (equal(((const Max*)r2)->a, b)) {
          return max(max(max(((const Max*)r2)->a, ((const Max*)r2)->b), ((const Max*)r1)->b), ((const Max*)r0)->b);
        }
        if (equal(((const Max*)r2)->b, b)) {
          return max(max(max(((const Max*)r2)->a, ((const Max*)r2)->b), ((const Max*)r1)->b), ((const Max*)r0)->b);
        }
        if ((r3 = ((const Max*)r2)->a.as<Max>())) {
          if (equal(((const Max*)r3)->a, b)) {
            return max(max(max(max(((const Max*)r3)->a, ((const Max*)r3)->b), ((const Max*)r2)->b), ((const Max*)r1)->b), ((const Max*)r0)->b);
          }
          if (equal(((const Max*)r3)->b, b)) {
            return max(max(max(max(((const Max*)r3)->a, ((const Max*)r3)->b), ((const Max*)r2)->b), ((const Max*)r1)->b), ((const Max*)r0)->b);
          }
        }
      }
    }
    if ((r1 = b.as<Min>())) {
      if (equal(((const Max*)r0)->a, ((const Min*)r1)->a)) {
        if (equal(((const Max*)r0)->b, ((const Min*)r1)->b)) {
          return max(((const Max*)r0)->a, ((const Max*)r0)->b);
        }
        return max(((const Max*)r0)->a, ((const Max*)r0)->b);
      }
      if (equal(((const Max*)r0)->b, ((const Min*)r1)->a)) {
        if (equal(((const Max*)r0)->a, ((const Min*)r1)->b)) {
          return max(((const Max*)r0)->a, ((const Max*)r0)->b);
        }
        return max(((const Max*)r0)->a, ((const Max*)r0)->b);
      }
      if (equal(((const Max*)r0)->a, ((const Min*)r1)->b)) {
        return max(((const Max*)r0)->a, ((const Max*)r0)->b);
      }
      if (equal(((const Max*)r0)->b, ((const Min*)r1)->b)) {
        return max(((const Max*)r0)->a, ((const Max*)r0)->b);
      }
    }
    if (is_const_v(((const Max*)r0)->b)) {
      if (is_const_v(b)) {
        return max(((const Max*)r0)->a, fold(max(((const Max*)r0)->b, b)));
      }
      return max(max(((const Max*)r0)->a, b), ((const Max*)r0)->b);
    }
    if ((r1 = b.as<Max>())) {
      if (equal(((const Max*)r0)->a, ((const Max*)r1)->a)) {
        return max(max(((const Max*)r0)->b, ((const Max*)r1)->b), ((const Max*)r0)->a);
      }
      if (equal(((const Max*)r0)->b, ((const Max*)r1)->a)) {
        return max(max(((const Max*)r0)->a, ((const Max*)r1)->b), ((const Max*)r0)->b);
      }
      if (equal(((const Max*)r0)->a, ((const Max*)r1)->b)) {
        return max(max(((const Max*)r0)->b, ((const Max*)r1)->a), ((const Max*)r0)->a);
      }
      if (equal(((const Max*)r0)->b, ((const Max*)r1)->b)) {
        return max(max(((const Max*)r0)->a, ((const Max*)r1)->a), ((const Max*)r0)->b);
      }
      return max(max(max(((const Max*)r0)->a, ((const Max*)r0)->b), ((const Max*)r1)->a), ((const Max*)r1)->b);
    }
    if ((r1 = ((const Max*)r0)->b.as<Broadcast>())) {
      if ((r2 = b.as<Broadcast>())) {
        return max(((const Max*)r0)->a, broadcast(max(((const Broadcast*)r1)->value, ((const Broadcast*)r2)->value), c0));
      }
    }
    if ((r1 = ((const Max*)r0)->a.as<Div>())) {
      if (is_const_v(((const Div*)r1)->b)) {
        if ((r2 = b.as<Div>())) {
          if (equal(((const Div*)r1)->b, ((const Div*)r2)->b)) {
            if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
              return max((max(((const Div*)r1)->a, ((const Div*)r2)->a) / ((const Div*)r1)->b), ((const Max*)r0)->b);
            }
          }
        }
      }
    }
    if ((r1 = ((const Max*)r0)->b.as<Min>())) {
      if (equal(((const Min*)r1)->a, b)) {
        return max(((const Max*)r0)->a, ((const Min*)r1)->a);
      }
      if (equal(((const Min*)r1)->b, b)) {
        return max(((const Max*)r0)->a, ((const Min*)r1)->b);
      }
    }
    if ((r1 = ((const Max*)r0)->a.as<Min>())) {
      if (equal(((const Min*)r1)->a, b)) {
        return max(((const Max*)r0)->b, ((const Min*)r1)->a);
      }
      if (equal(((const Min*)r1)->b, b)) {
        return max(((const Max*)r0)->b, ((const Min*)r1)->b);
      }
    }
  }
  if ((r0 = b.as<Max>())) {
    if (equal(a, ((const Max*)r0)->a)) {
      return max(a, ((const Max*)r0)->b);
    }
    if (equal(a, ((const Max*)r0)->b)) {
      return max(((const Max*)r0)->a, a);
    }
    if ((r1 = ((const Max*)r0)->b.as<Min>())) {
      if (equal(a, ((const Min*)r1)->a)) {
        return max(((const Max*)r0)->a, a);
      }
      if (equal(a, ((const Min*)r1)->b)) {
        return max(((const Max*)r0)->a, a);
      }
    }
    if ((r1 = ((const Max*)r0)->a.as<Min>())) {
      if (equal(a, ((const Min*)r1)->a)) {
        return max(a, ((const Max*)r0)->b);
      }
      if (equal(a, ((const Min*)r1)->b)) {
        return max(a, ((const Max*)r0)->b);
      }
    }
  }
  if ((r0 = b.as<Min>())) {
    if (equal(a, ((const Min*)r0)->a)) {
      return a;
    }
    if (equal(a, ((const Min*)r0)->b)) {
      return a;
    }
    if ((r1 = ((const Min*)r0)->b.as<Min>())) {
      if (equal(a, ((const Min*)r1)->a)) {
        return a;
      }
      if (equal(a, ((const Min*)r1)->b)) {
        return a;
      }
    }
    if ((r1 = ((const Min*)r0)->a.as<Min>())) {
      if (equal(a, ((const Min*)r1)->a)) {
        return a;
      }
      if (equal(a, ((const Min*)r1)->b)) {
        return a;
      }
    }
  }
  if ((r0 = a.as<Min>())) {
    if (equal(((const Min*)r0)->a, b)) {
      return ((const Min*)r0)->a;
    }
    if (equal(((const Min*)r0)->b, b)) {
      return ((const Min*)r0)->b;
    }
    if (is_const_v(((const Min*)r0)->b)) {
      if (is_const_v(b)) {
        if (evaluate_predicate(fold((b >= ((const Min*)r0)->b)))) {
          return b;
        }
      }
    }
    if ((r1 = ((const Min*)r0)->b.as<Min>())) {
      if (equal(((const Min*)r1)->a, b)) {
        return ((const Min*)r1)->a;
      }
      if (equal(((const Min*)r1)->b, b)) {
        return ((const Min*)r1)->b;
      }
    }
    if ((r1 = ((const Min*)r0)->a.as<Min>())) {
      if (equal(((const Min*)r1)->a, b)) {
        return ((const Min*)r1)->a;
      }
      if (equal(((const Min*)r1)->b, b)) {
        return ((const Min*)r1)->b;
      }
    }
    if ((r1 = b.as<Min>())) {
      if (equal(((const Min*)r0)->a, ((const Min*)r1)->a)) {
        return min(((const Min*)r0)->a, max(((const Min*)r0)->b, ((const Min*)r1)->b));
      }
      if (equal(((const Min*)r0)->a, ((const Min*)r1)->b)) {
        return min(((const Min*)r0)->a, max(((const Min*)r0)->b, ((const Min*)r1)->a));
      }
      if (equal(((const Min*)r0)->b, ((const Min*)r1)->a)) {
        return min(max(((const Min*)r0)->a, ((const Min*)r1)->b), ((const Min*)r0)->b);
      }
      if (equal(((const Min*)r0)->b, ((const Min*)r1)->b)) {
        return min(max(((const Min*)r0)->a, ((const Min*)r1)->a), ((const Min*)r0)->b);
      }
    }
    if ((r1 = ((const Min*)r0)->a.as<Max>())) {
      if (equal(((const Max*)r1)->b, b)) {
        return max(min(((const Max*)r1)->a, ((const Min*)r0)->b), ((const Max*)r1)->b);
      }
      if (equal(((const Max*)r1)->a, b)) {
        return max(((const Max*)r1)->a, min(((const Max*)r1)->b, ((const Min*)r0)->b));
      }
    }
  }
  if ((r0 = a.as<Select>())) {
    if ((r1 = ((const Select*)r0)->true_value.as<Max>())) {
      if (equal(((const Max*)r1)->a, b)) {
        return max(select(((const Select*)r0)->condition, ((const Max*)r1)->b, ((const Select*)r0)->false_value), ((const Max*)r1)->a);
      }
      if (equal(((const Max*)r1)->b, b)) {
        return max(select(((const Select*)r0)->condition, ((const Max*)r1)->a, ((const Select*)r0)->false_value), ((const Max*)r1)->b);
      }
    }
    if ((r1 = ((const Select*)r0)->false_value.as<Max>())) {
      if (equal(((const Max*)r1)->a, b)) {
        return max(select(((const Select*)r0)->condition, ((const Select*)r0)->true_value, ((const Max*)r1)->b), ((const Max*)r1)->a);
      }
      if (equal(((const Max*)r1)->b, b)) {
        return max(select(((const Select*)r0)->condition, ((const Select*)r0)->true_value, ((const Max*)r1)->a), ((const Max*)r1)->b);
      }
    }
    if ((r1 = ((const Select*)r0)->condition.as<EQ>())) {
      if (is_const_v(((const EQ*)r1)->b)) {
        if (is_const_v(((const Select*)r0)->true_value)) {
          if (equal(((const EQ*)r1)->a, ((const Select*)r0)->false_value)) {
            if (is_const_v(b)) {
              if (evaluate_predicate(fold(((((const EQ*)r1)->b <= b) && (((const Select*)r0)->true_value <= b))))) {
                return max(((const EQ*)r1)->a, b);
              }
            }
            if (equal(((const EQ*)r1)->a, b)) {
              if (evaluate_predicate(fold((((const EQ*)r1)->b < ((const Select*)r0)->true_value)))) {
                return select((((const EQ*)r1)->a == ((const EQ*)r1)->b), ((const Select*)r0)->true_value, ((const EQ*)r1)->a);
              }
              if (evaluate_predicate(fold((((const Select*)r0)->true_value <= ((const EQ*)r1)->b)))) {
                return ((const EQ*)r1)->a;
              }
            }
          }
        }
      }
    }
    if ((r1 = ((const Select*)r0)->true_value.as<Min>())) {
      if (equal(((const Min*)r1)->b, b)) {
        return select(((const Select*)r0)->condition, ((const Min*)r1)->b, max(((const Select*)r0)->false_value, ((const Min*)r1)->b));
      }
      if (equal(((const Min*)r1)->a, b)) {
        return select(((const Select*)r0)->condition, ((const Min*)r1)->a, max(((const Select*)r0)->false_value, ((const Min*)r1)->a));
      }
    }
    if ((r1 = ((const Select*)r0)->false_value.as<Min>())) {
      if (equal(((const Min*)r1)->b, b)) {
        return select(((const Select*)r0)->condition, max(((const Select*)r0)->true_value, ((const Min*)r1)->b), ((const Min*)r1)->b);
      }
      if (equal(((const Min*)r1)->a, b)) {
        return select(((const Select*)r0)->condition, max(((const Select*)r0)->true_value, ((const Min*)r1)->a), ((const Min*)r1)->a);
      }
    }
    if ((r1 = b.as<Select>())) {
      if (equal(((const Select*)r0)->condition, ((const Select*)r1)->condition)) {
        return select(((const Select*)r0)->condition, max(((const Select*)r0)->true_value, ((const Select*)r1)->true_value), max(((const Select*)r0)->false_value, ((const Select*)r1)->false_value));
      }
    }
  }
  if (type.is_no_overflow()) {
    if ((r0 = a.as<Ramp>())) {
      if ((r1 = b.as<Broadcast>())) {
        if (evaluate_predicate(fold(can_prove((((((const Ramp*)r0)->base + (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))) >= ((const Broadcast*)r1)->value) && (((const Ramp*)r0)->base >= ((const Broadcast*)r1)->value)), simplifier)))) {
          return ramp(((const Ramp*)r0)->base, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
        }
        if (evaluate_predicate(fold(can_prove((((((const Ramp*)r0)->base + (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))) <= ((const Broadcast*)r1)->value) && (((const Ramp*)r0)->base <= ((const Broadcast*)r1)->value)), simplifier)))) {
          return broadcast(((const Broadcast*)r1)->value, ((const Ramp*)r0)->lanes);
        }
      }
    }
    if ((r0 = a.as<Add>())) {
      if ((r1 = ((const Add*)r0)->a.as<Mul>())) {
        if ((r2 = ((const Mul*)r1)->a.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Add>())) {
            if (is_const_v(((const Add*)r3)->b)) {
              if (is_const_v(((const Div*)r2)->b)) {
                if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                  if (is_const_v(((const Add*)r0)->b)) {
                    if (equal(((const Add*)r3)->a, b)) {
                      if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r0)->b) >= (((const Div*)r2)->b - 1)))))) {
                        return ((((((const Add*)r3)->a + ((const Add*)r3)->b) / ((const Div*)r2)->b) * ((const Div*)r2)->b) + ((const Add*)r0)->b);
                      }
                      if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r0)->b) <= 0))))) {
                        return ((const Add*)r3)->a;
                      }
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(((const Div*)r2)->b)) {
            if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
              if (is_const_v(((const Add*)r0)->b)) {
                if (equal(((const Div*)r2)->a, b)) {
                  if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && (((const Add*)r0)->b >= (((const Div*)r2)->b - 1)))))) {
                    return (((((const Div*)r2)->a / ((const Div*)r2)->b) * ((const Div*)r2)->b) + ((const Add*)r0)->b);
                  }
                  if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && (((const Add*)r0)->b <= 0))))) {
                    return ((const Div*)r2)->a;
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Min>())) {
        if (is_const_v(((const Add*)r0)->b)) {
          if (equal(((const Min*)r1)->a, b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b <= 0)))) {
              return ((const Min*)r1)->a;
            }
          }
          if (equal(((const Min*)r1)->b, b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b <= 0)))) {
              return ((const Min*)r1)->b;
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Max>())) {
        if (is_const_v(((const Add*)r0)->b)) {
          if (equal(((const Max*)r1)->a, b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b < 0)))) {
              return max(((const Max*)r1)->a, (((const Max*)r1)->b + ((const Add*)r0)->b));
            }
            if (evaluate_predicate(fold((((const Add*)r0)->b > 0)))) {
              return (max(((const Max*)r1)->a, ((const Max*)r1)->b) + ((const Add*)r0)->b);
            }
          }
          if (equal(((const Max*)r1)->b, b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b < 0)))) {
              return max((((const Max*)r1)->a + ((const Add*)r0)->b), ((const Max*)r1)->b);
            }
            if (evaluate_predicate(fold((((const Add*)r0)->b > 0)))) {
              return (max(((const Max*)r1)->a, ((const Max*)r1)->b) + ((const Add*)r0)->b);
            }
          }
        }
      }
      if (is_const_v(((const Add*)r0)->b)) {
        if (is_const_v(b)) {
          return (max(((const Add*)r0)->a, fold((b - ((const Add*)r0)->b))) + ((const Add*)r0)->b);
        }
        if ((r1 = b.as<Add>())) {
          if (is_const_v(((const Add*)r1)->b)) {
            if (evaluate_predicate(fold((((const Add*)r1)->b > ((const Add*)r0)->b)))) {
              return (max(((const Add*)r0)->a, (((const Add*)r1)->a + fold((((const Add*)r1)->b - ((const Add*)r0)->b)))) + ((const Add*)r0)->b);
            }
            if (evaluate_predicate(fold((((const Add*)r0)->b > ((const Add*)r1)->b)))) {
              return (max((((const Add*)r0)->a + fold((((const Add*)r0)->b - ((const Add*)r1)->b))), ((const Add*)r1)->a) + ((const Add*)r1)->b);
            }
          }
        }
      }
      if ((r1 = b.as<Add>())) {
        if (equal(((const Add*)r0)->a, ((const Add*)r1)->a)) {
          return (((const Add*)r0)->a + max(((const Add*)r0)->b, ((const Add*)r1)->b));
        }
        if (equal(((const Add*)r0)->a, ((const Add*)r1)->b)) {
          return (((const Add*)r0)->a + max(((const Add*)r0)->b, ((const Add*)r1)->a));
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r1)->a)) {
          return (max(((const Add*)r0)->a, ((const Add*)r1)->b) + ((const Add*)r0)->b);
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r1)->b)) {
          return (max(((const Add*)r0)->a, ((const Add*)r1)->a) + ((const Add*)r0)->b);
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r0)->a, ((const Add*)r2)->b)) {
            return (((const Add*)r0)->a + max((((const Add*)r2)->a + ((const Add*)r1)->b), ((const Add*)r0)->b));
          }
          if (equal(((const Add*)r0)->a, ((const Add*)r2)->a)) {
            return (((const Add*)r0)->a + max((((const Add*)r2)->b + ((const Add*)r1)->b), ((const Add*)r0)->b));
          }
          if (equal(((const Add*)r0)->b, ((const Add*)r2)->b)) {
            return (max((((const Add*)r2)->a + ((const Add*)r1)->b), ((const Add*)r0)->a) + ((const Add*)r0)->b);
          }
          if (equal(((const Add*)r0)->b, ((const Add*)r2)->a)) {
            return (max((((const Add*)r2)->b + ((const Add*)r1)->b), ((const Add*)r0)->a) + ((const Add*)r0)->b);
          }
        }
      }
      if (equal(((const Add*)r0)->b, b)) {
        return (max(((const Add*)r0)->a, 0) + ((const Add*)r0)->b);
      }
      if (equal(((const Add*)r0)->a, b)) {
        return (((const Add*)r0)->a + max(((const Add*)r0)->b, 0));
      }
      if ((r1 = ((const Add*)r0)->a.as<Add>())) {
        if ((r2 = b.as<Add>())) {
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
            return (((const Add*)r1)->a + max((((const Add*)r1)->b + ((const Add*)r0)->b), ((const Add*)r2)->b));
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->a)) {
            return (max((((const Add*)r1)->a + ((const Add*)r0)->b), ((const Add*)r2)->b) + ((const Add*)r1)->b);
          }
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->b)) {
            return (((const Add*)r1)->a + max((((const Add*)r1)->b + ((const Add*)r0)->b), ((const Add*)r2)->a));
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->b)) {
            return (max((((const Add*)r1)->a + ((const Add*)r0)->b), ((const Add*)r2)->a) + ((const Add*)r1)->b);
          }
        }
        if (equal(((const Add*)r1)->a, b)) {
          return (((const Add*)r1)->a + max((((const Add*)r1)->b + ((const Add*)r0)->b), 0));
        }
        if (equal(((const Add*)r1)->b, b)) {
          return (((const Add*)r1)->b + max((((const Add*)r1)->a + ((const Add*)r0)->b), 0));
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
        if (equal(((const Sub*)r1)->a, b)) {
          return (max((((const Add*)r0)->b - ((const Sub*)r1)->b), 0) + ((const Sub*)r1)->a);
        }
      }
      if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
        if (equal(((const Sub*)r1)->a, b)) {
          return (max((((const Add*)r0)->a - ((const Sub*)r1)->b), 0) + ((const Sub*)r1)->a);
        }
      }
    }
    if ((r0 = b.as<Add>())) {
      if ((r1 = ((const Add*)r0)->a.as<Mul>())) {
        if ((r2 = ((const Mul*)r1)->a.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Add>())) {
            if (equal(a, ((const Add*)r3)->a)) {
              if (is_const_v(((const Add*)r3)->b)) {
                if (is_const_v(((const Div*)r2)->b)) {
                  if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                    if (is_const_v(((const Add*)r0)->b)) {
                      if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r0)->b) >= (((const Div*)r2)->b - 1)))))) {
                        return ((((a + ((const Add*)r3)->b) / ((const Div*)r2)->b) * ((const Div*)r2)->b) + ((const Add*)r0)->b);
                      }
                      if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r0)->b) <= 0))))) {
                        return a;
                      }
                    }
                  }
                }
              }
            }
          }
          if (equal(a, ((const Div*)r2)->a)) {
            if (is_const_v(((const Div*)r2)->b)) {
              if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                if (is_const_v(((const Add*)r0)->b)) {
                  if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && (((const Add*)r0)->b >= (((const Div*)r2)->b - 1)))))) {
                    return (((a / ((const Div*)r2)->b) * ((const Div*)r2)->b) + ((const Add*)r0)->b);
                  }
                  if (evaluate_predicate(fold(((((const Div*)r2)->b > 0) && (((const Add*)r0)->b <= 0))))) {
                    return a;
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Min>())) {
        if (equal(a, ((const Min*)r1)->a)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b <= 0)))) {
              return a;
            }
          }
        }
        if (equal(a, ((const Min*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b <= 0)))) {
              return a;
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Max>())) {
        if (equal(a, ((const Max*)r1)->a)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b < 0)))) {
              return max(a, (((const Max*)r1)->b + ((const Add*)r0)->b));
            }
            if (evaluate_predicate(fold((((const Add*)r0)->b > 0)))) {
              return (max(a, ((const Max*)r1)->b) + ((const Add*)r0)->b);
            }
          }
        }
        if (equal(a, ((const Max*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if (evaluate_predicate(fold((((const Add*)r0)->b < 0)))) {
              return max(a, (((const Max*)r1)->a + ((const Add*)r0)->b));
            }
            if (evaluate_predicate(fold((((const Add*)r0)->b > 0)))) {
              return (max(a, ((const Max*)r1)->a) + ((const Add*)r0)->b);
            }
          }
        }
      }
      if (equal(a, ((const Add*)r0)->a)) {
        return (a + max(((const Add*)r0)->b, 0));
      }
      if (equal(a, ((const Add*)r0)->b)) {
        return (a + max(((const Add*)r0)->a, 0));
      }
      if ((r1 = ((const Add*)r0)->a.as<Add>())) {
        if (equal(a, ((const Add*)r1)->b)) {
          return (a + max((((const Add*)r1)->a + ((const Add*)r0)->b), 0));
        }
        if (equal(a, ((const Add*)r1)->a)) {
          return (a + max((((const Add*)r1)->b + ((const Add*)r0)->b), 0));
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return (a + max((((const Add*)r0)->b - ((const Sub*)r1)->b), 0));
        }
      }
      if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return (a + max((((const Add*)r0)->a - ((const Sub*)r1)->b), 0));
        }
      }
    }
    if ((r0 = a.as<Mul>())) {
      if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
        if (is_const_v(((const Div*)r1)->b)) {
          if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
            if ((r2 = b.as<Add>())) {
              if ((r3 = ((const Add*)r2)->a.as<Mul>())) {
                if ((r4 = ((const Mul*)r3)->a.as<Div>())) {
                  if (equal(((const Div*)r1)->a, ((const Div*)r4)->a)) {
                    if (is_const_v(((const Div*)r4)->b)) {
                      if (equal(((const Div*)r4)->b, ((const Mul*)r3)->b)) {
                        if (is_const_v(((const Add*)r2)->b)) {
                          if (evaluate_predicate(fold((((((const Add*)r2)->b >= ((const Div*)r4)->b) && (((const Div*)r4)->b > 0)) && (((const Div*)r1)->b != 0))))) {
                            return (((((const Div*)r1)->a / ((const Div*)r4)->b) * ((const Div*)r4)->b) + ((const Add*)r2)->b);
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
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
                if (equal(((const Add*)r2)->a, b)) {
                  if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= (((const Div*)r1)->b - 1)))))) {
                    return (((((const Add*)r2)->a + ((const Add*)r2)->b) / ((const Div*)r1)->b) * ((const Div*)r1)->b);
                  }
                  if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b <= 0))))) {
                    return ((const Add*)r2)->a;
                  }
                }
                if ((r3 = b.as<Add>())) {
                  if (equal(((const Add*)r2)->a, ((const Add*)r3)->a)) {
                    if (is_const_v(((const Add*)r3)->b)) {
                      if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && ((((const Add*)r2)->b + 1) >= (((const Div*)r1)->b + ((const Add*)r3)->b)))))) {
                        return (((((const Add*)r2)->a + ((const Add*)r2)->b) / ((const Div*)r1)->b) * ((const Div*)r1)->b);
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Mul*)r0)->a.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if (is_const_v(((const Mul*)r0)->b)) {
              if ((r3 = b.as<Add>())) {
                if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
                  if (equal(((const Mul*)r2)->a, ((const Mul*)r4)->a)) {
                    if (is_const_v(((const Mul*)r4)->b)) {
                      if (evaluate_predicate(fold(((((const Mul*)r2)->b * ((const Mul*)r0)->b) == ((const Mul*)r4)->b)))) {
                        return (max((((const Add*)r1)->b * ((const Mul*)r0)->b), ((const Add*)r3)->b) + (((const Mul*)r2)->a * ((const Mul*)r4)->b));
                      }
                    }
                  }
                }
                if ((r4 = ((const Add*)r3)->b.as<Mul>())) {
                  if (equal(((const Mul*)r2)->a, ((const Mul*)r4)->a)) {
                    if (is_const_v(((const Mul*)r4)->b)) {
                      if (evaluate_predicate(fold(((((const Mul*)r2)->b * ((const Mul*)r0)->b) == ((const Mul*)r4)->b)))) {
                        return (max((((const Add*)r1)->b * ((const Mul*)r0)->b), ((const Add*)r3)->a) + (((const Mul*)r2)->a * ((const Mul*)r4)->b));
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if (is_const_v(((const Mul*)r0)->b)) {
              if ((r3 = b.as<Add>())) {
                if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
                  if (equal(((const Mul*)r2)->a, ((const Mul*)r4)->a)) {
                    if (is_const_v(((const Mul*)r4)->b)) {
                      if (evaluate_predicate(fold(((((const Mul*)r2)->b * ((const Mul*)r0)->b) == ((const Mul*)r4)->b)))) {
                        return (max((((const Add*)r1)->a * ((const Mul*)r0)->b), ((const Add*)r3)->b) + (((const Mul*)r2)->a * ((const Mul*)r4)->b));
                      }
                    }
                  }
                }
                if ((r4 = ((const Add*)r3)->b.as<Mul>())) {
                  if (equal(((const Mul*)r2)->a, ((const Mul*)r4)->a)) {
                    if (is_const_v(((const Mul*)r4)->b)) {
                      if (evaluate_predicate(fold(((((const Mul*)r2)->b * ((const Mul*)r0)->b) == ((const Mul*)r4)->b)))) {
                        return (max((((const Add*)r1)->a * ((const Mul*)r0)->b), ((const Add*)r3)->a) + (((const Mul*)r2)->a * ((const Mul*)r4)->b));
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (is_const_v(((const Mul*)r0)->b)) {
        if (is_const_v(b)) {
          if (evaluate_predicate(fold(((((const Mul*)r0)->b > 0) && ((b % ((const Mul*)r0)->b) == 0))))) {
            return (max(((const Mul*)r0)->a, fold((b / ((const Mul*)r0)->b))) * ((const Mul*)r0)->b);
          }
          if (evaluate_predicate(fold(((((const Mul*)r0)->b < 0) && ((b % ((const Mul*)r0)->b) == 0))))) {
            return (min(((const Mul*)r0)->a, fold((b / ((const Mul*)r0)->b))) * ((const Mul*)r0)->b);
          }
        }
        if ((r1 = b.as<Mul>())) {
          if (is_const_v(((const Mul*)r1)->b)) {
            if (evaluate_predicate(fold(((((const Mul*)r0)->b > 0) && ((((const Mul*)r1)->b % ((const Mul*)r0)->b) == 0))))) {
              return (max(((const Mul*)r0)->a, (((const Mul*)r1)->a * fold((((const Mul*)r1)->b / ((const Mul*)r0)->b)))) * ((const Mul*)r0)->b);
            }
            if (evaluate_predicate(fold(((((const Mul*)r0)->b < 0) && ((((const Mul*)r1)->b % ((const Mul*)r0)->b) == 0))))) {
              return (min(((const Mul*)r0)->a, (((const Mul*)r1)->a * fold((((const Mul*)r1)->b / ((const Mul*)r0)->b)))) * ((const Mul*)r0)->b);
            }
            if (evaluate_predicate(fold(((((const Mul*)r1)->b > 0) && ((((const Mul*)r0)->b % ((const Mul*)r1)->b) == 0))))) {
              return (max((((const Mul*)r0)->a * fold((((const Mul*)r0)->b / ((const Mul*)r1)->b))), ((const Mul*)r1)->a) * ((const Mul*)r1)->b);
            }
            if (evaluate_predicate(fold(((((const Mul*)r1)->b < 0) && ((((const Mul*)r0)->b % ((const Mul*)r1)->b) == 0))))) {
              return (min((((const Mul*)r0)->a * fold((((const Mul*)r0)->b / ((const Mul*)r1)->b))), ((const Mul*)r1)->a) * ((const Mul*)r1)->b);
            }
          }
        }
        if ((r1 = b.as<Add>())) {
          if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
            if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->b)) {
              if (is_const_v(((const Add*)r1)->b)) {
                if (evaluate_predicate(fold(((((const Mul*)r0)->b > 0) && ((((const Add*)r1)->b % ((const Mul*)r0)->b) == 0))))) {
                  return (max(((const Mul*)r0)->a, (((const Mul*)r2)->a + fold((((const Add*)r1)->b / ((const Mul*)r0)->b)))) * ((const Mul*)r0)->b);
                }
                if (evaluate_predicate(fold(((((const Mul*)r0)->b < 0) && ((((const Add*)r1)->b % ((const Mul*)r0)->b) == 0))))) {
                  return (min(((const Mul*)r0)->a, (((const Mul*)r2)->a + fold((((const Add*)r1)->b / ((const Mul*)r0)->b)))) * ((const Mul*)r0)->b);
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = b.as<Mul>())) {
      if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Div*)r1)->b)) {
                if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
                  if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= (((const Div*)r1)->b - 1)))))) {
                    return (((a + ((const Add*)r2)->b) / ((const Div*)r1)->b) * ((const Div*)r1)->b);
                  }
                  if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b <= 0))))) {
                    return a;
                  }
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Max>())) {
      if ((r1 = b.as<Add>())) {
        if (equal(((const Max*)r0)->a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
              return max((((const Max*)r0)->a + ((const Add*)r1)->b), ((const Max*)r0)->b);
            }
            if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
              return max(((const Max*)r0)->a, ((const Max*)r0)->b);
            }
          }
        }
        if (equal(((const Max*)r0)->b, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
              return max(((const Max*)r0)->a, (((const Max*)r0)->b + ((const Add*)r1)->b));
            }
            if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
              return max(((const Max*)r0)->a, ((const Max*)r0)->b);
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->a.as<Add>())) {
        if ((r2 = b.as<Add>())) {
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
            return max((((const Add*)r1)->a + max(((const Add*)r1)->b, ((const Add*)r2)->b)), ((const Max*)r0)->b);
          }
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->b)) {
            return max((((const Add*)r1)->a + max(((const Add*)r1)->b, ((const Add*)r2)->a)), ((const Max*)r0)->b);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->a)) {
            return max((max(((const Add*)r1)->a, ((const Add*)r2)->b) + ((const Add*)r1)->b), ((const Max*)r0)->b);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->b)) {
            return max((max(((const Add*)r1)->a, ((const Add*)r2)->a) + ((const Add*)r1)->b), ((const Max*)r0)->b);
          }
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Add>())) {
        if ((r2 = b.as<Add>())) {
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
            return max((((const Add*)r1)->a + max(((const Add*)r1)->b, ((const Add*)r2)->b)), ((const Max*)r0)->a);
          }
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->b)) {
            return max((((const Add*)r1)->a + max(((const Add*)r1)->b, ((const Add*)r2)->a)), ((const Max*)r0)->a);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->a)) {
            return max((max(((const Add*)r1)->a, ((const Add*)r2)->b) + ((const Add*)r1)->b), ((const Max*)r0)->a);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->b)) {
            return max((max(((const Add*)r1)->a, ((const Add*)r2)->a) + ((const Add*)r1)->b), ((const Max*)r0)->a);
          }
        }
      }
    }
    if ((r0 = a.as<Sub>())) {
      if ((r1 = b.as<Sub>())) {
        if (equal(((const Sub*)r0)->b, ((const Sub*)r1)->b)) {
          return (max(((const Sub*)r0)->a, ((const Sub*)r1)->a) - ((const Sub*)r0)->b);
        }
        if (equal(((const Sub*)r0)->a, ((const Sub*)r1)->a)) {
          return (((const Sub*)r0)->a - min(((const Sub*)r0)->b, ((const Sub*)r1)->b));
        }
      }
      if ((r1 = b.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Sub>())) {
          if (equal(((const Sub*)r0)->b, ((const Sub*)r2)->b)) {
            return (max(((const Sub*)r0)->a, (((const Sub*)r2)->a + ((const Add*)r1)->b)) - ((const Sub*)r0)->b);
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Sub>())) {
          if (equal(((const Sub*)r0)->b, ((const Sub*)r2)->b)) {
            return (max(((const Sub*)r0)->a, (((const Add*)r1)->a + ((const Sub*)r2)->a)) - ((const Sub*)r0)->b);
          }
        }
      }
      if (equal(((const Sub*)r0)->a, b)) {
        return (((const Sub*)r0)->a - min(((const Sub*)r0)->b, 0));
      }
      if ((r1 = ((const Sub*)r0)->a.as<Sub>())) {
        if (equal(((const Sub*)r1)->a, b)) {
          return (((const Sub*)r1)->a - min((((const Sub*)r1)->b + ((const Sub*)r0)->b), 0));
        }
      }
      if (is_const_v(((const Sub*)r0)->a)) {
        if (is_const_v(b)) {
          return (((const Sub*)r0)->a - min(((const Sub*)r0)->b, fold((((const Sub*)r0)->a - b))));
        }
      }
    }
    if ((r0 = b.as<Sub>())) {
      if (equal(a, ((const Sub*)r0)->a)) {
        return (a - min(((const Sub*)r0)->b, 0));
      }
      if ((r1 = ((const Sub*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return (a - min((((const Sub*)r1)->b + ((const Sub*)r0)->b), 0));
        }
      }
    }
    if ((r0 = a.as<Div>())) {
      if (is_const_v(((const Div*)r0)->b)) {
        if ((r1 = b.as<Div>())) {
          if (equal(((const Div*)r0)->b, ((const Div*)r1)->b)) {
            if (evaluate_predicate(fold((((const Div*)r0)->b > 0)))) {
              return (max(((const Div*)r0)->a, ((const Div*)r1)->a) / ((const Div*)r0)->b);
            }
            if (evaluate_predicate(fold((((const Div*)r0)->b < 0)))) {
              return (min(((const Div*)r0)->a, ((const Div*)r1)->a) / ((const Div*)r0)->b);
            }
          }
        }
        if (is_const_v(b)) {
          if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && !(overflows((b * ((const Div*)r0)->b))))))) {
            return (max(((const Div*)r0)->a, fold((b * ((const Div*)r0)->b))) / ((const Div*)r0)->b);
          }
          if (evaluate_predicate(fold(((((const Div*)r0)->b < 0) && !(overflows((b * ((const Div*)r0)->b))))))) {
            return (min(((const Div*)r0)->a, fold((b * ((const Div*)r0)->b))) / ((const Div*)r0)->b);
          }
        }
        if ((r1 = b.as<Add>())) {
          if ((r2 = ((const Add*)r1)->a.as<Div>())) {
            if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
              if (is_const_v(((const Add*)r1)->b)) {
                if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && !(overflows((((const Add*)r1)->b * ((const Div*)r0)->b))))))) {
                  return (max(((const Div*)r0)->a, (((const Div*)r2)->a + fold((((const Add*)r1)->b * ((const Div*)r0)->b)))) / ((const Div*)r0)->b);
                }
                if (evaluate_predicate(fold(((((const Div*)r0)->b < 0) && !(overflows((((const Add*)r1)->b * ((const Div*)r0)->b))))))) {
                  return (min(((const Div*)r0)->a, (((const Div*)r2)->a + fold((((const Add*)r1)->b * ((const Div*)r0)->b)))) / ((const Div*)r0)->b);
                }
              }
            }
          }
        }
        if ((r1 = b.as<Mul>())) {
          if ((r2 = ((const Mul*)r1)->a.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r0)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (is_const_v(((const Div*)r2)->b)) {
                    if (is_const_v(((const Mul*)r1)->b)) {
                      if (evaluate_predicate(fold(((((((const Add*)r3)->b <= 0) && (((const Div*)r0)->b > 0)) && (((const Div*)r2)->b > 0)) && ((((const Div*)r0)->b * ((const Mul*)r1)->b) == ((const Div*)r2)->b))))) {
                        return (((const Div*)r0)->a / ((const Div*)r0)->b);
                      }
                      if (evaluate_predicate(fold((((((((const Div*)r2)->b - ((const Div*)r0)->b) <= ((const Add*)r3)->b) && (((const Div*)r0)->b > 0)) && (((const Div*)r2)->b > 0)) && ((((const Div*)r0)->b * ((const Mul*)r1)->b) == ((const Div*)r2)->b))))) {
                        return (((((const Div*)r0)->a + ((const Add*)r3)->b) / ((const Div*)r2)->b) * ((const Mul*)r1)->b);
                      }
                    }
                  }
                }
              }
            }
            if (equal(((const Div*)r0)->a, ((const Div*)r2)->a)) {
              if (is_const_v(((const Div*)r2)->b)) {
                if (is_const_v(((const Mul*)r1)->b)) {
                  if (evaluate_predicate(fold((((((const Div*)r0)->b > 0) && (((const Div*)r2)->b > 0)) && ((((const Div*)r0)->b * ((const Mul*)r1)->b) == ((const Div*)r2)->b))))) {
                    return (((const Div*)r0)->a / ((const Div*)r0)->b);
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Div*)r0)->a.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if ((r2 = b.as<Mul>())) {
              if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r1)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (is_const_v(((const Div*)r3)->b)) {
                        if (is_const_v(((const Mul*)r2)->b)) {
                          if (evaluate_predicate(fold(((((((const Add*)r4)->b <= ((const Add*)r1)->b) && (((const Div*)r0)->b > 0)) && (((const Div*)r3)->b > 0)) && ((((const Div*)r0)->b * ((const Mul*)r2)->b) == ((const Div*)r3)->b))))) {
                            return ((((const Add*)r1)->a + ((const Add*)r1)->b) / ((const Div*)r0)->b);
                          }
                          if (evaluate_predicate(fold(((((((((const Add*)r1)->b + ((const Div*)r3)->b) - ((const Div*)r0)->b) <= ((const Add*)r4)->b) && (((const Div*)r0)->b > 0)) && (((const Div*)r3)->b > 0)) && ((((const Div*)r0)->b * ((const Mul*)r2)->b) == ((const Div*)r3)->b))))) {
                            return (((((const Add*)r1)->a + ((const Add*)r4)->b) / ((const Div*)r3)->b) * ((const Mul*)r2)->b);
                          }
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r1)->a, ((const Div*)r3)->a)) {
                  if (is_const_v(((const Div*)r3)->b)) {
                    if (is_const_v(((const Mul*)r2)->b)) {
                      if (evaluate_predicate(fold(((((0 <= ((const Add*)r1)->b) && (((const Div*)r0)->b > 0)) && (((const Div*)r3)->b > 0)) && ((((const Div*)r0)->b * ((const Mul*)r2)->b) == ((const Div*)r3)->b))))) {
                        return ((((const Add*)r1)->a + ((const Add*)r1)->b) / ((const Div*)r0)->b);
                      }
                      if (evaluate_predicate(fold(((((((((const Add*)r1)->b + ((const Div*)r3)->b) - ((const Div*)r0)->b) <= 0) && (((const Div*)r0)->b > 0)) && (((const Div*)r3)->b > 0)) && ((((const Div*)r0)->b * ((const Mul*)r2)->b) == ((const Div*)r3)->b))))) {
                        return ((((const Add*)r1)->a / ((const Div*)r3)->b) * ((const Mul*)r2)->b);
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
  }
  if (type.is_no_overflow_int()) {
    if ((r0 = a.as<Min>())) {
      if ((r1 = ((const Min*)r0)->a.as<Sub>())) {
        if (is_const_v(((const Sub*)r1)->a)) {
          if (equal(((const Sub*)r1)->b, ((const Min*)r0)->b)) {
            if (is_const_v(b)) {
              if (evaluate_predicate(fold(((2 * b) >= (((const Sub*)r1)->a - 1))))) {
                return b;
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Sub>())) {
        if (is_const_v(((const Sub*)r1)->a)) {
          if (equal(((const Min*)r0)->a, ((const Sub*)r1)->b)) {
            if (is_const_v(b)) {
              if (evaluate_predicate(fold(((2 * b) >= (((const Sub*)r1)->a - 1))))) {
                return b;
              }
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<Broadcast>())) {
    if ((r1 = b.as<Broadcast>())) {
      return broadcast(max(((const Broadcast*)r0)->value, ((const Broadcast*)r1)->value), c0);
    }
  }
  if ((r0 = b.as<Select>())) {
    if ((r1 = ((const Select*)r0)->condition.as<EQ>())) {
      if (equal(a, ((const EQ*)r1)->a)) {
        if (is_const_v(((const EQ*)r1)->b)) {
          if (is_const_v(((const Select*)r0)->true_value)) {
            if (equal(a, ((const Select*)r0)->false_value)) {
              if (evaluate_predicate(fold((((const EQ*)r1)->b < ((const Select*)r0)->true_value)))) {
                return select((a == ((const EQ*)r1)->b), ((const Select*)r0)->true_value, a);
              }
              if (evaluate_predicate(fold((((const Select*)r0)->true_value <= ((const EQ*)r1)->b)))) {
                return a;
              }
            }
          }
        }
      }
    }
    if ((r1 = ((const Select*)r0)->true_value.as<Min>())) {
      if (equal(a, ((const Min*)r1)->b)) {
        return select(((const Select*)r0)->condition, a, max(a, ((const Select*)r0)->false_value));
      }
      if (equal(a, ((const Min*)r1)->a)) {
        return select(((const Select*)r0)->condition, a, max(a, ((const Select*)r0)->false_value));
      }
    }
    if ((r1 = ((const Select*)r0)->false_value.as<Min>())) {
      if (equal(a, ((const Min*)r1)->b)) {
        return select(((const Select*)r0)->condition, max(a, ((const Select*)r0)->true_value), a);
      }
      if (equal(a, ((const Min*)r1)->a)) {
        return select(((const Select*)r0)->condition, max(a, ((const Select*)r0)->true_value), a);
      }
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
