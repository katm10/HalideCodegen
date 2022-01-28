#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr Simplify_LT(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  const BaseExprNode *r0 = nullptr;
  const BaseExprNode *r1 = nullptr;
  const BaseExprNode *r2 = nullptr;
  const BaseExprNode *r3 = nullptr;
  const BaseExprNode *r4 = nullptr;
  if (is_const_v(a)) {
    if (is_const_v(b)) {
      return fold((a < b));
    }
    if ((r0 = b.as<Mod>())) {
      if (is_const_v(((const Mod*)r0)->b)) {
        if (evaluate_predicate(fold((((a + 2) == ((const Mod*)r0)->b) && (((const Mod*)r0)->b > 0))))) {
          return ((((const Mod*)r0)->a % ((const Mod*)r0)->b) == fold((((const Mod*)r0)->b - 1)));
        }
      }
    }
    if ((r0 = b.as<Mul>())) {
      if (is_const_v(((const Mul*)r0)->b)) {
        if (evaluate_predicate(fold((((const Mul*)r0)->b > 0)))) {
          return (fold((a / ((const Mul*)r0)->b)) < ((const Mul*)r0)->a);
        }
      }
    }
  }
  if (equal(a, b)) {
    return false;
  }
  if ((r0 = a.as<Max>())) {
    if (equal(((const Max*)r0)->a, b)) {
      return false;
    }
    if (equal(((const Max*)r0)->b, b)) {
      return false;
    }
    if ((r1 = b.as<Min>())) {
      if (equal(((const Max*)r0)->a, ((const Min*)r1)->b)) {
        return false;
      }
      if (equal(((const Max*)r0)->a, ((const Min*)r1)->a)) {
        return false;
      }
      if (equal(((const Max*)r0)->b, ((const Min*)r1)->b)) {
        return false;
      }
      if (equal(((const Max*)r0)->b, ((const Min*)r1)->a)) {
        return false;
      }
    }
  }
  if ((r0 = b.as<Min>())) {
    if (equal(a, ((const Min*)r0)->a)) {
      return false;
    }
    if (equal(a, ((const Min*)r0)->b)) {
      return false;
    }
  }
  if (type.is_operand_no_overflow()) {
    if ((r0 = a.as<Ramp>())) {
      if (is_const_v(((const Ramp*)r0)->stride)) {
        if (is_const_v(((const Ramp*)r0)->lanes)) {
          if ((r1 = b.as<Broadcast>())) {
            if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
              if (evaluate_predicate(fold(can_prove(((((const Ramp*)r0)->base + fold(max(0, (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))))) < ((const Broadcast*)r1)->value), simplifier)))) {
                return true;
              }
              if (evaluate_predicate(fold(can_prove(((((const Ramp*)r0)->base + fold(min(0, (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))))) >= ((const Broadcast*)r1)->value), simplifier)))) {
                return false;
              }
            }
          }
        }
      }
      if (is_const_v(((const Ramp*)r0)->lanes)) {
        if ((r1 = b.as<Ramp>())) {
          if (equal(((const Ramp*)r0)->stride, ((const Ramp*)r1)->stride)) {
            if (equal(((const Ramp*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
              return broadcast((((const Ramp*)r0)->base < ((const Ramp*)r1)->base), ((const Ramp*)r0)->lanes);
            }
          }
          if (equal(((const Ramp*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
            return (ramp((((const Ramp*)r0)->base - ((const Ramp*)r1)->base), (((const Ramp*)r0)->stride - ((const Ramp*)r1)->stride), ((const Ramp*)r0)->lanes) < 0);
          }
        }
        if ((r1 = b.as<Broadcast>())) {
          if ((r2 = ((const Broadcast*)r1)->value.as<Add>())) {
            if (equal(((const Ramp*)r0)->base, ((const Add*)r2)->a)) {
              if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
                return (ramp(0, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast(((const Add*)r2)->b, ((const Ramp*)r0)->lanes));
              }
            }
            if (equal(((const Ramp*)r0)->base, ((const Add*)r2)->b)) {
              if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
                return (ramp(0, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast(((const Add*)r2)->a, ((const Ramp*)r0)->lanes));
              }
            }
          }
          if ((r2 = ((const Broadcast*)r1)->value.as<Sub>())) {
            if (equal(((const Ramp*)r0)->base, ((const Sub*)r2)->a)) {
              if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
                if (evaluate_predicate(fold(!(is_const(((const Ramp*)r0)->base, 0))))) {
                  return (ramp(0, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast((0 - ((const Sub*)r2)->b), ((const Ramp*)r0)->lanes));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Ramp*)r0)->base.as<Add>())) {
        if (is_const_v(((const Ramp*)r0)->lanes)) {
          if ((r2 = b.as<Broadcast>())) {
            if ((r3 = ((const Broadcast*)r2)->value.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                  return (ramp(((const Add*)r1)->b, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast(((const Add*)r3)->b, ((const Ramp*)r0)->lanes));
                }
              }
              if (equal(((const Add*)r1)->b, ((const Add*)r3)->a)) {
                if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                  return (ramp(((const Add*)r1)->a, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast(((const Add*)r3)->b, ((const Ramp*)r0)->lanes));
                }
              }
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->b)) {
                if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                  return (ramp(((const Add*)r1)->b, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast(((const Add*)r3)->a, ((const Ramp*)r0)->lanes));
                }
              }
              if (equal(((const Add*)r1)->b, ((const Add*)r3)->b)) {
                if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                  return (ramp(((const Add*)r1)->a, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast(((const Add*)r3)->a, ((const Ramp*)r0)->lanes));
                }
              }
            }
            if (equal(((const Add*)r1)->a, ((const Broadcast*)r2)->value)) {
              if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                return (ramp(((const Add*)r1)->b, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < 0);
              }
            }
            if (equal(((const Add*)r1)->b, ((const Broadcast*)r2)->value)) {
              if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                return (ramp(((const Add*)r1)->a, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < 0);
              }
            }
          }
        }
      }
      if ((r1 = ((const Ramp*)r0)->base.as<Sub>())) {
        if (is_const_v(((const Ramp*)r0)->lanes)) {
          if ((r2 = b.as<Broadcast>())) {
            if ((r3 = ((const Broadcast*)r2)->value.as<Sub>())) {
              if (equal(((const Sub*)r1)->a, ((const Sub*)r3)->a)) {
                if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(((const Sub*)r1)->a, 0))))) {
                    return (ramp((0 - ((const Sub*)r1)->b), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast((0 - ((const Sub*)r3)->b), ((const Ramp*)r0)->lanes));
                  }
                }
              }
              if (equal(((const Sub*)r1)->b, ((const Sub*)r3)->b)) {
                if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                  return (ramp(((const Sub*)r1)->a, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < broadcast(((const Sub*)r3)->a, ((const Ramp*)r0)->lanes));
                }
              }
            }
            if (equal(((const Sub*)r1)->a, ((const Broadcast*)r2)->value)) {
              if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                if (evaluate_predicate(fold(!(is_const(((const Sub*)r1)->a, 0))))) {
                  return (ramp((0 - ((const Sub*)r1)->b), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes) < 0);
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
          if (is_const_v(((const Ramp*)r1)->stride)) {
            if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
              if (evaluate_predicate(fold(can_prove((((const Broadcast*)r0)->value < (((const Ramp*)r1)->base + fold(min(0, (((const Ramp*)r1)->stride * (((const Broadcast*)r0)->lanes - 1)))))), simplifier)))) {
                return true;
              }
              if (evaluate_predicate(fold(can_prove((((const Broadcast*)r0)->value >= (((const Ramp*)r1)->base + fold(max(0, (((const Ramp*)r1)->stride * (((const Broadcast*)r0)->lanes - 1)))))), simplifier)))) {
                return false;
              }
            }
          }
          if ((r2 = ((const Ramp*)r1)->base.as<Add>())) {
            if (equal(((const Broadcast*)r0)->value, ((const Add*)r2)->a)) {
              if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
                return (0 < ramp(((const Add*)r2)->b, ((const Ramp*)r1)->stride, ((const Broadcast*)r0)->lanes));
              }
            }
            if (equal(((const Broadcast*)r0)->value, ((const Add*)r2)->b)) {
              if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
                return (0 < ramp(((const Add*)r2)->a, ((const Ramp*)r1)->stride, ((const Broadcast*)r0)->lanes));
              }
            }
          }
          if ((r2 = ((const Ramp*)r1)->base.as<Sub>())) {
            if (equal(((const Broadcast*)r0)->value, ((const Sub*)r2)->a)) {
              if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r1)->lanes)) {
                if (evaluate_predicate(fold(!(is_const(((const Broadcast*)r0)->value, 0))))) {
                  return (0 < ramp((0 - ((const Sub*)r2)->b), ((const Ramp*)r1)->stride, ((const Broadcast*)r0)->lanes));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Broadcast*)r0)->value.as<Add>())) {
        if (is_const_v(((const Broadcast*)r0)->lanes)) {
          if ((r2 = b.as<Ramp>())) {
            if ((r3 = ((const Ramp*)r2)->base.as<Add>())) {
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                  return (broadcast(((const Add*)r1)->b, ((const Broadcast*)r0)->lanes) < ramp(((const Add*)r3)->b, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
                }
              }
              if (equal(((const Add*)r1)->a, ((const Add*)r3)->b)) {
                if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                  return (broadcast(((const Add*)r1)->b, ((const Broadcast*)r0)->lanes) < ramp(((const Add*)r3)->a, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
                }
              }
              if (equal(((const Add*)r1)->b, ((const Add*)r3)->a)) {
                if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                  return (broadcast(((const Add*)r1)->a, ((const Broadcast*)r0)->lanes) < ramp(((const Add*)r3)->b, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
                }
              }
              if (equal(((const Add*)r1)->b, ((const Add*)r3)->b)) {
                if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                  return (broadcast(((const Add*)r1)->a, ((const Broadcast*)r0)->lanes) < ramp(((const Add*)r3)->a, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
                }
              }
            }
            if (equal(((const Add*)r1)->a, ((const Ramp*)r2)->base)) {
              if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                return (broadcast(((const Add*)r1)->b, ((const Broadcast*)r0)->lanes) < ramp(0, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
              }
            }
            if (equal(((const Add*)r1)->b, ((const Ramp*)r2)->base)) {
              if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                return (broadcast(((const Add*)r1)->a, ((const Broadcast*)r0)->lanes) < ramp(0, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
              }
            }
          }
        }
      }
      if ((r1 = ((const Broadcast*)r0)->value.as<Sub>())) {
        if (is_const_v(((const Broadcast*)r0)->lanes)) {
          if ((r2 = b.as<Ramp>())) {
            if ((r3 = ((const Ramp*)r2)->base.as<Sub>())) {
              if (equal(((const Sub*)r1)->a, ((const Sub*)r3)->a)) {
                if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(((const Sub*)r1)->a, 0))))) {
                    return (broadcast((0 - ((const Sub*)r1)->b), ((const Broadcast*)r0)->lanes) < ramp((0 - ((const Sub*)r3)->b), ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
                  }
                }
              }
              if (equal(((const Sub*)r1)->b, ((const Sub*)r3)->b)) {
                if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                  return (broadcast(((const Sub*)r1)->a, ((const Broadcast*)r0)->lanes) < ramp(((const Sub*)r3)->a, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
                }
              }
            }
            if (equal(((const Sub*)r1)->a, ((const Ramp*)r2)->base)) {
              if (equal(((const Broadcast*)r0)->lanes, ((const Ramp*)r2)->lanes)) {
                if (evaluate_predicate(fold(!(is_const(((const Sub*)r1)->a, 0))))) {
                  return (broadcast((0 - ((const Sub*)r1)->b), ((const Broadcast*)r0)->lanes) < ramp(0, ((const Ramp*)r2)->stride, ((const Broadcast*)r0)->lanes));
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Add>())) {
      if (is_const_v(((const Add*)r0)->b)) {
        return (((const Add*)r0)->a < (b + fold((0 - ((const Add*)r0)->b))));
      }
      if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
        return ((((const Sub*)r1)->a + ((const Add*)r0)->b) < (((const Sub*)r1)->b + b));
      }
      if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
        return ((((const Sub*)r1)->a + ((const Add*)r0)->a) < (((const Sub*)r1)->b + b));
      }
      if ((r1 = ((const Add*)r0)->a.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Sub>())) {
          return (((((const Sub*)r2)->a + ((const Add*)r1)->b) + ((const Add*)r0)->b) < (b + ((const Sub*)r2)->b));
        }
        if ((r2 = ((const Add*)r1)->b.as<Sub>())) {
          return (((((const Sub*)r2)->a + ((const Add*)r1)->a) + ((const Add*)r0)->b) < (b + ((const Sub*)r2)->b));
        }
        if (equal(((const Add*)r1)->a, b)) {
          return ((((const Add*)r1)->b + ((const Add*)r0)->b) < 0);
        }
        if (equal(((const Add*)r1)->b, b)) {
          return ((((const Add*)r1)->a + ((const Add*)r0)->b) < 0);
        }
        if ((r2 = b.as<Add>())) {
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
            return ((((const Add*)r1)->b + ((const Add*)r0)->b) < ((const Add*)r2)->b);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->a)) {
            return ((((const Add*)r1)->a + ((const Add*)r0)->b) < ((const Add*)r2)->b);
          }
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->b)) {
            return ((((const Add*)r1)->b + ((const Add*)r0)->b) < ((const Add*)r2)->a);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->b)) {
            return ((((const Add*)r1)->a + ((const Add*)r0)->b) < ((const Add*)r2)->a);
          }
          if ((r3 = ((const Add*)r2)->a.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->b) < (((const Add*)r3)->b + ((const Add*)r2)->b));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->b) < (((const Add*)r3)->b + ((const Add*)r2)->b));
            }
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->b) < (((const Add*)r3)->a + ((const Add*)r2)->b));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->b) < (((const Add*)r3)->a + ((const Add*)r2)->b));
            }
          }
          if ((r3 = ((const Add*)r2)->b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->b) < (((const Add*)r3)->b + ((const Add*)r2)->a));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->b) < (((const Add*)r3)->b + ((const Add*)r2)->a));
            }
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->b) < (((const Add*)r3)->a + ((const Add*)r2)->a));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->b) < (((const Add*)r3)->a + ((const Add*)r2)->a));
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->b.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Sub>())) {
          return (((((const Sub*)r2)->a + ((const Add*)r1)->b) + ((const Add*)r0)->a) < (b + ((const Sub*)r2)->b));
        }
        if ((r2 = ((const Add*)r1)->b.as<Sub>())) {
          return (((((const Sub*)r2)->a + ((const Add*)r1)->a) + ((const Add*)r0)->a) < (b + ((const Sub*)r2)->b));
        }
        if (equal(((const Add*)r1)->a, b)) {
          return ((((const Add*)r0)->a + ((const Add*)r1)->b) < 0);
        }
        if (equal(((const Add*)r1)->b, b)) {
          return ((((const Add*)r0)->a + ((const Add*)r1)->a) < 0);
        }
        if ((r2 = b.as<Add>())) {
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
            return ((((const Add*)r1)->b + ((const Add*)r0)->a) < ((const Add*)r2)->b);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->a)) {
            return ((((const Add*)r1)->a + ((const Add*)r0)->a) < ((const Add*)r2)->b);
          }
          if (equal(((const Add*)r1)->a, ((const Add*)r2)->b)) {
            return ((((const Add*)r1)->b + ((const Add*)r0)->a) < ((const Add*)r2)->a);
          }
          if (equal(((const Add*)r1)->b, ((const Add*)r2)->b)) {
            return ((((const Add*)r1)->a + ((const Add*)r0)->a) < ((const Add*)r2)->a);
          }
          if ((r3 = ((const Add*)r2)->a.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->a) < (((const Add*)r3)->b + ((const Add*)r2)->b));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->a) < (((const Add*)r3)->b + ((const Add*)r2)->b));
            }
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->a) < (((const Add*)r3)->a + ((const Add*)r2)->b));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->a) < (((const Add*)r3)->a + ((const Add*)r2)->b));
            }
          }
          if ((r3 = ((const Add*)r2)->b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->a) < (((const Add*)r3)->b + ((const Add*)r2)->a));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->a)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->a) < (((const Add*)r3)->b + ((const Add*)r2)->a));
            }
            if (equal(((const Add*)r1)->a, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->b + ((const Add*)r0)->a) < (((const Add*)r3)->a + ((const Add*)r2)->a));
            }
            if (equal(((const Add*)r1)->b, ((const Add*)r3)->b)) {
              return ((((const Add*)r1)->a + ((const Add*)r0)->a) < (((const Add*)r3)->a + ((const Add*)r2)->a));
            }
          }
        }
      }
      if (equal(((const Add*)r0)->a, b)) {
        return (((const Add*)r0)->b < 0);
      }
      if (equal(((const Add*)r0)->b, b)) {
        return (((const Add*)r0)->a < 0);
      }
      if ((r1 = b.as<Add>())) {
        if (equal(((const Add*)r0)->a, ((const Add*)r1)->a)) {
          return (((const Add*)r0)->b < ((const Add*)r1)->b);
        }
        if (equal(((const Add*)r0)->a, ((const Add*)r1)->b)) {
          return (((const Add*)r0)->b < ((const Add*)r1)->a);
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r1)->a)) {
          return (((const Add*)r0)->a < ((const Add*)r1)->b);
        }
        if (equal(((const Add*)r0)->b, ((const Add*)r1)->b)) {
          return (((const Add*)r0)->a < ((const Add*)r1)->a);
        }
        if ((r2 = ((const Add*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r0)->a, ((const Add*)r2)->a)) {
            return (((const Add*)r0)->b < (((const Add*)r2)->b + ((const Add*)r1)->b));
          }
          if (equal(((const Add*)r0)->a, ((const Add*)r2)->b)) {
            return (((const Add*)r0)->b < (((const Add*)r2)->a + ((const Add*)r1)->b));
          }
          if (equal(((const Add*)r0)->b, ((const Add*)r2)->a)) {
            return (((const Add*)r0)->a < (((const Add*)r2)->b + ((const Add*)r1)->b));
          }
          if (equal(((const Add*)r0)->b, ((const Add*)r2)->b)) {
            return (((const Add*)r0)->a < (((const Add*)r2)->a + ((const Add*)r1)->b));
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Add>())) {
          if (equal(((const Add*)r0)->a, ((const Add*)r2)->a)) {
            return (((const Add*)r0)->b < (((const Add*)r2)->b + ((const Add*)r1)->a));
          }
          if (equal(((const Add*)r0)->a, ((const Add*)r2)->b)) {
            return (((const Add*)r0)->b < (((const Add*)r2)->a + ((const Add*)r1)->a));
          }
          if (equal(((const Add*)r0)->b, ((const Add*)r2)->a)) {
            return (((const Add*)r0)->a < (((const Add*)r2)->b + ((const Add*)r1)->a));
          }
          if (equal(((const Add*)r0)->b, ((const Add*)r2)->b)) {
            return (((const Add*)r0)->a < (((const Add*)r2)->a + ((const Add*)r1)->a));
          }
        }
      }
    }
    if (is_const_v(a)) {
      if ((r0 = b.as<Sub>())) {
        if (is_const_v(((const Sub*)r0)->a)) {
          return (((const Sub*)r0)->b < fold((((const Sub*)r0)->a - a)));
        }
      }
      if ((r0 = b.as<Add>())) {
        if (is_const_v(((const Add*)r0)->b)) {
          return (fold((a - ((const Add*)r0)->b)) < ((const Add*)r0)->a);
        }
      }
      if ((r0 = b.as<Min>())) {
        if (is_const_v(((const Min*)r0)->b)) {
          return ((a < ((const Min*)r0)->a) && fold((a < ((const Min*)r0)->b)));
        }
      }
      if ((r0 = b.as<Max>())) {
        if (is_const_v(((const Max*)r0)->b)) {
          return ((a < ((const Max*)r0)->a) || fold((a < ((const Max*)r0)->b)));
        }
      }
      if ((r0 = b.as<Select>())) {
        if (is_const_v(((const Select*)r0)->true_value)) {
          if (is_const_v(((const Select*)r0)->false_value)) {
            return select(((const Select*)r0)->condition, fold((a < ((const Select*)r0)->true_value)), fold((a < ((const Select*)r0)->false_value)));
          }
        }
      }
    }
    if ((r0 = a.as<Sub>())) {
      return (((const Sub*)r0)->a < (b + ((const Sub*)r0)->b));
    }
    if ((r0 = b.as<Sub>())) {
      return ((a + ((const Sub*)r0)->b) < ((const Sub*)r0)->a);
    }
    if ((r0 = b.as<Add>())) {
      if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
        return ((a + ((const Sub*)r1)->b) < (((const Sub*)r1)->a + ((const Add*)r0)->b));
      }
      if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
        return ((a + ((const Sub*)r1)->b) < (((const Sub*)r1)->a + ((const Add*)r0)->a));
      }
      if ((r1 = ((const Add*)r0)->a.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Sub>())) {
          return ((a + ((const Sub*)r2)->b) < ((((const Sub*)r2)->a + ((const Add*)r1)->b) + ((const Add*)r0)->b));
        }
        if ((r2 = ((const Add*)r1)->b.as<Sub>())) {
          return ((a + ((const Sub*)r2)->b) < ((((const Sub*)r2)->a + ((const Add*)r1)->a) + ((const Add*)r0)->b));
        }
        if (equal(a, ((const Add*)r1)->a)) {
          return (0 < (((const Add*)r1)->b + ((const Add*)r0)->b));
        }
        if (equal(a, ((const Add*)r1)->b)) {
          return (0 < (((const Add*)r1)->a + ((const Add*)r0)->b));
        }
      }
      if ((r1 = ((const Add*)r0)->b.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Sub>())) {
          return ((a + ((const Sub*)r2)->b) < ((((const Sub*)r2)->a + ((const Add*)r1)->b) + ((const Add*)r0)->a));
        }
        if ((r2 = ((const Add*)r1)->b.as<Sub>())) {
          return ((a + ((const Sub*)r2)->b) < ((((const Sub*)r2)->a + ((const Add*)r1)->a) + ((const Add*)r0)->a));
        }
        if (equal(a, ((const Add*)r1)->a)) {
          return (0 < (((const Add*)r0)->a + ((const Add*)r1)->b));
        }
        if (equal(a, ((const Add*)r1)->b)) {
          return (0 < (((const Add*)r0)->a + ((const Add*)r1)->a));
        }
      }
      if (equal(a, ((const Add*)r0)->a)) {
        return (0 < ((const Add*)r0)->b);
      }
      if (equal(a, ((const Add*)r0)->b)) {
        return (0 < ((const Add*)r0)->a);
      }
      if ((r1 = ((const Add*)r0)->a.as<Min>())) {
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Add*)r0)->b)) {
                return ((a < (((const Min*)r1)->b + ((const Add*)r0)->b)) && fold((0 < (((const Add*)r2)->b + ((const Add*)r0)->b))));
              }
            }
          }
        }
        if ((r2 = ((const Min*)r1)->b.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Add*)r0)->b)) {
                return ((a < (((const Min*)r1)->a + ((const Add*)r0)->b)) && fold((0 < (((const Add*)r2)->b + ((const Add*)r0)->b))));
              }
            }
          }
        }
        if (equal(a, ((const Min*)r1)->a)) {
          if (is_const_v(((const Add*)r0)->b)) {
            return ((a < (((const Min*)r1)->b + ((const Add*)r0)->b)) && fold((0 < ((const Add*)r0)->b)));
          }
        }
        if (equal(a, ((const Min*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            return ((a < (((const Min*)r1)->a + ((const Add*)r0)->b)) && fold((0 < ((const Add*)r0)->b)));
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Max>())) {
        if ((r2 = ((const Max*)r1)->a.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Add*)r0)->b)) {
                return ((a < (((const Max*)r1)->b + ((const Add*)r0)->b)) || fold((0 < (((const Add*)r2)->b + ((const Add*)r0)->b))));
              }
            }
          }
        }
        if ((r2 = ((const Max*)r1)->b.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Add*)r0)->b)) {
                return ((a < (((const Max*)r1)->a + ((const Add*)r0)->b)) || fold((0 < (((const Add*)r2)->b + ((const Add*)r0)->b))));
              }
            }
          }
        }
        if (equal(a, ((const Max*)r1)->a)) {
          if (is_const_v(((const Add*)r0)->b)) {
            return ((a < (((const Max*)r1)->b + ((const Add*)r0)->b)) || fold((0 < ((const Add*)r0)->b)));
          }
        }
        if (equal(a, ((const Max*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            return ((a < (((const Max*)r1)->a + ((const Add*)r0)->b)) || fold((0 < ((const Add*)r0)->b)));
          }
        }
      }
      if ((r1 = ((const Add*)r0)->a.as<Select>())) {
        if ((r2 = ((const Select*)r1)->true_value.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Add*)r0)->b)) {
                if (evaluate_predicate(fold(((((const Add*)r2)->b + ((const Add*)r0)->b) <= 0)))) {
                  return (!(((const Select*)r1)->condition) && (a < (((const Select*)r1)->false_value + ((const Add*)r0)->b)));
                }
                if (evaluate_predicate(fold(((((const Add*)r2)->b + ((const Add*)r0)->b) > 0)))) {
                  return (((const Select*)r1)->condition || (a < (((const Select*)r1)->false_value + ((const Add*)r0)->b)));
                }
              }
            }
          }
        }
        if ((r2 = ((const Select*)r1)->false_value.as<Add>())) {
          if (equal(a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (is_const_v(((const Add*)r0)->b)) {
                if (evaluate_predicate(fold(((((const Add*)r2)->b + ((const Add*)r0)->b) <= 0)))) {
                  return (((const Select*)r1)->condition && (a < (((const Select*)r1)->true_value + ((const Add*)r0)->b)));
                }
                if (evaluate_predicate(fold(((((const Add*)r2)->b + ((const Add*)r0)->b) > 0)))) {
                  return (!(((const Select*)r1)->condition) || (a < (((const Select*)r1)->true_value + ((const Add*)r0)->b)));
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Mul>())) {
      if (is_const_v(((const Mul*)r0)->b)) {
        if ((r1 = b.as<Mul>())) {
          if (equal(((const Mul*)r0)->b, ((const Mul*)r1)->b)) {
            if (evaluate_predicate(fold((((const Mul*)r0)->b > 0)))) {
              return (((const Mul*)r0)->a < ((const Mul*)r1)->a);
            }
            if (evaluate_predicate(fold((((const Mul*)r0)->b < 0)))) {
              return (((const Mul*)r1)->a < ((const Mul*)r0)->a);
            }
          }
        }
      }
    }
    if ((r0 = a.as<Min>())) {
      if ((r1 = ((const Min*)r0)->a.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
              if (is_const_v(((const Add*)r2)->b)) {
                return ((((const Min*)r0)->b < (((const Add*)r1)->a + ((const Add*)r2)->b)) || fold((((const Add*)r1)->b < ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Add*)r1)->a, b)) {
            return ((((const Min*)r0)->b < ((const Add*)r1)->a) || fold((((const Add*)r1)->b < 0)));
          }
          if ((r2 = b.as<Min>())) {
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
                return (min(((const Min*)r0)->b, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Min*)r2)->a);
              }
            }
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->a)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
                return (min(((const Min*)r0)->b, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Min*)r2)->b);
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
              if (is_const_v(((const Add*)r2)->b)) {
                return ((((const Min*)r0)->a < (((const Add*)r1)->a + ((const Add*)r2)->b)) || fold((((const Add*)r1)->b < ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Add*)r1)->a, b)) {
            return ((((const Min*)r0)->a < ((const Add*)r1)->a) || fold((((const Add*)r1)->b < 0)));
          }
          if ((r2 = b.as<Min>())) {
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
                return (min(((const Min*)r0)->a, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Min*)r2)->a);
              }
            }
            if (equal(((const Add*)r1)->a, ((const Min*)r2)->a)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
                return (min(((const Min*)r0)->a, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Min*)r2)->b);
              }
            }
          }
        }
      }
      if ((r1 = b.as<Add>())) {
        if (equal(((const Min*)r0)->a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((((const Min*)r0)->b < (((const Min*)r0)->a + ((const Add*)r1)->b)) || fold((0 < ((const Add*)r1)->b)));
          }
        }
        if (equal(((const Min*)r0)->b, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((((const Min*)r0)->a < (((const Min*)r0)->b + ((const Add*)r1)->b)) || fold((0 < ((const Add*)r1)->b)));
          }
        }
      }
      if (equal(((const Min*)r0)->a, b)) {
        return (((const Min*)r0)->b < ((const Min*)r0)->a);
      }
      if (equal(((const Min*)r0)->b, b)) {
        return (((const Min*)r0)->a < ((const Min*)r0)->b);
      }
      if (is_const_v(((const Min*)r0)->b)) {
        if (is_const_v(b)) {
          return ((((const Min*)r0)->a < b) || fold((((const Min*)r0)->b < b)));
        }
      }
      if ((r1 = b.as<Min>())) {
        if (equal(((const Min*)r0)->b, ((const Min*)r1)->b)) {
          return (((const Min*)r0)->a < min(((const Min*)r1)->a, ((const Min*)r0)->b));
        }
        if (equal(((const Min*)r0)->b, ((const Min*)r1)->a)) {
          return (((const Min*)r0)->a < min(((const Min*)r0)->b, ((const Min*)r1)->b));
        }
        if ((r2 = ((const Min*)r1)->b.as<Add>())) {
          if (equal(((const Min*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b > 0)))) {
                return (min(((const Min*)r0)->a, ((const Min*)r0)->b) < ((const Min*)r1)->a);
              }
            }
          }
          if (equal(((const Min*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b > 0)))) {
                return (min(((const Min*)r0)->b, ((const Min*)r0)->a) < ((const Min*)r1)->a);
              }
            }
          }
        }
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if (equal(((const Min*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b > 0)))) {
                return (min(((const Min*)r0)->a, ((const Min*)r0)->b) < ((const Min*)r1)->b);
              }
            }
          }
          if (equal(((const Min*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b > 0)))) {
                return (min(((const Min*)r0)->b, ((const Min*)r0)->a) < ((const Min*)r1)->b);
              }
            }
          }
        }
        if (equal(((const Min*)r0)->a, ((const Min*)r1)->b)) {
          return (((const Min*)r0)->b < min(((const Min*)r1)->a, ((const Min*)r0)->a));
        }
        if (equal(((const Min*)r0)->a, ((const Min*)r1)->a)) {
          return (((const Min*)r0)->b < min(((const Min*)r0)->a, ((const Min*)r1)->b));
        }
      }
    }
    if ((r0 = a.as<Max>())) {
      if ((r1 = ((const Max*)r0)->a.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
              if (is_const_v(((const Add*)r2)->b)) {
                return ((((const Max*)r0)->b < (((const Add*)r1)->a + ((const Add*)r2)->b)) && fold((((const Add*)r1)->b < ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Add*)r1)->a, b)) {
            return ((((const Max*)r0)->b < ((const Add*)r1)->a) && fold((((const Add*)r1)->b < 0)));
          }
          if ((r2 = b.as<Max>())) {
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
                return (max(((const Max*)r0)->b, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Max*)r2)->a);
              }
            }
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->a)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
                return (max(((const Max*)r0)->b, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Max*)r2)->b);
              }
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if ((r2 = b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
              if (is_const_v(((const Add*)r2)->b)) {
                return ((((const Max*)r0)->a < (((const Add*)r1)->a + ((const Add*)r2)->b)) && fold((((const Add*)r1)->b < ((const Add*)r2)->b)));
              }
            }
          }
          if (equal(((const Add*)r1)->a, b)) {
            return ((((const Max*)r0)->a < ((const Add*)r1)->a) && fold((((const Add*)r1)->b < 0)));
          }
          if ((r2 = b.as<Max>())) {
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
                return (max(((const Max*)r0)->a, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Max*)r2)->a);
              }
            }
            if (equal(((const Add*)r1)->a, ((const Max*)r2)->a)) {
              if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
                return (max(((const Max*)r0)->a, (((const Add*)r1)->a + ((const Add*)r1)->b)) < ((const Max*)r2)->b);
              }
            }
          }
        }
      }
      if ((r1 = b.as<Add>())) {
        if (equal(((const Max*)r0)->a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((((const Max*)r0)->b < (((const Max*)r0)->a + ((const Add*)r1)->b)) && fold((0 < ((const Add*)r1)->b)));
          }
        }
        if (equal(((const Max*)r0)->b, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((((const Max*)r0)->a < (((const Max*)r0)->b + ((const Add*)r1)->b)) && fold((0 < ((const Add*)r1)->b)));
          }
        }
      }
      if (is_const_v(((const Max*)r0)->b)) {
        if (is_const_v(b)) {
          return ((((const Max*)r0)->a < b) && fold((((const Max*)r0)->b < b)));
        }
      }
      if ((r1 = b.as<Max>())) {
        if (equal(((const Max*)r0)->b, ((const Max*)r1)->b)) {
          return (max(((const Max*)r0)->a, ((const Max*)r0)->b) < ((const Max*)r1)->a);
        }
        if (equal(((const Max*)r0)->b, ((const Max*)r1)->a)) {
          return (max(((const Max*)r0)->a, ((const Max*)r0)->b) < ((const Max*)r1)->b);
        }
        if ((r2 = ((const Max*)r1)->b.as<Add>())) {
          if (equal(((const Max*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b < 0)))) {
                return (max(((const Max*)r0)->a, ((const Max*)r0)->b) < ((const Max*)r1)->a);
              }
            }
          }
          if (equal(((const Max*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b < 0)))) {
                return (max(((const Max*)r0)->b, ((const Max*)r0)->a) < ((const Max*)r1)->a);
              }
            }
          }
        }
        if ((r2 = ((const Max*)r1)->a.as<Add>())) {
          if (equal(((const Max*)r0)->b, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b < 0)))) {
                return (max(((const Max*)r0)->a, ((const Max*)r0)->b) < ((const Max*)r1)->b);
              }
            }
          }
          if (equal(((const Max*)r0)->a, ((const Add*)r2)->a)) {
            if (is_const_v(((const Add*)r2)->b)) {
              if (evaluate_predicate(fold((((const Add*)r2)->b < 0)))) {
                return (max(((const Max*)r0)->b, ((const Max*)r0)->a) < ((const Max*)r1)->b);
              }
            }
          }
        }
        if (equal(((const Max*)r0)->a, ((const Max*)r1)->b)) {
          return (max(((const Max*)r0)->b, ((const Max*)r0)->a) < ((const Max*)r1)->a);
        }
        if (equal(((const Max*)r0)->a, ((const Max*)r1)->a)) {
          return (max(((const Max*)r0)->b, ((const Max*)r0)->a) < ((const Max*)r1)->b);
        }
      }
    }
    if ((r0 = b.as<Min>())) {
      if ((r1 = ((const Min*)r0)->a.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((a < ((const Min*)r0)->b) && fold((0 < ((const Add*)r1)->b)));
          }
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((a < ((const Min*)r0)->a) && fold((0 < ((const Add*)r1)->b)));
          }
        }
      }
    }
    if ((r0 = b.as<Max>())) {
      if ((r1 = ((const Max*)r0)->a.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((a < ((const Max*)r0)->b) || fold((0 < ((const Add*)r1)->b)));
          }
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            return ((a < ((const Max*)r0)->a) || fold((0 < ((const Add*)r1)->b)));
          }
        }
      }
      if (equal(a, ((const Max*)r0)->a)) {
        return (a < ((const Max*)r0)->b);
      }
      if (equal(a, ((const Max*)r0)->b)) {
        return (a < ((const Max*)r0)->a);
      }
    }
    if ((r0 = b.as<Select>())) {
      if ((r1 = ((const Select*)r0)->true_value.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            if (evaluate_predicate(fold((((const Add*)r1)->b <= 0)))) {
              return (!(((const Select*)r0)->condition) && (a < ((const Select*)r0)->false_value));
            }
            if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
              return (((const Select*)r0)->condition || (a < ((const Select*)r0)->false_value));
            }
          }
        }
      }
      if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
        if (equal(a, ((const Add*)r1)->a)) {
          if (is_const_v(((const Add*)r1)->b)) {
            if (evaluate_predicate(fold((((const Add*)r1)->b <= 0)))) {
              return (((const Select*)r0)->condition && (a < ((const Select*)r0)->true_value));
            }
            if (evaluate_predicate(fold((((const Add*)r1)->b > 0)))) {
              return (!(((const Select*)r0)->condition) || (a < ((const Select*)r0)->true_value));
            }
          }
        }
      }
    }
    if ((r0 = a.as<Select>())) {
      if ((r1 = ((const Select*)r0)->true_value.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (equal(((const Add*)r1)->a, b)) {
            if (evaluate_predicate(fold((((const Add*)r1)->b >= 0)))) {
              return (!(((const Select*)r0)->condition) && (((const Select*)r0)->false_value < ((const Add*)r1)->a));
            }
            if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
              return (((const Select*)r0)->condition || (((const Select*)r0)->false_value < ((const Add*)r1)->a));
            }
          }
          if ((r2 = b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
              if (is_const_v(((const Add*)r2)->b)) {
                if (evaluate_predicate(fold((((const Add*)r1)->b >= ((const Add*)r2)->b)))) {
                  return (!(((const Select*)r0)->condition) && (((const Select*)r0)->false_value < (((const Add*)r1)->a + ((const Add*)r2)->b)));
                }
                if (evaluate_predicate(fold((((const Add*)r1)->b < ((const Add*)r2)->b)))) {
                  return (((const Select*)r0)->condition || (((const Select*)r0)->false_value < (((const Add*)r1)->a + ((const Add*)r2)->b)));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Select*)r0)->false_value.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (equal(((const Add*)r1)->a, b)) {
            if (evaluate_predicate(fold((((const Add*)r1)->b >= 0)))) {
              return (((const Select*)r0)->condition && (((const Select*)r0)->true_value < ((const Add*)r1)->a));
            }
            if (evaluate_predicate(fold((((const Add*)r1)->b < 0)))) {
              return (!(((const Select*)r0)->condition) || (((const Select*)r0)->true_value < ((const Add*)r1)->a));
            }
          }
          if ((r2 = b.as<Add>())) {
            if (equal(((const Add*)r1)->a, ((const Add*)r2)->a)) {
              if (is_const_v(((const Add*)r2)->b)) {
                if (evaluate_predicate(fold((((const Add*)r1)->b >= ((const Add*)r2)->b)))) {
                  return (((const Select*)r0)->condition && (((const Select*)r0)->true_value < (((const Add*)r1)->a + ((const Add*)r2)->b)));
                }
                if (evaluate_predicate(fold((((const Add*)r1)->b < ((const Add*)r2)->b)))) {
                  return (!(((const Select*)r0)->condition) || (((const Select*)r0)->true_value < (((const Add*)r1)->a + ((const Add*)r2)->b)));
                }
              }
            }
          }
        }
      }
      if (is_const_v(((const Select*)r0)->true_value)) {
        if (is_const_v(((const Select*)r0)->false_value)) {
          if (is_const_v(b)) {
            return select(((const Select*)r0)->condition, fold((((const Select*)r0)->true_value < b)), fold((((const Select*)r0)->false_value < b)));
          }
        }
      }
    }
  }
  if ((r0 = a.as<Broadcast>())) {
    if (is_const_v(((const Broadcast*)r0)->lanes)) {
      if ((r1 = b.as<Broadcast>())) {
        if (equal(((const Broadcast*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
          return broadcast((((const Broadcast*)r0)->value < ((const Broadcast*)r1)->value), ((const Broadcast*)r0)->lanes);
        }
      }
    }
  }
  if ((r0 = a.as<Mod>())) {
    if (is_const_int(b, 1)) {
      return ((((const Mod*)r0)->a % ((const Mod*)r0)->b) == 0);
    }
    if (is_const_v(((const Mod*)r0)->b)) {
      if (is_const_v(b)) {
        if (evaluate_predicate(fold((((b + 1) == ((const Mod*)r0)->b) && (((const Mod*)r0)->b > 0))))) {
          return ((((const Mod*)r0)->a % ((const Mod*)r0)->b) != fold((((const Mod*)r0)->b - 1)));
        }
      }
    }
  }
  if (is_const_int(a, 0)) {
    if ((r0 = b.as<Mod>())) {
      return ((((const Mod*)r0)->a % ((const Mod*)r0)->b) != 0);
    }
  }
  if (type.is_operand_no_overflow_int()) {
    if ((r0 = a.as<Mul>())) {
      if (is_const_v(((const Mul*)r0)->b)) {
        if (is_const_v(b)) {
          if (evaluate_predicate(fold((((const Mul*)r0)->b > 0)))) {
            return (((const Mul*)r0)->a < fold((((b + ((const Mul*)r0)->b) - 1) / ((const Mul*)r0)->b)));
          }
        }
        if ((r1 = b.as<Mul>())) {
          if (is_const_v(((const Mul*)r1)->b)) {
            if (evaluate_predicate(fold((((((const Mul*)r1)->b % ((const Mul*)r0)->b) == 0) && (((const Mul*)r0)->b > 0))))) {
              return (((const Mul*)r0)->a < (((const Mul*)r1)->a * fold((((const Mul*)r1)->b / ((const Mul*)r0)->b))));
            }
            if (evaluate_predicate(fold((((((const Mul*)r0)->b % ((const Mul*)r1)->b) == 0) && (((const Mul*)r1)->b > 0))))) {
              return ((((const Mul*)r0)->a * fold((((const Mul*)r0)->b / ((const Mul*)r1)->b))) < ((const Mul*)r1)->a);
            }
          }
        }
        if ((r1 = b.as<Add>())) {
          if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
            if (equal(((const Mul*)r0)->b, ((const Mul*)r2)->b)) {
              if (is_const_v(((const Add*)r1)->b)) {
                if (evaluate_predicate(fold((((const Mul*)r0)->b > 0)))) {
                  return (((const Mul*)r0)->a < (((const Mul*)r2)->a + fold((((((const Add*)r1)->b + ((const Mul*)r0)->b) - 1) / ((const Mul*)r0)->b))));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Mul*)r0)->a.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
                if ((r3 = b.as<Add>())) {
                  if (equal(((const Add*)r2)->a, ((const Add*)r3)->a)) {
                    if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                      return (((const Add*)r2)->b < (((((const Add*)r2)->a + ((const Add*)r2)->b) % ((const Div*)r1)->b) + ((const Add*)r3)->b));
                    }
                  }
                  if (equal(((const Add*)r2)->a, ((const Add*)r3)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                      return (((const Add*)r2)->b < (((((const Add*)r2)->a + ((const Add*)r2)->b) % ((const Div*)r1)->b) + ((const Add*)r3)->a));
                    }
                  }
                }
                if (equal(((const Add*)r2)->a, b)) {
                  if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                    return (((const Add*)r2)->b < ((((const Add*)r2)->a + ((const Add*)r2)->b) % ((const Div*)r1)->b));
                  }
                }
              }
            }
          }
        }
        if (is_const_v(((const Div*)r1)->b)) {
          if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
            if ((r2 = b.as<Add>())) {
              if (equal(((const Div*)r1)->a, ((const Add*)r2)->a)) {
                if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                  return (0 < ((((const Div*)r1)->a % ((const Div*)r1)->b) + ((const Add*)r2)->b));
                }
              }
              if (equal(((const Div*)r1)->a, ((const Add*)r2)->b)) {
                if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                  return (0 < ((((const Div*)r1)->a % ((const Div*)r1)->b) + ((const Add*)r2)->a));
                }
              }
            }
            if (equal(((const Div*)r1)->a, b)) {
              if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                return ((((const Div*)r1)->a % ((const Div*)r1)->b) != 0);
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Add>())) {
      if ((r1 = ((const Add*)r0)->a.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if (is_const_v(((const Add*)r0)->b)) {
            if ((r2 = b.as<Mul>())) {
              if (equal(((const Mul*)r1)->b, ((const Mul*)r2)->b)) {
                if (evaluate_predicate(fold((((const Mul*)r1)->b > 0)))) {
                  return ((((const Mul*)r1)->a + fold((((const Add*)r0)->b / ((const Mul*)r1)->b))) < ((const Mul*)r2)->a);
                }
              }
            }
          }
        }
        if ((r2 = ((const Mul*)r1)->a.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Add>())) {
            if (is_const_v(((const Add*)r3)->b)) {
              if (is_const_v(((const Div*)r2)->b)) {
                if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                  if ((r4 = b.as<Add>())) {
                    if (equal(((const Add*)r3)->a, ((const Add*)r4)->a)) {
                      if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                        return ((((const Add*)r0)->b + ((const Add*)r3)->b) < (((((const Add*)r3)->a + ((const Add*)r3)->b) % ((const Div*)r2)->b) + ((const Add*)r4)->b));
                      }
                    }
                    if (equal(((const Add*)r3)->a, ((const Add*)r4)->b)) {
                      if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                        return ((((const Add*)r0)->b + ((const Add*)r3)->b) < (((((const Add*)r3)->a + ((const Add*)r3)->b) % ((const Div*)r2)->b) + ((const Add*)r4)->a));
                      }
                    }
                  }
                  if (equal(((const Add*)r3)->a, b)) {
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return ((((const Add*)r0)->b + ((const Add*)r3)->b) < ((((const Add*)r3)->a + ((const Add*)r3)->b) % ((const Div*)r2)->b));
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(((const Div*)r2)->b)) {
            if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
              if ((r3 = b.as<Add>())) {
                if (equal(((const Div*)r2)->a, ((const Add*)r3)->a)) {
                  if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                    return (((const Add*)r0)->b < ((((const Div*)r2)->a % ((const Div*)r2)->b) + ((const Add*)r3)->b));
                  }
                }
                if (equal(((const Div*)r2)->a, ((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                    return (((const Add*)r0)->b < ((((const Div*)r2)->a % ((const Div*)r2)->b) + ((const Add*)r3)->a));
                  }
                }
              }
              if (equal(((const Div*)r2)->a, b)) {
                if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                  return (((const Add*)r0)->b < (((const Div*)r2)->a % ((const Div*)r2)->b));
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->b.as<Mul>())) {
        if ((r2 = ((const Mul*)r1)->a.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Add>())) {
            if (is_const_v(((const Add*)r3)->b)) {
              if (is_const_v(((const Div*)r2)->b)) {
                if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                  if ((r4 = b.as<Add>())) {
                    if (equal(((const Add*)r3)->a, ((const Add*)r4)->a)) {
                      if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                        return ((((const Add*)r0)->a + ((const Add*)r3)->b) < (((((const Add*)r3)->a + ((const Add*)r3)->b) % ((const Div*)r2)->b) + ((const Add*)r4)->b));
                      }
                    }
                    if (equal(((const Add*)r3)->a, ((const Add*)r4)->b)) {
                      if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                        return ((((const Add*)r0)->a + ((const Add*)r3)->b) < (((((const Add*)r3)->a + ((const Add*)r3)->b) % ((const Div*)r2)->b) + ((const Add*)r4)->a));
                      }
                    }
                  }
                  if (equal(((const Add*)r3)->a, b)) {
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return ((((const Add*)r0)->a + ((const Add*)r3)->b) < ((((const Add*)r3)->a + ((const Add*)r3)->b) % ((const Div*)r2)->b));
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(((const Div*)r2)->b)) {
            if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
              if ((r3 = b.as<Add>())) {
                if (equal(((const Div*)r2)->a, ((const Add*)r3)->a)) {
                  if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                    return (((const Add*)r0)->a < ((((const Div*)r2)->a % ((const Div*)r2)->b) + ((const Add*)r3)->b));
                  }
                }
                if (equal(((const Div*)r2)->a, ((const Add*)r3)->b)) {
                  if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                    return (((const Add*)r0)->a < ((((const Div*)r2)->a % ((const Div*)r2)->b) + ((const Add*)r3)->a));
                  }
                }
              }
              if (equal(((const Div*)r2)->a, b)) {
                if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                  return (((const Add*)r0)->a < (((const Div*)r2)->a % ((const Div*)r2)->b));
                }
              }
            }
          }
        }
      }
      if ((r1 = b.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if ((r4 = ((const Div*)r3)->a.as<Add>())) {
              if (equal(((const Add*)r0)->a, ((const Add*)r4)->a)) {
                if (is_const_v(((const Add*)r4)->b)) {
                  if (is_const_v(((const Div*)r3)->b)) {
                    if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                      if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                        return ((((((const Add*)r0)->a + ((const Add*)r4)->b) % ((const Div*)r3)->b) + ((const Add*)r0)->b) < (((const Add*)r1)->b + ((const Add*)r4)->b));
                      }
                    }
                  }
                }
              }
              if (equal(((const Add*)r0)->b, ((const Add*)r4)->a)) {
                if (is_const_v(((const Add*)r4)->b)) {
                  if (is_const_v(((const Div*)r3)->b)) {
                    if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                      if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                        return ((((((const Add*)r0)->b + ((const Add*)r4)->b) % ((const Div*)r3)->b) + ((const Add*)r0)->a) < (((const Add*)r1)->b + ((const Add*)r4)->b));
                      }
                    }
                  }
                }
              }
            }
            if (equal(((const Add*)r0)->a, ((const Div*)r3)->a)) {
              if (is_const_v(((const Div*)r3)->b)) {
                if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                  if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                    return (((((const Add*)r0)->a % ((const Div*)r3)->b) + ((const Add*)r0)->b) < ((const Add*)r1)->b);
                  }
                }
              }
            }
            if (equal(((const Add*)r0)->b, ((const Div*)r3)->a)) {
              if (is_const_v(((const Div*)r3)->b)) {
                if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                  if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                    return (((((const Add*)r0)->b % ((const Div*)r3)->b) + ((const Add*)r0)->a) < ((const Add*)r1)->b);
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if ((r4 = ((const Div*)r3)->a.as<Add>())) {
              if (equal(((const Add*)r0)->a, ((const Add*)r4)->a)) {
                if (is_const_v(((const Add*)r4)->b)) {
                  if (is_const_v(((const Div*)r3)->b)) {
                    if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                      if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                        return ((((((const Add*)r0)->a + ((const Add*)r4)->b) % ((const Div*)r3)->b) + ((const Add*)r0)->b) < (((const Add*)r1)->a + ((const Add*)r4)->b));
                      }
                    }
                  }
                }
              }
              if (equal(((const Add*)r0)->b, ((const Add*)r4)->a)) {
                if (is_const_v(((const Add*)r4)->b)) {
                  if (is_const_v(((const Div*)r3)->b)) {
                    if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                      if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                        return ((((((const Add*)r0)->b + ((const Add*)r4)->b) % ((const Div*)r3)->b) + ((const Add*)r0)->a) < (((const Add*)r1)->a + ((const Add*)r4)->b));
                      }
                    }
                  }
                }
              }
            }
            if (equal(((const Add*)r0)->a, ((const Div*)r3)->a)) {
              if (is_const_v(((const Div*)r3)->b)) {
                if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                  if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                    return (((((const Add*)r0)->a % ((const Div*)r3)->b) + ((const Add*)r0)->b) < ((const Add*)r1)->a);
                  }
                }
              }
            }
            if (equal(((const Add*)r0)->b, ((const Div*)r3)->a)) {
              if (is_const_v(((const Div*)r3)->b)) {
                if (equal(((const Div*)r3)->b, ((const Mul*)r2)->b)) {
                  if (evaluate_predicate(fold((((const Div*)r3)->b > 0)))) {
                    return (((((const Add*)r0)->b % ((const Div*)r3)->b) + ((const Add*)r0)->a) < ((const Add*)r1)->a);
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = b.as<Mul>())) {
        if ((r2 = ((const Mul*)r1)->a.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Add>())) {
            if (equal(((const Add*)r0)->a, ((const Add*)r3)->a)) {
              if (is_const_v(((const Add*)r3)->b)) {
                if (is_const_v(((const Div*)r2)->b)) {
                  if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return ((((((const Add*)r0)->a + ((const Add*)r3)->b) % ((const Div*)r2)->b) + ((const Add*)r0)->b) < ((const Add*)r3)->b);
                    }
                  }
                }
              }
            }
            if (equal(((const Add*)r0)->b, ((const Add*)r3)->a)) {
              if (is_const_v(((const Add*)r3)->b)) {
                if (is_const_v(((const Div*)r2)->b)) {
                  if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return ((((((const Add*)r0)->b + ((const Add*)r3)->b) % ((const Div*)r2)->b) + ((const Add*)r0)->a) < ((const Add*)r3)->b);
                    }
                  }
                }
              }
            }
          }
          if (equal(((const Add*)r0)->a, ((const Div*)r2)->a)) {
            if (is_const_v(((const Div*)r2)->b)) {
              if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                  return (((((const Add*)r0)->a % ((const Div*)r2)->b) + ((const Add*)r0)->b) < 0);
                }
              }
            }
          }
          if (equal(((const Add*)r0)->b, ((const Div*)r2)->a)) {
            if (is_const_v(((const Div*)r2)->b)) {
              if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                  return (((((const Add*)r0)->b % ((const Div*)r2)->b) + ((const Add*)r0)->a) < 0);
                }
              }
            }
          }
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
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return (((a + ((const Add*)r3)->b) % ((const Div*)r2)->b) < (((const Add*)r0)->b + ((const Add*)r3)->b));
                    }
                  }
                }
              }
            }
          }
          if (equal(a, ((const Div*)r2)->a)) {
            if (is_const_v(((const Div*)r2)->b)) {
              if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                  return ((a % ((const Div*)r2)->b) < ((const Add*)r0)->b);
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Add*)r0)->b.as<Mul>())) {
        if ((r2 = ((const Mul*)r1)->a.as<Div>())) {
          if ((r3 = ((const Div*)r2)->a.as<Add>())) {
            if (equal(a, ((const Add*)r3)->a)) {
              if (is_const_v(((const Add*)r3)->b)) {
                if (is_const_v(((const Div*)r2)->b)) {
                  if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                    if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                      return (((a + ((const Add*)r3)->b) % ((const Div*)r2)->b) < (((const Add*)r0)->a + ((const Add*)r3)->b));
                    }
                  }
                }
              }
            }
          }
          if (equal(a, ((const Div*)r2)->a)) {
            if (is_const_v(((const Div*)r2)->b)) {
              if (equal(((const Div*)r2)->b, ((const Mul*)r1)->b)) {
                if (evaluate_predicate(fold((((const Div*)r2)->b > 0)))) {
                  return ((a % ((const Div*)r2)->b) < ((const Add*)r0)->a);
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
                  if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                    return (((a + ((const Add*)r2)->b) % ((const Div*)r1)->b) < ((const Add*)r2)->b);
                  }
                }
              }
            }
          }
        }
        if (equal(a, ((const Div*)r1)->a)) {
          if (is_const_v(((const Div*)r1)->b)) {
            if (equal(((const Div*)r1)->b, ((const Mul*)r0)->b)) {
              if (evaluate_predicate(fold((((const Div*)r1)->b > 0)))) {
                return false;
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Div>())) {
      if ((r1 = ((const Div*)r0)->a.as<Add>())) {
        if (is_const_v(((const Add*)r1)->b)) {
          if (is_const_v(((const Div*)r0)->b)) {
            if ((r2 = b.as<Div>())) {
              if ((r3 = ((const Div*)r2)->a.as<Add>())) {
                if (equal(((const Add*)r1)->a, ((const Add*)r3)->a)) {
                  if (is_const_v(((const Add*)r3)->b)) {
                    if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                      if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= ((const Add*)r3)->b))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= (((const Add*)r3)->b - ((const Div*)r0)->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
              if (equal(((const Add*)r1)->a, ((const Div*)r2)->a)) {
                if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                  if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= 0))))) {
                    return false;
                  }
                  if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= (0 - ((const Div*)r0)->b)))))) {
                    return true;
                  }
                }
              }
            }
            if ((r2 = b.as<Add>())) {
              if ((r3 = ((const Add*)r2)->a.as<Div>())) {
                if (equal(((const Add*)r1)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                    if (is_const_v(((const Add*)r2)->b)) {
                      if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= (((const Add*)r2)->b * ((const Div*)r0)->b)))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= ((((const Add*)r2)->b * ((const Div*)r0)->b) - ((const Div*)r0)->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
              if ((r3 = ((const Add*)r2)->a.as<Min>())) {
                if ((r4 = ((const Min*)r3)->a.as<Div>())) {
                  if (equal(((const Add*)r1)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r0)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r2)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= (((const Add*)r2)->b * ((const Div*)r0)->b)))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
                if ((r4 = ((const Min*)r3)->b.as<Div>())) {
                  if (equal(((const Add*)r1)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r0)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r2)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= (((const Add*)r2)->b * ((const Div*)r0)->b)))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
              }
              if ((r3 = ((const Add*)r2)->a.as<Max>())) {
                if ((r4 = ((const Max*)r3)->a.as<Div>())) {
                  if (equal(((const Add*)r1)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r0)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r2)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= ((((const Add*)r2)->b * ((const Div*)r0)->b) - ((const Div*)r0)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if ((r4 = ((const Max*)r3)->b.as<Div>())) {
                  if (equal(((const Add*)r1)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r0)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r2)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= ((((const Add*)r2)->b * ((const Div*)r0)->b) - ((const Div*)r0)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
              }
            }
            if ((r2 = b.as<Min>())) {
              if ((r3 = ((const Min*)r2)->a.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r1)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= ((const Add*)r4)->b))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r1)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
              if ((r3 = ((const Min*)r2)->b.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r1)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= ((const Add*)r4)->b))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r1)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
            if ((r2 = b.as<Max>())) {
              if ((r3 = ((const Max*)r2)->a.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r1)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= (((const Add*)r4)->b - ((const Div*)r0)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r1)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= (0 - ((const Div*)r0)->b)))))) {
                      return true;
                    }
                  }
                }
              }
              if ((r3 = ((const Max*)r2)->b.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r1)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= (((const Add*)r4)->b - ((const Div*)r0)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r1)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r1)->b <= (0 - ((const Div*)r0)->b)))))) {
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Max>())) {
          if ((r3 = ((const Max*)r2)->b.as<Add>())) {
            if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
              if (is_const_v(((const Mul*)r4)->b)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (is_const_v(((const Add*)r1)->b)) {
                    if (equal(((const Mul*)r4)->b, ((const Div*)r0)->b)) {
                      if (equal(((const Mul*)r4)->a, b)) {
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) < 0))))) {
                          return (((((const Max*)r2)->a + ((const Add*)r1)->b) / ((const Mul*)r4)->b) < ((const Mul*)r4)->a);
                        }
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) >= 0))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if ((r3 = ((const Max*)r2)->b.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r1)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b < 0))))) {
                      return (((((const Max*)r2)->a + ((const Add*)r1)->b) / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
          if ((r3 = ((const Max*)r2)->a.as<Add>())) {
            if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
              if (is_const_v(((const Mul*)r4)->b)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (is_const_v(((const Add*)r1)->b)) {
                    if (equal(((const Mul*)r4)->b, ((const Div*)r0)->b)) {
                      if (equal(((const Mul*)r4)->a, b)) {
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) < 0))))) {
                          return (((((const Max*)r2)->b + ((const Add*)r1)->b) / ((const Mul*)r4)->b) < ((const Mul*)r4)->a);
                        }
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) >= 0))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if ((r3 = ((const Max*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r1)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b < 0))))) {
                      return (((((const Max*)r2)->b + ((const Add*)r1)->b) / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Add*)r1)->a.as<Min>())) {
          if ((r3 = ((const Min*)r2)->b.as<Add>())) {
            if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
              if (is_const_v(((const Mul*)r4)->b)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (is_const_v(((const Add*)r1)->b)) {
                    if (equal(((const Mul*)r4)->b, ((const Div*)r0)->b)) {
                      if (equal(((const Mul*)r4)->a, b)) {
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) < 0))))) {
                          return true;
                        }
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) >= 0))))) {
                          return (((((const Min*)r2)->a + ((const Add*)r1)->b) / ((const Mul*)r4)->b) < ((const Mul*)r4)->a);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if ((r3 = ((const Min*)r2)->b.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r1)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b < 0))))) {
                      return true;
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b >= 0))))) {
                      return (((((const Min*)r2)->a + ((const Add*)r1)->b) / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                  }
                }
              }
            }
          }
          if ((r3 = ((const Min*)r2)->a.as<Add>())) {
            if ((r4 = ((const Add*)r3)->a.as<Mul>())) {
              if (is_const_v(((const Mul*)r4)->b)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (is_const_v(((const Add*)r1)->b)) {
                    if (equal(((const Mul*)r4)->b, ((const Div*)r0)->b)) {
                      if (equal(((const Mul*)r4)->a, b)) {
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) < 0))))) {
                          return true;
                        }
                        if (evaluate_predicate(fold(((((const Mul*)r4)->b > 0) && ((((const Add*)r3)->b + ((const Add*)r1)->b) >= 0))))) {
                          return (((((const Min*)r2)->b + ((const Add*)r1)->b) / ((const Mul*)r4)->b) < ((const Mul*)r4)->a);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if ((r3 = ((const Min*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r1)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b < 0))))) {
                      return true;
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r1)->b >= 0))))) {
                      return (((((const Min*)r2)->b + ((const Add*)r1)->b) / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                  }
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
              if (is_const_v(((const Add*)r2)->b)) {
                if (equal(((const Div*)r0)->b, ((const Div*)r1)->b)) {
                  if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (0 >= ((const Add*)r2)->b))))) {
                    return false;
                  }
                  if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (0 <= (((const Add*)r2)->b - ((const Div*)r0)->b)))))) {
                    return true;
                  }
                }
              }
            }
          }
        }
        if ((r1 = b.as<Min>())) {
          if ((r2 = ((const Min*)r1)->a.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r0)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r3)->b < 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
          if ((r2 = ((const Min*)r1)->b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r0)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Add*)r3)->b < 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
        if ((r1 = b.as<Max>())) {
          if ((r2 = ((const Max*)r1)->a.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r0)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Div*)r0)->b <= ((const Add*)r3)->b))))) {
                      return true;
                    }
                  }
                }
              }
            }
          }
          if ((r2 = ((const Max*)r1)->b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r0)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r0)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r0)->b > 0) && (((const Div*)r0)->b <= ((const Add*)r3)->b))))) {
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Div*)r0)->a.as<Max>())) {
        if ((r2 = ((const Max*)r1)->b.as<Add>())) {
          if ((r3 = ((const Add*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r2)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b < 0))))) {
                      return ((((const Max*)r1)->a / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Max*)r1)->b.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if (equal(((const Mul*)r2)->b, ((const Div*)r0)->b)) {
              if (equal(((const Mul*)r2)->a, b)) {
                if (evaluate_predicate(fold((((const Mul*)r2)->b > 0)))) {
                  return false;
                }
              }
            }
          }
        }
        if ((r2 = ((const Max*)r1)->a.as<Add>())) {
          if ((r3 = ((const Add*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r2)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b < 0))))) {
                      return ((((const Max*)r1)->b / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Max*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if (equal(((const Mul*)r2)->b, ((const Div*)r0)->b)) {
              if (equal(((const Mul*)r2)->a, b)) {
                if (evaluate_predicate(fold((((const Mul*)r2)->b > 0)))) {
                  return false;
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Div*)r0)->a.as<Min>())) {
        if ((r2 = ((const Min*)r1)->b.as<Add>())) {
          if ((r3 = ((const Add*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r2)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b < 0))))) {
                      return true;
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b >= 0))))) {
                      return ((((const Min*)r1)->a / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Min*)r1)->b.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if (equal(((const Mul*)r2)->b, ((const Div*)r0)->b)) {
              if (equal(((const Mul*)r2)->a, b)) {
                if (evaluate_predicate(fold((((const Mul*)r2)->b > 0)))) {
                  return ((((const Min*)r1)->a / ((const Mul*)r2)->b) < ((const Mul*)r2)->a);
                }
              }
            }
          }
        }
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if ((r3 = ((const Add*)r2)->a.as<Mul>())) {
            if (is_const_v(((const Mul*)r3)->b)) {
              if (is_const_v(((const Add*)r2)->b)) {
                if (equal(((const Mul*)r3)->b, ((const Div*)r0)->b)) {
                  if (equal(((const Mul*)r3)->a, b)) {
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b < 0))))) {
                      return true;
                    }
                    if (evaluate_predicate(fold(((((const Mul*)r3)->b > 0) && (((const Add*)r2)->b >= 0))))) {
                      return ((((const Min*)r1)->b / ((const Mul*)r3)->b) < ((const Mul*)r3)->a);
                    }
                  }
                }
              }
            }
          }
        }
        if ((r2 = ((const Min*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if (equal(((const Mul*)r2)->b, ((const Div*)r0)->b)) {
              if (equal(((const Mul*)r2)->a, b)) {
                if (evaluate_predicate(fold((((const Mul*)r2)->b > 0)))) {
                  return ((((const Min*)r1)->b / ((const Mul*)r2)->b) < ((const Mul*)r2)->a);
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Max>())) {
      if ((r1 = ((const Max*)r0)->a.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if ((r3 = b.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r2)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= ((const Add*)r4)->b))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r2)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
              if ((r3 = b.as<Add>())) {
                if ((r4 = ((const Add*)r3)->a.as<Div>())) {
                  if (equal(((const Add*)r2)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r1)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= (((const Add*)r3)->b * ((const Div*)r1)->b)))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(((const Div*)r1)->b)) {
          if ((r2 = b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (0 >= ((const Add*)r3)->b))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Max*)r0)->b.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if ((r3 = b.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r2)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= ((const Add*)r4)->b))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r2)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= 0))))) {
                      return false;
                    }
                  }
                }
              }
              if ((r3 = b.as<Add>())) {
                if ((r4 = ((const Add*)r3)->a.as<Div>())) {
                  if (equal(((const Add*)r2)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r1)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b >= (((const Add*)r3)->b * ((const Div*)r1)->b)))))) {
                          return false;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(((const Div*)r1)->b)) {
          if ((r2 = b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (0 >= ((const Add*)r3)->b))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (is_const_v(((const Max*)r0)->b)) {
        if ((r1 = b.as<Max>())) {
          if (equal(((const Max*)r0)->a, ((const Max*)r1)->a)) {
            if (is_const_v(((const Max*)r1)->b)) {
              if (evaluate_predicate(fold((((const Max*)r0)->b >= ((const Max*)r1)->b)))) {
                return false;
              }
            }
          }
        }
        if ((r1 = b.as<Add>())) {
          if ((r2 = ((const Add*)r1)->a.as<Max>())) {
            if (equal(((const Max*)r0)->a, ((const Max*)r2)->a)) {
              if (is_const_v(((const Max*)r2)->b)) {
                if (is_const_v(((const Add*)r1)->b)) {
                  if (evaluate_predicate(fold(((((const Max*)r0)->b >= (((const Max*)r2)->b + ((const Add*)r1)->b)) && (((const Add*)r1)->b <= 0))))) {
                    return false;
                  }
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Min>())) {
      if ((r1 = ((const Min*)r0)->a.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if ((r3 = b.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r2)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b <= (((const Add*)r4)->b - ((const Div*)r1)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r2)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && ((((const Add*)r2)->b + ((const Div*)r1)->b) <= 0))))) {
                      return true;
                    }
                  }
                }
              }
              if ((r3 = b.as<Add>())) {
                if ((r4 = ((const Add*)r3)->a.as<Div>())) {
                  if (equal(((const Add*)r2)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r1)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b <= ((((const Add*)r3)->b * ((const Div*)r1)->b) - ((const Div*)r1)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(((const Div*)r1)->b)) {
          if ((r2 = b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (0 <= (((const Add*)r3)->b - ((const Div*)r1)->b)))))) {
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if ((r1 = ((const Min*)r0)->b.as<Div>())) {
        if ((r2 = ((const Div*)r1)->a.as<Add>())) {
          if (is_const_v(((const Add*)r2)->b)) {
            if (is_const_v(((const Div*)r1)->b)) {
              if ((r3 = b.as<Div>())) {
                if ((r4 = ((const Div*)r3)->a.as<Add>())) {
                  if (equal(((const Add*)r2)->a, ((const Add*)r4)->a)) {
                    if (is_const_v(((const Add*)r4)->b)) {
                      if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b <= (((const Add*)r4)->b - ((const Div*)r1)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (equal(((const Add*)r2)->a, ((const Div*)r3)->a)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r3)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && ((((const Add*)r2)->b + ((const Div*)r1)->b) <= 0))))) {
                      return true;
                    }
                  }
                }
              }
              if ((r3 = b.as<Add>())) {
                if ((r4 = ((const Add*)r3)->a.as<Div>())) {
                  if (equal(((const Add*)r2)->a, ((const Div*)r4)->a)) {
                    if (equal(((const Div*)r1)->b, ((const Div*)r4)->b)) {
                      if (is_const_v(((const Add*)r3)->b)) {
                        if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (((const Add*)r2)->b <= ((((const Add*)r3)->b * ((const Div*)r1)->b) - ((const Div*)r1)->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(((const Div*)r1)->b)) {
          if ((r2 = b.as<Div>())) {
            if ((r3 = ((const Div*)r2)->a.as<Add>())) {
              if (equal(((const Div*)r1)->a, ((const Add*)r3)->a)) {
                if (is_const_v(((const Add*)r3)->b)) {
                  if (equal(((const Div*)r1)->b, ((const Div*)r2)->b)) {
                    if (evaluate_predicate(fold(((((const Div*)r1)->b > 0) && (0 <= (((const Add*)r3)->b - ((const Div*)r1)->b)))))) {
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (is_const_v(((const Min*)r0)->b)) {
        if ((r1 = b.as<Min>())) {
          if (equal(((const Min*)r0)->a, ((const Min*)r1)->a)) {
            if (is_const_v(((const Min*)r1)->b)) {
              if (evaluate_predicate(fold((((const Min*)r0)->b >= ((const Min*)r1)->b)))) {
                return false;
              }
            }
          }
        }
        if ((r1 = b.as<Add>())) {
          if ((r2 = ((const Add*)r1)->a.as<Min>())) {
            if (equal(((const Min*)r0)->a, ((const Min*)r2)->a)) {
              if (is_const_v(((const Min*)r2)->b)) {
                if (is_const_v(((const Add*)r1)->b)) {
                  if (evaluate_predicate(fold(((((const Min*)r0)->b >= (((const Min*)r2)->b + ((const Add*)r1)->b)) && (((const Add*)r1)->b <= 0))))) {
                    return false;
                  }
                }
              }
            }
          }
        }
      }
    }
    if ((r0 = a.as<Ramp>())) {
      if ((r1 = ((const Ramp*)r0)->base.as<Add>())) {
        if ((r2 = ((const Add*)r1)->a.as<Mul>())) {
          if (is_const_v(((const Mul*)r2)->b)) {
            if (is_const_v(((const Add*)r1)->b)) {
              if (is_const_v(((const Ramp*)r0)->stride)) {
                if (is_const_v(((const Ramp*)r0)->lanes)) {
                  if ((r3 = b.as<Broadcast>())) {
                    if ((r4 = ((const Broadcast*)r3)->value.as<Mul>())) {
                      if (is_const_v(((const Mul*)r4)->b)) {
                        if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r3)->lanes)) {
                          if (evaluate_predicate(fold(((((((const Mul*)r4)->b > 0) && ((((const Mul*)r2)->b % ((const Mul*)r4)->b) == 0)) && (((((const Add*)r1)->b % ((const Mul*)r4)->b) + (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))) < ((const Mul*)r4)->b)) && (((((const Add*)r1)->b % ((const Mul*)r4)->b) + (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))) >= 0))))) {
                            return broadcast((((((const Mul*)r2)->a * fold((((const Mul*)r2)->b / ((const Mul*)r4)->b))) + fold((((const Add*)r1)->b / ((const Mul*)r4)->b))) < ((const Mul*)r4)->a), ((const Ramp*)r0)->lanes);
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
      if ((r1 = ((const Ramp*)r0)->base.as<Mul>())) {
        if (is_const_v(((const Mul*)r1)->b)) {
          if (is_const_v(((const Ramp*)r0)->stride)) {
            if (is_const_v(((const Ramp*)r0)->lanes)) {
              if ((r2 = b.as<Broadcast>())) {
                if ((r3 = ((const Broadcast*)r2)->value.as<Mul>())) {
                  if (is_const_v(((const Mul*)r3)->b)) {
                    if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r2)->lanes)) {
                      if (evaluate_predicate(fold(((((((const Mul*)r3)->b > 0) && ((((const Mul*)r1)->b % ((const Mul*)r3)->b) == 0)) && ((((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1)) < ((const Mul*)r3)->b)) && ((((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1)) >= 0))))) {
                        return broadcast(((((const Mul*)r1)->a * fold((((const Mul*)r1)->b / ((const Mul*)r3)->b))) < ((const Mul*)r3)->a), ((const Ramp*)r0)->lanes);
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
  if (type.is_operand_float()) {
    if ((r0 = a.as<Mul>())) {
      if (is_const_v(((const Mul*)r0)->b)) {
        if (is_const_v(b)) {
          if (evaluate_predicate(fold((((const Mul*)r0)->b > 0)))) {
            return (((const Mul*)r0)->a < fold((b / ((const Mul*)r0)->b)));
          }
        }
      }
    }
    if (is_const_v(a)) {
      if ((r0 = b.as<Div>())) {
        if (is_const_v(((const Div*)r0)->b)) {
          if (evaluate_predicate(fold((((const Div*)r0)->b < 0)))) {
            return (((const Div*)r0)->a < fold((a * ((const Div*)r0)->b)));
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
