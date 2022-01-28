#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"
#include "Expr.h"
#include "Type.h"

namespace Halide {
namespace Internal {
namespace CodeGen {

Expr Simplify_And(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier) {
  const BaseExprNode *r0 = nullptr;
  const BaseExprNode *r1 = nullptr;
  const BaseExprNode *r2 = nullptr;
  return a;
  return b;
  if (equal(a, b)) {
    return a;
  }
  if ((r0 = a.as<And>())) {
    if (equal(((const And*)r0)->a, b)) {
      return (((const And*)r0)->a && ((const And*)r0)->b);
    }
    if (equal(((const And*)r0)->b, b)) {
      return (((const And*)r0)->a && ((const And*)r0)->b);
    }
    if ((r1 = ((const And*)r0)->a.as<And>())) {
      if (equal(((const And*)r1)->a, b)) {
        return ((((const And*)r1)->a && ((const And*)r1)->b) && ((const And*)r0)->b);
      }
      if (equal(((const And*)r1)->b, b)) {
        return ((((const And*)r1)->a && ((const And*)r1)->b) && ((const And*)r0)->b);
      }
    }
    if ((r1 = ((const And*)r0)->b.as<And>())) {
      if (equal(((const And*)r1)->a, b)) {
        return (((const And*)r0)->a && (((const And*)r1)->a && ((const And*)r1)->b));
      }
      if (equal(((const And*)r1)->b, b)) {
        return (((const And*)r0)->a && (((const And*)r1)->a && ((const And*)r1)->b));
      }
    }
    if ((r1 = ((const And*)r0)->b.as<NE>())) {
      if ((r2 = b.as<EQ>())) {
        if (equal(((const NE*)r1)->a, ((const EQ*)r2)->a)) {
          if (equal(((const NE*)r1)->b, ((const EQ*)r2)->b)) {
            return false;
          }
        }
        if (equal(((const NE*)r1)->b, ((const EQ*)r2)->a)) {
          if (equal(((const NE*)r1)->a, ((const EQ*)r2)->b)) {
            return false;
          }
        }
      }
    }
    if ((r1 = ((const And*)r0)->a.as<NE>())) {
      if ((r2 = b.as<EQ>())) {
        if (equal(((const NE*)r1)->a, ((const EQ*)r2)->a)) {
          if (equal(((const NE*)r1)->b, ((const EQ*)r2)->b)) {
            return false;
          }
        }
        if (equal(((const NE*)r1)->b, ((const EQ*)r2)->a)) {
          if (equal(((const NE*)r1)->a, ((const EQ*)r2)->b)) {
            return false;
          }
        }
      }
    }
    if ((r1 = ((const And*)r0)->b.as<EQ>())) {
      if ((r2 = b.as<NE>())) {
        if (equal(((const EQ*)r1)->a, ((const NE*)r2)->a)) {
          if (equal(((const EQ*)r1)->b, ((const NE*)r2)->b)) {
            return false;
          }
        }
        if (equal(((const EQ*)r1)->b, ((const NE*)r2)->a)) {
          if (equal(((const EQ*)r1)->a, ((const NE*)r2)->b)) {
            return false;
          }
        }
      }
    }
    if ((r1 = ((const And*)r0)->a.as<EQ>())) {
      if ((r2 = b.as<NE>())) {
        if (equal(((const EQ*)r1)->a, ((const NE*)r2)->a)) {
          if (equal(((const EQ*)r1)->b, ((const NE*)r2)->b)) {
            return false;
          }
        }
        if (equal(((const EQ*)r1)->b, ((const NE*)r2)->a)) {
          if (equal(((const EQ*)r1)->a, ((const NE*)r2)->b)) {
            return false;
          }
        }
      }
    }
    if ((r1 = ((const And*)r0)->b.as<Or>())) {
      if (equal(((const Or*)r1)->a, b)) {
        return (((const And*)r0)->a && ((const Or*)r1)->a);
      }
      if (equal(((const Or*)r1)->b, b)) {
        return (((const And*)r0)->a && ((const Or*)r1)->b);
      }
    }
    if ((r1 = ((const And*)r0)->a.as<Or>())) {
      if (equal(((const Or*)r1)->a, b)) {
        return (((const And*)r0)->b && ((const Or*)r1)->a);
      }
      if (equal(((const Or*)r1)->b, b)) {
        return (((const And*)r0)->b && ((const Or*)r1)->b);
      }
    }
  }
  if ((r0 = b.as<And>())) {
    if (equal(a, ((const And*)r0)->a)) {
      return (a && ((const And*)r0)->b);
    }
    if (equal(a, ((const And*)r0)->b)) {
      return (((const And*)r0)->a && a);
    }
    if ((r1 = ((const And*)r0)->a.as<And>())) {
      if (equal(a, ((const And*)r1)->a)) {
        return ((a && ((const And*)r1)->b) && ((const And*)r0)->b);
      }
      if (equal(a, ((const And*)r1)->b)) {
        return ((((const And*)r1)->a && a) && ((const And*)r0)->b);
      }
    }
    if ((r1 = ((const And*)r0)->b.as<And>())) {
      if (equal(a, ((const And*)r1)->a)) {
        return (((const And*)r0)->a && (a && ((const And*)r1)->b));
      }
      if (equal(a, ((const And*)r1)->b)) {
        return (((const And*)r0)->a && (((const And*)r1)->a && a));
      }
    }
    if ((r1 = ((const And*)r0)->b.as<Or>())) {
      if (equal(a, ((const Or*)r1)->a)) {
        return (a && ((const And*)r0)->a);
      }
      if (equal(a, ((const Or*)r1)->b)) {
        return (a && ((const And*)r0)->a);
      }
    }
    if ((r1 = ((const And*)r0)->a.as<Or>())) {
      if (equal(a, ((const Or*)r1)->a)) {
        return (a && ((const And*)r0)->b);
      }
      if (equal(a, ((const Or*)r1)->b)) {
        return (a && ((const And*)r0)->b);
      }
    }
  }
  if ((r0 = a.as<Or>())) {
    if (equal(((const Or*)r0)->a, b)) {
      return ((const Or*)r0)->a;
    }
    if (equal(((const Or*)r0)->b, b)) {
      return ((const Or*)r0)->b;
    }
    if ((r1 = ((const Or*)r0)->b.as<And>())) {
      if (equal(((const And*)r1)->a, b)) {
        return ((((const Or*)r0)->a || ((const And*)r1)->b) && ((const And*)r1)->a);
      }
      if (equal(((const And*)r1)->b, b)) {
        return ((((const Or*)r0)->a || ((const And*)r1)->a) && ((const And*)r1)->b);
      }
    }
    if ((r1 = ((const Or*)r0)->a.as<And>())) {
      if (equal(((const And*)r1)->a, b)) {
        return ((((const And*)r1)->b || ((const Or*)r0)->b) && ((const And*)r1)->a);
      }
      if (equal(((const And*)r1)->b, b)) {
        return ((((const And*)r1)->a || ((const Or*)r0)->b) && ((const And*)r1)->b);
      }
    }
    if ((r1 = b.as<Or>())) {
      if (equal(((const Or*)r0)->a, ((const Or*)r1)->a)) {
        return (((const Or*)r0)->a || (((const Or*)r0)->b && ((const Or*)r1)->b));
      }
      if (equal(((const Or*)r0)->a, ((const Or*)r1)->b)) {
        return (((const Or*)r0)->a || (((const Or*)r0)->b && ((const Or*)r1)->a));
      }
      if (equal(((const Or*)r0)->b, ((const Or*)r1)->a)) {
        return (((const Or*)r0)->b || (((const Or*)r0)->a && ((const Or*)r1)->b));
      }
      if (equal(((const Or*)r0)->b, ((const Or*)r1)->b)) {
        return (((const Or*)r0)->b || (((const Or*)r0)->a && ((const Or*)r1)->a));
      }
    }
  }
  if ((r0 = b.as<Or>())) {
    if (equal(a, ((const Or*)r0)->a)) {
      return a;
    }
    if (equal(a, ((const Or*)r0)->b)) {
      return a;
    }
    if ((r1 = ((const Or*)r0)->b.as<And>())) {
      if (equal(a, ((const And*)r1)->a)) {
        return (a && (((const Or*)r0)->a || ((const And*)r1)->b));
      }
      if (equal(a, ((const And*)r1)->b)) {
        return (a && (((const Or*)r0)->a || ((const And*)r1)->a));
      }
    }
    if ((r1 = ((const Or*)r0)->a.as<And>())) {
      if (equal(a, ((const And*)r1)->a)) {
        return (a && (((const And*)r1)->b || ((const Or*)r0)->b));
      }
      if (equal(a, ((const And*)r1)->b)) {
        return (a && (((const And*)r1)->a || ((const Or*)r0)->b));
      }
    }
  }
  if ((r0 = a.as<NE>())) {
    if ((r1 = b.as<EQ>())) {
      if (equal(((const NE*)r0)->a, ((const EQ*)r1)->a)) {
        if (equal(((const NE*)r0)->b, ((const EQ*)r1)->b)) {
          return false;
        }
      }
      if (equal(((const NE*)r0)->b, ((const EQ*)r1)->a)) {
        if (equal(((const NE*)r0)->a, ((const EQ*)r1)->b)) {
          return false;
        }
      }
    }
    if (is_const_v(((const NE*)r0)->b)) {
      if ((r1 = b.as<EQ>())) {
        if (equal(((const NE*)r0)->a, ((const EQ*)r1)->a)) {
          if (is_const_v(((const EQ*)r1)->b)) {
            if (evaluate_predicate(fold((((const NE*)r0)->b != ((const EQ*)r1)->b)))) {
              return (((const NE*)r0)->a == ((const EQ*)r1)->b);
            }
          }
        }
      }
    }
  }
  if ((r0 = b.as<Not>())) {
    if (equal(a, ((const Not*)r0)->a)) {
      return false;
    }
  }
  if ((r0 = a.as<Not>())) {
    if (equal(((const Not*)r0)->a, b)) {
      return false;
    }
  }
  if ((r0 = a.as<LE>())) {
    if ((r1 = b.as<LT>())) {
      if (equal(((const LE*)r0)->b, ((const LT*)r1)->a)) {
        if (equal(((const LE*)r0)->a, ((const LT*)r1)->b)) {
          return false;
        }
      }
    }
    if (is_const_v(((const LE*)r0)->b)) {
      if ((r1 = b.as<LT>())) {
        if (is_const_v(((const LT*)r1)->a)) {
          if (equal(((const LE*)r0)->a, ((const LT*)r1)->b)) {
            if (evaluate_predicate(fold((((const LE*)r0)->b <= ((const LT*)r1)->a)))) {
              return false;
            }
          }
        }
      }
      if ((r1 = b.as<LE>())) {
        if (is_const_v(((const LE*)r1)->a)) {
          if (equal(((const LE*)r0)->a, ((const LE*)r1)->b)) {
            if (evaluate_predicate(fold((((const LE*)r0)->b < ((const LE*)r1)->a)))) {
              return false;
            }
          }
        }
        if (equal(((const LE*)r0)->a, ((const LE*)r1)->a)) {
          if (is_const_v(((const LE*)r1)->b)) {
            return (((const LE*)r0)->a <= fold(min(((const LE*)r0)->b, ((const LE*)r1)->b)));
          }
        }
      }
    }
    if (is_const_v(((const LE*)r0)->a)) {
      if ((r1 = b.as<LT>())) {
        if (equal(((const LE*)r0)->b, ((const LT*)r1)->a)) {
          if (is_const_v(((const LT*)r1)->b)) {
            if (evaluate_predicate(fold((((const LT*)r1)->b <= ((const LE*)r0)->a)))) {
              return false;
            }
          }
        }
      }
      if ((r1 = b.as<LE>())) {
        if (equal(((const LE*)r0)->b, ((const LE*)r1)->a)) {
          if (is_const_v(((const LE*)r1)->b)) {
            if (evaluate_predicate(fold((((const LE*)r1)->b < ((const LE*)r0)->a)))) {
              return false;
            }
          }
        }
        if (is_const_v(((const LE*)r1)->a)) {
          if (equal(((const LE*)r0)->b, ((const LE*)r1)->b)) {
            return (fold(max(((const LE*)r0)->a, ((const LE*)r1)->a)) <= ((const LE*)r0)->b);
          }
        }
      }
    }
    if ((r1 = b.as<LE>())) {
      if (equal(((const LE*)r0)->a, ((const LE*)r1)->a)) {
        return (((const LE*)r0)->a <= min(((const LE*)r0)->b, ((const LE*)r1)->b));
      }
      if (equal(((const LE*)r0)->b, ((const LE*)r1)->b)) {
        return (max(((const LE*)r0)->a, ((const LE*)r1)->a) <= ((const LE*)r0)->b);
      }
    }
  }
  if ((r0 = a.as<EQ>())) {
    if (is_const_v(((const EQ*)r0)->b)) {
      if ((r1 = b.as<EQ>())) {
        if (equal(((const EQ*)r0)->a, ((const EQ*)r1)->a)) {
          if (is_const_v(((const EQ*)r1)->b)) {
            if (evaluate_predicate(fold((((const EQ*)r0)->b != ((const EQ*)r1)->b)))) {
              return false;
            }
          }
        }
      }
    }
  }
  if ((r0 = a.as<LT>())) {
    if (is_const_v(((const LT*)r0)->a)) {
      if ((r1 = b.as<LT>())) {
        if (equal(((const LT*)r0)->b, ((const LT*)r1)->a)) {
          if (is_const_v(((const LT*)r1)->b)) {
            if (evaluate_predicate(fold((!(is_float(((const LT*)r0)->b)) && (((const LT*)r1)->b <= (((const LT*)r0)->a + 1)))))) {
              return false;
            }
          }
        }
        if (is_const_v(((const LT*)r1)->a)) {
          if (equal(((const LT*)r0)->b, ((const LT*)r1)->b)) {
            return (fold(max(((const LT*)r0)->a, ((const LT*)r1)->a)) < ((const LT*)r0)->b);
          }
        }
      }
    }
    if (is_const_v(((const LT*)r0)->b)) {
      if ((r1 = b.as<LT>())) {
        if (is_const_v(((const LT*)r1)->a)) {
          if (equal(((const LT*)r0)->a, ((const LT*)r1)->b)) {
            if (evaluate_predicate(fold((!(is_float(((const LT*)r0)->a)) && (((const LT*)r0)->b <= (((const LT*)r1)->a + 1)))))) {
              return false;
            }
          }
        }
        if (equal(((const LT*)r0)->a, ((const LT*)r1)->a)) {
          if (is_const_v(((const LT*)r1)->b)) {
            return (((const LT*)r0)->a < fold(min(((const LT*)r0)->b, ((const LT*)r1)->b)));
          }
        }
      }
    }
    if ((r1 = b.as<LT>())) {
      if (equal(((const LT*)r0)->a, ((const LT*)r1)->a)) {
        return (((const LT*)r0)->a < min(((const LT*)r0)->b, ((const LT*)r1)->b));
      }
      if (equal(((const LT*)r0)->b, ((const LT*)r1)->b)) {
        return (max(((const LT*)r0)->a, ((const LT*)r1)->a) < ((const LT*)r0)->b);
      }
    }
  }
  if ((r0 = a.as<Broadcast>())) {
    if (is_const_v(((const Broadcast*)r0)->lanes)) {
      if ((r1 = b.as<Broadcast>())) {
        if (equal(((const Broadcast*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
          return broadcast((((const Broadcast*)r0)->value && ((const Broadcast*)r1)->value), ((const Broadcast*)r0)->lanes);
        }
      }
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
