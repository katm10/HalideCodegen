bb((const Broadcast*)r1)->value((const Ramp*)r0)->base((const Ramp*)r1)->base((const Broadcast*)r0)->value((const Add*)r0)->b((const Add*)r0)->a((const Add*)r1)->bb((const Add*)r2)->b((const Add*)r0)->b((const Add*)r1)->bb((const Add*)r2)->bb((const Add*)r1)->bbbbb((const Add*)r0)->b((const Add*)r0)->a((const Add*)r1)->b((const Add*)r0)->b((const Add*)r1)->b((const Add*)r0)->a((const Min*)r1)->b((const Add*)r0)->a((const Max*)r1)->b((const Add*)r0)->a((const Select*)r1)->false_valueb((const Min*)r0)->bbbb((const Min*)r1)->ab((const Max*)r0)->bbbb((const Max*)r1)->a((const Min*)r0)->b((const Max*)r0)->b((const Select*)r0)->false_value((const Select*)r0)->false_valueb((const Add*)r0)->bb((const Add*)r1)->bb((const Add*)r0)->bb((const Add*)r2)->a((const Min*)r3)->b((const Add*)r2)->a((const Max*)r3)->bb((const Min*)r2)->bb((const Max*)r2)->b((const Max*)r2)->b((const Max*)r2)->a((const Max*)r2)->a((const Add*)r1)->a((const Min*)r2)->b((const Min*)r2)->a((const Min*)r2)->ab((const Min*)r1)->bb((const Max*)r1)->b((const Div*)r0)->a((const Max*)r1)->b((const Max*)r1)->a((const Max*)r1)->a((const Div*)r0)->a((const Min*)r1)->b((const Min*)r1)->a((const Min*)r1)->ab((const Max*)r0)->bbbb((const Min*)r0)->bbb((const Ramp*)r0)->base#include "Simplify_Internal.h"
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
    switch (b.node_type())
      {
      case IRNodeType::Mod: {        0x55a8cb214b00 = 0x55a8cb19aa90.as<Mod>();
        break;
      }
      case IRNodeType::Mul: {        0x55a8cb214b00 = 0x55a8cb19aa90.as<Mul>();
        break;
      }
      default:
        break;
      }  }
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
    switch (b.node_type())
      {
      case IRNodeType::Min: {        0x55a8cb215f60 = 0x55a8cb126b20.as<Min>();
        break;
      }
      default:
        break;
      }  }
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
          switch (b.node_type())
            {
            case IRNodeType::Broadcast: {              0x55a8cb217140 = 0x55a8cb127370.as<Broadcast>();
              break;
            }
            default:
              break;
            }        }
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
          switch (((const Broadcast*)r1)->value.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb219010 = 0x55a8cb219060.as<Add>();
              break;
            }
            case IRNodeType::Sub: {              0x55a8cb219010 = 0x55a8cb219060.as<Sub>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Ramp: {            0x55a8cb218110 = 0x55a8cb19b300.as<Ramp>();
            break;
          }
          case IRNodeType::Broadcast: {            0x55a8cb218110 = 0x55a8cb19b300.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
            switch (((const Broadcast*)r2)->value.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb21aec0 = 0x55a8cb21af10.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Broadcast: {              0x55a8cb21ad30 = 0x55a8cb1cd520.as<Broadcast>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Broadcast*)r2)->value.node_type())
              {
              case IRNodeType::Sub: {                0x55a8cb21dcc0 = 0x55a8cb21dd10.as<Sub>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Broadcast: {              0x55a8cb21db40 = 0x55a8cb1cf2b0.as<Broadcast>();
              break;
            }
            default:
              break;
            }        }
      }
      switch (((const Ramp*)r0)->base.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb21aa90 = 0x55a8cb21aae0.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x55a8cb21aa90 = 0x55a8cb21aae0.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
          switch (((const Ramp*)r1)->base.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb220a00 = 0x55a8cb220a50.as<Add>();
              break;
            }
            case IRNodeType::Sub: {              0x55a8cb220a00 = 0x55a8cb220a50.as<Sub>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Ramp: {            0x55a8cb21fa40 = 0x55a8cb198630.as<Ramp>();
            break;
          }
          default:
            break;
          }      }
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
            switch (((const Ramp*)r2)->base.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb222600 = 0x55a8cb222650.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Ramp: {              0x55a8cb222480 = 0x55a8cb1d2df0.as<Ramp>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Ramp*)r2)->base.node_type())
              {
              case IRNodeType::Sub: {                0x55a8cb2255a0 = 0x55a8cb2255f0.as<Sub>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Ramp: {              0x55a8cb2253f0 = 0x55a8cb1d4bd0.as<Ramp>();
              break;
            }
            default:
              break;
            }        }
      }
      switch (((const Broadcast*)r0)->value.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb2221f0 = 0x55a8cb222240.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x55a8cb2221f0 = 0x55a8cb222240.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb22aa40 = 0x55a8cb22aa90.as<Add>();
              break;
            }
            case IRNodeType::Add: {              0x55a8cb22aa40 = 0x55a8cb22aa90.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x55a8cb228490 = 0x55a8cb2284e0.as<Sub>();
            break;
          }
          case IRNodeType::Sub: {            0x55a8cb228490 = 0x55a8cb2284e0.as<Sub>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb228490 = 0x55a8cb2284e0.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb22fe80 = 0x55a8cb22fed0.as<Add>();
              break;
            }
            case IRNodeType::Add: {              0x55a8cb22fe80 = 0x55a8cb22fed0.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x55a8cb22d930 = 0x55a8cb22d980.as<Sub>();
            break;
          }
          case IRNodeType::Sub: {            0x55a8cb22d930 = 0x55a8cb22d980.as<Sub>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb22d930 = 0x55a8cb22d980.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb233e60 = 0x55a8cb233eb0.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb233e60 = 0x55a8cb233eb0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Add*)r0)->a.node_type())
        {
        case IRNodeType::Sub: {          0x55a8cb227790 = 0x55a8cb2277e0.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x55a8cb227790 = 0x55a8cb2277e0.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb227790 = 0x55a8cb2277e0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb227790 = 0x55a8cb2277e0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb227790 = 0x55a8cb2277e0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Sub: {          0x55a8cb236450 = 0x55a8cb19bf20.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb236450 = 0x55a8cb19bf20.as<Add>();
          break;
        }
        case IRNodeType::Min: {          0x55a8cb236450 = 0x55a8cb19bf20.as<Min>();
          break;
        }
        case IRNodeType::Max: {          0x55a8cb236450 = 0x55a8cb19bf20.as<Max>();
          break;
        }
        case IRNodeType::Select: {          0x55a8cb236450 = 0x55a8cb19bf20.as<Select>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x55a8cb239870 = 0x55a8cb2398c0.as<Sub>();
            break;
          }
          case IRNodeType::Sub: {            0x55a8cb239870 = 0x55a8cb2398c0.as<Sub>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x55a8cb23adb0 = 0x55a8cb23ae00.as<Sub>();
            break;
          }
          case IRNodeType::Sub: {            0x55a8cb23adb0 = 0x55a8cb23ae00.as<Sub>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Min*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb23c7e0 = 0x55a8cb23c830.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb23c7e0 = 0x55a8cb23c830.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Max*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb23e8d0 = 0x55a8cb23e920.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb23e8d0 = 0x55a8cb23e920.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Select*)r1)->true_value.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb2409c0 = 0x55a8cb240a10.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb2409c0 = 0x55a8cb240a10.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Add*)r0)->a.node_type())
        {
        case IRNodeType::Sub: {          0x55a8cb238bd0 = 0x55a8cb238c20.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x55a8cb238bd0 = 0x55a8cb238c20.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb238bd0 = 0x55a8cb238c20.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb238bd0 = 0x55a8cb238c20.as<Add>();
          break;
        }
        case IRNodeType::Min: {          0x55a8cb238bd0 = 0x55a8cb238c20.as<Min>();
          break;
        }
        case IRNodeType::Max: {          0x55a8cb238bd0 = 0x55a8cb238c20.as<Max>();
          break;
        }
        case IRNodeType::Select: {          0x55a8cb238bd0 = 0x55a8cb238c20.as<Select>();
          break;
        }
        default:
          break;
        }    }
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
        switch (b.node_type())
          {
          case IRNodeType::Mul: {            0x55a8cb242e20 = 0x55a8cb1aedb0.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
          switch (b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb243c70 = 0x55a8cb1b1130.as<Add>();
              break;
            }
            case IRNodeType::Min: {              0x55a8cb243c70 = 0x55a8cb1b1130.as<Min>();
              break;
            }
            default:
              break;
            }        }
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
          switch (b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb245ba0 = 0x55a8cb1b1bb0.as<Add>();
              break;
            }
            case IRNodeType::Min: {              0x55a8cb245ba0 = 0x55a8cb1b1bb0.as<Min>();
              break;
            }
            default:
              break;
            }        }
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
        switch (((const Min*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb249a40 = 0x55a8cb249a90.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb249a40 = 0x55a8cb249a90.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Min*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb2439b0 = 0x55a8cb243a00.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb2439b0 = 0x55a8cb243a00.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb2439b0 = 0x55a8cb243a00.as<Add>();
          break;
        }
        case IRNodeType::Min: {          0x55a8cb2439b0 = 0x55a8cb243a00.as<Min>();
          break;
        }
        default:
          break;
        }    }
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
          switch (b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb24c5c0 = 0x55a8cb1b2460.as<Add>();
              break;
            }
            case IRNodeType::Max: {              0x55a8cb24c5c0 = 0x55a8cb1b2460.as<Max>();
              break;
            }
            default:
              break;
            }        }
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
          switch (b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb24e4f0 = 0x55a8cb1b2e20.as<Add>();
              break;
            }
            case IRNodeType::Max: {              0x55a8cb24e4f0 = 0x55a8cb1b2e20.as<Max>();
              break;
            }
            default:
              break;
            }        }
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
        switch (((const Max*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb251e60 = 0x55a8cb251eb0.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb251e60 = 0x55a8cb251eb0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Max*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb24c330 = 0x55a8cb24c380.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb24c330 = 0x55a8cb24c380.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb24c330 = 0x55a8cb24c380.as<Add>();
          break;
        }
        case IRNodeType::Max: {          0x55a8cb24c330 = 0x55a8cb24c380.as<Max>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Min*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb2545f0 = 0x55a8cb254640.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb2545f0 = 0x55a8cb254640.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Max*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb255530 = 0x55a8cb255580.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb255530 = 0x55a8cb255580.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Select*)r0)->true_value.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb256980 = 0x55a8cb2569d0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb256980 = 0x55a8cb2569d0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
          switch (b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb259000 = 0x55a8cb1ca860.as<Add>();
              break;
            }
            default:
              break;
            }        }
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
          switch (b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb25ac70 = 0x55a8cb1cb650.as<Add>();
              break;
            }
            default:
              break;
            }        }
      }
      if (is_const_v(((const Select*)r0)->true_value)) {
        if (is_const_v(((const Select*)r0)->false_value)) {
          if (is_const_v(b)) {
            return select(((const Select*)r0)->condition, fold((((const Select*)r0)->true_value < b)), fold((((const Select*)r0)->false_value < b)));
          }
        }
      }
      switch (((const Select*)r0)->true_value.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb258330 = 0x55a8cb258380.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb258330 = 0x55a8cb258380.as<Add>();
          break;
        }
        default:
          break;
        }    }
  }
  if ((r0 = a.as<Broadcast>())) {
    if (is_const_v(((const Broadcast*)r0)->lanes)) {
      if ((r1 = b.as<Broadcast>())) {
        if (equal(((const Broadcast*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
          return broadcast((((const Broadcast*)r0)->value < ((const Broadcast*)r1)->value), ((const Broadcast*)r0)->lanes);
        }
      }
      switch (b.node_type())
        {
        case IRNodeType::Broadcast: {          0x55a8cb25c4d0 = 0x55a8cb1995f0.as<Broadcast>();
          break;
        }
        default:
          break;
        }    }
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
    switch (b.node_type())
      {
      case IRNodeType::Mod: {        0x55a8cb25d7e0 = 0x55a8cb199ea0.as<Mod>();
        break;
      }
      default:
        break;
      }  }
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
          switch (((const Add*)r1)->a.node_type())
            {
            case IRNodeType::Mul: {              0x55a8cb25f950 = 0x55a8cb25f9a0.as<Mul>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Mul: {            0x55a8cb25e530 = 0x55a8cb1d8620.as<Mul>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb25e530 = 0x55a8cb1d8620.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
                switch (b.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb260b30 = 0x55a8cb1e0160.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
            switch (b.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb262460 = 0x55a8cb1e9470.as<Add>();
                break;
              }
              default:
                break;
              }          }
        }
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb2606d0 = 0x55a8cb260720.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x55a8cb2604f0 = 0x55a8cb260540.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x55a8cb263c70 = 0x55a8cb1d9fd0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
                  switch (b.node_type())
                    {
                    case IRNodeType::Add: {                      0x55a8cb264be0 = 0x55a8cb1daa40.as<Add>();
                      break;
                    }
                    default:
                      break;
                    }                }
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
              switch (b.node_type())
                {
                case IRNodeType::Add: {                  0x55a8cb2667e0 = 0x55a8cb1e4b80.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
          }
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb264750 = 0x55a8cb2647a0.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Mul*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x55a8cb264540 = 0x55a8cb264590.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
                  switch (b.node_type())
                    {
                    case IRNodeType::Add: {                      0x55a8cb2684d0 = 0x55a8cb1db740.as<Add>();
                      break;
                    }
                    default:
                      break;
                    }                }
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
              switch (b.node_type())
                {
                case IRNodeType::Add: {                  0x55a8cb26a0d0 = 0x55a8cb1e53d0.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
          }
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb268040 = 0x55a8cb268090.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Mul*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x55a8cb267e30 = 0x55a8cb267e80.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
            switch (((const Div*)r3)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb26bae0 = 0x55a8cb26bb30.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (((const Mul*)r2)->a.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb26b8d0 = 0x55a8cb26b920.as<Div>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Div*)r3)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb26e920 = 0x55a8cb26e970.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (((const Mul*)r2)->a.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb26e740 = 0x55a8cb26e790.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Mul: {            0x55a8cb26b6c0 = 0x55a8cb26b710.as<Mul>();
            break;
          }
          case IRNodeType::Mul: {            0x55a8cb26b6c0 = 0x55a8cb26b710.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb271710 = 0x55a8cb271760.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Mul*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x55a8cb271530 = 0x55a8cb271580.as<Div>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Add*)r0)->a.node_type())
        {
        case IRNodeType::Mul: {          0x55a8cb263900 = 0x55a8cb263950.as<Mul>();
          break;
        }
        case IRNodeType::Mul: {          0x55a8cb263900 = 0x55a8cb263950.as<Mul>();
          break;
        }
        case IRNodeType::Add: {          0x55a8cb263900 = 0x55a8cb263950.as<Add>();
          break;
        }
        case IRNodeType::Mul: {          0x55a8cb263900 = 0x55a8cb263950.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb2743d0 = 0x55a8cb274420.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Mul*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x55a8cb2741c0 = 0x55a8cb274210.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb275a90 = 0x55a8cb275ae0.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Mul*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x55a8cb275880 = 0x55a8cb2758d0.as<Div>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Add*)r0)->a.node_type())
        {
        case IRNodeType::Mul: {          0x55a8cb273fe0 = 0x55a8cb274030.as<Mul>();
          break;
        }
        case IRNodeType::Mul: {          0x55a8cb273fe0 = 0x55a8cb274030.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb2770d0 = 0x55a8cb277120.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x55a8cb276ef0 = 0x55a8cb276f40.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
              switch (((const Div*)r2)->a.node_type())
                {
                case IRNodeType::Add: {                  0x55a8cb278760 = 0x55a8cb2787b0.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
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
                switch (((const Min*)r3)->a.node_type())
                  {
                  case IRNodeType::Div: {                    0x55a8cb27b4e0 = 0x55a8cb27b530.as<Div>();
                    break;
                  }
                  case IRNodeType::Div: {                    0x55a8cb27b4e0 = 0x55a8cb27b530.as<Div>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
                switch (((const Max*)r3)->a.node_type())
                  {
                  case IRNodeType::Div: {                    0x55a8cb27cba0 = 0x55a8cb27cbf0.as<Div>();
                    break;
                  }
                  case IRNodeType::Div: {                    0x55a8cb27cba0 = 0x55a8cb27cbf0.as<Div>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (((const Add*)r2)->a.node_type())
                {
                case IRNodeType::Div: {                  0x55a8cb27a260 = 0x55a8cb27a2b0.as<Div>();
                  break;
                }
                case IRNodeType::Min: {                  0x55a8cb27a260 = 0x55a8cb27a2b0.as<Min>();
                  break;
                }
                case IRNodeType::Max: {                  0x55a8cb27a260 = 0x55a8cb27a2b0.as<Max>();
                  break;
                }
                default:
                  break;
                }            }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb27e5e0 = 0x55a8cb27e630.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb27f790 = 0x55a8cb27f7e0.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (((const Min*)r2)->a.node_type())
                {
                case IRNodeType::Div: {                  0x55a8cb27e3d0 = 0x55a8cb27e420.as<Div>();
                  break;
                }
                case IRNodeType::Div: {                  0x55a8cb27e3d0 = 0x55a8cb27e420.as<Div>();
                  break;
                }
                default:
                  break;
                }            }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb280ad0 = 0x55a8cb280b20.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb281e60 = 0x55a8cb281eb0.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (((const Max*)r2)->a.node_type())
                {
                case IRNodeType::Div: {                  0x55a8cb2808c0 = 0x55a8cb280910.as<Div>();
                  break;
                }
                case IRNodeType::Div: {                  0x55a8cb2808c0 = 0x55a8cb280910.as<Div>();
                  break;
                }
                default:
                  break;
                }            }
            switch (b.node_type())
              {
              case IRNodeType::Div: {                0x55a8cb2785b0 = 0x55a8cb1ecea0.as<Div>();
                break;
              }
              case IRNodeType::Add: {                0x55a8cb2785b0 = 0x55a8cb1ecea0.as<Add>();
                break;
              }
              case IRNodeType::Min: {                0x55a8cb2785b0 = 0x55a8cb1ecea0.as<Min>();
                break;
              }
              case IRNodeType::Max: {                0x55a8cb2785b0 = 0x55a8cb1ecea0.as<Max>();
                break;
              }
              default:
                break;
              }          }
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
            switch (((const Add*)r3)->a.node_type())
              {
              case IRNodeType::Mul: {                0x55a8cb283400 = 0x55a8cb283450.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
            switch (((const Add*)r3)->a.node_type())
              {
              case IRNodeType::Mul: {                0x55a8cb285940 = 0x55a8cb285990.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
          switch (((const Max*)r2)->b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb2831f0 = 0x55a8cb283240.as<Add>();
              break;
            }
            case IRNodeType::Mul: {              0x55a8cb2831f0 = 0x55a8cb283240.as<Mul>();
              break;
            }
            case IRNodeType::Add: {              0x55a8cb2831f0 = 0x55a8cb283240.as<Add>();
              break;
            }
            case IRNodeType::Mul: {              0x55a8cb2831f0 = 0x55a8cb283240.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Add*)r3)->a.node_type())
              {
              case IRNodeType::Mul: {                0x55a8cb288060 = 0x55a8cb2880b0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
            switch (((const Add*)r3)->a.node_type())
              {
              case IRNodeType::Mul: {                0x55a8cb28a5a0 = 0x55a8cb28a5f0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
          switch (((const Min*)r2)->b.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb287e50 = 0x55a8cb287ea0.as<Add>();
              break;
            }
            case IRNodeType::Mul: {              0x55a8cb287e50 = 0x55a8cb287ea0.as<Mul>();
              break;
            }
            case IRNodeType::Add: {              0x55a8cb287e50 = 0x55a8cb287ea0.as<Add>();
              break;
            }
            case IRNodeType::Mul: {              0x55a8cb287e50 = 0x55a8cb287ea0.as<Mul>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Max: {            0x55a8cb282fe0 = 0x55a8cb283030.as<Max>();
            break;
          }
          case IRNodeType::Min: {            0x55a8cb282fe0 = 0x55a8cb283030.as<Min>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Div*)r1)->a.node_type())
            {
            case IRNodeType::Add: {              0x55a8cb28cb60 = 0x55a8cb28cbb0.as<Add>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb28dc60 = 0x55a8cb28dcb0.as<Add>();
                break;
              }
              default:
                break;
              }          }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb28e770 = 0x55a8cb28e7c0.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (((const Min*)r1)->a.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb28da50 = 0x55a8cb28daa0.as<Div>();
              break;
            }
            case IRNodeType::Div: {              0x55a8cb28da50 = 0x55a8cb28daa0.as<Div>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb28f400 = 0x55a8cb28f450.as<Add>();
                break;
              }
              default:
                break;
              }          }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb28ff80 = 0x55a8cb28ffd0.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (((const Max*)r1)->a.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb28f1f0 = 0x55a8cb28f240.as<Div>();
              break;
            }
            case IRNodeType::Div: {              0x55a8cb28f1f0 = 0x55a8cb28f240.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Div: {            0x55a8cb28c9e0 = 0x55a8cb1ee190.as<Div>();
            break;
          }
          case IRNodeType::Min: {            0x55a8cb28c9e0 = 0x55a8cb1ee190.as<Min>();
            break;
          }
          case IRNodeType::Max: {            0x55a8cb28c9e0 = 0x55a8cb1ee190.as<Max>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Mul: {              0x55a8cb290d00 = 0x55a8cb290d50.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Mul: {              0x55a8cb292590 = 0x55a8cb2925e0.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
        switch (((const Max*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb290af0 = 0x55a8cb290b40.as<Add>();
            break;
          }
          case IRNodeType::Mul: {            0x55a8cb290af0 = 0x55a8cb290b40.as<Mul>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb290af0 = 0x55a8cb290b40.as<Add>();
            break;
          }
          case IRNodeType::Mul: {            0x55a8cb290af0 = 0x55a8cb290b40.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Mul: {              0x55a8cb294040 = 0x55a8cb294090.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Mul: {              0x55a8cb295ad0 = 0x55a8cb295b20.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
        switch (((const Min*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb293e60 = 0x55a8cb293eb0.as<Add>();
            break;
          }
          case IRNodeType::Mul: {            0x55a8cb293e60 = 0x55a8cb293eb0.as<Mul>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb293e60 = 0x55a8cb293eb0.as<Add>();
            break;
          }
          case IRNodeType::Mul: {            0x55a8cb293e60 = 0x55a8cb293eb0.as<Mul>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Div*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb278240 = 0x55a8cb278290.as<Add>();
          break;
        }
        case IRNodeType::Max: {          0x55a8cb278240 = 0x55a8cb278290.as<Max>();
          break;
        }
        case IRNodeType::Min: {          0x55a8cb278240 = 0x55a8cb278290.as<Min>();
          break;
        }
        default:
          break;
        }    }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb297c30 = 0x55a8cb297c80.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
                switch (((const Add*)r3)->a.node_type())
                  {
                  case IRNodeType::Div: {                    0x55a8cb298d80 = 0x55a8cb298dd0.as<Div>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (b.node_type())
                {
                case IRNodeType::Div: {                  0x55a8cb297a80 = 0x55a8cb1f6c40.as<Div>();
                  break;
                }
                case IRNodeType::Add: {                  0x55a8cb297a80 = 0x55a8cb1f6c40.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb299a60 = 0x55a8cb299ab0.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb2998e0 = 0x55a8cb1f8770.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb297740 = 0x55a8cb297790.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb29aa90 = 0x55a8cb29aae0.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
                switch (((const Add*)r3)->a.node_type())
                  {
                  case IRNodeType::Div: {                    0x55a8cb29bbe0 = 0x55a8cb29bc30.as<Div>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (b.node_type())
                {
                case IRNodeType::Div: {                  0x55a8cb29a8e0 = 0x55a8cb1f99a0.as<Div>();
                  break;
                }
                case IRNodeType::Add: {                  0x55a8cb29a8e0 = 0x55a8cb1f99a0.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb29c8c0 = 0x55a8cb29c910.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb29c740 = 0x55a8cb1fb310.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb29a570 = 0x55a8cb29a5c0.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Add*)r1)->a.node_type())
            {
            case IRNodeType::Max: {              0x55a8cb29da80 = 0x55a8cb29dad0.as<Max>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Max: {            0x55a8cb29d280 = 0x55a8cb210ce0.as<Max>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb29d280 = 0x55a8cb210ce0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Max*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x55a8cb297560 = 0x55a8cb2975b0.as<Div>();
          break;
        }
        case IRNodeType::Div: {          0x55a8cb297560 = 0x55a8cb2975b0.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb29ed30 = 0x55a8cb29ed80.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
                switch (((const Add*)r3)->a.node_type())
                  {
                  case IRNodeType::Div: {                    0x55a8cb2a0060 = 0x55a8cb2a00b0.as<Div>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (b.node_type())
                {
                case IRNodeType::Div: {                  0x55a8cb29eb80 = 0x55a8cb1f7990.as<Div>();
                  break;
                }
                case IRNodeType::Add: {                  0x55a8cb29eb80 = 0x55a8cb1f7990.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb2a0e30 = 0x55a8cb2a0e80.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb2a0cb0 = 0x55a8cb1f9010.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb29e810 = 0x55a8cb29e860.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x55a8cb2a1f50 = 0x55a8cb2a1fa0.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
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
                switch (((const Add*)r3)->a.node_type())
                  {
                  case IRNodeType::Div: {                    0x55a8cb2a3280 = 0x55a8cb2a32d0.as<Div>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (b.node_type())
                {
                case IRNodeType::Div: {                  0x55a8cb2a1da0 = 0x55a8cb1fa640.as<Div>();
                  break;
                }
                case IRNodeType::Add: {                  0x55a8cb2a1da0 = 0x55a8cb1fa640.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x55a8cb2a4050 = 0x55a8cb2a40a0.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Div: {              0x55a8cb2a3ed0 = 0x55a8cb1fbbb0.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x55a8cb2a1a30 = 0x55a8cb2a1a80.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Add*)r1)->a.node_type())
            {
            case IRNodeType::Min: {              0x55a8cb2a5300 = 0x55a8cb2a5350.as<Min>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Min: {            0x55a8cb2a4b00 = 0x55a8cb20fd60.as<Min>();
            break;
          }
          case IRNodeType::Add: {            0x55a8cb2a4b00 = 0x55a8cb20fd60.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Min*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x55a8cb29e630 = 0x55a8cb29e680.as<Div>();
          break;
        }
        case IRNodeType::Div: {          0x55a8cb29e630 = 0x55a8cb29e680.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
                    switch (((const Broadcast*)r3)->value.node_type())
                      {
                      case IRNodeType::Mul: {                        0x55a8cb2a6710 = 0x55a8cb2a6760.as<Mul>();
                        break;
                      }
                      default:
                        break;
                      }                  }
                  switch (b.node_type())
                    {
                    case IRNodeType::Broadcast: {                      0x55a8cb2a6560 = 0x55a8cb211c00.as<Broadcast>();
                      break;
                    }
                    default:
                      break;
                    }                }
              }
            }
          }
        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Mul: {            0x55a8cb2a6090 = 0x55a8cb2a60e0.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
                switch (((const Broadcast*)r2)->value.node_type())
                  {
                  case IRNodeType::Mul: {                    0x55a8cb2a8680 = 0x55a8cb2a86d0.as<Mul>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (b.node_type())
                {
                case IRNodeType::Broadcast: {                  0x55a8cb2a8500 = 0x55a8cb213670.as<Broadcast>();
                  break;
                }
                default:
                  break;
                }            }
          }
        }
      }
      switch (((const Ramp*)r0)->base.node_type())
        {
        case IRNodeType::Add: {          0x55a8cb2a5eb0 = 0x55a8cb2a5f00.as<Add>();
          break;
        }
        case IRNodeType::Mul: {          0x55a8cb2a5eb0 = 0x55a8cb2a5f00.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Div: {          0x55a8cb2aa2e0 = 0x55a8cb1b0510.as<Div>();
          break;
        }
        default:
          break;
        }    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
