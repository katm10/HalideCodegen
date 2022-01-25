bb((const Max*)r0)->b((const Max*)r0)->a((const Max*)r0)->b((const Max*)r0)->a((const Max*)r0)->a((const Min*)r0)->a((const Min*)r0)->ab((const Min*)r0)->a((const Select*)r0)->false_value((const Select*)r0)->condition((const Select*)r0)->true_value((const Select*)r0)->false_valueb((const Add*)r0)->a((const Add*)r0)->ab((const Add*)r0)->a((const Add*)r0)->a((const Add*)r0)->b((const Add*)r0)->a((const Add*)r0)->a((const Add*)r0)->a((const Add*)r0)->a((const Add*)r0)->b((const Mul*)r0)->a((const Add*)r3)->b((const Add*)r1)->b((const Add*)r3)->bb((const Max*)r0)->a((const Max*)r0)->bb((const Add*)r1)->b((const Sub*)r0)->abb((const Min*)r0)->b((const Select*)r0)->true_value((const Select*)r0)->false_value#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"
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
    switch (((const Mul*)r0)->a.node_type())
      {
      case IRNodeType::Div: {        0x5629543b1b70 = 0x5629543b1bc0.as<Div>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Mul*)r0)->a.node_type())
      {
      case IRNodeType::Div: {        0x5629543b24d0 = 0x5629543b2520.as<Div>();
        break;
      }
      default:
        break;
      }  }
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
        switch (((const Max*)r2)->a.node_type())
          {
          case IRNodeType::Max: {            0x5629543b4820 = 0x5629543b4870.as<Max>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Max*)r1)->a.node_type())
        {
        case IRNodeType::Max: {          0x5629543b3ca0 = 0x5629543b3cf0.as<Max>();
          break;
        }
        default:
          break;
        }    }
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
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (equal(((const Broadcast*)r1)->lanes, ((const Broadcast*)r2)->lanes)) {
            return max(((const Max*)r0)->a, broadcast(max(((const Broadcast*)r1)->value, ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes));
          }
        }
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5629543b8920 = 0x562954388400.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
        switch (b.node_type())
          {
          case IRNodeType::Div: {            0x5629543b9290 = 0x56295438a410.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
    switch (((const Max*)r0)->a.node_type())
      {
      case IRNodeType::Max: {        0x5629543b3300 = 0x5629543b3350.as<Max>();
        break;
      }
      case IRNodeType::Min: {        0x5629543b3300 = 0x5629543b3350.as<Min>();
        break;
      }
      case IRNodeType::Max: {        0x5629543b3300 = 0x5629543b3350.as<Max>();
        break;
      }
      case IRNodeType::Broadcast: {        0x5629543b3300 = 0x5629543b3350.as<Broadcast>();
        break;
      }
      case IRNodeType::Div: {        0x5629543b3300 = 0x5629543b3350.as<Div>();
        break;
      }
      case IRNodeType::Min: {        0x5629543b3300 = 0x5629543b3350.as<Min>();
        break;
      }
      case IRNodeType::Min: {        0x5629543b3300 = 0x5629543b3350.as<Min>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Max*)r0)->b.node_type())
      {
      case IRNodeType::Min: {        0x5629543bb0f0 = 0x5629543bb140.as<Min>();
        break;
      }
      case IRNodeType::Min: {        0x5629543bb0f0 = 0x5629543bb140.as<Min>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Min*)r0)->b.node_type())
      {
      case IRNodeType::Min: {        0x5629543bc340 = 0x5629543bc390.as<Min>();
        break;
      }
      case IRNodeType::Min: {        0x5629543bc340 = 0x5629543bc390.as<Min>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Min*)r0)->b.node_type())
      {
      case IRNodeType::Min: {        0x5629543bd620 = 0x5629543bd670.as<Min>();
        break;
      }
      case IRNodeType::Min: {        0x5629543bd620 = 0x5629543bd670.as<Min>();
        break;
      }
      case IRNodeType::Min: {        0x5629543bd620 = 0x5629543bd670.as<Min>();
        break;
      }
      case IRNodeType::Max: {        0x5629543bd620 = 0x5629543bd670.as<Max>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Select*)r0)->true_value.node_type())
      {
      case IRNodeType::Max: {        0x5629543bfec0 = 0x5629543bff10.as<Max>();
        break;
      }
      case IRNodeType::Max: {        0x5629543bfec0 = 0x5629543bff10.as<Max>();
        break;
      }
      case IRNodeType::EQ: {        0x5629543bfec0 = 0x5629543bff10.as<EQ>();
        break;
      }
      case IRNodeType::Min: {        0x5629543bfec0 = 0x5629543bff10.as<Min>();
        break;
      }
      case IRNodeType::Min: {        0x5629543bfec0 = 0x5629543bff10.as<Min>();
        break;
      }
      case IRNodeType::Select: {        0x5629543bfec0 = 0x5629543bff10.as<Select>();
        break;
      }
      default:
        break;
      }  }
  if (type.is_no_overflow()) {
    if ((r0 = a.as<Ramp>())) {
      if (is_const_v(((const Ramp*)r0)->lanes)) {
        if ((r1 = b.as<Broadcast>())) {
          if (equal(((const Ramp*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
            if (evaluate_predicate(fold(can_prove((((((const Ramp*)r0)->base + (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))) >= ((const Broadcast*)r1)->value) && (((const Ramp*)r0)->base >= ((const Broadcast*)r1)->value)), simplifier)))) {
              return ramp(((const Ramp*)r0)->base, ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
            }
            if (evaluate_predicate(fold(can_prove((((((const Ramp*)r0)->base + (((const Ramp*)r0)->stride * (((const Ramp*)r0)->lanes - 1))) <= ((const Broadcast*)r1)->value) && (((const Ramp*)r0)->base <= ((const Broadcast*)r1)->value)), simplifier)))) {
              return broadcast(((const Broadcast*)r1)->value, ((const Ramp*)r0)->lanes);
            }
          }
        }
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5629543c48e0 = 0x56295437bf40.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x5629543c6340 = 0x5629543c6390.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Mul*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x5629543c6130 = 0x5629543c6180.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
        switch (b.node_type())
          {
          case IRNodeType::Add: {            0x5629543cacf0 = 0x562954393c70.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5629543ccf70 = 0x5629543ccfc0.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (b.node_type())
          {
          case IRNodeType::Add: {            0x5629543cedf0 = 0x56295439d340.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
      switch (((const Add*)r0)->a.node_type())
        {
        case IRNodeType::Mul: {          0x5629543c5f20 = 0x5629543c5f70.as<Mul>();
          break;
        }
        case IRNodeType::Min: {          0x5629543c5f20 = 0x5629543c5f70.as<Min>();
          break;
        }
        case IRNodeType::Max: {          0x5629543c5f20 = 0x5629543c5f70.as<Max>();
          break;
        }
        case IRNodeType::Add: {          0x5629543c5f20 = 0x5629543c5f70.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5629543c5f20 = 0x5629543c5f70.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5629543c5f20 = 0x5629543c5f70.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5629543c5f20 = 0x5629543c5f70.as<Sub>();
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
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x5629543d1f60 = 0x5629543d1fb0.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Mul*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x5629543d1d50 = 0x5629543d1da0.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
      switch (((const Add*)r0)->a.node_type())
        {
        case IRNodeType::Mul: {          0x5629543d1b40 = 0x5629543d1b90.as<Mul>();
          break;
        }
        case IRNodeType::Min: {          0x5629543d1b40 = 0x5629543d1b90.as<Min>();
          break;
        }
        case IRNodeType::Max: {          0x5629543d1b40 = 0x5629543d1b90.as<Max>();
          break;
        }
        case IRNodeType::Add: {          0x5629543d1b40 = 0x5629543d1b90.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5629543d1b40 = 0x5629543d1b90.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5629543d1b40 = 0x5629543d1b90.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
                switch (((const Mul*)r3)->a.node_type())
                  {
                  case IRNodeType::Div: {                    0x5629543d85e0 = 0x5629543d8630.as<Div>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (((const Add*)r2)->a.node_type())
                {
                case IRNodeType::Mul: {                  0x5629543d83d0 = 0x5629543d8420.as<Mul>();
                  break;
                }
                default:
                  break;
                }            }
            switch (b.node_type())
              {
              case IRNodeType::Add: {                0x5629543d8220 = 0x56295437fbd0.as<Add>();
                break;
              }
              default:
                break;
              }          }
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
                switch (b.node_type())
                  {
                  case IRNodeType::Add: {                    0x5629543da620 = 0x5629543abac0.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
            }
          }
        }
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5629543d9540 = 0x5629543d9590.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
                switch (((const Add*)r3)->a.node_type())
                  {
                  case IRNodeType::Mul: {                    0x5629543db9e0 = 0x5629543dba30.as<Mul>();
                    break;
                  }
                  case IRNodeType::Mul: {                    0x5629543db9e0 = 0x5629543dba30.as<Mul>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (b.node_type())
                {
                case IRNodeType::Add: {                  0x5629543db830 = 0x562954397aa0.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
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
                switch (((const Add*)r3)->a.node_type())
                  {
                  case IRNodeType::Mul: {                    0x5629543dd6b0 = 0x5629543dd700.as<Mul>();
                    break;
                  }
                  case IRNodeType::Mul: {                    0x5629543dd6b0 = 0x5629543dd700.as<Mul>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (b.node_type())
                {
                case IRNodeType::Add: {                  0x5629543dd500 = 0x5629543989f0.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
          }
        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Mul: {            0x5629543db4c0 = 0x5629543db510.as<Mul>();
            break;
          }
          case IRNodeType::Mul: {            0x5629543db4c0 = 0x5629543db510.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Add*)r1)->a.node_type())
            {
            case IRNodeType::Mul: {              0x5629543e25c0 = 0x5629543e2610.as<Mul>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Mul: {            0x5629543dfde0 = 0x5629543a5a90.as<Mul>();
            break;
          }
          case IRNodeType::Add: {            0x5629543dfde0 = 0x5629543a5a90.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x5629543d7e70 = 0x5629543d7ec0.as<Div>();
          break;
        }
        case IRNodeType::Add: {          0x5629543d7e70 = 0x5629543d7ec0.as<Add>();
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
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5629543e3fc0 = 0x5629543e4010.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x5629543e3de0 = 0x5629543e3e30.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
        switch (b.node_type())
          {
          case IRNodeType::Add: {            0x5629543e69a0 = 0x56295439a970.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (b.node_type())
          {
          case IRNodeType::Add: {            0x5629543e8180 = 0x56295439afb0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (b.node_type())
        {
        case IRNodeType::Add: {          0x5629543e5210 = 0x562954394a20.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5629543e5210 = 0x562954394a20.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5629543e5210 = 0x562954394a20.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x5629543ea4b0 = 0x5629543ea500.as<Sub>();
            break;
          }
          case IRNodeType::Sub: {            0x5629543ea4b0 = 0x5629543ea500.as<Sub>();
            break;
          }
          default:
            break;
          }      }
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
      switch (b.node_type())
        {
        case IRNodeType::Sub: {          0x5629543e9970 = 0x5629543a0df0.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x5629543e9970 = 0x5629543a0df0.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5629543e9970 = 0x5629543a0df0.as<Sub>();
          break;
        }
        default:
          break;
        }    }
    if ((r0 = b.as<Sub>())) {
      if (equal(a, ((const Sub*)r0)->a)) {
        return (a - min(((const Sub*)r0)->b, 0));
      }
      if ((r1 = ((const Sub*)r0)->a.as<Sub>())) {
        if (equal(a, ((const Sub*)r1)->a)) {
          return (a - min((((const Sub*)r1)->b + ((const Sub*)r0)->b), 0));
        }
      }
      switch (((const Sub*)r0)->a.node_type())
        {
        case IRNodeType::Sub: {          0x5629543ec5c0 = 0x5629543ec610.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
          switch (((const Add*)r1)->a.node_type())
            {
            case IRNodeType::Div: {              0x5629543eeac0 = 0x5629543eeb10.as<Div>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x5629543f04f0 = 0x5629543f0540.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (((const Mul*)r1)->a.node_type())
            {
            case IRNodeType::Div: {              0x5629543f0310 = 0x5629543f0360.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Div: {            0x5629543ecdd0 = 0x5629543a8d90.as<Div>();
            break;
          }
          case IRNodeType::Add: {            0x5629543ecdd0 = 0x5629543a8d90.as<Add>();
            break;
          }
          case IRNodeType::Mul: {            0x5629543ecdd0 = 0x5629543a8d90.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
                switch (((const Div*)r3)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x5629543f3200 = 0x5629543f3250.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (((const Mul*)r2)->a.node_type())
                {
                case IRNodeType::Div: {                  0x5629543f2ff0 = 0x5629543f3040.as<Div>();
                  break;
                }
                default:
                  break;
                }            }
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5629543f2e40 = 0x5629543ac400.as<Mul>();
                break;
              }
              default:
                break;
              }          }
        }
      }
      switch (((const Div*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x5629543f2b00 = 0x5629543f2b50.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Min*)r0)->a.node_type())
        {
        case IRNodeType::Sub: {          0x5629543f6bd0 = 0x5629543f6c20.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5629543f6bd0 = 0x5629543f6c20.as<Sub>();
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
          return broadcast(max(((const Broadcast*)r0)->value, ((const Broadcast*)r1)->value), ((const Broadcast*)r0)->lanes);
        }
      }
      switch (b.node_type())
        {
        case IRNodeType::Broadcast: {          0x5629543f7db0 = 0x562954387e00.as<Broadcast>();
          break;
        }
        default:
          break;
        }    }
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
    switch (((const Select*)r0)->condition.node_type())
      {
      case IRNodeType::EQ: {        0x5629543f8500 = 0x5629543f8550.as<EQ>();
        break;
      }
      case IRNodeType::Min: {        0x5629543f8500 = 0x5629543f8550.as<Min>();
        break;
      }
      case IRNodeType::Min: {        0x5629543f8500 = 0x5629543f8550.as<Min>();
        break;
      }
      default:
        break;
      }  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
