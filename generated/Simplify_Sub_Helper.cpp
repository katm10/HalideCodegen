b((const Ramp*)r0)->baseb((const Sub*)r0)->ab((const Sub*)r0)->b((const Sub*)r0)->ab((const Sub*)r0)->a((const Sub*)r0)->a((const Add*)r0)->a((const Add*)r0)->bb((const Add*)r0)->b((const Add*)r0)->ab((const Add*)r1)->a((const Add*)r0)->a((const Add*)r0)->b((const Add*)r0)->b((const Add*)r0)->abb((const Select*)r0)->true_value((const Add*)r1)->ab((const Select*)r0)->false_valueb((const Add*)r1)->b((const Select*)r0)->false_value((const Add*)r0)->a((const Add*)r0)->b((const Add*)r0)->ab((const Add*)r1)->ab((const Sub*)r1)->a((const Add*)r0)->ab((const Max*)r0)->a((const Add*)r1)->a((const Max*)r2)->b((const Max*)r0)->b((const Add*)r1)->a((const Max*)r2)->ab((const Max*)r1)->bb((const Min*)r0)->a((const Add*)r1)->a((const Min*)r2)->b((const Min*)r0)->b((const Add*)r1)->a((const Min*)r2)->ab((const Min*)r1)->b((const Min*)r0)->a((const Max*)r0)->a((const Max*)r0)->a((const Max*)r0)->b((const Add*)r1)->a((const Max*)r0)->a((const Add*)r1)->a((const Min*)r0)->a((const Min*)r0)->a((const Min*)r0)->b((const Add*)r1)->a((const Min*)r0)->a((const Add*)r1)->a((const Div*)r0)->a((const Div*)r0)->a((const Div*)r2)->a((const Add*)r1)->a((const Min*)r2)->b((const Div*)r0)->a((const Div*)r1)->a((const Div*)r0)->a((const Min*)r1)->b((const Add*)r1)->a((const Min*)r0)->a((const Min*)r1)->b#include "Simplify_Internal.h"
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
    switch (b.node_type())
      {
      case IRNodeType::Select: {        0x5590c9611ac0 = 0x5590c95a9080.as<Select>();
        break;
      }
      default:
        break;
      }  }
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
      switch (b.node_type())
        {
        case IRNodeType::Ramp: {          0x5590c9612840 = 0x5590c9529000.as<Ramp>();
          break;
        }
        case IRNodeType::Broadcast: {          0x5590c9612840 = 0x5590c9529000.as<Broadcast>();
          break;
        }
        default:
          break;
        }    }
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
          switch (b.node_type())
            {
            case IRNodeType::Broadcast: {              0x5590c96139b0 = 0x5590c959d250.as<Broadcast>();
              break;
            }
            default:
              break;
            }        }
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
          switch (b.node_type())
            {
            case IRNodeType::Broadcast: {              0x5590c9614730 = 0x5590c959dd60.as<Broadcast>();
              break;
            }
            default:
              break;
            }        }
      }
    }
    switch (((const Ramp*)r0)->base.node_type())
      {
      case IRNodeType::Broadcast: {        0x5590c9613640 = 0x5590c9613690.as<Broadcast>();
        break;
      }
      case IRNodeType::Ramp: {        0x5590c9613640 = 0x5590c9613690.as<Ramp>();
        break;
      }
      default:
        break;
      }  }
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
      switch (b.node_type())
        {
        case IRNodeType::Ramp: {          0x5590c96154d0 = 0x5590c9529e60.as<Ramp>();
          break;
        }
        case IRNodeType::Broadcast: {          0x5590c96154d0 = 0x5590c9529e60.as<Broadcast>();
          break;
        }
        default:
          break;
        }    }
  }
  if ((r0 = a.as<Sub>())) {
    if ((r1 = ((const Sub*)r0)->b.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (equal(((const Broadcast*)r1)->lanes, ((const Broadcast*)r2)->lanes)) {
            return (((const Sub*)r0)->a - broadcast((((const Broadcast*)r1)->value + ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes));
          }
        }
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5590c9617560 = 0x5590c959c150.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
      switch (b.node_type())
        {
        case IRNodeType::Select: {          0x5590c96180a0 = 0x5590c95a87a0.as<Select>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Sub: {          0x5590c9618a00 = 0x5590c95aa7e0.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9618a00 = 0x5590c95aa7e0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Mul: {          0x5590c9619c30 = 0x5590c95aecd0.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Mul: {          0x5590c961b440 = 0x5590c95b1710.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
    switch (((const Sub*)r0)->b.node_type())
      {
      case IRNodeType::Broadcast: {        0x5590c96172a0 = 0x5590c96172f0.as<Broadcast>();
        break;
      }
      case IRNodeType::Select: {        0x5590c96172a0 = 0x5590c96172f0.as<Select>();
        break;
      }
      case IRNodeType::Mul: {        0x5590c96172a0 = 0x5590c96172f0.as<Mul>();
        break;
      }
      case IRNodeType::Mul: {        0x5590c96172a0 = 0x5590c96172f0.as<Mul>();
        break;
      }
      case IRNodeType::Add: {        0x5590c96172a0 = 0x5590c96172f0.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5590c96172a0 = 0x5590c96172f0.as<Add>();
        break;
      }
      case IRNodeType::Sub: {        0x5590c96172a0 = 0x5590c96172f0.as<Sub>();
        break;
      }
      default:
        break;
      }  }
  if ((r0 = a.as<Add>())) {
    if ((r1 = ((const Add*)r0)->b.as<Broadcast>())) {
      if (is_const_v(((const Broadcast*)r1)->lanes)) {
        if ((r2 = b.as<Broadcast>())) {
          if (equal(((const Broadcast*)r1)->lanes, ((const Broadcast*)r2)->lanes)) {
            return (((const Add*)r0)->a + broadcast((((const Broadcast*)r1)->value - ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes));
          }
        }
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5590c961e4e0 = 0x5590c959c9d0.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
      switch (b.node_type())
        {
        case IRNodeType::Select: {          0x5590c961f190 = 0x5590c95a64b0.as<Select>();
          break;
        }
        default:
          break;
        }    }
    if ((r1 = ((const Add*)r0)->b.as<Select>())) {
      if ((r2 = b.as<Select>())) {
        if (equal(((const Select*)r1)->condition, ((const Select*)r2)->condition)) {
          return (select(((const Select*)r1)->condition, (((const Select*)r1)->true_value - ((const Select*)r2)->true_value), (((const Select*)r1)->false_value - ((const Select*)r2)->false_value)) + ((const Add*)r0)->a);
        }
      }
      switch (b.node_type())
        {
        case IRNodeType::Select: {          0x5590c961fbd0 = 0x5590c95a6ec0.as<Select>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Sub: {          0x5590c96207d0 = 0x5590c95a99a0.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x5590c96207d0 = 0x5590c95a99a0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Mul: {          0x5590c9621930 = 0x5590c95ad770.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::Mul: {          0x5590c9623130 = 0x5590c95b0210.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Add*)r1)->b.node_type())
        {
        case IRNodeType::Add: {          0x5590c9625570 = 0x5590c96255c0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9625570 = 0x5590c96255c0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
    switch (((const Add*)r0)->b.node_type())
      {
      case IRNodeType::Broadcast: {        0x5590c961e220 = 0x5590c961e270.as<Broadcast>();
        break;
      }
      case IRNodeType::Select: {        0x5590c961e220 = 0x5590c961e270.as<Select>();
        break;
      }
      case IRNodeType::Select: {        0x5590c961e220 = 0x5590c961e270.as<Select>();
        break;
      }
      case IRNodeType::Mul: {        0x5590c961e220 = 0x5590c961e270.as<Mul>();
        break;
      }
      case IRNodeType::Mul: {        0x5590c961e220 = 0x5590c961e270.as<Mul>();
        break;
      }
      case IRNodeType::Add: {        0x5590c961e220 = 0x5590c961e270.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5590c961e220 = 0x5590c961e270.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5590c961e220 = 0x5590c961e270.as<Add>();
        break;
      }
      case IRNodeType::Sub: {        0x5590c961e220 = 0x5590c961e270.as<Sub>();
        break;
      }
      case IRNodeType::Sub: {        0x5590c961e220 = 0x5590c961e270.as<Sub>();
        break;
      }
      case IRNodeType::Min: {        0x5590c961e220 = 0x5590c961e270.as<Min>();
        break;
      }
      case IRNodeType::Max: {        0x5590c961e220 = 0x5590c961e270.as<Max>();
        break;
      }
      default:
        break;
      }  }
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
      switch (((const Add*)r1)->b.node_type())
        {
        case IRNodeType::Add: {          0x5590c962c4c0 = 0x5590c962c510.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c962c4c0 = 0x5590c962c510.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c962c4c0 = 0x5590c962c510.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Add*)r1)->a.node_type())
        {
        case IRNodeType::Select: {          0x5590c9630310 = 0x5590c9630360.as<Select>();
          break;
        }
        case IRNodeType::Select: {          0x5590c9630310 = 0x5590c9630360.as<Select>();
          break;
        }
        default:
          break;
        }    }
    switch (b.node_type())
      {
      case IRNodeType::Select: {        0x5590c962aa40 = 0x5590c959e900.as<Select>();
        break;
      }
      case IRNodeType::Add: {        0x5590c962aa40 = 0x5590c959e900.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5590c962aa40 = 0x5590c959e900.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5590c962aa40 = 0x5590c959e900.as<Add>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Select*)r0)->true_value.node_type())
      {
      case IRNodeType::Add: {        0x5590c9631e30 = 0x5590c9631e80.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5590c9631e30 = 0x5590c9631e80.as<Add>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Add*)r0)->b.node_type())
      {
      case IRNodeType::Sub: {        0x5590c9633e20 = 0x5590c9633e70.as<Sub>();
        break;
      }
      case IRNodeType::Sub: {        0x5590c9633e20 = 0x5590c9633e70.as<Sub>();
        break;
      }
      case IRNodeType::Add: {        0x5590c9633e20 = 0x5590c9633e70.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5590c9633e20 = 0x5590c9633e70.as<Add>();
        break;
      }
      default:
        break;
      }  }
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
      switch (((const Div*)r1)->a.node_type())
        {
        case IRNodeType::Add: {          0x5590c96367b0 = 0x5590c9636800.as<Add>();
          break;
        }
        default:
          break;
        }    }
    switch (((const Mul*)r0)->a.node_type())
      {
      case IRNodeType::Div: {        0x5590c96365a0 = 0x5590c96365f0.as<Div>();
        break;
      }
      default:
        break;
      }  }
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
      switch (((const Add*)r1)->b.node_type())
        {
        case IRNodeType::Mul: {          0x5590c96387c0 = 0x5590c9638810.as<Mul>();
          break;
        }
        case IRNodeType::Mul: {          0x5590c96387c0 = 0x5590c9638810.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Sub*)r1)->b.node_type())
        {
        case IRNodeType::Mul: {          0x5590c963b5e0 = 0x5590c963b630.as<Mul>();
          break;
        }
        case IRNodeType::Mul: {          0x5590c963b5e0 = 0x5590c963b630.as<Mul>();
          break;
        }
        default:
          break;
        }    }
    switch (b.node_type())
      {
      case IRNodeType::Mul: {        0x5590c96373e0 = 0x5590c95ac640.as<Mul>();
        break;
      }
      case IRNodeType::Add: {        0x5590c96373e0 = 0x5590c95ac640.as<Add>();
        break;
      }
      case IRNodeType::Sub: {        0x5590c96373e0 = 0x5590c95ac640.as<Sub>();
        break;
      }
      default:
        break;
      }  }
  if ((r0 = b.as<Min>())) {
    if ((r1 = ((const Min*)r0)->a.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->a)) {
        if (is_const_int(((const Min*)r0)->b, 0)) {
          return max(a, ((const Sub*)r1)->b);
        }
      }
    }
    switch (((const Min*)r0)->a.node_type())
      {
      case IRNodeType::Sub: {        0x5590c963e440 = 0x5590c963e490.as<Sub>();
        break;
      }
      default:
        break;
      }  }
  if ((r0 = b.as<Max>())) {
    if ((r1 = ((const Max*)r0)->a.as<Sub>())) {
      if (equal(a, ((const Sub*)r1)->a)) {
        if (is_const_int(((const Max*)r0)->b, 0)) {
          return min(a, ((const Sub*)r1)->b);
        }
      }
    }
    switch (((const Max*)r0)->a.node_type())
      {
      case IRNodeType::Sub: {        0x5590c963eb20 = 0x5590c963eb70.as<Sub>();
        break;
      }
      default:
        break;
      }  }
  if (is_const_int(a, 0)) {
    if ((r0 = b.as<Add>())) {
      if ((r1 = ((const Add*)r0)->b.as<Sub>())) {
        return (((const Sub*)r1)->b - (((const Add*)r0)->a + ((const Sub*)r1)->a));
      }
      if ((r1 = ((const Add*)r0)->a.as<Sub>())) {
        return (((const Sub*)r1)->b - (((const Sub*)r1)->a + ((const Add*)r0)->b));
      }
      switch (((const Add*)r0)->b.node_type())
        {
        case IRNodeType::Sub: {          0x5590c963f260 = 0x5590c963f2b0.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5590c963f260 = 0x5590c963f2b0.as<Sub>();
          break;
        }
        default:
          break;
        }    }
    switch (b.node_type())
      {
      case IRNodeType::Add: {        0x5590c963f0e0 = 0x5590c95c0c00.as<Add>();
        break;
      }
      default:
        break;
      }  }
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
            switch (((const Max*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x5590c9645120 = 0x5590c9645170.as<Add>();
                break;
              }
              case IRNodeType::Add: {                0x5590c9645120 = 0x5590c9645170.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Max: {              0x5590c9643f30 = 0x5590c95ee8c0.as<Max>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c96427c0 = 0x5590c9642810.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c96427c0 = 0x5590c9642810.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
            switch (((const Max*)r2)->b.node_type())
              {
              case IRNodeType::Add: {                0x5590c964c4f0 = 0x5590c964c540.as<Add>();
                break;
              }
              case IRNodeType::Add: {                0x5590c964c4f0 = 0x5590c964c540.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Max: {              0x5590c964b300 = 0x5590c95f2600.as<Max>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c9649b90 = 0x5590c9649be0.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9649b90 = 0x5590c9649be0.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Max*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c9652e40 = 0x5590c9652e90.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9652e40 = 0x5590c9652e90.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Max*)r0)->a.node_type())
        {
        case IRNodeType::Sub: {          0x5590c9640c70 = 0x5590c9640cc0.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9640c70 = 0x5590c9640cc0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9640c70 = 0x5590c9640cc0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9640c70 = 0x5590c9640cc0.as<Add>();
          break;
        }
        case IRNodeType::Max: {          0x5590c9640c70 = 0x5590c9640cc0.as<Max>();
          break;
        }
        default:
          break;
        }    }
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
            switch (((const Min*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x5590c965e210 = 0x5590c965e260.as<Add>();
                break;
              }
              case IRNodeType::Add: {                0x5590c965e210 = 0x5590c965e260.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Min: {              0x5590c965d020 = 0x5590c95dfc80.as<Min>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c965b8b0 = 0x5590c965b900.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c965b8b0 = 0x5590c965b900.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
            switch (((const Min*)r2)->b.node_type())
              {
              case IRNodeType::Add: {                0x5590c96655e0 = 0x5590c9665630.as<Add>();
                break;
              }
              case IRNodeType::Add: {                0x5590c96655e0 = 0x5590c9665630.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Min: {              0x5590c96643f0 = 0x5590c95e39c0.as<Min>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c9662c80 = 0x5590c9662cd0.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9662c80 = 0x5590c9662cd0.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Min*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c966bf30 = 0x5590c966bf80.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c966bf30 = 0x5590c966bf80.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
              switch (((const Mul*)r2)->a.node_type())
                {
                case IRNodeType::Min: {                  0x5590c9672b20 = 0x5590c9672b70.as<Min>();
                  break;
                }
                default:
                  break;
                }            }
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5590c9672970 = 0x5590c95d48a0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
        }
      }
      switch (((const Min*)r0)->a.node_type())
        {
        case IRNodeType::Sub: {          0x5590c9659d60 = 0x5590c9659db0.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9659d60 = 0x5590c9659db0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9659d60 = 0x5590c9659db0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9659d60 = 0x5590c9659db0.as<Add>();
          break;
        }
        case IRNodeType::Min: {          0x5590c9659d60 = 0x5590c9659db0.as<Min>();
          break;
        }
        case IRNodeType::Mul: {          0x5590c9659d60 = 0x5590c9659db0.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Min*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x5590c9675560 = 0x5590c96755b0.as<Sub>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c9676bc0 = 0x5590c9676c10.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9676bc0 = 0x5590c9676c10.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c9679550 = 0x5590c96795a0.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9679550 = 0x5590c96795a0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Max*)r0)->b.node_type())
        {
        case IRNodeType::Sub: {          0x5590c9674390 = 0x5590c96743e0.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5590c9674390 = 0x5590c96743e0.as<Sub>();
          break;
        }
        case IRNodeType::Min: {          0x5590c9674390 = 0x5590c96743e0.as<Min>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9674390 = 0x5590c96743e0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c9674390 = 0x5590c96743e0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Max*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x5590c967ce60 = 0x5590c967ceb0.as<Sub>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c967e4c0 = 0x5590c967e510.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c967e4c0 = 0x5590c967e510.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Add: {            0x5590c9680e50 = 0x5590c9680ea0.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9680e50 = 0x5590c9680ea0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Min*)r0)->b.node_type())
        {
        case IRNodeType::Sub: {          0x5590c967bc90 = 0x5590c967bce0.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5590c967bc90 = 0x5590c967bce0.as<Sub>();
          break;
        }
        case IRNodeType::Max: {          0x5590c967bc90 = 0x5590c967bce0.as<Max>();
          break;
        }
        case IRNodeType::Add: {          0x5590c967bc90 = 0x5590c967bce0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5590c967bc90 = 0x5590c967bce0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Div*)r0)->a.node_type())
          {
          case IRNodeType::Sub: {            0x5590c9683d60 = 0x5590c9683db0.as<Sub>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9683d60 = 0x5590c9683db0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (b.node_type())
        {
        case IRNodeType::Div: {          0x5590c9683bb0 = 0x5590c95fcb30.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Div*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x5590c96855b0 = 0x5590c9685600.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5590c96855b0 = 0x5590c9685600.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x5590c9688f30 = 0x5590c9688f80.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Div: {              0x5590c9688d80 = 0x5590c9605c70.as<Div>();
              break;
            }
            default:
              break;
            }        }
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
                switch (((const Add*)r4)->a.node_type())
                  {
                  case IRNodeType::Add: {                    0x5590c968b150 = 0x5590c968b1a0.as<Add>();
                    break;
                  }
                  default:
                    break;
                  }              }
              switch (((const Div*)r3)->a.node_type())
                {
                case IRNodeType::Add: {                  0x5590c968af40 = 0x5590c968af90.as<Add>();
                  break;
                }
                default:
                  break;
                }            }
            switch (b.node_type())
              {
              case IRNodeType::Div: {                0x5590c968ad90 = 0x5590c9604cb0.as<Div>();
                break;
              }
              default:
                break;
              }          }
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
              switch (((const Div*)r2)->a.node_type())
                {
                case IRNodeType::Add: {                  0x5590c968c360 = 0x5590c968c3b0.as<Add>();
                  break;
                }
                case IRNodeType::Sub: {                  0x5590c968c360 = 0x5590c968c3b0.as<Sub>();
                  break;
                }
                default:
                  break;
                }            }
            switch (b.node_type())
              {
              case IRNodeType::Div: {                0x5590c968c1e0 = 0x5590c9606d70.as<Div>();
                break;
              }
              default:
                break;
              }          }
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
                  switch (b.node_type())
                    {
                    case IRNodeType::Mul: {                      0x5590c968e840 = 0x5590c960fad0.as<Mul>();
                      break;
                    }
                    default:
                      break;
                    }                }
              }
            }
            switch (((const Add*)r3)->a.node_type())
              {
              case IRNodeType::Mul: {                0x5590c968e4d0 = 0x5590c968e520.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
                  switch (b.node_type())
                    {
                    case IRNodeType::Mul: {                      0x5590c968fa40 = 0x5590c96109e0.as<Mul>();
                      break;
                    }
                    default:
                      break;
                    }                }
              }
            }
            switch (((const Add*)r3)->a.node_type())
              {
              case IRNodeType::Mul: {                0x5590c968f700 = 0x5590c968f750.as<Mul>();
                break;
              }
              default:
                break;
              }          }
          switch (((const Min*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x5590c968e2c0 = 0x5590c968e310.as<Add>();
              break;
            }
            case IRNodeType::Add: {              0x5590c968e2c0 = 0x5590c968e310.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c968ab00 = 0x5590c968ab50.as<Add>();
            break;
          }
          case IRNodeType::Min: {            0x5590c968ab00 = 0x5590c968ab50.as<Min>();
            break;
          }
          default:
            break;
          }      }
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
            switch (((const Div*)r2)->a.node_type())
              {
              case IRNodeType::Add: {                0x5590c96915d0 = 0x5590c9691620.as<Add>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Div: {              0x5590c9691420 = 0x5590c9607a50.as<Div>();
              break;
            }
            default:
              break;
            }        }
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
          switch (((const Div*)r1)->a.node_type())
            {
            case IRNodeType::Add: {              0x5590c9692dd0 = 0x5590c9692e20.as<Add>();
              break;
            }
            case IRNodeType::Sub: {              0x5590c9692dd0 = 0x5590c9692e20.as<Sub>();
              break;
            }
            default:
              break;
            }        }
        switch (b.node_type())
          {
          case IRNodeType::Div: {            0x5590c9692c50 = 0x5590c9609100.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
                switch (b.node_type())
                  {
                  case IRNodeType::Mul: {                    0x5590c9694ca0 = 0x5590c960e010.as<Mul>();
                    break;
                  }
                  default:
                    break;
                  }              }
            }
          }
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Mul: {              0x5590c9694930 = 0x5590c9694980.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
                switch (b.node_type())
                  {
                  case IRNodeType::Mul: {                    0x5590c9695db0 = 0x5590c960ee30.as<Mul>();
                    break;
                  }
                  default:
                    break;
                  }              }
            }
          }
          switch (((const Add*)r2)->a.node_type())
            {
            case IRNodeType::Mul: {              0x5590c9695a70 = 0x5590c9695ac0.as<Mul>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Min*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c9694720 = 0x5590c9694770.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c9694720 = 0x5590c9694770.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Div*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x5590c9687ff0 = 0x5590c9688040.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5590c9687ff0 = 0x5590c9688040.as<Sub>();
          break;
        }
        case IRNodeType::Min: {          0x5590c9687ff0 = 0x5590c9688040.as<Min>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c96973b0 = 0x5590c9697400.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (b.node_type())
          {
          case IRNodeType::Mul: {            0x5590c9698070 = 0x5590c9603df0.as<Mul>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x5590c9696b30 = 0x5590c9696b80.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c9699bb0 = 0x5590c9699c00.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x5590c9699380 = 0x5590c96993d0.as<Div>();
          break;
        }
        default:
          break;
        }    }
    if ((r0 = a.as<Add>())) {
      if ((r1 = ((const Add*)r0)->a.as<Min>())) {
        if ((r2 = ((const Min*)r1)->a.as<Add>())) {
          if (equal(((const Add*)r2)->a, b)) {
            return (min((((const Min*)r1)->b - ((const Add*)r2)->a), ((const Add*)r2)->b) + ((const Add*)r0)->b);
          }
        }
        switch (((const Min*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c969ad50 = 0x5590c969ada0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Add*)r0)->a.node_type())
        {
        case IRNodeType::Min: {          0x5590c969ab40 = 0x5590c969ab90.as<Min>();
          break;
        }
        default:
          break;
        }    }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5590c969c270 = 0x5590c960ce10.as<Mul>();
                break;
              }
              default:
                break;
              }          }
          switch (((const Mul*)r2)->a.node_type())
            {
            case IRNodeType::Add: {              0x5590c969c060 = 0x5590c969c0b0.as<Add>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c969b790 = 0x5590c969b7e0.as<Add>();
            break;
          }
          case IRNodeType::Mul: {            0x5590c969b790 = 0x5590c969b7e0.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Min*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5590c969d680 = 0x5590c969d6d0.as<Add>();
            break;
          }
          case IRNodeType::Add: {            0x5590c969d680 = 0x5590c969d6d0.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Min*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x5590c969b5b0 = 0x5590c969b600.as<Add>();
          break;
        }
        case IRNodeType::Min: {          0x5590c969b5b0 = 0x5590c969b600.as<Min>();
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
