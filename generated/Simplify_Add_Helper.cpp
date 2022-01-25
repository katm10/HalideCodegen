b((const Ramp*)r0)->base((const Add*)r0)->a((const Add*)r0)->a((const Add*)r0)->b((const Sub*)r0)->abb((const Sub*)r0)->a((const Sub*)r0)->b((const Select*)r0)->true_valueb((const Add*)r1)->bb((const Sub*)r1)->b((const Select*)r0)->true_value((const Select*)r0)->false_valueb((const Add*)r0)->b((const Sub*)r0)->b((const Div*)r0)->a((const Add*)r0)->a((const Div*)r0)->a((const Min*)r0)->a((const Min*)r0)->b((const Add*)r1)->a((const Min*)r0)->a((const Add*)r1)->a((const Min*)r0)->b((const Min*)r0)->a((const Min*)r0)->a((const Max*)r0)->a((const Max*)r0)->a((const Max*)r0)->b((const Add*)r1)->a((const Max*)r0)->a((const Add*)r1)->ab((const Max*)r0)->b((const Max*)r0)->ab((const Add*)r2)->bb((const Mul*)r0)->ab((const Add*)r2)->bb((const Mul*)r0)->b((const Add*)r1)->a((const Mul*)r0)->a((const Add*)r1)->a((const Add*)r1)->bb((const Mul*)r0)->a((const Add*)r1)->b#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"
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
      switch (b.node_type())
        {
        case IRNodeType::Ramp: {          0x5651f3ea4960 = 0x5651f3e41cc0.as<Ramp>();
          break;
        }
        case IRNodeType::Broadcast: {          0x5651f3ea4960 = 0x5651f3e41cc0.as<Broadcast>();
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
                return ramp(broadcast((((const Broadcast*)r1)->value + ((const Broadcast*)r2)->value), ((const Broadcast*)r1)->lanes), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
              }
            }
          }
          switch (b.node_type())
            {
            case IRNodeType::Broadcast: {              0x5651f3ea5ad0 = 0x5651f3e76830.as<Broadcast>();
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
                return ramp(ramp((((const Ramp*)r1)->base + ((const Broadcast*)r2)->value), ((const Ramp*)r1)->stride, ((const Ramp*)r1)->lanes), ((const Ramp*)r0)->stride, ((const Ramp*)r0)->lanes);
              }
            }
          }
          switch (b.node_type())
            {
            case IRNodeType::Broadcast: {              0x5651f3ea6850 = 0x5651f3e77280.as<Broadcast>();
              break;
            }
            default:
              break;
            }        }
      }
    }
    switch (((const Ramp*)r0)->base.node_type())
      {
      case IRNodeType::Broadcast: {        0x5651f3ea5760 = 0x5651f3ea57b0.as<Broadcast>();
        break;
      }
      case IRNodeType::Ramp: {        0x5651f3ea5760 = 0x5651f3ea57b0.as<Ramp>();
        break;
      }
      default:
        break;
      }  }
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
      switch (b.node_type())
        {
        case IRNodeType::Broadcast: {          0x5651f3ea75f0 = 0x5651f3e42b20.as<Broadcast>();
          break;
        }
        default:
          break;
        }    }
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
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5651f3ea8b70 = 0x5651f3e6f880.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5651f3eaa1a0 = 0x5651f3e70bc0.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
    switch (((const Add*)r0)->b.node_type())
      {
      case IRNodeType::Broadcast: {        0x5651f3ea88b0 = 0x5651f3ea8900.as<Broadcast>();
        break;
      }
      case IRNodeType::Broadcast: {        0x5651f3ea88b0 = 0x5651f3ea8900.as<Broadcast>();
        break;
      }
      case IRNodeType::Sub: {        0x5651f3ea88b0 = 0x5651f3ea8900.as<Sub>();
        break;
      }
      case IRNodeType::Sub: {        0x5651f3ea88b0 = 0x5651f3ea8900.as<Sub>();
        break;
      }
      default:
        break;
      }  }
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
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5651f3eac990 = 0x5651f3e71d90.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
        switch (b.node_type())
          {
          case IRNodeType::Broadcast: {            0x5651f3eadfc0 = 0x5651f3e73070.as<Broadcast>();
            break;
          }
          default:
            break;
          }      }
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
    switch (((const Sub*)r0)->b.node_type())
      {
      case IRNodeType::Broadcast: {        0x5651f3eac6d0 = 0x5651f3eac720.as<Broadcast>();
        break;
      }
      case IRNodeType::Broadcast: {        0x5651f3eac6d0 = 0x5651f3eac720.as<Broadcast>();
        break;
      }
      case IRNodeType::Sub: {        0x5651f3eac6d0 = 0x5651f3eac720.as<Sub>();
        break;
      }
      case IRNodeType::Add: {        0x5651f3eac6d0 = 0x5651f3eac720.as<Add>();
        break;
      }
      case IRNodeType::Sub: {        0x5651f3eac6d0 = 0x5651f3eac720.as<Sub>();
        break;
      }
      case IRNodeType::Add: {        0x5651f3eac6d0 = 0x5651f3eac720.as<Add>();
        break;
      }
      default:
        break;
      }  }
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
      switch (((const Select*)r0)->false_value.node_type())
        {
        case IRNodeType::Add: {          0x5651f3eb2f80 = 0x5651f3eb2fd0.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Select*)r0)->false_value.node_type())
          {
          case IRNodeType::Add: {            0x5651f3eb4140 = 0x5651f3eb4190.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
      switch (((const Add*)r1)->a.node_type())
        {
        case IRNodeType::Select: {          0x5651f3eb4c60 = 0x5651f3eb4cb0.as<Select>();
          break;
        }
        case IRNodeType::Select: {          0x5651f3eb4c60 = 0x5651f3eb4cb0.as<Select>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Sub*)r1)->a.node_type())
        {
        case IRNodeType::Select: {          0x5651f3eb5f50 = 0x5651f3eb5fa0.as<Select>();
          break;
        }
        case IRNodeType::Select: {          0x5651f3eb5f50 = 0x5651f3eb5fa0.as<Select>();
          break;
        }
        default:
          break;
        }    }
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
    switch (b.node_type())
      {
      case IRNodeType::Select: {        0x5651f3eb21d0 = 0x5651f3e74240.as<Select>();
        break;
      }
      case IRNodeType::Add: {        0x5651f3eb21d0 = 0x5651f3e74240.as<Add>();
        break;
      }
      case IRNodeType::Add: {        0x5651f3eb21d0 = 0x5651f3e74240.as<Add>();
        break;
      }
      case IRNodeType::Sub: {        0x5651f3eb21d0 = 0x5651f3e74240.as<Sub>();
        break;
      }
      case IRNodeType::Sub: {        0x5651f3eb21d0 = 0x5651f3e74240.as<Sub>();
        break;
      }
      case IRNodeType::Add: {        0x5651f3eb21d0 = 0x5651f3e74240.as<Add>();
        break;
      }
      default:
        break;
      }  }
  if ((r0 = b.as<Mul>())) {
    if ((r1 = ((const Mul*)r0)->b.as<Sub>())) {
      if (is_const_int(((const Sub*)r1)->a, 0)) {
        if (is_const_int(((const Sub*)r1)->b, 1)) {
          return (a - ((const Mul*)r0)->a);
        }
      }
    }
    switch (((const Mul*)r0)->b.node_type())
      {
      case IRNodeType::Sub: {        0x5651f3eb8aa0 = 0x5651f3eb8af0.as<Sub>();
        break;
      }
      default:
        break;
      }  }
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
      switch (b.node_type())
        {
        case IRNodeType::Mul: {          0x5651f3eba9b0 = 0x5651f3e83970.as<Mul>();
          break;
        }
        default:
          break;
        }    }
    switch (((const Mul*)r0)->b.node_type())
      {
      case IRNodeType::Sub: {        0x5651f3eb9180 = 0x5651f3eb91d0.as<Sub>();
        break;
      }
      case IRNodeType::Mul: {        0x5651f3eb9180 = 0x5651f3eb91d0.as<Mul>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Add*)r0)->a.node_type())
      {
      case IRNodeType::Sub: {        0x5651f3ebc060 = 0x5651f3ebc0b0.as<Sub>();
        break;
      }
      case IRNodeType::Sub: {        0x5651f3ebc060 = 0x5651f3ebc0b0.as<Sub>();
        break;
      }
      default:
        break;
      }  }
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
            switch (((const Mul*)r3)->a.node_type())
              {
              case IRNodeType::Sub: {                0x5651f3ebd1e0 = 0x5651f3ebd230.as<Sub>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Mul: {              0x5651f3ebd030 = 0x5651f3e7cf20.as<Mul>();
              break;
            }
            default:
              break;
            }        }
      }
      switch (((const Add*)r1)->a.node_type())
        {
        case IRNodeType::Mul: {          0x5651f3ebcd70 = 0x5651f3ebcdc0.as<Mul>();
          break;
        }
        default:
          break;
        }    }
    switch (((const Max*)r0)->b.node_type())
      {
      case IRNodeType::Add: {        0x5651f3ebcb90 = 0x5651f3ebcbe0.as<Add>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Sub*)r0)->a.node_type())
      {
      case IRNodeType::Sub: {        0x5651f3ebe330 = 0x5651f3ebe380.as<Sub>();
        break;
      }
      case IRNodeType::Add: {        0x5651f3ebe330 = 0x5651f3ebe380.as<Add>();
        break;
      }
      default:
        break;
      }  }
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
      switch (((const Div*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x5651f3ec0640 = 0x5651f3ec0690.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5651f3ec0640 = 0x5651f3ec0690.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5651f3ec3d90 = 0x5651f3ec3de0.as<Add>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Add: {            0x5651f3ec4ad0 = 0x5651f3ec4b20.as<Add>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Add*)r0)->b.node_type())
        {
        case IRNodeType::Div: {          0x5651f3ec3ba0 = 0x5651f3ec3bf0.as<Div>();
          break;
        }
        case IRNodeType::Div: {          0x5651f3ec3ba0 = 0x5651f3ec3bf0.as<Div>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Div*)r0)->a.node_type())
        {
        case IRNodeType::Add: {          0x5651f3ec5770 = 0x5651f3ec57c0.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5651f3ec5770 = 0x5651f3ec57c0.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ec90c0 = 0x5651f3e90aa0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ec9d90 = 0x5651f3e915c0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Mul: {            0x5651f3ec8e00 = 0x5651f3ec8e50.as<Mul>();
            break;
          }
          case IRNodeType::Mul: {            0x5651f3ec8e00 = 0x5651f3ec8e50.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ecb290 = 0x5651f3e92930.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ecbf30 = 0x5651f3e93390.as<Mul>();
                break;
              }
              default:
                break;
              }          }
        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Mul: {            0x5651f3ecb000 = 0x5651f3ecb050.as<Mul>();
            break;
          }
          case IRNodeType::Mul: {            0x5651f3ecb000 = 0x5651f3ecb050.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
          switch (b.node_type())
            {
            case IRNodeType::Mul: {              0x5651f3eccc40 = 0x5651f3e91fd0.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
          switch (b.node_type())
            {
            case IRNodeType::Mul: {              0x5651f3ecd870 = 0x5651f3e93da0.as<Mul>();
              break;
            }
            default:
              break;
            }        }
      }
      switch (((const Min*)r0)->b.node_type())
        {
        case IRNodeType::Sub: {          0x5651f3ec7a70 = 0x5651f3ec7ac0.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5651f3ec7a70 = 0x5651f3ec7ac0.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x5651f3ec7a70 = 0x5651f3ec7ac0.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5651f3ec7a70 = 0x5651f3ec7ac0.as<Add>();
          break;
        }
        case IRNodeType::Mul: {          0x5651f3ec7a70 = 0x5651f3ec7ac0.as<Mul>();
          break;
        }
        case IRNodeType::Mul: {          0x5651f3ec7a70 = 0x5651f3ec7ac0.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Min*)r0)->b.node_type())
        {
        case IRNodeType::Sub: {          0x5651f3ece3b0 = 0x5651f3ece400.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5651f3ece3b0 = 0x5651f3ece400.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
      switch (((const Max*)r0)->b.node_type())
        {
        case IRNodeType::Sub: {          0x5651f3ecefd0 = 0x5651f3ecf020.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5651f3ecefd0 = 0x5651f3ecf020.as<Sub>();
          break;
        }
        default:
          break;
        }    }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ed1270 = 0x5651f3e946c0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ed1f40 = 0x5651f3e95120.as<Mul>();
                break;
              }
              default:
                break;
              }          }
        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Mul: {            0x5651f3ed0fb0 = 0x5651f3ed1000.as<Mul>();
            break;
          }
          case IRNodeType::Mul: {            0x5651f3ed0fb0 = 0x5651f3ed1000.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ed3440 = 0x5651f3e96450.as<Mul>();
                break;
              }
              default:
                break;
              }          }
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
            switch (b.node_type())
              {
              case IRNodeType::Mul: {                0x5651f3ed40e0 = 0x5651f3e96eb0.as<Mul>();
                break;
              }
              default:
                break;
              }          }
        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Mul: {            0x5651f3ed31b0 = 0x5651f3ed3200.as<Mul>();
            break;
          }
          case IRNodeType::Mul: {            0x5651f3ed31b0 = 0x5651f3ed3200.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
          switch (b.node_type())
            {
            case IRNodeType::Mul: {              0x5651f3ed5870 = 0x5651f3e95b30.as<Mul>();
              break;
            }
            default:
              break;
            }        }
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
          switch (b.node_type())
            {
            case IRNodeType::Mul: {              0x5651f3ed6490 = 0x5651f3e978c0.as<Mul>();
              break;
            }
            default:
              break;
            }        }
      }
      switch (((const Max*)r0)->b.node_type())
        {
        case IRNodeType::Sub: {          0x5651f3ecfc20 = 0x5651f3ecfc70.as<Sub>();
          break;
        }
        case IRNodeType::Sub: {          0x5651f3ecfc20 = 0x5651f3ecfc70.as<Sub>();
          break;
        }
        case IRNodeType::Add: {          0x5651f3ecfc20 = 0x5651f3ecfc70.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5651f3ecfc20 = 0x5651f3ecfc70.as<Add>();
          break;
        }
        case IRNodeType::Min: {          0x5651f3ecfc20 = 0x5651f3ecfc70.as<Min>();
          break;
        }
        case IRNodeType::Mul: {          0x5651f3ecfc20 = 0x5651f3ecfc70.as<Mul>();
          break;
        }
        case IRNodeType::Mul: {          0x5651f3ecfc20 = 0x5651f3ecfc70.as<Mul>();
          break;
        }
        default:
          break;
        }    }
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
            switch (((const Add*)r2)->a.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3ed7d00 = 0x5651f3ed7d50.as<Mod>();
                break;
              }
              case IRNodeType::Mod: {                0x5651f3ed7d00 = 0x5651f3ed7d50.as<Mod>();
                break;
              }
              default:
                break;
              }          }
          if ((r2 = b.as<Sub>())) {
            if ((r3 = ((const Sub*)r2)->a.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Mul*)r0)->a, ((const Mod*)r3)->b)) {
                  return (select((((const Mul*)r0)->a == 0), 0, ((const Div*)r1)->a) - ((const Sub*)r2)->b);
                }
              }
            }
            switch (((const Sub*)r2)->a.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3ed8ee0 = 0x5651f3ed8f30.as<Mod>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Mod: {              0x5651f3ed7470 = 0x5651f3e981e0.as<Mod>();
              break;
            }
            case IRNodeType::Add: {              0x5651f3ed7470 = 0x5651f3e981e0.as<Add>();
              break;
            }
            case IRNodeType::Sub: {              0x5651f3ed7470 = 0x5651f3e981e0.as<Sub>();
              break;
            }
            default:
              break;
            }        }
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
            switch (((const Add*)r2)->a.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3eda2d0 = 0x5651f3eda320.as<Mod>();
                break;
              }
              case IRNodeType::Mod: {                0x5651f3eda2d0 = 0x5651f3eda320.as<Mod>();
                break;
              }
              default:
                break;
              }          }
          if ((r2 = b.as<Sub>())) {
            if ((r3 = ((const Sub*)r2)->a.as<Mod>())) {
              if (equal(((const Div*)r1)->a, ((const Mod*)r3)->a)) {
                if (equal(((const Div*)r1)->b, ((const Mod*)r3)->b)) {
                  return (select((((const Div*)r1)->b == 0), 0, ((const Div*)r1)->a) - ((const Sub*)r2)->b);
                }
              }
            }
            switch (((const Sub*)r2)->a.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3edb4b0 = 0x5651f3edb500.as<Mod>();
                break;
              }
              default:
                break;
              }          }
          switch (b.node_type())
            {
            case IRNodeType::Mod: {              0x5651f3ed9aa0 = 0x5651f3e98a20.as<Mod>();
              break;
            }
            case IRNodeType::Add: {              0x5651f3ed9aa0 = 0x5651f3e98a20.as<Add>();
              break;
            }
            case IRNodeType::Sub: {              0x5651f3ed9aa0 = 0x5651f3e98a20.as<Sub>();
              break;
            }
            default:
              break;
            }        }
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
            switch (b.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3edc210 = 0x5651f3e991c0.as<Mod>();
                break;
              }
              default:
                break;
              }          }
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
            switch (b.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3edce10 = 0x5651f3e9a6c0.as<Mod>();
                break;
              }
              default:
                break;
              }          }
        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Div: {            0x5651f3edbf10 = 0x5651f3edbf60.as<Div>();
            break;
          }
          case IRNodeType::Div: {            0x5651f3edbf10 = 0x5651f3edbf60.as<Div>();
            break;
          }
          default:
            break;
          }      }
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
            switch (b.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3eddc00 = 0x5651f3e99c80.as<Mod>();
                break;
              }
              default:
                break;
              }          }
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
            switch (b.node_type())
              {
              case IRNodeType::Mod: {                0x5651f3ede800 = 0x5651f3e9afe0.as<Mod>();
                break;
              }
              default:
                break;
              }          }
        }
        switch (((const Add*)r1)->b.node_type())
          {
          case IRNodeType::Div: {            0x5651f3edd900 = 0x5651f3edd950.as<Div>();
            break;
          }
          case IRNodeType::Div: {            0x5651f3edd900 = 0x5651f3edd950.as<Div>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->b.node_type())
        {
        case IRNodeType::Div: {          0x5651f3ed7140 = 0x5651f3ed7190.as<Div>();
          break;
        }
        case IRNodeType::Div: {          0x5651f3ed7140 = 0x5651f3ed7190.as<Div>();
          break;
        }
        case IRNodeType::Add: {          0x5651f3ed7140 = 0x5651f3ed7190.as<Add>();
          break;
        }
        case IRNodeType::Add: {          0x5651f3ed7140 = 0x5651f3ed7190.as<Add>();
          break;
        }
        default:
          break;
        }    }
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
            switch (((const Mul*)r2)->b.node_type())
              {
              case IRNodeType::Div: {                0x5651f3edf710 = 0x5651f3edf760.as<Div>();
                break;
              }
              default:
                break;
              }          }
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
              if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) + ((const Add*)r1)->b);
                }
              }
            }
          }
          switch (((const Mul*)r2)->a.node_type())
            {
            case IRNodeType::Div: {              0x5651f3edff60 = 0x5651f3edffb0.as<Div>();
              break;
            }
            default:
              break;
            }        }
        if ((r2 = ((const Add*)r1)->b.as<Mul>())) {
          if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->a)) {
            if ((r3 = ((const Mul*)r2)->b.as<Div>())) {
              if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
                if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) + ((const Add*)r1)->a);
                }
              }
            }
            switch (((const Mul*)r2)->b.node_type())
              {
              case IRNodeType::Div: {                0x5651f3ee0be0 = 0x5651f3ee0c30.as<Div>();
                break;
              }
              default:
                break;
              }          }
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
              if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) + ((const Add*)r1)->a);
                }
              }
            }
          }
          switch (((const Mul*)r2)->a.node_type())
            {
            case IRNodeType::Div: {              0x5651f3ee1430 = 0x5651f3ee1480.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Mul: {            0x5651f3edf3e0 = 0x5651f3edf430.as<Mul>();
            break;
          }
          case IRNodeType::Mul: {            0x5651f3edf3e0 = 0x5651f3edf430.as<Mul>();
            break;
          }
          default:
            break;
          }      }
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
            switch (((const Mul*)r2)->b.node_type())
              {
              case IRNodeType::Div: {                0x5651f3ee2240 = 0x5651f3ee2290.as<Div>();
                break;
              }
              default:
                break;
              }          }
          if ((r3 = ((const Mul*)r2)->a.as<Div>())) {
            if (equal(((const Mod*)r0)->a, ((const Div*)r3)->a)) {
              if (equal(((const Mod*)r0)->b, ((const Div*)r3)->b)) {
                if (equal(((const Mod*)r0)->b, ((const Mul*)r2)->b)) {
                  return (select((((const Mod*)r0)->b == 0), 0, ((const Mod*)r0)->a) - ((const Sub*)r1)->b);
                }
              }
            }
          }
          switch (((const Mul*)r2)->a.node_type())
            {
            case IRNodeType::Div: {              0x5651f3ee2a90 = 0x5651f3ee2ae0.as<Div>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Sub*)r1)->a.node_type())
          {
          case IRNodeType::Mul: {            0x5651f3ee1f10 = 0x5651f3ee1f60.as<Mul>();
            break;
          }
          default:
            break;
          }      }
      switch (b.node_type())
        {
        case IRNodeType::Add: {          0x5651f3edf260 = 0x5651f3e9b900.as<Add>();
          break;
        }
        case IRNodeType::Sub: {          0x5651f3edf260 = 0x5651f3e9b900.as<Sub>();
          break;
        }
        default:
          break;
        }    }
    if ((r0 = a.as<Div>())) {
      if (is_const_int(((const Div*)r0)->b, 2)) {
        if ((r1 = b.as<Mod>())) {
          if (equal(((const Div*)r0)->a, ((const Mod*)r1)->a)) {
            if (is_const_int(((const Mod*)r1)->b, 2)) {
              return ((((const Div*)r0)->a + 1) / 2);
            }
          }
        }
        switch (b.node_type())
          {
          case IRNodeType::Mod: {            0x5651f3ee3610 = 0x5651f3ea1890.as<Mod>();
            break;
          }
          default:
            break;
          }      }
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
        switch (((const Div*)r1)->a.node_type())
          {
          case IRNodeType::Sub: {            0x5651f3ee3fb0 = 0x5651f3ee4000.as<Sub>();
            break;
          }
          default:
            break;
          }      }
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
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Sub: {              0x5651f3ee4e90 = 0x5651f3ee4ee0.as<Sub>();
              break;
            }
            default:
              break;
            }        }
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
          switch (((const Div*)r2)->a.node_type())
            {
            case IRNodeType::Sub: {              0x5651f3ee5d40 = 0x5651f3ee5d90.as<Sub>();
              break;
            }
            default:
              break;
            }        }
        switch (((const Add*)r1)->a.node_type())
          {
          case IRNodeType::Div: {            0x5651f3ee4c80 = 0x5651f3ee4cd0.as<Div>();
            break;
          }
          case IRNodeType::Div: {            0x5651f3ee4c80 = 0x5651f3ee4cd0.as<Div>();
            break;
          }
          default:
            break;
          }      }
      switch (((const Mul*)r0)->a.node_type())
        {
        case IRNodeType::Div: {          0x5651f3ee3dd0 = 0x5651f3ee3e20.as<Div>();
          break;
        }
        case IRNodeType::Add: {          0x5651f3ee3dd0 = 0x5651f3ee3e20.as<Add>();
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
