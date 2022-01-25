((const And*)r0)->b((const And*)r0)->b((const And*)r0)->a((const And*)r0)->b((const And*)r0)->a((const And*)r0)->b((const And*)r0)->a((const And*)r0)->b((const And*)r0)->b((const And*)r0)->a((const Or*)r0)->ab((const Or*)r0)->abbb#include "Simplify_Internal.h"
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
      switch (b.node_type())
        {
        case IRNodeType::EQ: {          0x55bc923409f0 = 0x55bc92331190.as<EQ>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::EQ: {          0x55bc92341390 = 0x55bc92331b30.as<EQ>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::NE: {          0x55bc92341d40 = 0x55bc923323d0.as<NE>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::NE: {          0x55bc923426f0 = 0x55bc92332c70.as<NE>();
          break;
        }
        default:
          break;
        }    }
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
    switch (((const And*)r0)->a.node_type())
      {
      case IRNodeType::And: {        0x55bc9233f530 = 0x55bc9233f580.as<And>();
        break;
      }
      case IRNodeType::And: {        0x55bc9233f530 = 0x55bc9233f580.as<And>();
        break;
      }
      case IRNodeType::NE: {        0x55bc9233f530 = 0x55bc9233f580.as<NE>();
        break;
      }
      case IRNodeType::NE: {        0x55bc9233f530 = 0x55bc9233f580.as<NE>();
        break;
      }
      case IRNodeType::EQ: {        0x55bc9233f530 = 0x55bc9233f580.as<EQ>();
        break;
      }
      case IRNodeType::EQ: {        0x55bc9233f530 = 0x55bc9233f580.as<EQ>();
        break;
      }
      case IRNodeType::Or: {        0x55bc9233f530 = 0x55bc9233f580.as<Or>();
        break;
      }
      case IRNodeType::Or: {        0x55bc9233f530 = 0x55bc9233f580.as<Or>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const And*)r0)->a.node_type())
      {
      case IRNodeType::And: {        0x55bc92344590 = 0x55bc923445e0.as<And>();
        break;
      }
      case IRNodeType::And: {        0x55bc92344590 = 0x55bc923445e0.as<And>();
        break;
      }
      case IRNodeType::Or: {        0x55bc92344590 = 0x55bc923445e0.as<Or>();
        break;
      }
      case IRNodeType::Or: {        0x55bc92344590 = 0x55bc923445e0.as<Or>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Or*)r0)->b.node_type())
      {
      case IRNodeType::And: {        0x55bc92346960 = 0x55bc923469b0.as<And>();
        break;
      }
      case IRNodeType::And: {        0x55bc92346960 = 0x55bc923469b0.as<And>();
        break;
      }
      case IRNodeType::Or: {        0x55bc92346960 = 0x55bc923469b0.as<Or>();
        break;
      }
      default:
        break;
      }  }
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
    switch (((const Or*)r0)->b.node_type())
      {
      case IRNodeType::And: {        0x55bc92349300 = 0x55bc92349350.as<And>();
        break;
      }
      case IRNodeType::And: {        0x55bc92349300 = 0x55bc92349350.as<And>();
        break;
      }
      default:
        break;
      }  }
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
      switch (b.node_type())
        {
        case IRNodeType::EQ: {          0x55bc9234ae30 = 0x55bc92333f90.as<EQ>();
          break;
        }
        default:
          break;
        }    }
    switch (b.node_type())
      {
      case IRNodeType::EQ: {        0x55bc9234a5e0 = 0x55bc92330960.as<EQ>();
        break;
      }
      default:
        break;
      }  }
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
      switch (b.node_type())
        {
        case IRNodeType::LT: {          0x55bc9234c420 = 0x55bc92335df0.as<LT>();
          break;
        }
        case IRNodeType::LE: {          0x55bc9234c420 = 0x55bc92335df0.as<LE>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::LT: {          0x55bc9234d6d0 = 0x55bc923363e0.as<LT>();
          break;
        }
        case IRNodeType::LE: {          0x55bc9234d6d0 = 0x55bc923363e0.as<LE>();
          break;
        }
        default:
          break;
        }    }
    if ((r1 = b.as<LE>())) {
      if (equal(((const LE*)r0)->a, ((const LE*)r1)->a)) {
        return (((const LE*)r0)->a <= min(((const LE*)r0)->b, ((const LE*)r1)->b));
      }
      if (equal(((const LE*)r0)->b, ((const LE*)r1)->b)) {
        return (max(((const LE*)r0)->a, ((const LE*)r1)->a) <= ((const LE*)r0)->b);
      }
    }
    switch (b.node_type())
      {
      case IRNodeType::LT: {        0x55bc9234beb0 = 0x55bc923339d0.as<LT>();
        break;
      }
      case IRNodeType::LE: {        0x55bc9234beb0 = 0x55bc923339d0.as<LE>();
        break;
      }
      default:
        break;
      }  }
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
      switch (b.node_type())
        {
        case IRNodeType::EQ: {          0x55bc9234f430 = 0x55bc92334660.as<EQ>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::LT: {          0x55bc9234fc90 = 0x55bc92334d60.as<LT>();
          break;
        }
        default:
          break;
        }    }
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
      switch (b.node_type())
        {
        case IRNodeType::LT: {          0x55bc92350b10 = 0x55bc92335630.as<LT>();
          break;
        }
        default:
          break;
        }    }
    if ((r1 = b.as<LT>())) {
      if (equal(((const LT*)r0)->a, ((const LT*)r1)->a)) {
        return (((const LT*)r0)->a < min(((const LT*)r0)->b, ((const LT*)r1)->b));
      }
      if (equal(((const LT*)r0)->b, ((const LT*)r1)->b)) {
        return (max(((const LT*)r0)->a, ((const LT*)r1)->a) < ((const LT*)r0)->b);
      }
    }
    switch (b.node_type())
      {
      case IRNodeType::LT: {        0x55bc923518f0 = 0x55bc9233da70.as<LT>();
        break;
      }
      default:
        break;
      }  }
  if ((r0 = a.as<Broadcast>())) {
    if (is_const_v(((const Broadcast*)r0)->lanes)) {
      if ((r1 = b.as<Broadcast>())) {
        if (equal(((const Broadcast*)r0)->lanes, ((const Broadcast*)r1)->lanes)) {
          return broadcast((((const Broadcast*)r0)->value && ((const Broadcast*)r1)->value), ((const Broadcast*)r0)->lanes);
        }
      }
      switch (b.node_type())
        {
        case IRNodeType::Broadcast: {          0x55bc92352550 = 0x55bc923386a0.as<Broadcast>();
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
