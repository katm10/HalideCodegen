#include "SimplifyGeneratedInternal.h"
#include "IR.h"
#include "IROperator.h"
#include "Type.h"

namespace Halide {
namespace Internal {

static constexpr uint16_t signed_integer_overflow_mask = 0x8000;

Expr fold(bool value) {
    if (value) {
        return const_true();
    } else {
        return const_false();
    }
}

void recursive_fold(const Expr &expr, halide_scalar_value_t &val, halide_type_t &ty) {
    const IRNodeType node_type = expr.node_type();

    halide_scalar_value_t val_b;

    // TODO: need better overflow tracking, i.e. BinOp::make_folded_const in IRMatch.h
    switch (node_type) {
        case IRNodeType::IntImm: {
            const IntImm *imm = expr.as<IntImm>();
            internal_assert(imm) << "Bad cast to IntImm\n" << expr << "\n";
            val.u.i64 = imm->value;
            ty = expr.type();
            break;
        }
        case IRNodeType::UIntImm: {
            const UIntImm *imm = expr.as<UIntImm>();
            internal_assert(imm) << "Bad cast to UIntImm\n" << expr << "\n";
            val.u.u64 = imm->value;
            ty = expr.type();
            break;
        }
        case IRNodeType::FloatImm: {
            const FloatImm *imm = expr.as<FloatImm>();
            internal_assert(imm) << "Bad cast to FloatImm\n" << expr << "\n";
            val.u.f64 = imm->value;
            ty = expr.type();
            break;
        }
        case IRNodeType::Add: {
            const Add *add = expr.as<Add>();
            internal_assert(add) << "Bad cast to Add\n" << expr << "\n";
            recursive_fold(add->a, val, ty);
            recursive_fold(add->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    ty.lanes |= ((ty.bits >= 32) && add_would_overflow(ty.bits, val.u.i64, val_b.u.i64)) ?  signed_integer_overflow_mask : 0;
                    int dead_bits = 64 - ty.bits;
                    // Drop the high bits then sign-extend them back    
                    val.u.i64 = ((val.u.i64 + val_b.u.i64) << dead_bits) >> dead_bits;
                    break;
                }
                case halide_type_uint: {
                    uint64_t ones = (uint64_t)(-1);
                    val.u.u64 = (val.u.u64 + val_b.u.u64) & (ones >> (64 - ty.bits));
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 += val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            break;
        }
        case IRNodeType::Sub: {
            const Sub *sub = expr.as<Sub>();
            internal_assert(sub) << "Bad cast to Sub\n" << expr << "\n";
            recursive_fold(sub->a, val, ty);
            recursive_fold(sub->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    ty.lanes |= ((ty.bits >= 32) && sub_would_overflow(ty.bits, val.u.i64, val_b.u.i64)) ? signed_integer_overflow_mask : 0;
                    // Drop the high bits then sign-extend them back
                    int dead_bits = 64 - ty.bits;
                    val.u.i64 = ((val.u.i64 - val_b.u.i64) << dead_bits) >> dead_bits;
                    break;
                }
                case halide_type_uint: {
                    uint64_t ones = (uint64_t)(-1);
                    val.u.u64 = (val.u.u64 - val_b.u.u64) & (ones >> (64 - ty.bits));
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 -= val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            break;
        }
        case IRNodeType::Mod: {
            const Mod *mod = expr.as<Mod>();
            internal_assert(mod) << "Bad cast to Mod\n" << expr << "\n";
            recursive_fold(mod->a, val, ty);
            recursive_fold(mod->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = mod_imp(val.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = mod_imp(val.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = mod_imp(val.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            break;
        }
        case IRNodeType::Mul: {
            const Mul *mul = expr.as<Mul>();
            internal_assert(mul) << "Bad cast to Mul\n" << expr << "\n";
            recursive_fold(mul->a, val, ty);
            recursive_fold(mul->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    ty.lanes |= ((ty.bits >= 32) && mul_would_overflow(ty.bits, val.u.i64, val_b.u.i64)) ? signed_integer_overflow_mask : 0;
                    int dead_bits = 64 - ty.bits;
                    // Drop the high bits then sign-extend them back
                    val.u.i64 = ((val.u.i64 * val_b.u.i64) << dead_bits) >> dead_bits;
                    break;
                }
                case halide_type_uint: {
                    uint64_t ones = (uint64_t)(-1);
                    val.u.u64 = (val.u.u64 * val_b.u.u64) & (ones >> (64 - ty.bits));
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 *= val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            break;
        }
        case IRNodeType::Div: {
            const Div *div = expr.as<Div>();
            internal_assert(div) << "Bad cast to Div\n" << expr << "\n";
            recursive_fold(div->a, val, ty);
            recursive_fold(div->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = div_imp(val.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = div_imp(val.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = div_imp(val.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            break;
        }
        case IRNodeType::Min: {
            const Min *min = expr.as<Min>();
            internal_assert(min) << "Bad cast to Min\n" << expr << "\n";
            recursive_fold(min->a, val, ty);
            recursive_fold(min->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = std::min(val.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = std::min(val.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = std::min(val.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            break;
        }
        case IRNodeType::Max: {
            const Max *max = expr.as<Max>();
            internal_assert(max) << "Bad cast to Max\n" << expr << "\n";
            recursive_fold(max->a, val, ty);
            recursive_fold(max->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = std::max(val.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = std::max(val.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = std::max(val.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            break;
        }
        case IRNodeType::EQ: {
            const EQ *eq = expr.as<EQ>();
            internal_assert(eq) << "Bad cast to EQ\n" << expr << "\n";
            recursive_fold(eq->a, val, ty);
            recursive_fold(eq->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.u64 = (val.u.i64 == val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = (val.u.u64 == val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.u64 = (val.u.f64 == val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            ty.code = halide_type_uint;
            ty.bits = 1;
            break;
        }
        case IRNodeType::NE: {
            const NE *ne = expr.as<NE>();
            internal_assert(ne) << "Bad cast to NE\n" << expr << "\n";
            recursive_fold(ne->a, val, ty);
            recursive_fold(ne->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.u64 = (val.u.i64 != val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = (val.u.u64 != val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.u64 = (val.u.f64 != val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            ty.code = halide_type_uint;
            ty.bits = 1;
            break;
        }        
        case IRNodeType::LT: {
            const LT *lt = expr.as<LT>();
            internal_assert(lt) << "Bad cast to LT\n" << expr << "\n";
            recursive_fold(lt->a, val, ty);
            recursive_fold(lt->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.u64 = (val.u.i64 < val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = (val.u.u64 < val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.u64 = (val.u.f64 < val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            ty.code = halide_type_uint;
            ty.bits = 1;
            break;
        }        
        case IRNodeType::LE: {
            const LE *le = expr.as<LE>();
            internal_assert(le) << "Bad cast to LE\n" << expr << "\n";
            recursive_fold(le->a, val, ty);
            recursive_fold(le->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.u64 = (val.u.i64 <= val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = (val.u.u64 <= val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.u64 = (val.u.f64 <= val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            ty.code = halide_type_uint;
            ty.bits = 1;
            break;
        }        
        case IRNodeType::GT: {
            const GT *gt = expr.as<GT>();
            internal_assert(gt) << "Bad cast to GT\n" << expr << "\n";
            recursive_fold(gt->a, val, ty);
            recursive_fold(gt->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.u64 = (val.u.i64 > val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = (val.u.u64 > val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.u64 = (val.u.f64 > val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            ty.code = halide_type_uint;
            ty.bits = 1;
            break;
        }        
        case IRNodeType::GE: {
            const GE *ge = expr.as<GE>();
            internal_assert(ge) << "Bad cast to GE\n" << expr << "\n";
            recursive_fold(ge->a, val, ty);
            recursive_fold(ge->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.u64 = (val.u.i64 >= val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = (val.u.u64 >= val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.u64 = (val.u.f64 >= val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_error << "Should never be here\n";
                    break;
                }
            }
            ty.code = halide_type_uint;
            ty.bits = 1;
            break;
        }
        case IRNodeType::And: {
            const And *and_op = expr.as<And>();
            internal_assert(and_op) << "Bad cast to And\n" << expr << "\n";
            recursive_fold(and_op->a, val, ty);
            if (val.u.u64 == 0) {
                // Short circuit
                return;
            }
            recursive_fold(and_op->b, val_b, ty);
            internal_assert(ty.code == halide_type_uint);
            val.u.u64 = (val.u.u64 & val_b.u.u64 & 1);
            break;
        }
        case IRNodeType::Or: {
            const Or *or_op = expr.as<Or>();
            internal_assert(or_op) << "Bad cast to Or\n" << expr << "\n";
            recursive_fold(or_op->a, val, ty);
            if (val.u.u64 == 1) {
                // Short circuit
                return;
            }
            recursive_fold(or_op->b, val_b, ty);
            internal_assert(ty.code == halide_type_uint);
            val.u.u64 = (val.u.u64 | val_b.u.u64) & 1;
            break;
        }
        case IRNodeType::Not: {
            const Not *not_op = expr.as<Not>();
            internal_assert(not_op) << "Bad cast to Not\n" << expr << "\n";
            recursive_fold(not_op->a, val, ty);
            internal_assert(ty.code == halide_type_uint);
            val.u.u64 = ~val.u.u64;
            val.u.u64 &= 1;
            break;
        }
        case IRNodeType::Broadcast: {
            const Broadcast *broadcast = expr.as<Broadcast>();
            internal_assert(broadcast) << "Bad cast to Broadcast\n" << expr << "\n";
            recursive_fold(broadcast->value, val, ty);

            uint16_t l = (uint16_t)broadcast->lanes;
            ty.lanes = l | (ty.lanes & signed_integer_overflow_mask);
            break;
        }
        default: {
            // TODO select
            internal_error << "Don't know this Expr type: " << expr << "\n";
        }
    }
}

Expr make_const_special_expr(halide_type_t ty) {
    const uint16_t flags = ty.lanes & signed_integer_overflow_mask;
    ty.lanes &= ~signed_integer_overflow_mask;
    if (flags & signed_integer_overflow_mask) {
        return make_signed_integer_overflow(ty);
    }
    // unreachable
    return Expr();
}

Expr make_const_expr(halide_scalar_value_t val, halide_type_t ty) {
    halide_type_t scalar_type = ty;
    if (scalar_type.lanes & signed_integer_overflow_mask) {
        return make_const_special_expr(scalar_type);
    }

    const int lanes = scalar_type.lanes;
    scalar_type.lanes = 1;

    Expr e;
    switch (scalar_type.code) {
    case halide_type_int:
        e = IntImm::make(scalar_type, val.u.i64);
        break;
    case halide_type_uint:
        e = UIntImm::make(scalar_type, val.u.u64);
        break;
    case halide_type_float:
    case halide_type_bfloat:
        e = FloatImm::make(scalar_type, val.u.f64);
        break;
    default:
        // Unreachable
        return Expr();
    }
    if (lanes > 1) {
        e = Broadcast::make(e, lanes);
    }
    return e;
}

Expr fold(const Expr &expr) {
    halide_scalar_value_t val;
    halide_type_t ty;
    recursive_fold(expr, val, ty);
    Expr temp = make_const_expr(val, ty);
    internal_assert(temp.type() == expr.type()) << "Folding has a type failure: " << expr << " -> " << temp << "\n";
    return temp;
}

bool evaluate_predicate(const Expr &expr) {
    internal_assert(expr.type().is_bool()) << "Expected boolean predicate!\n\t" << expr << "\n";
    return is_const_one(expr);
}

bool can_prove(const Expr &expr, Simplify *simplifier) {
    Expr condition = simplifier->mutate(expr, nullptr);
    return is_const_one(condition);
}

bool is_const_v(const Expr &e) {
    if (e.as<IntImm>() ||
        e.as<UIntImm>() ||
        e.as<FloatImm>() ||
        e.as<StringImm>()) {
        return true;
    } else if (const Broadcast *b = e.as<Broadcast>()) {
        return is_const(b->value);
    } else {
        return false;
    }
}

bool overflows(const Expr &expr) {
    halide_scalar_value_t val;
    halide_type_t ty;
    recursive_fold(expr, val, ty);
    return (ty.lanes & signed_integer_overflow_mask) != 0;
}

}  // namespace Internal
}  // namespace Halide
