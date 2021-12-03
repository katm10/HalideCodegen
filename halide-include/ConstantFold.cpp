#include "ConstantFold.h"

using namespace Halide;
using namespace Halide::Internal;

#define internal_assert _halide_user_assert

void recursive_fold(const Expr &expr, halide_scalar_value_t &val, halide_type_t &ty) {
    IRNodeType node_type = expr.node_type();

    switch (node_type) {
        case IRNodeType::Variable:{
            const Variable *var = expr.as<Variable>();
            std::cerr << "Constant folding cannot handle variables.\nFound " << var->name << std::endl;
            exit(1);
            break;
        }
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
            halide_scalar_value_t val_a, val_b;
            recursive_fold(add->a, val_a, ty);
            recursive_fold(add->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    // TODO do we plan to get rid of IRMatcher?
                    ty.lanes |= ((ty.bits >= 32) && add_would_overflow(ty.bits, val_a.u.i64, val_b.u.i64)) ?  IRMatcher::MatcherState::signed_integer_overflow : 0;
                    int dead_bits = 64 - ty.bits;
                    // Drop the high bits then sign-extend them back    
                    val.u.i64 = ((val_a.u.i64 + val_b.u.i64) << dead_bits) >> dead_bits;
                    break;
                }
                case halide_type_uint: {
                    uint64_t ones = (uint64_t)(-1);
                    val.u.u64 = (val_a.u.u64 + val_b.u.u64) & (ones >> (64 - ty.bits));
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 + val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Sub: {
            const Sub *sub = expr.as<Sub>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(sub->a, val_a, ty);
            recursive_fold(sub->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    ty.lanes |= ((ty.bits >= 32) && sub_would_overflow(ty.bits, val_a.u.i64, val_b.u.i64)) ? IRMatcher::MatcherState::signed_integer_overflow : 0;
                    // Drop the high bits then sign-extend them back
                    int dead_bits = 64 - ty.bits;
                    val.u.i64 = ((val_a.u.i64 - val_b.u.i64) << dead_bits) >> dead_bits;
                    break;
                }
                case halide_type_uint: {
                    uint64_t ones = (uint64_t)(-1);
                    val.u.u64 = (val_a.u.u64 - val_b.u.u64) & (ones >> (64 - ty.bits));
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 - val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Mod: {
            const Mod *mod = expr.as<Mod>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(mod->a, val_a, ty);
            recursive_fold(mod->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = mod_imp(val_a.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = mod_imp(val_a.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = mod_imp(val_a.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Mul: {
            const Mul *mul = expr.as<Mul>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(mul->a, val_a, ty);
            recursive_fold(mul->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    ty.lanes |= ((ty.bits >= 32) && mul_would_overflow(ty.bits, val_a.u.i64, val_b.u.i64)) ? IRMatcher::MatcherState::signed_integer_overflow : 0;
                    int dead_bits = 64 - ty.bits;
                    // Drop the high bits then sign-extend them back
                    val.u.i64 = ((val_a.u.i64 * val_b.u.i64) << dead_bits) >> dead_bits;
                    break;
                }
                case halide_type_uint: {
                    uint64_t ones = (uint64_t)(-1);
                    val.u.u64 = (val_a.u.u64 * val_b.u.u64) & (ones >> (64 - ty.bits));
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 * val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Div: {
            const Div *div = expr.as<Div>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(div->a, val_a, ty);
            recursive_fold(div->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = div_imp(val_a.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = div_imp(val_a.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = div_imp(val_a.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Min: {
            const Min *min = expr.as<Min>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(min->a, val_a, ty);
            recursive_fold(min->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = std::min(val_a.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = std::min(val_a.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = std::min(val_a.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Max: {
            const Max *max = expr.as<Max>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(max->a, val_a, ty);
            recursive_fold(max->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = std::max(val_a.u.i64, val_b.u.i64);
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = std::max(val_a.u.u64, val_b.u.u64);
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = std::max(val_a.u.f64, val_b.u.f64);
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::EQ: {
            const EQ *eq = expr.as<EQ>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(eq->a, val_a, ty);
            recursive_fold(eq->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = val_a.u.i64 == val_b.u.i64;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = val_a.u.u64 == val_b.u.u64;
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 == val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::NE: {
            const NE *ne = expr.as<NE>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(ne->a, val_a, ty);
            recursive_fold(ne->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = val_a.u.i64 != val_b.u.i64;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = val_a.u.u64 != val_b.u.u64;
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 != val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }        
        case IRNodeType::LT: {
            const LT *lt = expr.as<LT>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(lt->a, val_a, ty);
            recursive_fold(lt->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = val_a.u.i64 < val_b.u.i64;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = val_a.u.u64 < val_b.u.u64;
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 < val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }        
        case IRNodeType::LE: {
            const LE *le = expr.as<LE>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(le->a, val_a, ty);
            recursive_fold(le->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = val_a.u.i64 <= val_b.u.i64;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = val_a.u.u64 <= val_b.u.u64;
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 <= val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }        
        case IRNodeType::GT: {
            const GT *gt = expr.as<GT>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(gt->a, val_a, ty);
            recursive_fold(gt->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = val_a.u.i64 > val_b.u.i64;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = val_a.u.u64 > val_b.u.u64;
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 > val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }        
        case IRNodeType::GE: {
            const GE *ge = expr.as<GE>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(ge->a, val_a, ty);
            recursive_fold(ge->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = val_a.u.i64 >= val_b.u.i64;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = val_a.u.u64 >= val_b.u.u64;
                    break;
                }
                case halide_type_float:
                case halide_type_bfloat: {
                    val.u.f64 = val_a.u.f64 >= val_b.u.f64;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::And: {
            const And *and_op = expr.as<And>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(and_op->a, val_a, ty);
            recursive_fold(and_op->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = val_a.u.i64 & val_b.u.i64 & 1;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = val_a.u.u64 & val_b.u.u64 & 1;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Or: {
            const Or *or_op = expr.as<Or>();
            halide_scalar_value_t val_a, val_b;
            recursive_fold(or_op->a, val_a, ty);
            recursive_fold(or_op->b, val_b, ty);
            switch (ty.code) {
                case halide_type_int: {
                    val.u.i64 = (val_a.u.i64 | val_b.u.i64) & 1;
                    break;
                }
                case halide_type_uint: {
                    val.u.u64 = (val_a.u.u64 | val_b.u.u64) & 1;
                    break;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Not: {
            const Not *not_op = expr.as<Not>();
            halide_scalar_value_t val_a;
            recursive_fold(not_op->a, val_a, ty);
            switch (ty.code) {
                // TODO: does this make sense with other types?
                case halide_type_uint: 
                case halide_type_int: {
                    val.u.u64 = ~val.u.u64;
                    val.u.u64 &= 1;
                }
                default: {
                    // unreachable
                    internal_assert(false) << "Should never be here\n";
                    break;
                }
            }
        }
        case IRNodeType::Broadcast: {
            const Broadcast *broadcast = expr.as<Broadcast>();
            halide_scalar_value_t lanes_val, value;
            recursive_fold(broadcast->lanes, lanes_val, ty);
            recursive_fold(broadcast->value, value, ty);

            uint16_t l = (uint16_t)lanes_val.u.i64; 
            ty.lanes = l | (ty.lanes & IRMatcher::MatcherState::special_values_mask);
        }
        default: {
            // TODO select
            internal_assert(false) << "Don't know this Expr type: " << expr << "\n";
        }
    }
}
