#include "Expr.h"
#include "IR.h"
#include "IROperator.h"
#include "Simplify_Internal.h"
#include "Type.h"

namespace Halide {
namespace Internal {

// Taken from FindIntrinsics.cpp, should be moved somewhere more useful.
inline bool no_overflow_int(Type t) {
    return t.is_int() && t.bits() >= 32;
}

inline bool no_overflow(Type t) {
    return t.is_float() || no_overflow_int(t);
}

template<typename Op>
inline bool is_uint(const Op *op) {
    return op->type->is_uint();
}

template<typename Op>
inline bool is_int(const Op *op) {
    return op->type->is_int();
}

template<typename Op>
inline bool is_float(const Op *op) {
    return op->type->is_float();
}

template<typename Op>
inline bool is_no_overflow_int(const Op *op) {
    return no_overflow_int(op->type);
}

template<typename Op>
inline bool is_no_overflow_scalar_int(const Op *op) {
    return op->type.is_scalar() && no_overflow_int(op->type);
}

template<typename Op>
inline bool is_no_overflow(const Op *op) {
    return no_overflow(op->type);
}

template<typename Op>
inline bool is_bool(const Op *op) {
    return op->type->is_bool();
}

// TODO: figure out how to enable these only for Halide binary ops
template<typename BinOp>
inline bool is_operand_uint(const BinOp *bop) {
    return bop->a.type().is_uint();
}

template<typename BinOp>
inline bool is_operand_int(const BinOp *bop) {
    return bop->a.type().is_int();
}

template<typename BinOp>
inline bool is_operand_float(const BinOp *bop) {
    return bop->a.type().is_float();
}

template<typename BinOp>
inline bool is_operand_no_overflow_scalar_int(const BinOp *bop) {
    auto t = bop->a.type();
    return t.is_scalar() && no_overflow_int(t);
}

template<typename BinOp>
inline bool is_operand_no_overflow_int(const BinOp *bop) {
    return no_overflow_int(bop->a.type());
}

template<typename BinOp>
inline bool is_operand_no_overflow(const BinOp *bop) {
    return no_overflow(bop->a.type());
}

inline bool is_const_int(const Expr &expr, int64_t value) {
    if (const UIntImm *as_uint = expr.as<UIntImm>()) {
        return as_uint->value == (uint64_t)value;
    } else if (const IntImm *as_int = expr.as<IntImm>()) {
        return as_int->value == (int64_t)value;
    } else if (const FloatImm *as_float = expr.as<FloatImm>()) {
        return as_float->value == (double)value;
    }
    return false;
}

Expr fold(bool value);
Expr fold(const Expr &expr);
bool evaluate_predicate(const Expr &expr);
bool can_prove(const Expr &expr, Simplify *simplifier);

inline Expr ramp(const Expr &base, const Expr &stride, int lanes) {
    return Ramp::make(base, stride, lanes);
}

inline Expr broadcast(const Expr &value, const Expr &lanes) {
    const int64_t *planes = as_const_int(lanes);
    internal_assert(planes) << "Expected constant lanes for forming Broadcast\n";
    const int64_t clanes = *planes;
    return Broadcast::make(value, clanes);
}

// Ramps and Casts are not constants.
// Same behavior as WildConst matching.
bool is_const_v(const Expr &expr);
constexpr bool is_const_v(int value) {
    return true;
}

bool overflows(const Expr &expr);

}  // namespace Internal
}  // namespace Halide
