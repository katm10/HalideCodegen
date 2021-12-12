#pragma once

#include <cassert>
#include <cstdint>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <map>

typedef std::map<std::string, std::string> VarScope;

namespace AST
{

    // subset of Halide's NodeType from Expr.h
    enum class NodeType
    {
        // TODO: do we need any other constants?
        ConstantInt,
        ConstantVar,
        Var,
        Add,
        Sub,
        Mod,
        Mul,
        Div,
        Min,
        Max,
        EQ,
        NE,
        LT,
        LE,
        GT,
        GE,
        And,
        Or,
        Not,
        Select,
        // Vector expressions.
        Ramp,
        Broadcast,

        // TODO: add these.
        // Call,
        // VectorReduce,

        // These are useful only for pattern matching
        Fold,
        CanProve,
        Call,
    };

    struct Visitor;
    struct Mutator;
    struct Expr;

    typedef std::shared_ptr<Expr> ExprPtr;

    struct Expr
    {
        Expr(NodeType nt) : node_type(nt) {}
        NodeType node_type;
        virtual void accept(Visitor *v) const = 0;
        virtual ExprPtr mutate(Mutator *m) const = 0;

        template <typename T>
        const T *as() const
        {
            if (node_type == T::_node_type)
            {
                return (const T *)this;
            }
            return nullptr;
        }
    };

    typedef std::shared_ptr<Expr> ExprPtr;

    struct ConstantInt final : public Expr
    {
        const int64_t value;
        ConstantInt(int64_t _value)
            : Expr(NodeType::ConstantInt), value(_value)
        {
        }

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::ConstantInt;
    };

    template <typename T>
    struct VariableBase : public Expr
    {
        const std::string name;
        VariableBase(const std::string &_name)
            : Expr(T::_node_type), name(_name)
        {
        }
    };

    template <typename T>
    struct BinaryOp : public Expr
    {
        const ExprPtr a, b;
        BinaryOp(ExprPtr &_a, ExprPtr &_b)
            : Expr(T::_node_type), a(std::move(_a)), b(std::move(_b))
        {
        }
    };

    template <typename T>
    struct UnaryOp : public Expr
    {
        const ExprPtr a;
        UnaryOp(ExprPtr &_a)
            : Expr(T::_node_type), a(std::move(_a))
        {
        }
    };

    /*
 * Variable types
 */
    struct ConstantVar final : public VariableBase<ConstantVar>
    {
        ConstantVar(const std::string &_name)
            : VariableBase(_name)
        {
        }

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::ConstantVar;
    };

    struct Var final : public VariableBase<Var>
    {
        Var(const std::string &_name)
            : VariableBase(_name)
        {
        }

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Var;
    };

    /*
 * Binary Operation types
 */
    struct Add final : public BinaryOp<Add>
    {
        Add(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Add;
    };

    struct Sub final : public BinaryOp<Sub>
    {
        Sub(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Sub;
    };

    struct Mul final : public BinaryOp<Mul>
    {
        Mul(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Mul;
    };

    struct Div final : public BinaryOp<Div>
    {
        Div(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Div;
    };

    struct Mod final : public BinaryOp<Mod>
    {
        Mod(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Mod;
    };

    struct Min final : public BinaryOp<Min>
    {
        Min(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Min;
    };

    struct Max final : public BinaryOp<Max>
    {
        Max(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Max;
    };

    struct EQ final : public BinaryOp<EQ>
    {
        EQ(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::EQ;
    };

    struct NE final : public BinaryOp<NE>
    {
        NE(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::NE;
    };

    struct LT final : public BinaryOp<LT>
    {
        LT(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::LT;
    };

    struct LE final : public BinaryOp<LE>
    {
        LE(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::LE;
    };

    struct GT final : public BinaryOp<GT>
    {
        GT(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::GT;
    };

    struct GE final : public BinaryOp<GE>
    {
        GE(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::GE;
    };

    struct And final : public BinaryOp<And>
    {
        And(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::And;
    };

    struct Or final : public BinaryOp<Or>
    {
        Or(ExprPtr a, ExprPtr b) : BinaryOp(a, b) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Or;
    };

    /*
 * Unary Operation types
 */
    struct Not final : public UnaryOp<Not>
    {
        Not(ExprPtr a) : UnaryOp(a) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Not;
    };

    // TODO: should we have a Negate? Halide makes Negate(op) -> 0 - op

    /*
 * Special types
 */
    struct Select final : public Expr
    {
        const ExprPtr cond; // TODO: restrict this to a boolean type.
        const ExprPtr a, b;

        Select(ExprPtr _cond, ExprPtr _a, ExprPtr _b)
            : Expr(NodeType::Select), cond(std::move(_cond)), a(std::move(_a)), b(std::move(_b))
        {
            // TODO: restrict cond to be boolean, and restrict a and b to be the same type.
        }

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Select;
    };

    struct Ramp final : public Expr
    {
        const ExprPtr base, stride;
        const ExprPtr lanes; // restrict this to ConstantInt or ConstantVar

        Ramp(ExprPtr _base, ExprPtr _stride, ExprPtr _lanes)
            : Expr(NodeType::Ramp), base(std::move(_base)), stride(std::move(_stride)), lanes(std::move(_lanes)) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Ramp;
    };

    struct Broadcast final : public Expr
    {
        const ExprPtr value;
        const ExprPtr lanes; // restrict this to ConstantInt or ConstantVar

        Broadcast(ExprPtr _value, ExprPtr _lanes)
            : Expr(NodeType::Broadcast), value(std::move(_value)), lanes(std::move(_lanes)) {}

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Broadcast;
    };

    struct Fold final : public Expr
    {
        const ExprPtr value;

        Fold(ExprPtr _value)
            : Expr(NodeType::Fold), value(std::move(_value))
        {
        }

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Fold;
    };

    struct CanProve final : public Expr
    {
        const ExprPtr value;

        CanProve(ExprPtr _value)
            : Expr(NodeType::CanProve), value(std::move(_value))
        {
        }

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::CanProve;
    };

    struct Call final : public Expr
    {
        const std::vector<ExprPtr> args;
        const std::string name;

        Call(const std::vector<ExprPtr> &_args, const std::string &_name)
            : Expr(NodeType::Call), args(_args), name(_name)
        {
        }

        void accept(Visitor *v) const override;
        ExprPtr mutate(Mutator *m) const override;
        static const NodeType _node_type = NodeType::Call;
    };

} // namespace AST
