#pragma once

#include "cfir/Printer.h"
#include "cfir/Visitor.h"
#include "cfir/Mutator.h"
#include "Identifier.h"
#include <algorithm>
#include <memory>
#include <vector>
#include <string>

using std::make_shared;
using std::shared_ptr;
using std::vector;

namespace CFIR {

enum class IRType {
    // Type checks
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
    ConstantInt,
    Broadcast,
    Ramp,

    // Stmt
    Equality,
    Return,
    Condition,
    IsConstant,
    Predicate,

    Sequence,
    Declaration,
};

struct Node;

typedef std::shared_ptr<Node> NodePtr;

struct Node {
    virtual void print(std::ostream &stream, const std::string &indent) const = 0;  // This makes the struct abstract.
    virtual bool equal(const shared_ptr<Node> &other) const = 0;
    virtual void accept(Visitor *v) const = 0;
    virtual NodePtr mutate(Mutator *m) const = 0;
    virtual ~Node() = default;  // Otherwise C++ breaks for some reason.

    vector<shared_ptr<Node>> children;
    const IRType type;

    Node(IRType _type)
        : type(_type) {
    }

    template<typename T>
    const T *as(IRType _type) const {
        if (type != _type) {
            return nullptr;
        } else {
            return dynamic_cast<const T *>(this);
        }
    }

    // Might want to make this virtual so Return nodes can override it and fail early.
    template<typename T>  // T must inherit from Node.
    shared_ptr<T> get_child(shared_ptr<T> _child) {
        auto is_node = [&_child](const shared_ptr<Node> &child) { return _child->equal(child); };
        auto result = std::find_if(children.begin(), children.end(), is_node);
        if (result != children.end()) {
            // This is safe, I think?
            return std::dynamic_pointer_cast<T>(*result);
        } else {
            // Need to insert the child
            children.push_back(_child);
            return _child;
        }
    }
};

template<typename T>
struct TypeCheck : public Node {
    const IdPtr current_id;
    const IdPtr typed_id;

    bool equal(const shared_ptr<Node> &other) const override {
        if (const T *other_tc = other->as<T>(type)) {
            // We only care about the object's name (and type of course)
            return current_id->equals(other_tc->current_id);
        } else {
            return false;
        }
    }

    TypeCheck(IRType _type, const IdPtr &_curr, const IdPtr &_out)
        : Node(_type), current_id(_curr), typed_id(_out) {
    }

    TypeCheck(const T *tc)
      : Node(tc->type), current_id(tc->current_id), typed_id(tc->typed_id) {
    }

    // TODO: this could probably be manually inlined below.
    const std::string get_type_name() const {
        return T::type_name;
    }

    void print(std::ostream &stream, const std::string &indent) const override {
        const std::string type_name = get_type_name();
        stream << indent << "if (";
        print_type_checker_condition(stream, current_id, type_name, typed_id);
        stream << ") {\n";
        for (const auto &child : children) {
            child->print(stream, indent + "  ");
        }
        stream << indent << "}\n";
    }

    void accept(Visitor *v) const override {
        v->visit((T*)this);
    }

    NodePtr mutate(Mutator *m) const override {
        return m->visit((T*)this);
    }
};

struct Add final : public TypeCheck<Add> {
    Add(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Add, _curr, _out) {
    }
    Add(const Add *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Add";
};

struct Sub final : public TypeCheck<Sub> {
    Sub(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Sub, _curr, _out) {
    }
    Sub(const Sub *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Sub";
};

struct Mod final : public TypeCheck<Mod> {
    Mod(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Mod, _curr, _out) {
    }
    Mod(const Mod *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Mod";
};

struct Mul final : public TypeCheck<Mul> {
    Mul(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Mul, _curr, _out) {
    }
    Mul(const Mul*tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Mul";
};

struct Div final : public TypeCheck<Div> {
    Div(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Div, _curr, _out) {
    }
    Div(const Div *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Div";
};

struct Min final : public TypeCheck<Min> {
    Min(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Min, _curr, _out) {
    }
    Min(const Min *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Min";
};

struct Max final : public TypeCheck<Max> {
    Max(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Max, _curr, _out) {
    }
    Max(const Max *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Max";
};

struct EQ final : public TypeCheck<EQ> {
    EQ(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::EQ, _curr, _out) {
    }
    EQ(const EQ *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "EQ";
};

struct NE final : public TypeCheck<NE> {
    NE(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::NE, _curr, _out) {
    }
    NE(const NE *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "NE";
};

struct LT final : public TypeCheck<LT> {
    LT(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::LT, _curr, _out) {
    }
    LT(const LT *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "LT";
};

struct LE final : public TypeCheck<LE> {
    LE(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::LE, _curr, _out) {
    }
    LE(const LE *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "LE";
};

struct GT final : public TypeCheck<GT> {
    GT(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::GT, _curr, _out) {
    }
    GT(const GT *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "GT";
};

struct GE final : public TypeCheck<GE> {
    GE(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::GE, _curr, _out) {
    }
    GE(const GE *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "GE";
};

struct And final : public TypeCheck<And> {
    And(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::And, _curr, _out) {
    }
    And(const And *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "And";
};

struct Or final : public TypeCheck<Or> {
    Or(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Or, _curr, _out) {
    }
    Or(const Or *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Or";
};

struct Not final : public TypeCheck<Not> {
    Not(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Not, _curr, _out) {
    }
    Not(const Not *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Not";
};

struct Select final : public TypeCheck<Select> {
    Select(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Select, _curr, _out) {
    }
    Select(const Select *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Select";
};

struct Broadcast final : public TypeCheck<Broadcast> {
    Broadcast(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Broadcast, _curr, _out) {
    }
    Broadcast(const Broadcast *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Broadcast";
};

struct Ramp final : public TypeCheck<Ramp> {
    Ramp(const IdPtr &_curr, const IdPtr &_out)
        : TypeCheck(IRType::Ramp, _curr, _out) {
    }
    Ramp(const Ramp *tc) : TypeCheck(tc) {}
    inline static const std::string type_name = "Ramp";
};

struct ConstantInt final : public Node {
    const IdPtr id;
    const int64_t value;

    ConstantInt(const IdPtr &_id, int64_t _value)
        : Node(IRType::ConstantInt), id(_id), value(_value) {
    }
    ConstantInt(const ConstantInt *ci)
      : Node(IRType::ConstantInt), id(ci->id), value(ci->value) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};

struct Equality final : public Node {
    const IdPtr expr0, expr1;

    Equality(const IdPtr &e0, const IdPtr &e1)
        : Node(IRType::Equality), expr0(e0), expr1(e1) {
    }
    Equality(const Equality *eq)
      : Node(IRType::Equality), expr0(eq->expr0), expr1(eq->expr1) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};

struct Return final : public Node {
    const AST::ExprPtr ret_expr;
    Return(const AST::ExprPtr &retval)
        : Node(IRType::Return), ret_expr(retval) {
    }
    Return(const Return *r)
        : Node(IRType::Return), ret_expr(r->ret_expr) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};

// Used as a generic condition, makes a lot of stuff easier. Probably could have just inherited from this.
// TODO: NEED TO GET RID OF THIS.
struct Condition final : public Node {
    const std::string condition;
    Condition(const std::string &_condition)
        : Node(IRType::Condition), condition(_condition) {
    }
    Condition(const Condition *c)
        : Node(IRType::Condition), condition(c->condition) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};

struct IsConstant final : public Node {
    const IdPtr id;
    IsConstant(const IdPtr &_id)
        : Node(IRType::IsConstant), id(_id) {
    }
    IsConstant(const IsConstant *ic)
        : Node(IRType::IsConstant), id(ic->id) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};

struct Predicate final : public Node {
    const AST::ExprPtr pred_expr;
    Predicate(const AST::ExprPtr &pred)
        : Node(IRType::Predicate), pred_expr(pred) {
    }
    Predicate(const Predicate *p)
        : Node(IRType::Predicate), pred_expr(p->pred_expr) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};


// Used as the top level node *ONLY*
struct Sequence final : public Node {
    Sequence()
        : Node(IRType::Sequence) {
    }
    Sequence(const Sequence *s)
        : Node(IRType::Sequence) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};

// Used for reuse analysis to pre-declare a series of `const BaseExprNode *`s
struct Declaration final : public Node {
    const size_t n;
    const std::string prefix;
    Declaration(size_t _n, const std::string _prefix)
        : Node(IRType::Declaration), n(_n), prefix(_prefix) {
        assert(!_prefix.empty());
    }
    Declaration(const Declaration *d)
        : Node(IRType::Declaration), n(d->n), prefix(d->prefix) {
    }
    bool equal(const shared_ptr<Node> &other) const override;
    void print(std::ostream &stream, const std::string &indent) const override;
    void accept(Visitor *v) const override;
    NodePtr mutate(Mutator *m) const override;
};
}  // namespace CFIR

