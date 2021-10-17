#include "Halide.h"
#include "Language.h"
#include "Printer.h"
#include <iostream>
#include <sstream>

using namespace Halide;

#include <map>
#include <memory>
#include <string>
#include <vector>

using std::make_shared;
using std::shared_ptr;
using std::vector;

struct RewriteRule {
    const Expr before;
    const Expr after;
    const Expr pred;
};

// Too many conflicts with Halide IR for other names
using Language::Node;

shared_ptr<Node> tree_constructor(shared_ptr<Node> root, const Expr &expr, const std::string &name, VarScope &scope);

template<typename BinOp>
inline shared_ptr<Node> handle_bin_op_helper(shared_ptr<Node> &typed_root, const BinOp *expr, const std::string &typed_name, VarScope &scope) {
    const std::string a_name = typed_name + "->a";
    const std::string b_name = typed_name + "->b";

    shared_ptr<Node> a_node = tree_constructor(typed_root, expr->a, a_name, scope);
    return tree_constructor(a_node, expr->b, b_name, scope);
}

// BinOp is the Halide type, LBinOp is the IR type
template<typename BinOp, typename LBinOp>
inline shared_ptr<Node> handle_bin_op(shared_ptr<Node> &root, const Expr &expr, const std::string &name, VarScope &scope) {
    const BinOp *op = expr.as<BinOp>();
    assert(op != nullptr);

    std::string typed_name = Printer::make_new_unique_name();
    // Make type check node in tree.
    shared_ptr<LBinOp> node = make_shared<LBinOp>(name, typed_name);
    node = root->get_child(node);    // Possible replace if it already exists.
    assert(node);                    // get_child returned the wrong type...?
    typed_name = node->output_name;  // This might have changed the name.

    shared_ptr<Node> typed_root = std::move(node);

    return handle_bin_op_helper<BinOp>(typed_root, op, typed_name, scope);
}

shared_ptr<Node> handle_variable(shared_ptr<Node> root, const Variable *var, const std::string &name, VarScope &scope) {
    // TODO: handle constants
    auto iter = scope.find(var->name);
    bool is_const_var = var->name.at(0) == 'c';
    if (iter == scope.end()) {
        scope.insert(std::make_pair(var->name, VarInfo(var->type, name)));
        if (!is_const_var) {
            // Insert into scope and don't worry about it.
            return root;
        } else {
            // TODO: change this to is_const, I am using is_const_v for testing purposes
            const std::string condition = "is_const_v(" + name + ")";
            shared_ptr<Language::Condition> cond_node = make_shared<Language::Condition>(condition);
            return root->get_child(cond_node);
        }
    } else {
        std::string existing_name = iter->second.name;
        shared_ptr<Language::Equality> equal = make_shared<Language::Equality>(existing_name, name);
        shared_ptr<Language::Equality> pequal = root->get_child(equal);  // Don't duplicate if possible.
        return pequal;
    }
}

inline shared_ptr<Node> handle_select_helper(shared_ptr<Node> &typed_root, const Select *expr, const std::string &typed_name, VarScope &scope) {
    const std::string cond_name = typed_name + "->condition";
    const std::string true_name = typed_name + "->true_value";
    const std::string false_name = typed_name + "->false_value";

    shared_ptr<Node> cond_node = tree_constructor(typed_root, expr->condition, cond_name, scope);
    shared_ptr<Node> true_node = tree_constructor(cond_node, expr->true_value, true_name, scope);
    return tree_constructor(true_node, expr->false_value, false_name, scope);
}

inline shared_ptr<Node> handle_select(shared_ptr<Node> &root, const Expr &expr, const std::string &name, VarScope &scope) {
    const Select *op = expr.as<Select>();
    assert(op != nullptr);  // We failed to identify the Expr properly.

    std::string typed_name = Printer::make_new_unique_name();

    shared_ptr<Language::Select> node = make_shared<Language::Select>(name, typed_name);
    node = root->get_child(node);    // Possible replace if it already exists.
    assert(node);                    // get_child returned the wrong type...?
    typed_name = node->output_name;  // This might have changed the name...?
    shared_ptr<Node> typed_root = std::move(node);

    return handle_select_helper(typed_root, op, typed_name, scope);
}

inline shared_ptr<Node> handle_broadcast_helper(shared_ptr<Node> &typed_root, const Call *expr, const std::string &typed_name, VarScope &scope) {

    const std::string value_name = typed_name + "->value";
    const std::string lanes_name = typed_name + "->lanes";
    const Expr value = expr->args[0];
    const Expr lanes = expr->args[1];

    shared_ptr<Node> value_node = tree_constructor(typed_root, value, value_name, scope);
    return tree_constructor(value_node, lanes, lanes_name, scope);
}

inline shared_ptr<Node> handle_broadcast(shared_ptr<Node> &root, const Expr &expr, const std::string &name, VarScope &scope) {
    const Call *op = expr.as<Call>();
    assert(op && op->name == "broadcast");
    std::string typed_name = Printer::make_new_unique_name();

    shared_ptr<Language::Broadcast> node = make_shared<Language::Broadcast>(name, typed_name);
    node = root->get_child(node);
    assert(node);
    typed_name = node->output_name;
    shared_ptr<Node> typed_root = std::move(node);
    return handle_broadcast_helper(typed_root, op, typed_name, scope);
}

inline shared_ptr<Node> handle_ramp_helper(shared_ptr<Node> &typed_root, const Call *expr, const std::string &typed_name, VarScope &scope) {
    const std::string base_name = typed_name + "->base";
    const std::string stride_name = typed_name + "->stride";
    const std::string lanes_name = typed_name + "->lanes";
    const Expr base = expr->args[0];
    const Expr stride = expr->args[1];
    const Expr lanes = expr->args[2];
    shared_ptr<Node> base_node = tree_constructor(typed_root, base, base_name, scope);
    shared_ptr<Node> stride_node = tree_constructor(base_node, stride, stride_name, scope);
    return tree_constructor(stride_node, lanes, lanes_name, scope);
}

inline shared_ptr<Node> handle_ramp(shared_ptr<Node> &root, const Expr &expr, const std::string &name, VarScope &scope) {
    const Call *op = expr.as<Call>();
    assert(op && op->name == "ramp");
    std::string typed_name = Printer::make_new_unique_name();

    shared_ptr<Language::Ramp> node = make_shared<Language::Ramp>(name, typed_name);
    node = root->get_child(node);
    assert(node);
    typed_name = node->output_name;
    shared_ptr<Node> typed_root = std::move(node);
    return handle_ramp_helper(typed_root, op, typed_name, scope);
}

inline shared_ptr<Node> handle_not_helper(shared_ptr<Node> &typed_root, const Not *expr, const std::string &typed_name, const std::string &name, VarScope &scope) {
    const std::string a_name = typed_name + "->a";
    return tree_constructor(typed_root, expr->a, name, scope);
}

inline shared_ptr<Node> handle_not(shared_ptr<Node> &root, const Expr &expr, const std::string &name, VarScope &scope) {
    const Not *op = expr.as<Not>();
    assert(op);
    std::string typed_name = Printer::make_new_unique_name();
    shared_ptr<Language::Not> node = make_shared<Language::Not>(name, typed_name);
    node = root->get_child(node);
    assert(node);
    typed_name = node->output_name;
    shared_ptr<Node> typed_root = std::move(node);
    return handle_not_helper(typed_root, op, typed_name, name, scope);
}

inline shared_ptr<Node> handle_int_imm(shared_ptr<Node> &root, const IntImm *imm, const std::string &name, VarScope &scope) {
    std::string typed_name = Printer::make_new_unique_name();

    // Inserts the typecheck and fixes name if necessary
    shared_ptr<Language::IntImm> imm_node = make_shared<Language::IntImm>(name, typed_name);
    imm_node = root->get_child(imm_node);
    assert(imm_node);
    typed_name = imm_node->output_name;

    const std::string condition = typed_name + "->value == " + std::to_string(imm->value);
    shared_ptr<Language::Condition> cond_node = make_shared<Language::Condition>(condition);
    // Inserts the condition after the typecheck
    // It seems unlikely that this condition will already exist, but who knows? *shrug*
    return imm_node->get_child(cond_node);
}

/*
TODOs:
    // IntImm,
    UIntImm, // I don't think we will need this, but it's possible
    FloatImm, // or this
    StringImm, // or this
    Broadcast,
    Cast, // not sure about this one, it might make types and stuff difficult. lmk if you see one of these in a rule.
    // Variable,
    // Add,
    // Sub,
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
    // Select,
    Load, // do we actually need this? check simplifier
    Ramp,
    Call, // this will be tricky
    Let, // Don't need this.
    Shuffle, // I don't think we need this right now.
    VectorReduce, // Need this as well
*/
shared_ptr<Node> tree_constructor(shared_ptr<Node> root, const Expr &expr, const std::string &name, VarScope &scope) {
    switch (expr->node_type) {
    case IRNodeType::Sub:
        return handle_bin_op<Halide::Internal::Sub, Language::Sub>(root, expr, name, scope);
    case IRNodeType::Add:
        return handle_bin_op<Halide::Internal::Add, Language::Add>(root, expr, name, scope);
    case IRNodeType::Mod:
        return handle_bin_op<Halide::Internal::Mod, Language::Mod>(root, expr, name, scope);
    case IRNodeType::Mul:
        return handle_bin_op<Halide::Internal::Mul, Language::Mul>(root, expr, name, scope);
    case IRNodeType::Div:
        return handle_bin_op<Halide::Internal::Div, Language::Div>(root, expr, name, scope);
    case IRNodeType::Min:
        return handle_bin_op<Halide::Internal::Min, Language::Min>(root, expr, name, scope);
    case IRNodeType::Max:
        return handle_bin_op<Halide::Internal::Max, Language::Max>(root, expr, name, scope);
    case IRNodeType::EQ:
        return handle_bin_op<Halide::Internal::EQ, Language::EQ>(root, expr, name, scope);
    case IRNodeType::NE:
        return handle_bin_op<Halide::Internal::NE, Language::NE>(root, expr, name, scope);
    case IRNodeType::LT:
        return handle_bin_op<Halide::Internal::LT, Language::LT>(root, expr, name, scope);
    case IRNodeType::LE:
        return handle_bin_op<Halide::Internal::LE, Language::LE>(root, expr, name, scope);
    case IRNodeType::GT:
        return handle_bin_op<Halide::Internal::GT, Language::GT>(root, expr, name, scope);
    case IRNodeType::GE:
        return handle_bin_op<Halide::Internal::GE, Language::GE>(root, expr, name, scope);
    case IRNodeType::And:
        return handle_bin_op<Halide::Internal::And, Language::And>(root, expr, name, scope);
    case IRNodeType::Or:
        return handle_bin_op<Halide::Internal::Or, Language::Or>(root, expr, name, scope);
    case IRNodeType::Not:
        return handle_not(root, expr, name, scope);
    case IRNodeType::Select:
        return handle_select(root, expr, name, scope);
    case IRNodeType::Variable: {
        const Variable *var = expr.as<Variable>();
        return handle_variable(root, var, name, scope);
    }
    case IRNodeType::IntImm: {
        const IntImm *imm = expr.as<IntImm>();
        return handle_int_imm(root, imm, name, scope);
    }
    case IRNodeType::Call: {
        const Call *call = expr.as<Call>();
        if (call->name == "ramp") {
            return handle_ramp(root, expr, name, scope);
        } else if (call->name == "broadcast") {
            return handle_broadcast(root, expr, name, scope);
        } else {
            assert(false);
        }
    }
    default:
        assert(false);
    }
    return nullptr;
}

template<typename T>
shared_ptr<Node> start_tree_constructor(shared_ptr<Node> root, const T *expr, const std::string &name, VarScope &scope) {
    if constexpr (std::is_same_v<T, Sub>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Add>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Mod>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Mul>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Div>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Min>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Max>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Mod>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, EQ>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, NE>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, LT>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, LE>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, GT>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, GE>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, And>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Or>) {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Not>) {
        return handle_not_helper(root, expr, name, scope);  // todo** check that this works
    } else if constexpr (std::is_same_v<T, Select>) {
        return handle_select_helper(root, expr, name, scope);
    } else if constexpr (std::is_same_v<T, Call>) {
        if (expr->name == "ramp") {
            return handle_ramp_helper(root, expr, name, scope);
        } else if (expr->name == "broadcast") {
            return handle_broadcast_helper(root, expr, name, scope);
        } else {
            assert(false);
        }
    } else {
        assert(false);
    }
    assert(false);
    return nullptr;
}

template<typename T>
void add_rule_typed(shared_ptr<Node> root, const RewriteRule &rule, const std::string &name) {
    VarScope scope;
    const T *expr = rule.before.as<T>();
    assert(expr);
    shared_ptr<Node> deepest = start_tree_constructor(root, expr, name, scope);
    if (rule.pred.defined()) {
        // TODO: probably want to assert that child node doesn't exist...?
        const std::string condition = "evaluate_predicate(fold(" + Printer::build_expr(rule.pred, scope) + ", simplifier))";
        shared_ptr<Language::Condition> cond_node = make_shared<Language::Condition>(condition);
        deepest = deepest->get_child(cond_node);
    }

    const std::string retval = Printer::build_expr(rule.after, scope);
    shared_ptr<Language::Return> ret_node = make_shared<Language::Return>(retval);
    deepest = deepest->get_child(ret_node);
}

template<typename T>
shared_ptr<Node> create_graph_typed(const vector<RewriteRule> &rules, const std::string &expr_name) {
    assert(rules.size() > 0);

    shared_ptr<Node> root = make_shared<Language::Sequence>();

    // have nothing

    for (const auto &rule : rules) {
        add_rule_typed<T>(root, rule, expr_name);
    }
    return root;
}

template<typename T>
void print_function_typed(const vector<RewriteRule> &rules, const std::string &func_name, const std::string &type_name) {
    shared_ptr<Node> root = create_graph_typed<T>(rules, "expr");

    std::cout << "Expr " << func_name << "(const " << type_name << " *expr, Simplify *simplifier) {\n";
    root->print(std::cout, "");
    std::cout << "  return expr;\n}\n";
}

// TODO: handle fold somehow...
Expr fold(const Expr &expr) {
    static Expr var = Variable::make(Int(32), "simplifier");
    return Call::make(expr.type(), "fold", {expr, var}, Call::PureIntrinsic);
}

// This is for generated code
bool is_const_v(const Expr &expr) {
    if (const Variable *var = expr.as<Variable>()) {
        return var->name.at(0) == 'c';
    } else {
        return is_const(expr);
    }
}

Expr ramp(Expr base, Expr stride, Expr lanes) {
    return Call::make(base.type(), "ramp", {base, stride, lanes}, Call::PureIntrinsic);
}

Expr broadcast(Expr a, Expr lanes) {
    return Call::make(a.type(), "broadcast", {a, lanes}, Call::PureIntrinsic);
}

Expr ramp(Expr base, Expr stride, int lanes) {
    return Ramp::make(base, stride, lanes);
}

Expr broadcast(Expr base, int lanes) {
    return Broadcast::make(base, lanes);
}

Expr _can_prove(const Expr &simplifier, const Expr &expr) {
    return Call::make(UInt(1), "_can_prove", {simplifier, expr}, Call::PureIntrinsic);
}

Expr _is_const(const Expr &expr) {
    return Call::make(UInt(1), "is_const", {expr}, Call::PureIntrinsic);
}

int main(void) {
    Var x("x"), y("y"), z("z"), w("w"), u("u"), v("v");
    Var c0("c0"), c1("c1"), c2("c2"), c3("c3"), c4("c4");

    // had to change select(x, stuff) to select(b0, stuff) for type reasons.
    Expr b0 = Variable::make(UInt(1), "b0");

    Var simplifier("simplifier");

    // TODO: these should be sorted probably.
    // TODO: add some with conditions to check that (probably need more than just Add/Sub/Select)
    vector<RewriteRule> rules = {
        {c0 - c1, fold(c0 - c1)},
        {x - x, 0},  // We want to remutate this just to get better bounds
        {ramp(x, y, c0) - ramp(z, w, c0), ramp(x - z, y - w, c0)},
        {ramp(x, y, c0) - broadcast(z, c0), ramp(x - z, y, c0)},
        {broadcast(x, c0) - ramp(z, w, c0), ramp(x - z, -w, c0)},
        {broadcast(x, c0) - broadcast(y, c0), broadcast(x - y, c0)},
        {broadcast(x, c0) - broadcast(y, c1), broadcast(x - broadcast(y, fold(c1 / c0)), c0), c1 % c0 == 0},
        {broadcast(y, c1) - broadcast(x, c0), broadcast(broadcast(y, fold(c1 / c0)) - x, c0), c1 % c0 == 0},
        {(x - broadcast(y, c0)) - broadcast(z, c0), x - broadcast(y + z, c0)},
        {(x + broadcast(y, c0)) - broadcast(z, c0), x + broadcast(y - z, c0)},

        {ramp(broadcast(x, c0), y, c1) - broadcast(z, c2), ramp(broadcast(x - z, c0), y, c1), c2 == c0 * c1},
        {ramp(ramp(x, y, c0), z, c1) - broadcast(w, c2), ramp(ramp(x - w, y, c0), z, c1), c2 == c0 * c1},
        {select(b0, y, z) - select(b0, w, u), select(b0, y - w, z - u)},
        {select(b0, y, z) - y, select(b0, 0, z - y)},
        {select(b0, y, z) - z, select(b0, y - z, 0)},
        {y - select(b0, y, z), select(b0, 0, y - z)},
        {z - select(b0, y, z), select(b0, z - y, 0)},

        {select(b0, y + w, z) - y, select(b0, w, z - y)},
        {select(b0, w + y, z) - y, select(b0, w, z - y)},
        {select(b0, y, z + w) - z, select(b0, y - z, w)},
        {select(b0, y, w + z) - z, select(b0, y - z, w)},
        {y - select(b0, y + w, z), 0 - select(b0, w, z - y)},
        {y - select(b0, w + y, z), 0 - select(b0, w, z - y)},
        {z - select(b0, y, z + w), 0 - select(b0, y - z, w)},
        {z - select(b0, y, w + z), 0 - select(b0, y - z, w)},

        {(x + y) - x, y},
        {(x + y) - y, x},
        {x - (x + y), -y},
        {y - (x + y), -x},
        {(x - y) - x, -y},
        {(select(b0, y, z) + w) - select(b0, u, v), select(b0, y - u, z - v) + w},
        {(w + select(b0, y, z)) - select(b0, u, v), select(b0, y - u, z - v) + w},
        {select(b0, y, z) - (select(b0, u, v) + w), select(b0, y - u, z - v) - w},
        {select(b0, y, z) - (w + select(b0, u, v)), select(b0, y - u, z - v) - w},
        {(select(b0, y, z) - w) - select(b0, u, v), select(b0, y - u, z - v) - w},
        {c0 - select(b0, c1, c2), select(b0, fold(c0 - c1), fold(c0 - c2))},
        {(x + c0) - c1, x + fold(c0 - c1)},
        {(x + c0) - (c1 - y), (x + y) + fold(c0 - c1)},
        {(x + c0) - (y + c1), (x - y) + fold(c0 - c1)},
        {(x + c0) - y, (x - y) + c0},
        {(c0 - x) - (c1 - y), (y - x) + fold(c0 - c1)},
        {(c0 - x) - (y + c1), fold(c0 - c1) - (x + y)},
        {x - (y - z), x + (z - y)},
        {x - y * c0, x + y * fold(-c0), c0 < 0 && -c0 > 0},
        {x - (y + c0), (x - y) - c0},
        {(c0 - x) - c1, fold(c0 - c1) - x},
        {x * y - z * y, (x - z) * y},
        {x * y - y * z, (x - z) * y},
        {y * x - z * y, y * (x - z)},
        {y * x - y * z, y * (x - z)},
        {(u + x * y) - z * y, u + (x - z) * y},
        {(u + x * y) - y * z, u + (x - z) * y},
        {(u + y * x) - z * y, u + y * (x - z)},
        {(u + y * x) - y * z, u + y * (x - z)},
        {(u - x * y) - z * y, u - (x + z) * y},
        {(u - x * y) - y * z, u - (x + z) * y},
        {(u - y * x) - z * y, u - y * (x + z)},
        {(u - y * x) - y * z, u - y * (x + z)},
        {(x * y + u) - z * y, u + (x - z) * y},
        {(x * y + u) - y * z, u + (x - z) * y},
        {(y * x + u) - z * y, u + y * (x - z)},
        {(y * x + u) - y * z, u + y * (x - z)},
        {(x * y - u) - z * y, (x - z) * y - u},
        {(x * y - u) - y * z, (x - z) * y - u},
        {(y * x - u) - z * y, y * (x - z) - u},
        {(y * x - u) - y * z, y * (x - z) - u},
        {x * y - (u + z * y), (x - z) * y - u},
        {x * y - (u + y * z), (x - z) * y - u},
        {y * x - (u + z * y), y * (x - z) - u},
        {y * x - (u + y * z), y * (x - z) - u},
        {x * y - (u - z * y), (x + z) * y - u},
        {x * y - (u - y * z), (x + z) * y - u},
        {y * x - (u - z * y), y * (x + z) - u},
        {y * x - (u - y * z), y * (x + z) - u},
        {x * y - (z * y + u), (x - z) * y - u},
        {x * y - (y * z + u), (x - z) * y - u},
        {y * x - (z * y + u), y * (x - z) - u},
        {y * x - (y * z + u), y * (x - z) - u},
        {x * y - (z * y - u), (x - z) * y + u},
        {x * y - (y * z - u), (x - z) * y + u},
        {y * x - (z * y - u), y * (x - z) + u},
        {y * x - (y * z - u), y * (x - z) + u},
        {(x + y) - (x + z), y - z},
        {(x + y) - (z + x), y - z},
        {(y + x) - (x + z), y - z},
        {(y + x) - (z + x), y - z},
        {((x + y) + z) - x, y + z},
        {((y + x) + z) - x, y + z},
        {(z + (x + y)) - x, z + y},
        {(z + (y + x)) - x, z + y},

        {x - (y + (x - z)), z - y},
        {x - ((x - y) + z), y - z},
        {(x + (y - z)) - y, x - z},
        {((x - y) + z) - x, z - y},

        {x - (y + (x + z)), 0 - (y + z)},
        {x - (y + (z + x)), 0 - (y + z)},
        {x - ((x + y) + z), 0 - (y + z)},
        {x - ((y + x) + z), 0 - (y + z)},
        {(x + y) - (z + (w + x)), y - (z + w)},
        {(x + y) - (z + (w + y)), x - (z + w)},
        {(x + y) - (z + (x + w)), y - (z + w)},
        {(x + y) - (z + (y + w)), x - (z + w)},
        {(x + y) - ((x + z) + w), y - (z + w)},
        {(x + y) - ((y + z) + w), x - (z + w)},
        {(x + y) - ((z + x) + w), y - (z + w)},
        {(x + y) - ((z + y) + w), x - (z + w)},

        {(x - y) - (x + z), 0 - y - z},
        {(x - y) - (z + x), 0 - y - z},

        {((x + y) - z) - x, y - z},
        {((x + y) - z) - y, x - z},

        {x - min(x - y, 0), max(x, y)},
        {x - max(x - y, 0), min(x, y)},
        {(x + y) - min(x, y), max(y, x)},
        {(x + y) - min(y, x), max(y, x)},
        {(x + y) - max(x, y), min(y, x)},
        {(x + y) - max(y, x), min(x, y)},

        {0 - (x + (y - z)), z - (x + y)},
        {0 - ((x - y) + z), y - (x + z)},
        {((x - y) - z) - x, 0 - (y + z)},

        {x - x % c0, (x / c0) * c0},
        {x - ((x + c0) / c1) * c1, (x + c0) % c1 - c0, c1 > 0},

        {max(x, y) - x, max(y - x, 0)},
        {min(x, y) - x, min(y - x, 0)},
        {max(x, y) - y, max(x - y, 0)},
        {min(x, y) - y, min(x - y, 0)},

        {x - max(x, y), min(x - y, 0), !_is_const(x)},
        {x - min(x, y), max(x - y, 0), !_is_const(x)},
        {y - max(x, y), min(y - x, 0), !_is_const(y)},
        {y - min(x, y), max(y - x, 0), !_is_const(y)},

        {x - min(y, x - z), max(x - y, z)},
        {x - min(x - y, z), max(y, x - z)},
        {x - max(y, x - z), min(x - y, z)},
        {x - max(x - y, z), min(y, x - z)},

        {min(x - y, 0) - x, 0 - max(x, y)},
        {max(x - y, 0) - x, 0 - min(x, y)},
        {min(x, y) - (x + y), 0 - max(y, x)},
        {min(x, y) - (y + x), 0 - max(x, y)},
        {max(x, y) - (x + y), 0 - min(x, y)},
        {max(x, y) - (y + x), 0 - min(y, x)},

        // Negate a clamped subtract
        {z - max(x - y, c0), z + min(y - x, fold(-c0))},
        {z - min(x - y, c0), z + max(y - x, fold(-c0))},
        {z - max(min(x - y, c0), c1), z + min(max(y - x, fold(-c0)), fold(-c1))},
        {z - min(max(x - y, c0), c1), z + max(min(y - x, fold(-c0)), fold(-c1))},

        {x * y - x, x * (y - 1)},
        {x * y - y, (x - 1) * y},
        {x - x * y, x * (1 - y)},
        {x - y * x, (1 - y) * x},

        // Cancel a term from one side of a min or max. Some of
        // these rules introduce a new constant zero, so we require
        // that the cancelled term is not a constant. This way
        // there can't be a cycle. For some rules we know by
        // context that the cancelled term is not a constant
        // (e.g. it appears on the LHS of an addition).
        {(x - min(z, (x + y))), (0 - min(z - x, y)), !_is_const(x)},
        {(x - min(z, (y + x))), (0 - min(z - x, y)), !_is_const(x)},
        {(x - min((x + y), z)), (0 - min(z - x, y)), !_is_const(x)},
        {(x - min((y + x), z)), (0 - min(z - x, y)), !_is_const(x)},
        {(x - min(y, (w + (x + z)))), (0 - min(y - x, w + z)), !_is_const(x)},
        {(x - min(y, (w + (z + x)))), (0 - min(y - x, z + w)), !_is_const(x)},
        {(x - min(y, ((x + z) + w))), (0 - min(y - x, z + w)), !_is_const(x)},
        {(x - min(y, ((z + x) + w))), (0 - min(y - x, z + w)), !_is_const(x)},
        {(x - min((w + (x + z)), y)), (0 - min(y - x, w + z)), !_is_const(x)},
        {(x - min((w + (z + x)), y)), (0 - min(y - x, z + w)), !_is_const(x)},
        {(x - min(((x + z) + w), y)), (0 - min(y - x, w + z)), !_is_const(x)},
        {(x - min(((z + x) + w), y)), (0 - min(y - x, w + z)), !_is_const(x)},

        {min(x + y, z) - x, min(z - x, y)},
        {min(y + x, z) - x, min(z - x, y)},
        {min(z, x + y) - x, min(z - x, y)},
        {min(z, y + x) - x, min(z - x, y)},
        {(min(x, (w + (y + z))) - z), min(x - z, w + y)},
        {(min(x, (w + (z + y))) - z), min(x - z, w + y)},
        {(min(x, ((y + z) + w)) - z), min(x - z, y + w)},
        {(min(x, ((z + y) + w)) - z), min(x - z, y + w)},
        {(min((w + (y + z)), x) - z), min(x - z, w + y)},
        {(min((w + (z + y)), x) - z), min(x - z, w + y)},
        {(min(((y + z) + w), x) - z), min(x - z, y + w)},
        {(min(((z + y) + w), x) - z), min(x - z, y + w)},

        {min(x, y) - min(y, x), 0},
        {min(x, y) - min(z, w), y - w, _can_prove(simplifier, x - y == z - w)},
        {min(x, y) - min(w, z), y - w, _can_prove(simplifier, x - y == z - w)},
        {min(x * c0, c1) - min(x, c2) * c0, min(c1 - min(x, c2) * c0, 0), c0 > 0 && c1 <= c2 * c0},

        {(x - max(z, (x + y))), (0 - max(z - x, y)), !_is_const(x)},
        {(x - max(z, (y + x))), (0 - max(z - x, y)), !_is_const(x)},
        {(x - max((x + y), z)), (0 - max(z - x, y)), !_is_const(x)},
        {(x - max((y + x), z)), (0 - max(z - x, y)), !_is_const(x)},
        {(x - max(y, (w + (x + z)))), (0 - max(y - x, w + z)), !_is_const(x)},
        {(x - max(y, (w + (z + x)))), (0 - max(y - x, z + w)), !_is_const(x)},
        {(x - max(y, ((x + z) + w))), (0 - max(y - x, z + w)), !_is_const(x)},
        {(x - max(y, ((z + x) + w))), (0 - max(y - x, z + w)), !_is_const(x)},
        {(x - max((w + (x + z)), y)), (0 - max(y - x, w + z)), !_is_const(x)},
        {(x - max((w + (z + x)), y)), (0 - max(y - x, z + w)), !_is_const(x)},
        {(x - max(((x + z) + w), y)), (0 - max(y - x, w + z)), !_is_const(x)},
        {(x - max(((z + x) + w), y)), (0 - max(y - x, w + z)), !_is_const(x)},

        {max(x + y, z) - x, max(z - x, y)},
        {max(y + x, z) - x, max(z - x, y)},
        {max(z, x + y) - x, max(z - x, y)},
        {max(z, y + x) - x, max(z - x, y)},
        {(max(x, (w + (y + z))) - z), max(x - z, w + y)},
        {(max(x, (w + (z + y))) - z), max(x - z, w + y)},
        {(max(x, ((y + z) + w)) - z), max(x - z, y + w)},
        {(max(x, ((z + y) + w)) - z), max(x - z, y + w)},
        {(max((w + (y + z)), x) - z), max(x - z, w + y)},
        {(max((w + (z + y)), x) - z), max(x - z, w + y)},
        {(max(((y + z) + w), x) - z), max(x - z, y + w)},
        {(max(((z + y) + w), x) - z), max(x - z, y + w)},

        {max(x, y) - max(y, x), 0},
        {max(x, y) - max(z, w), y - w, _can_prove(simplifier, x - y == z - w)},
        {max(x, y) - max(w, z), y - w, _can_prove(simplifier, x - y == z - w)},
        {min(x, y) - min(x, w), min(y - min(x, w), 0), _can_prove(simplifier, y <= w)},
        {min(x, y) - min(x, w), max(min(x, y) - w, 0), _can_prove(simplifier, y >= w)},
        {min(x + c0, y) - min(x, w), min(y - min(x, w), c0), _can_prove(simplifier, y <= w + c0)},
        {min(x + c0, y) - min(x, w), max(min(x + c0, y) - w, c0), _can_prove(simplifier, y >= w + c0)},
        {min(x, y) - min(x + c1, w), min(y - min(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {min(x, y) - min(x + c1, w), max(min(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {min(x + c0, y) - min(x + c1, w), min(y - min(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},
        {min(x + c0, y) - min(x + c1, w), max(min(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},

        {min(y, x) - min(w, x), min(y - min(x, w), 0), _can_prove(simplifier, y <= w)},
        {min(y, x) - min(w, x), max(min(x, y) - w, 0), _can_prove(simplifier, y >= w)},
        {min(y, x + c0) - min(w, x), min(y - min(x, w), c0), _can_prove(simplifier, y <= w + c0)},
        {min(y, x + c0) - min(w, x), max(min(x + c0, y) - w, c0), _can_prove(simplifier, y >= w + c0)},
        {min(y, x) - min(w, x + c1), min(y - min(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {min(y, x) - min(w, x + c1), max(min(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {min(y, x + c0) - min(w, x + c1), min(y - min(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},
        {min(y, x + c0) - min(w, x + c1), max(min(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},

        {min(x, y) - min(w, x), min(y - min(x, w), 0), _can_prove(simplifier, y <= w)},
        {min(x, y) - min(w, x), max(min(x, y) - w, 0), _can_prove(simplifier, y >= w)},
        {min(x + c0, y) - min(w, x), min(y - min(x, w), c0), _can_prove(simplifier, y <= w + c0)},
        {min(x + c0, y) - min(w, x), max(min(x + c0, y) - w, c0), _can_prove(simplifier, y >= w + c0)},
        {min(x, y) - min(w, x + c1), min(y - min(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {min(x, y) - min(w, x + c1), max(min(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {min(x + c0, y) - min(w, x + c1), min(y - min(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},
        {min(x + c0, y) - min(w, x + c1), max(min(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},

        {min(y, x) - min(x, w), min(y - min(x, w), 0), _can_prove(simplifier, y <= w)},
        {min(y, x) - min(x, w), max(min(x, y) - w, 0), _can_prove(simplifier, y >= w)},
        {min(y, x + c0) - min(x, w), min(y - min(x, w), c0), _can_prove(simplifier, y <= w + c0)},
        {min(y, x + c0) - min(x, w), max(min(x + c0, y) - w, c0), _can_prove(simplifier, y >= w + c0)},
        {min(y, x) - min(x + c1, w), min(y - min(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {min(y, x) - min(x + c1, w), max(min(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {min(y, x + c0) - min(x + c1, w), min(y - min(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},
        {min(y, x + c0) - min(x + c1, w), max(min(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},

        // The equivalent rules for max are what you'd
        // expect. Just swap < and > and min and max (apply the
        // isomorphism x -> -x).
        {max(x, y) - max(x, w), max(y - max(x, w), 0), _can_prove(simplifier, y >= w)},
        {max(x, y) - max(x, w), min(max(x, y) - w, 0), _can_prove(simplifier, y <= w)},
        {max(x + c0, y) - max(x, w), max(y - max(x, w), c0), _can_prove(simplifier, y >= w + c0)},
        {max(x + c0, y) - max(x, w), min(max(x + c0, y) - w, c0), _can_prove(simplifier, y <= w + c0)},
        {max(x, y) - max(x + c1, w), max(y - max(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {max(x, y) - max(x + c1, w), min(max(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {max(x + c0, y) - max(x + c1, w), max(y - max(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},
        {max(x + c0, y) - max(x + c1, w), min(max(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},

        {max(y, x) - max(w, x), max(y - max(x, w), 0), _can_prove(simplifier, y >= w)},
        {max(y, x) - max(w, x), min(max(x, y) - w, 0), _can_prove(simplifier, y <= w)},
        {max(y, x + c0) - max(w, x), max(y - max(x, w), c0), _can_prove(simplifier, y >= w + c0)},
        {max(y, x + c0) - max(w, x), min(max(x + c0, y) - w, c0), _can_prove(simplifier, y <= w + c0)},
        {max(y, x) - max(w, x + c1), max(y - max(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {max(y, x) - max(w, x + c1), min(max(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {max(y, x + c0) - max(w, x + c1), max(y - max(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},
        {max(y, x + c0) - max(w, x + c1), min(max(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},

        {max(x, y) - max(w, x), max(y - max(x, w), 0), _can_prove(simplifier, y >= w)},
        {max(x, y) - max(w, x), min(max(x, y) - w, 0), _can_prove(simplifier, y <= w)},
        {max(x + c0, y) - max(w, x), max(y - max(x, w), c0), _can_prove(simplifier, y >= w + c0)},
        {max(x + c0, y) - max(w, x), min(max(x + c0, y) - w, c0), _can_prove(simplifier, y <= w + c0)},
        {max(x, y) - max(w, x + c1), max(y - max(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {max(x, y) - max(w, x + c1), min(max(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {max(x + c0, y) - max(w, x + c1), max(y - max(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},
        {max(x + c0, y) - max(w, x + c1), min(max(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},

        {max(y, x) - max(x, w), max(y - max(x, w), 0), _can_prove(simplifier, y >= w)},
        {max(y, x) - max(x, w), min(max(x, y) - w, 0), _can_prove(simplifier, y <= w)},
        {max(y, x + c0) - max(x, w), max(y - max(x, w), c0), _can_prove(simplifier, y >= w + c0)},
        {max(y, x + c0) - max(x, w), min(max(x + c0, y) - w, c0), _can_prove(simplifier, y <= w + c0)},
        {max(y, x) - max(x + c1, w), max(y - max(x + c1, w), fold(-c1)), _can_prove(simplifier, y + c1 >= w)},
        {max(y, x) - max(x + c1, w), min(max(x, y) - w, fold(-c1)), _can_prove(simplifier, y + c1 <= w)},
        {max(y, x + c0) - max(x + c1, w), max(y - max(x + c1, w), fold(c0 - c1)), _can_prove(simplifier, y + c1 >= w + c0)},
        {max(y, x + c0) - max(x + c1, w), min(max(x + c0, y) - w, fold(c0 - c1)), _can_prove(simplifier, y + c1 <= w + c0)},

        {c0 - (c1 - x) / c2, (fold(c0 * c2 - c1 + c2 - 1) + x) / c2, c2 > 0},
        {c0 - (x + c1) / c2, (fold(c0 * c2 - c1 + c2 - 1) - x) / c2, c2 > 0},
        {x - (x + y) / c0, (x * fold(c0 - 1) - y + fold(c0 - 1)) / c0, c0 > 0},
        {x - (x - y) / c0, (x * fold(c0 - 1) + y + fold(c0 - 1)) / c0, c0 > 0},
        {x - (y + x) / c0, (x * fold(c0 - 1) - y + fold(c0 - 1)) / c0, c0 > 0},
        {x - (y - x) / c0, (x * fold(c0 + 1) - y + fold(c0 - 1)) / c0, c0 > 0},
        {(x + y) / c0 - x, (x * fold(1 - c0) + y) / c0},
        {(y + x) / c0 - x, (y + x * fold(1 - c0)) / c0},
        {(x - y) / c0 - x, (x * fold(1 - c0) - y) / c0},
        {(y - x) / c0 - x, (y - x * fold(1 + c0)) / c0},

        {(x / c0) * c0 - x, -(x % c0), c0 > 0},
        {x - (x / c0) * c0, x % c0, c0 > 0},
        {((x + c0) / c1) * c1 - x, (-x) % c1, c1 > 0 && c0 + 1 == c1},
        {x - ((x + c0) / c1) * c1, ((x + c0) % c1) + fold(-c0), c1 > 0 && c0 + 1 == c1},
        {x * c0 - y * c1, (x * fold(c0 / c1) - y) * c1, c0 % c1 == 0},
        {x * c0 - y * c1, (x - y * fold(c1 / c0)) * c0, c1 % c0 == 0},
        // Various forms of (x +/- a)/c - (x +/- b)/c. We can
        // *almost* cancel the x.  The right thing to do depends
        // on which of a or b is a constant, and we also need to
        // catch the cases where that constant is zero.
        {((x + y) + z) / c0 - ((y + x) + w) / c0, ((x + y) + z) / c0 - ((x + y) + w) / c0, c0 > 0},
        {(x + y) / c0 - (y + x) / c0, 0, c0 != 0},
        {(x + y) / c0 - (x + c1) / c0, (((x + fold(c1 % c0)) % c0) + (y - c1)) / c0, c0 > 0},
        {(x + c1) / c0 - (x + y) / c0, ((fold(c0 + c1 - 1) - y) - ((x + fold(c1 % c0)) % c0)) / c0, c0 > 0},
        {(x - y) / c0 - (x + c1) / c0, (((x + fold(c1 % c0)) % c0) - y - c1) / c0, c0 > 0},
        {(x + c1) / c0 - (x - y) / c0, ((y + fold(c0 + c1 - 1)) - ((x + fold(c1 % c0)) % c0)) / c0, c0 > 0},
        {x / c0 - (x + y) / c0, ((fold(c0 - 1) - y) - (x % c0)) / c0, c0 > 0},
        {(x + y) / c0 - x / c0, ((x % c0) + y) / c0, c0 > 0},
        {x / c0 - (x - y) / c0, ((y + fold(c0 - 1)) - (x % c0)) / c0, c0 > 0},
        {(x - y) / c0 - x / c0, ((x % c0) - y) / c0, c0 > 0},

        // Simplification of bounds code for various tail
        // strategies requires cancellations of the form:
        // min(f(x), y) - g(x)

        // There are many potential variants of these rules if
        // we start adding commutative/associative rewritings
        // of them, or consider max as well as min. We
        // explicitly only include the ones necessary to get
        // correctness_nested_tail_strategies to pass.
        {(min(x + y, z) + w) - x, min(z - x, y) + w},
        {min((x + y) + w, z) - x, min(z - x, y + w)},
        {min(min(x + z, y), w) - x, min(min(y, w) - x, z)},
        {min(min(y, x + z), w) - x, min(min(y, w) - x, z)},

        {min((x + y) * u + z, w) - x * u, min(w - x * u, y * u + z)},
        {min((y + x) * u + z, w) - x * u, min(w - x * u, y * u + z)},

        // Splits can introduce confounding divisions
        {min(x * c0 + y, z) / c1 - x * c2, min(y, z - x * c0) / c1, c0 == c1 * c2},
        {min(z, x * c0 + y) / c1 - x * c2, min(y, z - x * c0) / c1, c0 == c1 * c2},

        // There could also be an addition inside the division (e.g. if it's division rounding up)
        {(min(x * c0 + y, z) + w) / c1 - x * c2, (min(y, z - x * c0) + w) / c1, c0 == c1 * c2},
        {(min(z, x * c0 + y) + w) / c1 - x * c2, (min(z - x * c0, y) + w) / c1, c0 == c1 * c2},
    };

    // for (const auto &rule : rules) {
    //     std::cerr << "rewrite(" << rule.before << ", " << rule.after;
    //     if (rule.pred.defined()) {
    //         std::cerr << ", " << rule.pred;
    //     }
    //     std::cerr << ")\n";
    // }

    print_function_typed<Halide::Internal::Sub>(rules, "simplify_sub", "Sub");

    // this is for checking correctness, uncomment out when checking.

    // for (const auto &rule : rules) {
    //     Expr simpl = simplify_sub(rule.before);
    //     std::cerr << "Original: " << rule.before << "\n";
    //     std::cerr << simpl << " vs. " << rule.after << "\n";
    //     if (!equal(simpl, rule.after)) {
    //         std::cerr << "ERROR\n";
    //     }
    // }

    // For testing a single rule (debugging codegen)
    /*
    Expr expr = ((c0 - x) - (y + c1));
    Expr expected = (fold(c0 - c1) - (x + y));
    Expr simpl = simplify_sub(expr);
    std::cerr << expr << " -> " << simpl << "\n";
    std::cerr << "Expected: " << expected << "\n";
    */

    return 0;
}
