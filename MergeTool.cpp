#include "AST.h"
#include "ASTPrinter.h"
#include "CFIR.h"
#include "CFIRPrinter.h"
#include "Rule.h"
#include "Parser.h"
#include <iostream>
#include <sstream>
#include <map>
#include <memory>
#include <string>
#include <vector>

using std::make_shared;
using std::shared_ptr;
using std::vector;

// Too many conflicts with Halide IR for other names
using CFIR::Node;

shared_ptr<Node> tree_constructor(shared_ptr<Node> root, const ExprPtr &expr, const std::string &name, VarScope &scope);

template <typename BinOp>
inline shared_ptr<Node> handle_bin_op_helper(shared_ptr<Node> &typed_root, const BinOp *expr, const std::string &typed_name, VarScope &scope)
{
    const std::string a_name = typed_name + "->a";
    const std::string b_name = typed_name + "->b";

    shared_ptr<Node> a_node = tree_constructor(typed_root, expr->a, a_name, scope);
    return tree_constructor(a_node, expr->b, b_name, scope);
}

// BinOp is the AST type, LBinOp is the CFIR type
template <typename BinOp, typename LBinOp>
inline shared_ptr<Node> handle_bin_op(shared_ptr<Node> &root, const ExprPtr &expr, const std::string &name, VarScope &scope)
{
    const BinOp *op = expr->as<BinOp>();
    assert(op != nullptr);

    std::string typed_name = make_new_unique_name();
    // Make type check node in tree.
    shared_ptr<LBinOp> node = make_shared<LBinOp>(name, typed_name);
    node = root->get_child(node);   // Possible replace if it already exists.
    assert(node);                   // get_child returned the wrong type...?
    typed_name = node->output_name; // This might have changed the name.

    shared_ptr<Node> typed_root = std::move(node);

    return handle_bin_op_helper<BinOp>(typed_root, op, typed_name, scope);
}

shared_ptr<Node> handle_variable(shared_ptr<Node> root, const Var *var, const std::string &name, VarScope &scope)
{
    // TODO: handle constants
    auto iter = scope.find(var->name);
    if (iter == scope.end())
    {
        scope.insert(std::make_pair(var->name, name));
        // Insert into scope and don't worry about it.
        return root;
    }
    else
    {
        std::string existing_name = iter->second;
        shared_ptr<CFIR::Equality> equal = make_shared<CFIR::Equality>(existing_name, name);
        shared_ptr<CFIR::Equality> pequal = root->get_child(equal); // Don't duplicate if possible.
        return pequal;
    }
}

shared_ptr<Node> handle_const_variable(shared_ptr<Node> root, const ConstantVar *var, const std::string &name, VarScope &scope)
{
    // TODO: handle constants
    auto iter = scope.find(var->name);
    if (iter == scope.end())
    {
        scope.insert(std::make_pair(var->name, name));

        // TODO: change this to is_const, I am using is_const_v for testing purposes
        const std::string condition = "is_const_v(" + name + ")";
        shared_ptr<CFIR::Condition> cond_node = make_shared<CFIR::Condition>(condition);
        return root->get_child(cond_node);
    }
    else
    {
        std::string existing_name = iter->second;
        shared_ptr<CFIR::Equality> equal = make_shared<CFIR::Equality>(existing_name, name);
        shared_ptr<CFIR::Equality> pequal = root->get_child(equal); // Don't duplicate if possible.
        return pequal;
    }
}

inline shared_ptr<Node> handle_select_helper(shared_ptr<Node> &typed_root, const Select *expr, const std::string &typed_name, VarScope &scope)
{
    const std::string cond_name = typed_name + "->cond";
    const std::string true_name = typed_name + "->a";
    const std::string false_name = typed_name + "->b";

    shared_ptr<Node> cond_node = tree_constructor(typed_root, expr->cond, cond_name, scope);
    shared_ptr<Node> true_node = tree_constructor(cond_node, expr->a, true_name, scope);
    return tree_constructor(true_node, expr->b, false_name, scope);
}

inline shared_ptr<Node> handle_select(shared_ptr<Node> &root, const ExprPtr &expr, const std::string &name, VarScope &scope)
{
    const Select *op = expr->as<Select>();
    assert(op != nullptr); // We failed to identify the Expr properly.

    std::string typed_name = make_new_unique_name();

    shared_ptr<CFIR::Select> node = make_shared<CFIR::Select>(name, typed_name);
    node = root->get_child(node);   // Possible replace if it already exists.
    assert(node);                   // get_child returned the wrong type...?
    typed_name = node->output_name; // This might have changed the name...?
    shared_ptr<Node> typed_root = std::move(node);

    return handle_select_helper(typed_root, op, typed_name, scope);
}

inline shared_ptr<Node> handle_broadcast_helper(shared_ptr<Node> &typed_root, const Broadcast *expr, const std::string &typed_name, VarScope &scope)
{

    const std::string value_name = typed_name + "->value";
    const std::string lanes_name = typed_name + "->lanes";
    const ExprPtr value = expr->value;
    const ExprPtr lanes = expr->lanes;

    shared_ptr<Node> value_node = tree_constructor(typed_root, value, value_name, scope);
    return tree_constructor(value_node, lanes, lanes_name, scope);
}

inline shared_ptr<Node> handle_broadcast(shared_ptr<Node> &root, const ExprPtr &expr, const std::string &name, VarScope &scope)
{
    const Broadcast *op = expr->as<Broadcast>();
    assert(op);
    std::string typed_name = make_new_unique_name();

    shared_ptr<CFIR::Broadcast> node = make_shared<CFIR::Broadcast>(name, typed_name);
    node = root->get_child(node);
    assert(node);
    typed_name = node->output_name;
    shared_ptr<Node> typed_root = std::move(node);
    return handle_broadcast_helper(typed_root, op, typed_name, scope);
}

inline shared_ptr<Node> handle_ramp_helper(shared_ptr<Node> &typed_root, const Ramp *expr, const std::string &typed_name, VarScope &scope)
{
    const std::string base_name = typed_name + "->base";
    const std::string stride_name = typed_name + "->stride";
    const std::string lanes_name = typed_name + "->lanes";
    const ExprPtr base = expr->base;
    const ExprPtr stride = expr->stride;
    const ExprPtr lanes = expr->lanes;
    shared_ptr<Node> base_node = tree_constructor(typed_root, base, base_name, scope);
    shared_ptr<Node> stride_node = tree_constructor(base_node, stride, stride_name, scope);
    return tree_constructor(stride_node, lanes, lanes_name, scope);
}

inline shared_ptr<Node> handle_ramp(shared_ptr<Node> &root, const ExprPtr &expr, const std::string &name, VarScope &scope)
{
    const Ramp *op = expr->as<Ramp>();
    assert(op);
    std::string typed_name = make_new_unique_name();

    shared_ptr<CFIR::Ramp> node = make_shared<CFIR::Ramp>(name, typed_name);
    node = root->get_child(node);
    assert(node);
    typed_name = node->output_name;
    shared_ptr<Node> typed_root = std::move(node);
    return handle_ramp_helper(typed_root, op, typed_name, scope);
}

inline shared_ptr<Node> handle_not_helper(shared_ptr<Node> &typed_root, const Not *expr, const std::string &typed_name, const std::string &name, VarScope &scope)
{
    const std::string a_name = typed_name + "->a";
    return tree_constructor(typed_root, expr->a, name, scope);
}

inline shared_ptr<Node> handle_not(shared_ptr<Node> &root, const ExprPtr &expr, const std::string &name, VarScope &scope)
{
    const Not *op = expr->as<Not>();
    assert(op);
    std::string typed_name = make_new_unique_name();
    shared_ptr<CFIR::Not> node = make_shared<CFIR::Not>(name, typed_name);
    node = root->get_child(node);
    assert(node);
    typed_name = node->output_name;
    shared_ptr<Node> typed_root = std::move(node);
    return handle_not_helper(typed_root, op, typed_name, name, scope);
}

inline shared_ptr<Node> handle_constant_int(shared_ptr<Node> &root, const ConstantInt *imm, const std::string &name, VarScope &scope)
{
    std::string typed_name = make_new_unique_name();

    // Inserts the typecheck and fixes name if necessary
    shared_ptr<CFIR::IntImm> imm_node = make_shared<CFIR::IntImm>(name, typed_name);
    imm_node = root->get_child(imm_node);
    assert(imm_node);
    typed_name = imm_node->output_name;

    const std::string condition = typed_name + "->value == " + std::to_string(imm->value);
    shared_ptr<CFIR::Condition> cond_node = make_shared<CFIR::Condition>(condition);
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
shared_ptr<Node> tree_constructor(shared_ptr<Node> root, const ExprPtr &expr, const std::string &name, VarScope &scope)
{
    switch (expr->node_type)
    {
    case NodeType::Sub:
        return handle_bin_op<Sub, CFIR::Sub>(root, expr, name, scope);
    case NodeType::Add:
        return handle_bin_op<Add, CFIR::Add>(root, expr, name, scope);
    case NodeType::Mod:
        return handle_bin_op<Mod, CFIR::Mod>(root, expr, name, scope);
    case NodeType::Mul:
        return handle_bin_op<Mul, CFIR::Mul>(root, expr, name, scope);
    case NodeType::Div:
        return handle_bin_op<Div, CFIR::Div>(root, expr, name, scope);
    case NodeType::Min:
        return handle_bin_op<Min, CFIR::Min>(root, expr, name, scope);
    case NodeType::Max:
        return handle_bin_op<Max, CFIR::Max>(root, expr, name, scope);
    case NodeType::EQ:
        return handle_bin_op<EQ, CFIR::EQ>(root, expr, name, scope);
    case NodeType::NE:
        return handle_bin_op<NE, CFIR::NE>(root, expr, name, scope);
    case NodeType::LT:
        return handle_bin_op<LT, CFIR::LT>(root, expr, name, scope);
    case NodeType::LE:
        return handle_bin_op<LE, CFIR::LE>(root, expr, name, scope);
    case NodeType::GT:
        return handle_bin_op<GT, CFIR::GT>(root, expr, name, scope);
    case NodeType::GE:
        return handle_bin_op<GE, CFIR::GE>(root, expr, name, scope);
    case NodeType::And:
        return handle_bin_op<And, CFIR::And>(root, expr, name, scope);
    case NodeType::Or:
        return handle_bin_op<Or, CFIR::Or>(root, expr, name, scope);
    case NodeType::Not:
        return handle_not(root, expr, name, scope);
    case NodeType::Select:
        return handle_select(root, expr, name, scope);
    case NodeType::Var:
    {
        const Var* var = expr->as<Var>();
        return handle_variable(root, var, name, scope);
    }
    case NodeType::ConstantVar:
    {
        const ConstantVar* var = expr->as<ConstantVar>();
        return handle_const_variable(root, var, name, scope);
    }
    case NodeType::ConstantInt:
    {
        const ConstantInt* imm = expr->as<ConstantInt>();
        return handle_constant_int(root, imm, name, scope);
    }
    case NodeType::Ramp:
        return handle_ramp(root, expr, name, scope);
    case NodeType::Broadcast:
        return handle_broadcast(root, expr, name, scope);
    /** TODO:
     *  - Call
     *  - CanProve
     *  - Fold
     */
    default:
        assert(false);
    }
    return nullptr;
}

template <typename T>
shared_ptr<Node> start_tree_constructor(shared_ptr<Node> root, const T *expr, const std::string &name, VarScope &scope)
{
    if constexpr (std::is_same_v<T, Sub>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Add>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Mod>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Mul>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Div>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Min>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Max>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Mod>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, EQ>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, NE>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, LT>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, LE>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, GT>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, GE>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, And>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Or>)
    {
        return handle_bin_op_helper<T>(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Not>)
    {
        return handle_not_helper(root, expr, name, scope); // todo** check that this works
    }
    else if constexpr (std::is_same_v<T, Select>)
    {
        return handle_select_helper(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Broadcast>)
    {
        return handle_broadcast_helper(root, expr, name, scope);
    }
    else if constexpr (std::is_same_v<T, Ramp>)
    {
        return handle_ramp_helper(root, expr, name, scope);
    }
    else
    {
        assert(false);
    }
    assert(false);
    return nullptr;
}

template <typename T>
void add_rule_typed(shared_ptr<Node> root, const Rule *rule, const std::string &name)
{
    VarScope scope;
    const T *expr = rule->before->as<T>();
    assert(expr);
    shared_ptr<Node> deepest = start_tree_constructor(root, expr, name, scope);
    if (rule->pred)
    {
        // TODO: probably want to assert that child node doesn't exist...?
        const std::string condition = "evaluate_predicate(fold(" + build_expr(rule->pred, scope) + ", simplifier))";
        shared_ptr<CFIR::Condition> cond_node = make_shared<CFIR::Condition>(condition);
        deepest = deepest->get_child(cond_node);
    }

    const std::string retval = build_expr(rule->after, scope);
    shared_ptr<CFIR::Return> ret_node = make_shared<CFIR::Return>(retval);
    deepest = deepest->get_child(ret_node);
}

template <typename T>
shared_ptr<Node> create_graph_typed(const vector<Rule*> &rules, const std::string &expr_name)
{
    assert(rules.size() > 0);

    shared_ptr<Node> root = make_shared<CFIR::Sequence>();

    for (const auto &rule : rules)
    {
        add_rule_typed<T>(root, rule, expr_name);
    }
    return root;
}

template <typename T>
void print_function_typed(const vector<Rule*> &rules, const std::string &func_name, const std::string &type_name)
{
    shared_ptr<Node> root = create_graph_typed<T>(rules, "expr");

    std::cout << "Expr " << func_name << "(const " << type_name << " *expr, Simplify *simplifier) {\n";
    root->print(std::cout, "");
    std::cout << "  return expr;\n}\n";
}

// TODO: handle fold somehow...
ExprPtr fold(const ExprPtr expr)
{
    return make_shared<Fold>(expr);
}

// This is for generated code
// TODO this isn't really necessary anymore?
// bool is_const_v(const ExprPtr &expr)
// {
//     if (const Var var = expr->as<Var>())
//     {
//         return var->name.at(0) == 'c';
//     }
//     else
//     {
//         return is_const(expr);
//     }
// }

ExprPtr ramp(ExprPtr base, ExprPtr stride, ExprPtr lanes)
{
    return make_shared<Ramp>(base, stride, lanes);
}

ExprPtr broadcast(ExprPtr value, ExprPtr lanes)
{
    return make_shared<Broadcast>(value, lanes);
}

// TODO uhhh should I replace these?
// Expr ramp(Expr base, Expr stride, int lanes)
// {
//     return Ramp::make(base, stride, lanes);
// }

// Expr broadcast(Expr base, int lanes)
// {
//     return Broadcast::make(base, lanes);
// }

// Expr _can_prove(const Expr &simplifier, const Expr &expr)
// {
//     return Call::make(UInt(1), "_can_prove", {simplifier, expr}, Call::PureIntrinsic);
// }

// Expr _is_const(const Expr &expr)
// {
//     return Call::make(UInt(1), "is_const", {expr}, Call::PureIntrinsic);
// }

int main(void)
{
    std::string filename = "rules/good1.txt";
    std::vector<Rule *> rules = parse_rules_from_file(filename);
    print_function_typed<Sub>(rules, "simplify_sub", "Sub");

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
