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
    return tree_constructor(typed_root, expr->a, a_name, scope);
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
    shared_ptr<CFIR::ConstantInt> imm_node = make_shared<CFIR::ConstantInt>(name, imm->value);
    imm_node = root->get_child(imm_node);
    assert(imm_node);
    return imm_node;
}

/*
TODOs:
    // ConstantInt,
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
        const Var *var = expr->as<Var>();
        return handle_variable(root, var, name, scope);
    }
    case NodeType::ConstantVar:
    {
        const ConstantVar *var = expr->as<ConstantVar>();
        return handle_const_variable(root, var, name, scope);
    }
    case NodeType::ConstantInt:
    {
        const ConstantInt *imm = expr->as<ConstantInt>();
        return handle_constant_int(root, imm, name, scope);
    }
    case NodeType::Ramp:
        return handle_ramp(root, expr, name, scope);
    case NodeType::Broadcast:
        return handle_broadcast(root, expr, name, scope);
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
    shared_ptr<Node> deepest;

    if (rule->types != UINT16_MAX)
    {
        const std::string type_condition = rule->generate_condition(name);
        shared_ptr<CFIR::Condition> type_node = make_shared<CFIR::Condition>(type_condition);
        deepest = root->get_child(type_node);
        deepest = tree_constructor(deepest, rule->before, name, scope);
    }
    else
    {
        deepest = start_tree_constructor(root, expr, name, scope);
    }

    if (rule->pred)
    {
        // TODO: probably want to assert that child node doesn't exist...?
        const std::string condition = "evaluate_predicate(fold(" + build_expr(rule->pred, scope) + "))";
        shared_ptr<CFIR::Condition> cond_node = make_shared<CFIR::Condition>(condition);
        deepest = deepest->get_child(cond_node);
    }

    const std::string retval = build_expr(rule->after, scope);
    shared_ptr<CFIR::Return> ret_node = make_shared<CFIR::Return>(retval);
    deepest = deepest->get_child(ret_node);
}

template <typename T>
shared_ptr<Node> create_graph_typed(const vector<Rule *> &rules, const std::string &expr_name)
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
void print_function_typed(const vector<Rule *> &rules, const std::string &func_name, const std::string &type_name)
{
    shared_ptr<Node> root = create_graph_typed<T>(rules, "expr");

    // TODO: include files? ie. #include "AST.h"
    std::cout << "ExprPtr " << func_name << "(const " << type_name << " *expr, Simplify *simplifier) {\n";
    root->print(std::cout, "");
    std::cout << "  return expr;\n}\n";
}

int main(int argc, char *argv[])
{
    if (argc != 2)
    {
        std::cout << "Usage: ./MergeTool.o <input filename>\n";
        return 1;
    }
    std::string filename = argv[1];
    std::vector<Rule *> rules = parse_rules_from_file(filename);

    // Remove directory if present.
    // Do this before extension removal incase directory has a period character.
    const size_t last_slash_idx = filename.find_last_of("\\/");
    if (std::string::npos != last_slash_idx)
    {
        filename.erase(0, last_slash_idx + 1);
    }

    // Remove extension if present.
    const size_t period_idx = filename.rfind('.');
    if (std::string::npos != period_idx)
    {
        filename.erase(period_idx);
    }

    switch (rules.front()->before->node_type)
    {
    case NodeType::Add:
        print_function_typed<Add>(rules, filename, "Add");
        break;
    case NodeType::Sub:
        print_function_typed<Sub>(rules, filename, "Sub");
        break;
    case NodeType::Mod:
        print_function_typed<Mod>(rules, filename, "Mod");
        break;
    case NodeType::Mul:
        print_function_typed<Mul>(rules, filename, "Mul");
        break;
    case NodeType::Div:
        print_function_typed<Div>(rules, filename, "Div");
        break;
    case NodeType::And:
        print_function_typed<And>(rules, filename, "And");
        break;
    case NodeType::Or:
        print_function_typed<Or>(rules, filename, "Or");
        break;
    case NodeType::EQ:
        print_function_typed<EQ>(rules, filename, "EQ");
        break;
    case NodeType::NE:
        print_function_typed<EQ>(rules, filename, "NE");
        break;
    case NodeType::LT:
        print_function_typed<LT>(rules, filename, "LT");
        break;
    case NodeType::GT:
        print_function_typed<GT>(rules, filename, "GT");
        break;
    case NodeType::GE:
        print_function_typed<GE>(rules, filename, "GE");
        break;
    case NodeType::LE:
        print_function_typed<LE>(rules, filename, "LE");
        break;
    case NodeType::Max:
        print_function_typed<Max>(rules, filename, "Max");
        break;
    case NodeType::Min:
        print_function_typed<Min>(rules, filename, "Min");
        break;
    // TODO add more of these
    default:
        std::cout << "Not implemented\n";
        return 1;
    }
    return 0;
}
