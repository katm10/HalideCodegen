#include "ast/Printer.h"
#include "ast/Substitute.h"
#include "ast/Types.h"
#include "cfir/Nodes.h"
#include "cfir/Printer.h"
#include "cfir/ReuseAnalysis.h"
#include "Identifier.h"
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

shared_ptr<Node> tree_constructor(shared_ptr<Node> root, const ExprPtr &expr, const IdPtr &id, VarScope &scope);

template <typename BinOp>
inline shared_ptr<Node> handle_bin_op_helper(shared_ptr<Node> &typed_root, const BinOp *expr, const IdPtr &typed_id, VarScope &scope)
{
    const IdPtr a_id = make_id_ptr(typed_id, "a");
    const IdPtr b_id = make_id_ptr(typed_id, "b");

    shared_ptr<Node> a_node = tree_constructor(typed_root, expr->a, a_id, scope);
    return tree_constructor(a_node, expr->b, b_id, scope);
}

template <typename BinOp>
inline shared_ptr<Node> handle_bin_op_starter(shared_ptr<Node> &typed_root, const BinOp *expr, VarScope &scope)
{
    const IdPtr a_id = make_name("a");
    const IdPtr b_id = make_name("b");

    shared_ptr<Node> a_node = tree_constructor(typed_root, expr->a, a_id, scope);
    return tree_constructor(a_node, expr->b, b_id, scope);
}

// BinOp is the AST type, LBinOp is the CFIR type
template <typename BinOp, typename LBinOp>
inline shared_ptr<Node> handle_bin_op(shared_ptr<Node> &root, const ExprPtr &expr, const IdPtr &id, VarScope &scope)
{
    const BinOp *op = expr->as<BinOp>();
    assert(op != nullptr);

    IdPtr typed_id = make_new_unique_name();
    // Make type check node in tree.
    shared_ptr<LBinOp> node = make_shared<LBinOp>(id, typed_id);
    node = root->get_child(node);   // Possible replace if it already exists.
    assert(node);                   // get_child returned the wrong type...?
    typed_id = node->typed_id;      // This might have changed the name.

    shared_ptr<Node> typed_root = std::move(node);

    return handle_bin_op_helper<BinOp>(typed_root, op, typed_id, scope);
}

shared_ptr<Node> handle_variable(shared_ptr<Node> root, const Var *var, const IdPtr &id, VarScope &scope)
{
    auto iter = scope.find(var->name);
    if (iter == scope.end()) {
        scope.insert(std::make_pair(var->name, id));
        // Insert into scope and don't worry about it.
        return root;
    }
    else {
        const IdPtr existing_id = iter->second;
        shared_ptr<CFIR::Equality> equal = make_shared<CFIR::Equality>(existing_id, id);
        return root->get_child(equal); // Don't duplicate if possible.
    }
}

shared_ptr<Node> handle_const_variable(shared_ptr<Node> root, const ConstantVar *var, const IdPtr &id, VarScope &scope)
{
    auto iter = scope.find(var->name);
    if (iter == scope.end()) {
        scope.insert(std::make_pair(var->name, id));

        shared_ptr<CFIR::IsConstant> cond_node = make_shared<CFIR::IsConstant>(id);
        return root->get_child(cond_node);
    }
    else {
        const IdPtr existing_id = iter->second;
        shared_ptr<CFIR::Equality> equal = make_shared<CFIR::Equality>(existing_id, id);
        shared_ptr<CFIR::Equality> pequal = root->get_child(equal); // Don't duplicate if possible.
        return pequal;
    }
}

inline shared_ptr<Node> handle_select_helper(shared_ptr<Node> &typed_root, const Select *expr, const IdPtr &id, VarScope &scope)
{
    const IdPtr cond_id = make_id_ptr(id, "condition");
    const IdPtr true_id = make_id_ptr(id, "true_value");
    const IdPtr false_id = make_id_ptr(id, "false_value");

    shared_ptr<Node> cond_node = tree_constructor(typed_root, expr->cond, cond_id, scope);
    shared_ptr<Node> true_node = tree_constructor(cond_node, expr->a, true_id, scope);
    return tree_constructor(true_node, expr->b, false_id, scope);
}

inline shared_ptr<Node> handle_select_starter(shared_ptr<Node> &typed_root, const Select *expr, VarScope &scope)
{
    const IdPtr cond_id = make_name("condition");
    const IdPtr true_id = make_name("true_value");
    const IdPtr false_id = make_name("false_value");

    shared_ptr<Node> cond_node = tree_constructor(typed_root, expr->cond, cond_id, scope);
    shared_ptr<Node> true_node = tree_constructor(cond_node, expr->a, true_id, scope);
    return tree_constructor(true_node, expr->b, false_id, scope);
}

inline shared_ptr<Node> handle_select(shared_ptr<Node> &root, const ExprPtr &expr, const IdPtr &id, VarScope &scope)
{
    const Select *op = expr->as<Select>();
    assert(op != nullptr); // We failed to identify the Expr properly.

    IdPtr typed_id = make_new_unique_name();

    shared_ptr<CFIR::Select> node = make_shared<CFIR::Select>(id, typed_id);
    node = root->get_child(node);   // Possible replace if it already exists.
    assert(node);                   // get_child returned the wrong type...?
    typed_id = node->typed_id; // This might have changed the name...?
    shared_ptr<Node> untyped_root = std::move(node);

    return handle_select_helper(untyped_root, op, typed_id, scope);
}

inline shared_ptr<Node> handle_broadcast_helper(shared_ptr<Node> &typed_root, const Broadcast *expr, const IdPtr &typed_id, VarScope &scope)
{
    const IdPtr value_id = make_id_ptr(typed_id, "value");
    // TODO: should probably not recurse on lanes, they should be constants?
    const IdPtr lanes_id = make_id_ptr(typed_id, "lanes");

    const ExprPtr value = expr->value;
    const ExprPtr lanes = expr->lanes;

    return tree_constructor(typed_root, value, value_id, scope);
}

inline shared_ptr<Node> handle_broadcast_starter(shared_ptr<Node> &typed_root, const Broadcast *expr, VarScope &scope)
{
    const IdPtr value_id = make_name("value");
    // TODO: should probably not recurse on lanes, they should be constants?
    const IdPtr lanes_id = make_name("lanes");

    const ExprPtr value = expr->value;
    const ExprPtr lanes = expr->lanes;

    scope.insert(std::make_pair(lanes->as<ConstantVar>()->name, lanes_id));

    return tree_constructor(typed_root, value, value_id, scope);
    // return tree_constructor(value_node, lanes, lanes_id, scope);
}

inline shared_ptr<Node> handle_broadcast(shared_ptr<Node> &root, const ExprPtr &expr, const IdPtr &id, VarScope &scope)
{
    const Broadcast *op = expr->as<Broadcast>();
    assert(op);
    IdPtr typed_id = make_new_unique_name();

    shared_ptr<CFIR::Broadcast> node = make_shared<CFIR::Broadcast>(id, typed_id);
    node = root->get_child(node);
    assert(node);
    typed_id = node->typed_id; // In case there was already a broadcast child

    shared_ptr<Node> untyped_root = std::move(node);
    return handle_broadcast_helper(untyped_root, op, typed_id, scope);
}

inline shared_ptr<Node> handle_ramp_helper(shared_ptr<Node> &typed_root, const Ramp *expr, const IdPtr &typed_id, VarScope &scope)
{
    const IdPtr base_id = make_id_ptr(typed_id, "base");
    const IdPtr stride_id = make_id_ptr(typed_id, "stride");
    // TODO: should probably not recurse on lanes, they should be constants?
    const IdPtr lanes_id = make_id_ptr(typed_id, "lanes");

    const ExprPtr base = expr->base;
    const ExprPtr stride = expr->stride;
    const ExprPtr lanes = expr->lanes;

    scope.insert(std::make_pair(lanes->as<ConstantVar>()->name, lanes_id));

    shared_ptr<Node> base_node = tree_constructor(typed_root, base, base_id, scope);
    return tree_constructor(base_node, stride, stride_id, scope);
    // return tree_constructor(stride_node, lanes, lanes_id, scope);
}

inline shared_ptr<Node> handle_ramp_starter(shared_ptr<Node> &typed_root, const Ramp *expr, VarScope &scope)
{
    const IdPtr base_id = make_name("base");
    const IdPtr stride_id = make_name("stride");
    // TODO: should probably not recurse on lanes, they should be constants?
    const IdPtr lanes_id = make_name("lanes");

    const ExprPtr base = expr->base;
    const ExprPtr stride = expr->stride;
    const ExprPtr lanes = expr->lanes;

    scope.insert(std::make_pair(lanes->as<ConstantVar>()->name, lanes_id));

    shared_ptr<Node> base_node = tree_constructor(typed_root, base, base_id, scope);
    return tree_constructor(base_node, stride, stride_id, scope);
    // return tree_constructor(stride_node, lanes, lanes_id, scope);
}

inline shared_ptr<Node> handle_ramp(shared_ptr<Node> &root, const ExprPtr &expr, const IdPtr &id, VarScope &scope)
{
    const Ramp *op = expr->as<Ramp>();
    assert(op);
    IdPtr typed_id = make_new_unique_name();

    shared_ptr<CFIR::Ramp> node = make_shared<CFIR::Ramp>(id, typed_id);
    node = root->get_child(node);
    assert(node);
    typed_id = node->typed_id;

    shared_ptr<Node> untyped_root = std::move(node);
    return handle_ramp_helper(untyped_root, op, typed_id, scope);
}

inline shared_ptr<Node> handle_not_helper(shared_ptr<Node> &typed_root, const Not *expr, const IdPtr &typed_id, VarScope &scope)
{
    const IdPtr a_id = make_id_ptr(typed_id, "a");
    return tree_constructor(typed_root, expr->a, a_id, scope);
}

inline shared_ptr<Node> handle_not_starter(shared_ptr<Node> &typed_root, const Not *expr, VarScope &scope)
{
    const IdPtr a_id = make_name("a");
    return tree_constructor(typed_root, expr->a, a_id, scope);
}

inline shared_ptr<Node> handle_not(shared_ptr<Node> &root, const ExprPtr &expr, const IdPtr &id, VarScope &scope)
{
    const Not *op = expr->as<Not>();
    assert(op);
    IdPtr typed_id = make_new_unique_name();
    shared_ptr<CFIR::Not> node = make_shared<CFIR::Not>(id, typed_id);
    node = root->get_child(node);
    assert(node);
    typed_id = node->typed_id;
    shared_ptr<Node> untyped_root = std::move(node);
    return handle_not_helper(untyped_root, op, typed_id, scope);
}

inline shared_ptr<Node> handle_constant_int(shared_ptr<Node> &root, const ConstantInt *imm, const IdPtr &id, VarScope &scope)
{
    // Inserts the typecheck and fixes name if necessary
    shared_ptr<CFIR::ConstantInt> imm_node = make_shared<CFIR::ConstantInt>(id, imm->value);
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
shared_ptr<Node> tree_constructor(shared_ptr<Node> root, const ExprPtr &expr, const IdPtr &id, VarScope &scope)
{
    switch (expr->node_type)
    {
    case NodeType::Sub:
        return handle_bin_op<Sub, CFIR::Sub>(root, expr, id, scope);
    case NodeType::Add:
        return handle_bin_op<Add, CFIR::Add>(root, expr, id, scope);
    case NodeType::Mod:
        return handle_bin_op<Mod, CFIR::Mod>(root, expr, id, scope);
    case NodeType::Mul:
        return handle_bin_op<Mul, CFIR::Mul>(root, expr, id, scope);
    case NodeType::Div:
        return handle_bin_op<Div, CFIR::Div>(root, expr, id, scope);
    case NodeType::Min:
        return handle_bin_op<Min, CFIR::Min>(root, expr, id, scope);
    case NodeType::Max:
        return handle_bin_op<Max, CFIR::Max>(root, expr, id, scope);
    case NodeType::EQ:
        return handle_bin_op<EQ, CFIR::EQ>(root, expr, id, scope);
    case NodeType::NE:
        return handle_bin_op<NE, CFIR::NE>(root, expr, id, scope);
    case NodeType::LT:
        return handle_bin_op<LT, CFIR::LT>(root, expr, id, scope);
    case NodeType::LE:
        return handle_bin_op<LE, CFIR::LE>(root, expr, id, scope);
    case NodeType::GT:
        return handle_bin_op<GT, CFIR::GT>(root, expr, id, scope);
    case NodeType::GE:
        return handle_bin_op<GE, CFIR::GE>(root, expr, id, scope);
    case NodeType::And:
        return handle_bin_op<And, CFIR::And>(root, expr, id, scope);
    case NodeType::Or:
        return handle_bin_op<Or, CFIR::Or>(root, expr, id, scope);
    case NodeType::Not:
        return handle_not(root, expr, id, scope);
    case NodeType::Select:
        return handle_select(root, expr, id, scope);
    case NodeType::Var:
    {
        const Var *var = expr->as<Var>();
        return handle_variable(root, var, id, scope);
    }
    case NodeType::ConstantVar:
    {
        const ConstantVar *var = expr->as<ConstantVar>();
        return handle_const_variable(root, var, id, scope);
    }
    case NodeType::ConstantInt:
    {
        const ConstantInt *imm = expr->as<ConstantInt>();
        return handle_constant_int(root, imm, id, scope);
    }
    case NodeType::Ramp:
        return handle_ramp(root, expr, id, scope);
    case NodeType::Broadcast:
        return handle_broadcast(root, expr, id, scope);
    default:
        assert(false);
    }
    return nullptr;
}

template <typename T>
shared_ptr<Node> start_tree_constructor(shared_ptr<Node> root, const T *expr, VarScope &scope)
{
    if constexpr (std::is_same_v<T, Sub>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Add>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Mod>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Mul>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Div>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Min>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Max>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Mod>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, EQ>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, NE>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, LT>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, LE>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, GT>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, GE>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, And>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Or>)
    {
        return handle_bin_op_starter<T>(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Not>)
    {
        return handle_not_starter(root, expr, scope); // TODO: check that this works
    }
    else if constexpr (std::is_same_v<T, Select>)
    {
        return handle_select_starter(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Broadcast>)
    {
        return handle_broadcast_starter(root, expr, scope);
    }
    else if constexpr (std::is_same_v<T, Ramp>)
    {
        return handle_ramp_helper(root, expr, scope);
    }
    else
    {
        assert(false);
    }
    assert(false);
    return nullptr;
}

template <typename T>
void add_rule_typed(shared_ptr<Node> root, const Rule *rule, const std::string &type_name)
{
    VarScope scope;
    const T *expr = rule->before->as<T>();
    assert(expr);
    shared_ptr<Node> deepest;

    // TODO: GET RID OF GENERIC CONDITION NODES AND DON"T USE STRINGS FOR RETURNS.

    if (rule->types != UINT16_MAX)
    {
        // TODO: need to get rid of generic Condition node.
        const std::string type_condition = rule->generate_condition(type_name);
        shared_ptr<CFIR::Condition> type_node = make_shared<CFIR::Condition>(type_condition);
        deepest = root->get_child(type_node);
        deepest = start_tree_constructor(deepest, expr, scope);
    }
    else
    {
        deepest = start_tree_constructor(root, expr, scope);
    }

    if (rule->pred)
    {
        const AST::ExprPtr predicate = AST::substitute(rule->pred, scope);
        // TODO: probably want to assert that child node doesn't exist...?
        shared_ptr<CFIR::Predicate> cond_node = make_shared<CFIR::Predicate>(predicate);
        deepest = deepest->get_child(cond_node);
    }

    const AST::ExprPtr retval = AST::substitute(rule->after, scope);
    shared_ptr<CFIR::Return> ret_node = make_shared<CFIR::Return>(retval);
    deepest = deepest->get_child(ret_node);
}

template <typename T>
shared_ptr<Node> create_graph_typed(const vector<Rule *> &rules, const std::string &type_name)
{
    assert(rules.size() > 0);

    shared_ptr<Node> root = make_shared<CFIR::Sequence>();

    for (const auto &rule : rules)
    {
        add_rule_typed<T>(root, rule, type_name);
    }
    return root;
}

std::string get_input_string(const ExprPtr &starter) {
    if (starter->is_bin_op()) {
        return "(const Expr &a, const Expr &b, const Type &type, Simplify *simplifier)";
    } else {
        std::cerr << "Not implemented:\n";
        print(std::cerr, starter);
        std::cerr << "\n";
        assert(false);
    }
}

template <typename T>
void print_function_typed(const vector<Rule *> &rules, const std::string &func_name)
{
    const std::string type_name = "type";
    const std::string arg_string = get_input_string(rules.front()->before);

    shared_ptr<Node> root = create_graph_typed<T>(rules, type_name);
    root = do_reuse_analysis(root);

    std::cout << "#include \"Simplify_Internal.h\"\n#include \"Expr.h\"\n#include \"Type.h\"\n\n";
    std::cout << "namespace Halide {\n"
              << "namespace Internal {\n"
              << "namespace CodeGen {\n\n";

    std::cout << "Expr " << func_name << arg_string << " {\n";
    root->print(std::cout, "");
    std::cout << "  return Expr();\n}\n";

    std::cout << "}  // namespace CodeGen\n"
              << "}  // namespace Internal\n"
              << "}  // namespace Halide\n";
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
        print_function_typed<Add>(rules, filename);
        break;
    case NodeType::Sub:
        print_function_typed<Sub>(rules, filename);
        break;
    case NodeType::Mod:
        print_function_typed<Mod>(rules, filename);
        break;
    case NodeType::Mul:
        print_function_typed<Mul>(rules, filename);
        break;
    case NodeType::Div:
        print_function_typed<Div>(rules, filename);
        break;
    case NodeType::And:
        print_function_typed<And>(rules, filename);
        break;
    case NodeType::Or:
        print_function_typed<Or>(rules, filename);
        break;
    case NodeType::EQ:
        print_function_typed<EQ>(rules, filename);
        break;
    case NodeType::NE:
        print_function_typed<EQ>(rules, filename);
        break;
    case NodeType::LT:
        print_function_typed<LT>(rules, filename);
        break;
    case NodeType::GT:
        print_function_typed<GT>(rules, filename);
        break;
    case NodeType::GE:
        print_function_typed<GE>(rules, filename);
        break;
    case NodeType::LE:
        print_function_typed<LE>(rules, filename);
        break;
    case NodeType::Max:
        print_function_typed<Max>(rules, filename);
        break;
    case NodeType::Min:
        print_function_typed<Min>(rules, filename);
        break;
    // TODO add more of these
    default:
        std::cout << "Not implemented\n";
        return 1;
    }
    return 0;
}
