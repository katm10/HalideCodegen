#include "ast/LinearizeNodes.h"
#include <algorithm>

namespace AST {

std::string type_to_str(NodeType type){
    switch (type)
    {
    case NodeType::Add:
        return "add";
    case NodeType::Sub:
        return "sub";    
    case NodeType::Div:
        return "div";
    case NodeType::Mul:
        return "mul";  
    case NodeType::Mod:
        return "mod";
    case NodeType::Min:
        return "min";
    case NodeType::Max:
        return "max";
    case NodeType::EQ:
        return "eq";
    case NodeType::NE:
        return "ne";
    case NodeType::LE:
        return "le";
    case NodeType::GT:
        return "gt";
    case NodeType::GE:
        return "ge";
    case NodeType::And:
        return "and";
    case NodeType::Or:
        return "or";
    case NodeType::Not:
        return "not";
    case NodeType::Select:
        return "select";
    case NodeType::Broadcast:
        return "broadcast";
    default:
        return std::to_string((int)type);
    }

    return "ERROR";
}

struct LinearizeNodes : public Visitor {
    int counter = 0;
    std::stack<IdPtr> args;
    std::stack<IdPtr> types; 

    const IdPtr default_type = make_name("default_type");

    std::vector<FoldCall> calls;
    VarScope scope;

    LinearizeNodes(VarScope &scope) : scope(scope) {}

    template<typename T>
    void transfer(const T *node) {
        const std::string value_name = "cln" + std::to_string(counter);
        const std::string type_name = "tln" + std::to_string(counter);
        IdPtr name = make_name(value_name);
        IdPtr type = make_name(type_name);
        ++counter;

        args.push(name);
        types.push(type);

        size_t n = args.size();

        Visitor::visit(node);

        n = args.size() - n;

        std::vector<IdPtr> call_args;
        for (size_t i = 0; i < n; ++i){
            call_args.push_back(args.top());

            args.pop();
            types.pop();

            // TODO is there a better way of filling this vector?
            std::reverse(call_args.begin(), call_args.end());
        }

        calls.emplace_back(name, type, type_to_str(node->node_type), call_args);

        assert(args.top() == name);
    }

    void visit(const ConstantInt *expr) {

    }

    void visit(const ConstantVar *expr) {
        auto name_map = scope.find(expr->name);
        if (name_map != scope.end()) {
            args.push(name_map->second);
            types.push(default_type);
        } else {
            assert(false); 
        }

    }

    void visit(const Var *expr) {
    }

    void visit(const Add *expr) {
        transfer(expr);
    }

    void visit(const Sub *expr) {
        transfer(expr);
    }

    void visit(const Mod *expr) {
        transfer(expr);
    }

    void visit(const Mul *expr) {
        transfer(expr);
    }

    void visit(const Div *expr) {
        transfer(expr);
    }

    void visit(const Min *expr) {
        transfer(expr);
    }

    void visit(const Max *expr) {
        transfer(expr);
    }

    void visit(const EQ *expr) {
        transfer(expr);
    }

    void visit(const NE *expr) {
        transfer(expr);
    }

    void visit(const LT *expr) {
        transfer(expr);
    }

    void visit(const LE *expr) {
        transfer(expr);
    }

    void visit(const GT *expr) {
        transfer(expr);
    }

    void visit(const GE *expr) {
        transfer(expr);
    }

    void visit(const And *expr) {
        transfer(expr);
    }

    void visit(const Or *expr) {
        transfer(expr);
    }

    void visit(const Not *expr) {
        transfer(expr);
    }

    void visit(const Select *expr) {
        transfer(expr);
        expr->cond->accept(this);
        expr->a->accept(this);
        expr->b->accept(this);
    }

    void visit(const Ramp *expr) {
        transfer(expr);
        expr->base->accept(this);
        expr->stride->accept(this);
        expr->lanes->accept(this);
    }

    void visit(const Broadcast *expr) {
        transfer(expr);
        expr->value->accept(this);
        expr->lanes->accept(this);
    }

    void visit(const Fold *expr) {
        expr->value->accept(this);
    }

};

ExprPtr linearize_fold(const Fold *node, VarScope &scope) {
    LinearizeNodes ln(scope);
    node->accept(&ln);

    IdPtr out_expr = make_name("expr");

    return std::make_shared<FoldBlock>(ln.args.top(), ln.types.top(), ln.calls, out_expr);
}
} // AST