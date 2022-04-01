#include "cfir/ReuseAnalysis.h"

#include "cfir/Nodes.h"
#include "cfir/Visitor.h"

#include "ast/Substitute.h"

#include <algorithm>
#include <memory>

namespace CFIR {

struct VariableCounter : public Visitor {
    size_t n_variables = 0;

    void visit(const Node *node) override {
        size_t maximum = 0;
        for (const auto &child : node->children) {
            n_variables = 0;
            child->accept(this);
            maximum = std::max(maximum, n_variables);
        }
        n_variables = maximum;
    }

    template<typename T>
    void visit_type_check(const T *node) {
        visit((const Node *)node);
        n_variables++;
    }

    void visit(const Add *node) override {
        visit_type_check(node);
    }

    void visit(const Sub *node) override {
        visit_type_check(node);
    }

    void visit(const Mod *node) override {
        visit_type_check(node);
    }

    void visit(const Mul *node) override {
        visit_type_check(node);
    }

    void visit(const Div *node) override {
        visit_type_check(node);
    }

    void visit(const Min *node) override {
        visit_type_check(node);
    }

    void visit(const Max *node) override {
        visit_type_check(node);
    }

    void visit(const EQ *node) override {
        visit_type_check(node);
    }

    void visit(const NE *node) override {
        visit_type_check(node);
    }

    void visit(const LT *node) override {
        visit_type_check(node);
    }

    void visit(const LE *node) override {
        visit_type_check(node);
    }

    void visit(const GT *node) override {
        visit_type_check(node);
    }

    void visit(const GE *node) override {
        visit_type_check(node);
    }

    void visit(const And *node) override {
        visit_type_check(node);
    }

    void visit(const Or *node) override {
        visit_type_check(node);
    }

    void visit(const Not *node) override {
        visit_type_check(node);
    }

    void visit(const Select *node) override {
        visit_type_check(node);
    }

    void visit(const ConstantInt *node) override {
        visit_type_check(node);
    }

    void visit(const Broadcast *node) override {
        visit_type_check(node);
    }

    void visit(const Ramp *node) override {
        visit_type_check(node);
    }
};

struct VariableReplacer : public Mutator {
    const std::string prefix;
    size_t variable_count = 0;
    VarScope map;

    VariableReplacer(const std::string &_prefix) : prefix(_prefix) {}

    IdPtr update_id(const IdPtr id) {
        return substitute(id, map);
    }

    const std::string make_id() {
        const std::string name = prefix + std::to_string(variable_count++);
        return name;
    }

    template<typename T>
    void recurse_on_children(const T *node, std::shared_ptr<T> n, const size_t current) {
        for (const auto &child : node->children) {
            variable_count = current;
            n->children.push_back(child->mutate(this));
        }
    }

    template<typename T>
    NodePtr visit_type_check(const T *node) {
        const size_t current = variable_count;
        std::shared_ptr<T> n = nullptr;

        {
            // TODO: is there a cleaner way than this?
            // Should include type as part of Identifier.
            const std::string new_id = make_id();
            const std::string typed_id = "((const " + T::type_name + "*)" + new_id + ")";
            const std::shared_ptr<Name> as_name = std::dynamic_pointer_cast<Name>(node->typed_id);
            assert(as_name);
            // In the map, give this value a type.
            map[as_name->name] = make_name(typed_id);
            const IdPtr id = make_name(new_id, true);
            const IdPtr current_id = update_id(node->current_id);
            n = std::make_shared<T>(current_id, id);

            recurse_on_children<T>(node, n, current + 1);
        }

        variable_count = current;
        return n;
    }

    NodePtr visit(const Add *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Sub *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Mod *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Mul *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Div *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Min *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Max *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const EQ *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const NE *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const LT *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const LE *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const GT *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const GE *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const And *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Or *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Not *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Select *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Broadcast *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const Ramp *node) override {
        return visit_type_check(node);
    }

    NodePtr visit(const ConstantInt *node) override {
        const size_t current = variable_count;
        const IdPtr new_id = substitute(node->id, map);
        std::shared_ptr<ConstantInt> ptr = std::make_shared<ConstantInt>(new_id, node->value);
        recurse_on_children<ConstantInt>(node, ptr, current);
        variable_count = current;
        return ptr;
    }


    NodePtr visit(const Equality *node) override {
        const size_t current = variable_count;
        const IdPtr expr0 = substitute(node->expr0, map);
        const IdPtr expr1 = substitute(node->expr1, map);
        std::shared_ptr<Equality> ptr = std::make_shared<Equality>(expr0, expr1);
        recurse_on_children<Equality>(node, ptr, current);
        variable_count = current;
        return ptr;
    }

    NodePtr visit(const Return *node) override {
        const size_t current = variable_count;
        // TODO: this doesn't work because variables are in pointer form here...
        const AST::ExprPtr ret_expr = AST::substitute(node->ret_expr, map);
        std::shared_ptr<Return> ptr = std::make_shared<Return>(ret_expr);
        recurse_on_children<Return>(node, ptr, current);
        variable_count = current;
        return ptr;
    }

    NodePtr visit(const IsConstant *node) override {
        const size_t current = variable_count;
        const IdPtr id = substitute(node->id, map);
        const IdPtr value_id = substitute(node->value_id, map);
        const IdPtr type_id = substitute(node->type_id, map);
        std::shared_ptr<IsConstant> ptr = std::make_shared<IsConstant>(id, value_id, type_id);
        recurse_on_children<IsConstant>(node, ptr, current);
        variable_count = current;
        return ptr;
    }

    NodePtr visit(const Predicate *node) override {
        const size_t current = variable_count;
        const AST::ExprPtr pred_expr = AST::substitute(node->pred_expr, map);
        std::shared_ptr<Predicate> ptr = std::make_shared<Predicate>(pred_expr);
        recurse_on_children<Predicate>(node, ptr, current);
        variable_count = current;
        return ptr;
    }
};

size_t get_max_types_needed(const std::shared_ptr<Node> &root) {
    VariableCounter counter;
    root->accept(&counter);
    return counter.n_variables;
}

NodePtr do_reuse_analysis(const std::shared_ptr<Node> &root) {
    size_t n_declarations = get_max_types_needed(root);
    static const std::string replacement_prefix = "r";
    VariableReplacer replacer(replacement_prefix);
    std::shared_ptr<Node> update = root->mutate(&replacer);

    // Add pre-declarations.
    NodePtr declare = std::make_shared<Declaration>(n_declarations, replacement_prefix);
    update->children.insert(update->children.begin(), declare);

    return update;
}

}  // namespace CFIR
