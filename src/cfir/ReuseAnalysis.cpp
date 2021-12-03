#include "cfir/ReuseAnalysis.h"

#include "cfir/Nodes.h"
#include "cfir/Visitor.h"

#include <algorithm>
#include <memory>

namespace CFIR {

struct VariableCounter : public Visitor {
    size_t n_variables = 0;

    void visit(const Node *node) override {
        const size_t current = n_variables;
        size_t maximum = 0;
        for (const auto &child : node->children) {
            n_variables = current;
            child->accept(this);
            maximum = std::max(maximum, n_variables);
        }
        n_variables = current + maximum;
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
    size_t variable_count = 0;
    VarScope map;

    IdPtr update_id(const IdPtr id) {
        return substitute(id, map);
    }

    const std::string make_id() {
        const std::string name = "r" + std::to_string(variable_count++);
        return name;
    }

    template<typename T>
    void recurse_on_children(const T *node, const T *n, const size_t current) {
        for (const auto &child : node->children) {
            variable_count = current;
            n->children.push_back(child->mutate(this));
        }
    }

    template<typename T>
    NodePtr visit_type_check(const T *node) {
        const size_t current = variable_count;
        NodePtr n = nullptr;

        {
            // TODO: is there a cleaner way than this?
            // Should include type as part of Identifier.
            const std::string new_id = make_id();
            const std::string typed_id = "((" + T::type_name + "*)" + new_id + ")";
            const std::shared_ptr<Name> as_name = std::dynamic_pointer_cast<Name>(node->typed_id);
            assert(as_name);
            // In the map, give this value a type.
            map[as_name->name] = make_name(typed_id);
            const IdPtr id = make_name(new_id, true);
            const IdPtr current_id = update_id(node->current_id);
            n = std::make_shared<T>(current_id, id);

            recurse_on_children(node, n, current + 1);
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

    // TODO: ConstantInt, Equality, Return, IsConstant, Predicate
};

size_t get_max_types_needed(std::shared_ptr<Node> &root) {
    VariableCounter counter;
    root->accept(&counter);
    return counter.n_variables;
}

ReuseResult do_reuse_analysis(std::shared_ptr<Node> &root) {
    size_t n_declarations = get_max_types_needed(root);
    std::cerr << "Deepest depth: " << n_declarations << "\n";
    assert(false);
    return {root, n_declarations};
}

}  // namespace CFIR
