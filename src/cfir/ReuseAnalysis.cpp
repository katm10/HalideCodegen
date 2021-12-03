#include "cfir/ReuseAnalysis.h"

#include "cfir/Nodes.h"
#include "cfir/Visitor.h"
#include <algorithm>

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
