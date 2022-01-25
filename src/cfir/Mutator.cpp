#include "cfir/Mutator.h"
#include "cfir/Nodes.h"

#include <vector>

namespace CFIR {

template<typename T>
NodePtr make_new_node(Mutator *m, const T *node) {
    const size_t n = node->children.size();
    std::shared_ptr<T> new_T = std::make_shared<T>(node);

    for (const auto &child : node->children) {
        new_T->children.push_back(child->mutate(m));
    }

    return new_T;
}

NodePtr Mutator::visit(const Add *node) {
    return make_new_node<Add>(this, node);
}

NodePtr Mutator::visit(const Sub *node) {
    return make_new_node<Sub>(this, node);
}

NodePtr Mutator::visit(const Mod *node) {
    return make_new_node<Mod>(this, node);
}

NodePtr Mutator::visit(const Mul *node) {
    return make_new_node<Mul>(this, node);
}

NodePtr Mutator::visit(const Div *node) {
    return make_new_node<Div>(this, node);
}

NodePtr Mutator::visit(const Min *node) {
    return make_new_node<Min>(this, node);
}

NodePtr Mutator::visit(const Max *node) {
    return make_new_node<Max>(this, node);
}

NodePtr Mutator::visit(const EQ *node) {
    return make_new_node<EQ>(this, node);
}

NodePtr Mutator::visit(const NE *node) {
    return make_new_node<NE>(this, node);
}

NodePtr Mutator::visit(const LT *node) {
    return make_new_node<LT>(this, node);
}

NodePtr Mutator::visit(const LE *node) {
    return make_new_node<LE>(this, node);
}

NodePtr Mutator::visit(const GT *node) {
    return make_new_node<GT>(this, node);
}

NodePtr Mutator::visit(const GE *node) {
    return make_new_node<GE>(this, node);
}

NodePtr Mutator::visit(const And *node) {
    return make_new_node<And>(this, node);
}

NodePtr Mutator::visit(const Or *node) {
    return make_new_node<Or>(this, node);
}

NodePtr Mutator::visit(const Not *node) {
    return make_new_node<Not>(this, node);
}

NodePtr Mutator::visit(const Select *node) {
    return make_new_node<Select>(this, node);
}

NodePtr Mutator::visit(const ConstantInt *node) {
    return make_new_node<ConstantInt>(this, node);
}

NodePtr Mutator::visit(const Broadcast *node) {
    return make_new_node<Broadcast>(this, node);
}

NodePtr Mutator::visit(const Ramp *node) {
    return make_new_node<Ramp>(this, node);
}

NodePtr Mutator::visit(const Equality *node) {
    return make_new_node<Equality>(this, node);
}

NodePtr Mutator::visit(const Return *node) {
    return make_new_node<Return>(this, node);
}

NodePtr Mutator::visit(const Condition *node) {
    return make_new_node<Condition>(this, node);
}

NodePtr Mutator::visit(const IsConstant *node) {
    return make_new_node<IsConstant>(this, node);
}

NodePtr Mutator::visit(const Predicate *node) {
    return make_new_node<Predicate>(this, node);
}

NodePtr Mutator::visit(const Sequence *node) {
    return make_new_node<Sequence>(this, node);
}

NodePtr Mutator::visit(const Declaration *node) {
    return make_new_node<Declaration>(this, node);
}

NodePtr Mutator::visit(const TypeSwitch *node) {
    return make_new_node<TypeSwitch>(this, node);
}

}  // namsepace CFIR
