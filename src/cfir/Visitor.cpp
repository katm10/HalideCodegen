#include "cfir/Visitor.h"
#include "cfir/Nodes.h"

namespace CFIR {

void Visitor::visit(const Node *node) {
    for (const auto &child : node->children) {
        child->accept(this);
    }
}

void Visitor::visit(const Add *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Sub *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Mod *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Mul *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Div *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Min *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Max *node) {
    visit((const Node *)node);
}

void Visitor::visit(const EQ *node) {
    visit((const Node *)node);
}

void Visitor::visit(const NE *node) {
    visit((const Node *)node);
}

void Visitor::visit(const LT *node) {
    visit((const Node *)node);
}

void Visitor::visit(const LE *node) {
    visit((const Node *)node);
}

void Visitor::visit(const GT *node) {
    visit((const Node *)node);
}

void Visitor::visit(const GE *node) {
    visit((const Node *)node);
}

void Visitor::visit(const And *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Or *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Not *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Select *node) {
    visit((const Node *)node);
}

void Visitor::visit(const ConstantInt *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Broadcast *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Ramp *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Fold *node) {
    visit((const Node *)node);
}

void Visitor::visit(const CanProve *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Equality *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Return *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Condition *node) {
    visit((const Node *)node);
}

void Visitor::visit(const IsConstant *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Predicate *node) {
    visit((const Node *)node);
}

void Visitor::visit(const Sequence *node) {
    visit((const Node *)node);
}

}  // namsepace CFIR
