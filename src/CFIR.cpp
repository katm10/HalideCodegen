#include "CFIR.h"

#include "ASTPrinter.h"
#include <string>
#include <iostream>
#include <cassert>

using std::make_shared;
using std::shared_ptr;
using std::vector;

namespace CFIR {

bool ConstantInt::equal(const shared_ptr<Node> &other) const {
    if (const ConstantInt *other_ci = other->as<ConstantInt>(IRType::ConstantInt)) {
        return (value == other_ci->value) && id->equals(other_ci->id);
    } else {
        return false;
    }
}

void ConstantInt::print(std::ostream &stream, const std::string &indent) const {
    stream << indent << "if (is_const_int(";
    id->print(stream);
    stream << ", " << value << ")) {\n";
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
    stream << indent << "}\n";
}

bool Equality::equal(const shared_ptr<Node> &other) const {
    if (const Equality *other_equal = other->as<Equality>(IRType::Equality)) {
        return expr0->equals(other_equal->expr0) && expr1->equals(other_equal->expr1);
    } else {
        return false;
    }
}

void Equality::print(std::ostream &stream, const std::string &indent) const {
    stream << indent << "if (equal(";
    expr0->print(stream);
    stream << ", ";
    expr1->print(stream);
    stream << ")) {\n";
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
    stream << indent << "}\n";
}

bool Return::equal(const shared_ptr<Node> &other) const {
    if (const Return *other_return = other->as<Return>(IRType::Return)) {
        return ret_expr->equals(other_return->ret_expr);
    } else {
        return false;
    }
}

void Return::print(std::ostream &stream, const std::string &indent) const {
    assert(children.empty());  // Return nodes should never have children.
    stream << indent << "return " << pretty_print(ret_expr) << ";\n";
}

bool Condition::equal(const shared_ptr<Node> &other) const {
    if (const Condition *other_c = other->as<Condition>(IRType::Condition)) {
        return condition == other_c->condition;
    } else {
        return false;
    }
}

void Condition::print(std::ostream &stream, const std::string &indent) const {
    stream << indent << "if (" << condition << ") {\n";
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
    stream << indent << "}\n";
}

bool IsConstant::equal(const shared_ptr<Node> &other) const {
    if (const IsConstant *other_c = other->as<IsConstant>(IRType::IsConstant)) {
        return id->equals(other_c->id);
    } else {
        return false;
    }
}

void IsConstant::print(std::ostream &stream, const std::string &indent) const {
    // TODO: change this to is_const, I am using is_const_v for testing purposes
    stream << indent << "if (is_const_v(";
    id->print(stream);
    stream << ")) {\n";
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
    stream << indent << "}\n";
}

bool Predicate::equal(const shared_ptr<Node> &other) const {
    if (const Predicate *other_pred = other->as<Predicate>(IRType::Predicate)) {
        return pred_expr->equals(other_pred->pred_expr);
    } else {
        return false;
    }
}

void Predicate::print(std::ostream &stream, const std::string &indent) const {
    stream << indent << "if (evaluate_predicate(fold(";
    stream << pretty_print(pred_expr);
    stream << "))) {\n";
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
    stream << indent << "}\n";
}

bool Sequence::equal(const shared_ptr<Node> &other) const {
    assert(false);  // Should never be compared to other nodes.
}

void Sequence::print(std::ostream &stream, const std::string &indent) const {
    for (const auto &child : children) {
        child->print(stream, indent + "  ");
    }
}
}  // namespace CFIR