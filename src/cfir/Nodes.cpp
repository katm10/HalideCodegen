#include "cfir/Nodes.h"

#include "ast/Printer.h"
#include "cfir/Visitor.h"
#include "cfir/Mutator.h"
#include <ios>
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
    /*
        is_const_v(string id, string ret_val, string ret_type)
        in generated code, will save evaluate Expr id and save its type to ret_type and its value to ret_val
    */

    // Declare the return value and type
    stream << indent << "halide_scalar_value_t ";
    value_id->print(stream);
    stream << ";\n";
    stream << indent << "halide_type_t ";
    type_id->print(stream);
    stream << ";\n";

    stream << indent << "if (is_const_v(";
    id->print(stream);
    stream << ", ";
    value_id->print(stream);
    stream << ", ";
    type_id->print(stream); // Should these be IdPtrs instead of strings?

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

bool Declaration::equal(const shared_ptr<Node> &other) const {
    assert(false);  // Should never be compared to other nodes.
}

void Declaration::print(std::ostream &stream, const std::string &indent) const {
    assert(children.size() == 0);
    for (size_t i = 0; i < n; i++) {
        stream << indent << "const BaseExprNode *" << prefix << i << " = nullptr;\n";
    }
}

void ConstantInt::accept(Visitor *v) const {
    v->visit(this);
}

void Equality::accept(Visitor *v) const {
    v->visit(this);
}

void Return::accept(Visitor *v) const {
    v->visit(this);
}

void Condition::accept(Visitor *v) const {
    v->visit(this);
}

void IsConstant::accept(Visitor *v) const {
    v->visit(this);
}

void Predicate::accept(Visitor *v) const {
    v->visit(this);
}

void Sequence::accept(Visitor *v) const {
    v->visit(this);
}

void Declaration::accept(Visitor *v) const {
    v->visit(this);
}

NodePtr ConstantInt::mutate(Mutator *m) const {
    return m->visit(this);
}

NodePtr Equality::mutate(Mutator *m) const {
    return m->visit(this);
}

NodePtr Return::mutate(Mutator *m) const {
    return m->visit(this);
}

NodePtr Condition::mutate(Mutator *m) const {
    return m->visit(this);
}

NodePtr IsConstant::mutate(Mutator *m) const {
    return m->visit(this);
}

NodePtr Predicate::mutate(Mutator *m) const {
    return m->visit(this);
}

NodePtr Sequence::mutate(Mutator *m) const {
    return m->visit(this);
}

NodePtr Declaration::mutate(Mutator *m) const {
    return m->visit(this);
}

}  // namespace CFIR
