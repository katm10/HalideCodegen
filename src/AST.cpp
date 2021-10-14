#include "AST.h"
#include "Visitor.h"

namespace AST {

void ConstantInt::accept(Visitor *v) const {
    v->visit(this);
}

template<typename T>
void VariableBase<T>::accept(Visitor *v) const {
    const T* t = this->as<T>();
    if (!t) {
        std::cerr << "VariableBase failed to cast to expected class\n";
        assert(false);
        exit(1);
    } else {
        v->visit(t);
    }
}

template<typename T>
void BinaryOp<T>::accept(Visitor *v) const {
    const T* t = this->as<T>();
    if (!t) {
        std::cerr << "BinaryOp failed to cast to expected class\n";
        assert(false);
        exit(1);
    } else {
        v->visit(t);
    }
}

template<typename T>
void UnaryOp<T>::accept(Visitor *v) const {
    const T* t = this->as<T>();
    if (!t) {
        std::cerr << "UnaryOp failed to cast to expected class\n";
        assert(false);
        exit(1);
    } else {
        v->visit(t);
    }
}

void Select::accept(Visitor *v) const {
    v->visit(this);
}

void Ramp::accept(Visitor *v) const {
    v->visit(this);
}

void Broadcast::accept(Visitor *v) const {
    v->visit(this);
}

}  // namsepace AST
