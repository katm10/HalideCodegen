#include "cfir/SwitchOnType.h"

#include "cfir/Nodes.h"
#include "cfir/Visitor.h"

#include "ast/Substitute.h"

#include <algorithm>
#include <memory>
#include <deque>

namespace CFIR {

struct IfTypeReplacer : public Mutator {

    /*
        Example: 
        if ((r0 = a.as<Ramp>())) {
            ...
        }
        if ((r0 = a.as<Broadcast>())) {
            ...
        }

        becomes

        switch (a.node_type())
        {
        case IRNodeType::Ramp:
            r0 = a.as<Ramp>();
            ...
            break;
        case IRNodeType::Broadcast:
            r0 = a.as<Broadcast>();
            ...
            break;
        default:
            break;
        }
    */
    std::deque<std::shared_ptr<TypeSwitch>> type_switches;

/*

visit()
for each child:
    - mutate it
    - if typecheck
        - create typeswitch and add to it
    - else 
        - push onto current children

*/

    template<typename T>
    void recurse_on_children(const T *node, std::shared_ptr<T> n) {
        size_t i = 0;
        while (i < node->children.size()){
            NodePtr mutated_child = node->children[i]->mutate(this);

            if (mutated_child != nullptr){
                n->children.push_back(mutated_child);
            }  
            i++;
        }

        if (type_switches.back()->children.size() > 0){
            n->children.push_back(type_switches.back());
        }
    }

    template<typename T>
    NodePtr visit_general(const T *node) {
        type_switches.push_back(std::make_shared<TypeSwitch>());
        std::shared_ptr<T> ptr = std::make_shared<T>(node);
        recurse_on_children<T>(node, ptr);
        type_switches.pop_back();

        return ptr;
    }

    template<typename T>
    NodePtr visit_type_check(const T *node) {
        visit_general(node);

        // Add this TypeCheck to the last TypeSwitch in type_switches
        if (type_switches.back()->current_id == nullptr){
            type_switches.back()->current_id = node->current_id;
            type_switches.back()->typed_id = node->typed_id;
        } else {
            // assert(type_switches.back()->current_id->equals(node->current_id));
            // assert(type_switches.back()->typed_id->equals(node->typed_id));
        }

        type_switches.back()->children.push_back(std::make_shared<T>(node));
        type_switches.back()->children.back()->print(std::cout, "");
        type_switches.back()->types.push_back(T::type_name);

        return nullptr;
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
        return visit_general(node);
    }

    NodePtr visit(const Sequence *node) override {        
        return visit_general(node);
    }

    NodePtr visit(const Equality *node) override {        
        return visit_general(node);
    }

    NodePtr visit(const Return *node) override {
        return visit_general(node);
    }

    NodePtr visit(const IsConstant *node) override {
        return visit_general(node);
    }

    NodePtr visit(const Predicate *node) override {
        return visit_general(node);
    }

    NodePtr visit(const TypeSwitch *node) override {
        return visit_general(node);    
    }
};

NodePtr switch_on_type(const std::shared_ptr<Node> &root) {
    IfTypeReplacer replacer;
    std::shared_ptr<Node> update = root->mutate(&replacer);
    return update;
}

}  // namespace CFIR
