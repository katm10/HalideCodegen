#include "Identifier.h"

#include <memory>
#include <cassert>

void Name::print(std::ostream &stream) const {
    stream << name;
}

bool Name::equals(const IdPtr &other_id) const {
    const std::shared_ptr<Name> as_name = std::dynamic_pointer_cast<Name>(other_id);
    return (as_name != nullptr) && (as_name->name == name);
}

void PtrAccess::print(std::ostream &stream) const {
    id->print(stream);
    stream << "->" << member;
}

bool PtrAccess::equals(const IdPtr &other_id) const {
    const std::shared_ptr<PtrAccess> as_ptr = std::dynamic_pointer_cast<PtrAccess>(other_id);
    return (as_ptr != nullptr) && (as_ptr->member == member) && (id->equals(as_ptr->id));
}

IdPtr make_name(const std::string &name, bool declared) {
    return std::make_shared<Name>(name, declared);
}

IdPtr make_id_ptr(const IdPtr &id, const std::string &member) {
    return std::make_shared<PtrAccess>(id, member);
}

const IdPtr substitute(const IdPtr id, const VarScope &scope) {
    const std::shared_ptr<Name> as_name = std::dynamic_pointer_cast<Name>(id);
    if (as_name) {
        auto replacement = scope.find(as_name->name);
        if (replacement != scope.end()) {
            return replacement->second;
        }
        return id;
    } else {
        const std::shared_ptr<PtrAccess> as_ptr = std::dynamic_pointer_cast<PtrAccess>(id);
        assert(as_ptr);
        return make_id_ptr(substitute(as_ptr->id, scope), as_ptr->member);
    }
}