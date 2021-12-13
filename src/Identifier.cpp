#include "Identifier.h"

namespace CFIR {

void Name::print(std::ostream &stream) const {
    stream << name;
}

bool Name::equals(const std::shared_ptr<Identifier> &other_id) const {
    const std::shared_ptr<Name> as_name = std::dynamic_pointer_cast<Name>(other_id);
    return (as_name != nullptr) && (as_name->name == name);
}

void PtrAccess::print(std::ostream &stream) const {
    id->print(stream);
    stream << "->" << member;
}

bool PtrAccess::equals(const std::shared_ptr<Identifier> &other_id) const {
    const std::shared_ptr<PtrAccess> as_ptr = std::dynamic_pointer_cast<PtrAccess>(other_id);
    return (as_ptr != nullptr) && (as_ptr->member == member) && (id->equals(as_ptr->id));
}

}  // namespace CFIR

IdPtr make_name(const std::string &name) {
    return std::make_shared<CFIR::Name>(name);
}

IdPtr make_id_ptr(const IdPtr &id, const std::string &member) {
    return std::make_shared<CFIR::PtrAccess>(id, member);
}
