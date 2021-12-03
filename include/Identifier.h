#pragma once
#include <iostream>
#include <memory>
#include <string>

namespace CFIR {

// TODO: we will eventually need to track types for printing.

struct Identifier {
    virtual void print(std::ostream &stream) const = 0;
    virtual bool equals(const std::shared_ptr<Identifier> &other_id) const = 0;

    Identifier(bool declared) : pre_declared(declared) {}
    const bool pre_declared;
};

// TODO: might not want these to be constants.
struct Name : public Identifier {
    Name(const std::string &_name, bool declared = false) : Identifier(declared), name(_name) {}
    void print(std::ostream &stream) const override;
    bool equals(const std::shared_ptr<Identifier> &other_id) const override;

    const std::string name;
};

struct PtrAccess : public Identifier {
    // Pointer accesses are always pre-declared.
    PtrAccess(const std::shared_ptr<Identifier> _id, const std::string &_member)
      : Identifier(true), id(_id), member(_member) {}
    void print(std::ostream &stream) const override;
    bool equals(const std::shared_ptr<Identifier> &other_id) const override;

    const std::shared_ptr<Identifier> id;
    const std::string member;
};

}  // namespace CFIR

typedef std::shared_ptr<CFIR::Identifier> IdPtr;

IdPtr make_name(const std::string &name);
IdPtr make_id_ptr(const IdPtr &id, const std::string &member);
