#pragma once

#include <iostream>
#include <map>
#include <memory>
#include <string>

// TODO: we will eventually need to track types for printing.

struct Identifier;
typedef std::shared_ptr<Identifier> IdPtr;

struct Identifier {
    virtual void print(std::ostream &stream) const = 0;
    virtual bool equals(const IdPtr &other_id) const = 0;

    Identifier(bool declared) : pre_declared(declared) {}
    const bool pre_declared;
};

// TODO: might not want these to be constants.
struct Name : public Identifier {
    Name(const std::string &_name, bool declared) : Identifier(declared), name(_name) {}
    void print(std::ostream &stream) const override;
    bool equals(const IdPtr &other_id) const override;

    const std::string name;
};

struct PtrAccess : public Identifier {
    // Pointer accesses are always pre-declared.
    PtrAccess(const IdPtr _id, const std::string &_member)
      : Identifier(true), id(_id), member(_member) {}
    void print(std::ostream &stream) const override;
    bool equals(const IdPtr &other_id) const override;

    const IdPtr id;
    const std::string member;
};

typedef std::map<std::string, IdPtr> VarScope;

IdPtr make_name(const std::string &name, bool declared = false);
IdPtr make_id_ptr(const IdPtr &id, const std::string &member);
const IdPtr substitute(const IdPtr id, const VarScope &scope);
