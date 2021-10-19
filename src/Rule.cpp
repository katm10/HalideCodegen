#include "Rule.h"

void Rule::add_type(bool allowed, uint16_t type)
{
    if (!allowed)
    {
        types &= ~type;
    }
    else
    {
        types |= type;
    }
}

void Rule::set_types(uint16_t _types)
{
    types = _types;
}

uint16_t Rule::get_types()
{
    return types;
}
