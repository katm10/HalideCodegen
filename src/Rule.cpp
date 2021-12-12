#include "Rule.h"

// TODO: helper, might want to move to different file
uint8_t get_setbits(uint16_t n)
{
    uint8_t r = n & 1;
    while (n >>= 1)
        r += (n & 1);
    return r;
}

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

std::string Rule::generate_condition(std::string expr_name) const
{
    std::string condition = "";
    uint8_t setbits = get_setbits(types);
    if (setbits < 8)
    {
        // Most likely set the allowed types ie. float
        // Collect allowed types into a giant OR condition
        for (const auto typePair : typeStrings)
        {
            if (types & (uint16_t)typePair.second)
            {
                condition += expr_name + "->is_" + typePair.first + "()";
                if (setbits > 1)
                {
                    condition += " || ";
                }
                --setbits;
            }
        }
    }
    else
    {
        // Most likely set the disallowed types ie. !(float)
        // Collect disallowed types into a giant OR condition
        setbits = 16 - setbits;
        condition += "!(";
        for (const auto typePair : typeStrings)
        {
            if (!(types & (uint16_t)typePair.second))
            {
                condition += expr_name + "->is_" + typePair.first + "()";
                if (setbits > 1)
                {
                    condition += " || ";
                }
                --setbits;
            }
        }
        condition += ")";
    }
    return condition;
}
