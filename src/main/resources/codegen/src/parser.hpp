#pragma once

#include <iostream>
#include <stdexcept>
#include <sstream>
#include <string>

#include "Term.hpp"
#include "Tuple.hpp"

namespace flg {

namespace parser {

using namespace std;

// Exception class thrown when parsing facts
class parsing_error : public logic_error {
    using logic_error::logic_error;
};

term_ptr parse_term(const string &term);

inline void parse_facts(istream &in, souffle::Relation &rel) {
    // Parse each fact of the stream on a new line
    size_t arity = rel.getPrimaryArity();
    string line;
    while (getline(in, line)) {
        istringstream ss(line);
        souffle::tuple tup(&rel);
        // Tab-separated term format
        string term;
        size_t count = 0;
        while (getline(ss, term, '\t')) {
            if (count >= arity) {
                throw parsing_error("Too many terms in tab-separated line");
            }
            tup << parse_term(term)->intize();
            count++;
        }
        if (count != arity) {
            throw parsing_error("Too few terms in tab-separated line");
        }
        rel.insert(tup);
    }
}

} // namespace parser

using parser::parse_facts;

} // namespace flg
