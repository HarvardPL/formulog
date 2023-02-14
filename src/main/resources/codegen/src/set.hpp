//
// Created by Aaron Bembenek on 2/10/23.
//

#ifndef SMT_PARSER_CPP_SET_H
#define SMT_PARSER_CPP_SET_H

#include <boost/container/flat_set.hpp>
#include <optional>
#include <vector>

namespace flg {

struct Term;

typedef const flg::Term *term_ptr;
typedef boost::container::flat_set<term_ptr> Set;

namespace set {

Set empty();

Set singleton(term_ptr val);

Set plus(term_ptr val, const Set &set);

Set minus(term_ptr val, const Set &set);

Set plus_all(const Set &s1, const Set &s2);

Set minus_all(const Set &s1, const Set &s2);

bool member(term_ptr val, const Set &set);

std::size_t size(const Set &set);

bool subset(const Set &s1, const Set &s2);

std::optional<std::pair<term_ptr, Set>> choose(const Set &s);

Set from_vec(const std::vector<term_ptr> &vec);

}
}

#endif //SMT_PARSER_CPP_SET_H
