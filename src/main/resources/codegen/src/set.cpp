//
// Created by Aaron Bembenek on 2/10/23.
//

#include "set.hpp"

namespace flg::set {

Set empty() {
    return {};
}

Set singleton(term_ptr val) {
    return { val };
}

Set plus(term_ptr val, const Set &set) {
    Set r{set};
    r.emplace(val);
    return r;
}

Set minus(term_ptr val, const Set &set) {
    Set r{set};
    r.erase(val);
    return r;
}

Set plus_all(const Set &s1, const Set &s2) {
    Set r{s1};
    r.insert(boost::container::ordered_unique_range, s2.begin(), s2.end());
    return r;
}

Set minus_all(const Set &s1, const Set &s2) {
    Set r{s1};
    auto it = r.begin();
    for (auto elt : s2)
    {
        it = std::lower_bound(it, r.end(), elt);
        if (it == r.end()) {
            break;
        }
        if (*it != elt) {
            continue;
        }
        it = r.erase(it);
    }
    return r;
}

bool member(term_ptr val, const Set &set) {
    return set.contains(val);
}

std::size_t size(const Set &set) {
    return set.size();
}

bool subset(const Set &s1, const Set &s2) {
    auto it = s2.begin();
    for (auto elt : s1)
    {
        it = std::lower_bound(it, s2.end(), elt);
        if (it == s2.end() || *it != elt)
        {
            return false;
        }
    }
    return true;
}

std::optional<std::pair<term_ptr, Set>> choose(const Set &s) {
    if (s.empty()) {
        return {};
    }
    Set r{s};
    auto it = r.end();
    --it;
    auto t = *it;
    r.erase(it);
    return {{t, r}};
}

Set from_vec(const std::vector<term_ptr> &vec) {
    return {vec.begin(), vec.end()};
}

}