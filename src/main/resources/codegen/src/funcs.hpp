#pragma once

#include <algorithm>
#include <cstdlib>
#include <limits>
#include <sstream>
#include <regex>

#include "globals.h"
#include "Term.hpp"
#include "smt.hpp"

namespace flg {

namespace funcs {

using namespace std;

template<size_t N>
term_ptr __access(term_ptr t1) {
    return t1->as_complex().val[N];
}

term_ptr beq(term_ptr t1, term_ptr t2) {
    return Term::make<bool>(t1 == t2);
}

term_ptr bneq(term_ptr t1, term_ptr t2) {
    return Term::make<bool>(t1 != t2);
}

term_ptr bnot(term_ptr t1) {
    return Term::make<bool>(!t1->as_base<bool>().val);
}

template<typename T>
term_ptr __add(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val + t2->as_base<T>().val);
}

template<typename T>
term_ptr __sub(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val - t2->as_base<T>().val);
}

template<typename T>
term_ptr __mul(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val * t2->as_base<T>().val);
}

template<typename T>
term_ptr __div(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val / t2->as_base<T>().val);
}

template<typename T>
term_ptr __rem(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val % t2->as_base<T>().val);
}

template<typename T>
term_ptr __bitwise_and(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val & t2->as_base<T>().val);
}

template<typename T>
term_ptr __bitwise_or(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val | t2->as_base<T>().val);
}

template<typename T>
term_ptr __bitwise_xor(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val ^ t2->as_base<T>().val);
}

template<typename T>
term_ptr __neg(term_ptr t1) {
    return Term::make(-t1->as_base<T>().val);
}

template<typename T>
term_ptr __eq(term_ptr t1, term_ptr t2) {
    return Term::make<bool>(t1->as_base<T>().val == t2->as_base<T>().val);
}

template<typename T>
term_ptr __lt(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val < t2->as_base<T>().val);
}

template<typename T>
term_ptr __le(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val <= t2->as_base<T>().val);
}

template<typename T>
term_ptr __gt(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val > t2->as_base<T>().val);
}

template<typename T>
term_ptr __ge(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<T>().val >= t2->as_base<T>().val);
}

template<typename T>
term_ptr __cmp(term_ptr t1, term_ptr t2) {
#ifdef FLG_DEV
    return nullptr;
#else
    auto xval = t1->as_base<T>().val;
    auto yval = t2->as_base<T>().val;
    if (xval < yval) {
      return Term::make<Symbol::cmp_lt>();
    } else if (xval > yval) {
      return Term::make<Symbol::cmp_gt>();
    } else {
      return Term::make<Symbol::cmp_eq>();
    }
#endif
}

term_ptr print(term_ptr t1) {
    cout << *t1 << endl;
    return Term::make<bool>(true);
}

term_ptr string_concat(term_ptr t1, term_ptr t2) {
    return Term::make(t1->as_base<string>().val + t2->as_base<string>().val);
}

term_ptr string_matches(term_ptr t1, term_ptr t2) {
    regex re(t2->as_base<string>().val);
    return Term::make<bool>(regex_match(t1->as_base<string>().val, re));
}

term_ptr string_starts_with(term_ptr t1, term_ptr t2) {
    auto str = t1->as_base<string>().val;
    auto pre = t2->as_base<string>().val;
    if (pre.size() > str.size()) {
        return Term::make<bool>(false);
    }
    auto res = mismatch(pre.begin(), pre.end(), str.begin());
    return Term::make<bool>(res.first == pre.end());
}

term_ptr _make_some(term_ptr t) {
#ifdef FLG_DEV
    return nullptr;
#else
    return Term::make<Symbol::some>(t);
#endif
}

term_ptr _make_none() {
#ifdef FLG_DEV
    return nullptr;
#else
    return Term::make<Symbol::none>();
#endif
}

term_ptr char_at(term_ptr s, term_ptr i) {
    auto str = s->as_base<string>().val;
    auto pos = i->as_base<int32_t>().val;
    if (pos < 0 || (size_t) pos >= str.size()) {
        return _make_none();
    }
    return _make_some(Term::make<int32_t>(str[pos]));
}

term_ptr string_length(term_ptr s) {
    return Term::make<int32_t>(s->as_base<string>().val.size());
}

term_ptr vec_to_term_list(const std::vector<term_ptr> &v) {
#ifdef FLG_DEV
    return nullptr;
#else
    term_ptr acc = Term::make<Symbol::nil>();
    for (auto it = v.rbegin(); it != v.rend(); ++it) {
        acc = Term::make<Symbol::cons>(*it, acc);
    }
    return acc;
#endif
}

term_ptr string_to_list(term_ptr s) {
    vector<term_ptr> v;
    auto str = s->as_base<string>().val;
    for (char ch: str) {
        v.push_back(Term::make<int32_t>(ch));
    }
    return vec_to_term_list(v);
}

term_ptr list_to_string(term_ptr l) {
    vector<term_ptr> v = Term::vectorize_list_term(l);
    string str;
    for (auto sub: v) {
        str += (char) sub->as_base<int32_t>().val;
    }
    return Term::make(str);
}

term_ptr substring(term_ptr str_term, term_ptr start_term, term_ptr len_term) {
    auto str = str_term->as_base<string>().val;
    auto start = start_term->as_base<int32_t>().val;
    auto len = len_term->as_base<int32_t>().val;
    if (start < 0 || len < 0 || str.size() < start + (size_t) len) {
        return _make_none();
    }
    return _make_some(Term::make(str.substr(start, len)));
}

term_ptr string_to_i32(term_ptr str_term) {
    auto str = str_term->as_base<string>().val;
    static regex dec("[+-]?\\d+");
    static regex hex("0x[0-9a-fA-F]+");
    try {
        if (regex_match(str, dec)) {
            long r = stol(str);
            if (r >= INT32_MIN && r <= INT32_MAX) {
                return _make_some(Term::make((int32_t) r));
            }
        } else if (regex_match(str, hex)) {
            unsigned long r = stoul(str, nullptr, 16);
            if (r <= UINT32_MAX) {
                return _make_some(Term::make((int32_t) r));
            }
        }
    } catch (out_of_range &_) {
        // fall through
    }
    return _make_none();
}

term_ptr string_to_i64(term_ptr str_term) {
    auto str = str_term->as_base<string>().val;
    static regex dec("[+-]?\\d+");
    static regex hex("0x[0-9a-fA-F]+");
    try {
        if (regex_match(str, dec)) {
            long long r = stoll(str);
            if (r >= INT64_MIN && r <= INT64_MAX) {
                return _make_some(Term::make((int64_t) r));
            }
        } else if (regex_match(str, hex)) {
            unsigned long long r = stoull(str, nullptr, 16);
            if (r <= UINT64_MAX) {
                return _make_some(Term::make((int64_t) r));
            }
        }
    } catch (out_of_range &_) {
        // fall through
    }
    return _make_none();
}

term_ptr to_string(term_ptr t1) {
    if (t1->sym == Symbol::boxed_string) {
        return t1;
    }
    stringstream ss;
    ss << *t1;
    return Term::make(ss.str());
}

template<typename S, typename T>
term_ptr __conv(term_ptr t1) {
    return Term::make<T>(t1->as_base<S>().val);
}

term_ptr is_sat(term_ptr t1) {
    switch (smt_shim.check({t1})) {
        case SmtStatus::sat:
            return Term::make<bool>(true);
        case SmtStatus::unsat:
            return Term::make<bool>(false);
        case SmtStatus::unknown:
            throw runtime_error("SMT returned `unknown`");
    }
    __builtin_unreachable();
}

term_ptr _make_smt_not(term_ptr t) {
#ifdef FLG_DEV
    return nullptr;
#else
    return Term::make<Symbol::smt_not>(t);
#endif
}

term_ptr is_valid(term_ptr t1) {
    switch (smt_shim.check({_make_smt_not(t1)})) {
        case SmtStatus::sat:
            return Term::make<bool>(false);
        case SmtStatus::unsat:
            return Term::make<bool>(true);
        case SmtStatus::unknown:
            abort();
    }
    __builtin_unreachable();
}

int _extract_timeout_from_option(term_ptr o) {
    int timeout{numeric_limits<int>::max()};
#ifndef FLG_DEV
    if (o->sym == Symbol::some) {
        auto &x = o->as_complex();
        timeout = x.val[0]->as_base<int32_t>().val;
    }
#endif
    return timeout;
}

term_ptr is_sat_opt(term_ptr t1, term_ptr t2) {
    int timeout = _extract_timeout_from_option(t2);
    auto assertions = Term::vectorize_list_term(t1);
    switch (smt_shim.check(assertions, timeout)) {
        case SmtStatus::sat:
            return _make_some(Term::make<bool>(true));
        case SmtStatus::unsat:
            return _make_some(Term::make<bool>(false));
        case SmtStatus::unknown:
            return _make_none();
    }
    __builtin_unreachable();
}

std::vector<souffle::RamDomain> make_int_key(std::vector<term_ptr> key) {
    unsigned arity = key.size();
    std::vector<souffle::RamDomain> intKey(arity);
    for (unsigned i = 0; i < arity; ++i) {
        if (key[i]) {
            intKey[i] = key[i]->intize();
        }
    }
    return intKey;
}

term_ptr _relation_contains(const std::string &relname, const std::vector<term_ptr> &key) {
    auto rel = globals::program->getRelation(relname);
    assert(rel);
    size_t arity = rel->getPrimaryArity();
    assert(arity == key.size());
    std::vector<souffle::RamDomain> intKey = make_int_key(key);
    for (auto &tup: *rel) {
        bool match = true;
        for (unsigned i = 0; i < arity; ++i) {
            match &= !key[i] || intKey[i] == tup[i];
        }
        if (match) {
            return Term::make(true);
        }
    }
    return Term::make(false);
}

term_ptr _relation_agg_mono(const std::string &relname, const std::vector<term_ptr> &key, unsigned pos) {
    auto rel = globals::program->getRelation(relname);
    assert(rel);
    size_t arity = rel->getPrimaryArity();
    assert(arity == key.size());
    assert(pos < arity);
    std::vector<souffle::RamDomain> intKey = make_int_key(key);
    std::vector<term_ptr> v;
    for (auto &tup: *rel) {
        bool match = true;
        for (unsigned i = 0; i < arity; ++i) {
            match &= !key[i] || intKey[i] == tup[i];
        }
        if (match) {
            v.push_back(Term::unintize(tup[pos]));
        }
    }
    return vec_to_term_list(v);
}

template<Symbol S>
term_ptr
_relation_agg_poly(const std::string &relname, const std::vector<term_ptr> &key, const std::vector<bool> &projection) {
    auto rel = globals::program->getRelation(relname);
    assert(rel);
    size_t arity = rel->getPrimaryArity();
    assert(arity == key.size());
    assert(projection.size() == arity);
    std::vector<souffle::RamDomain> intKey = make_int_key(key);
    std::vector<term_ptr> v;
    for (auto &tup: *rel) {
        bool match = true;
        for (unsigned i = 0; i < arity; ++i) {
            match &= !key[i] || intKey[i] == tup[i];
        }
        if (match) {
            std::vector<term_ptr> args;
            for (unsigned i = 0; i < arity; ++i) {
                if (projection[i]) {
                    args.push_back(Term::unintize(tup[i]));
                }
            }
            v.push_back(Term::make_generic(S, args));
        }
    }
    return vec_to_term_list(v);
}
/* INSERT 0 */

} // namespace funcs
/* INSERT 1 */

} // namespace flg
