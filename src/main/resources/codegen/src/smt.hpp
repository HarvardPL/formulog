#pragma once

#include <limits>
#include <vector>
#include <unordered_set>

#include <boost/container_hash/hash.hpp>
#include <boost/multi_index_container.hpp>
#include <boost/multi_index/hashed_index.hpp>
#include <boost/multi_index/sequenced_index.hpp>

#include "Term.hpp"

namespace flg {

using namespace std;

namespace smt {

enum class SmtStatus {
    sat, unsat, unknown
};

struct SmtWorker;

using linked_term_set =
boost::multi_index_container<term_ptr,
        boost::multi_index::indexed_by<
                boost::multi_index::sequenced<>,
                boost::multi_index::hashed_unique<boost::multi_index::identity<term_ptr>>
        >
>;

struct SmtShim {
    SmtShim();

    SmtStatus check(const vector<term_ptr> &assertions,
                    int timeout = numeric_limits<int>::max());

    static bool needs_type_annotation(Symbol sym);

    static bool is_solver_var(Term *t);

private:
    SmtWorker *worker;

    static void break_into_conjuncts(term_ptr t, linked_term_set &acc, bool negated = false);

    static inline tbb::concurrent_unordered_map<set<term_ptr>, SmtStatus, boost::hash<set<term_ptr>>> s_memo;
};

inline thread_local SmtShim smt_shim;

} // namespace smt

using smt::SmtStatus;
using smt::smt_shim;

} // namespace flg
