//
// Created by Aaron Bembenek on 8/9/22.
//

#ifndef CODEGEN_SMT_SOLVER_H
#define CODEGEN_SMT_SOLVER_H

#include "smt_shim.h"

#include <boost/container_hash/hash.hpp>
#include <boost/multi_index_container.hpp>
#include <boost/multi_index/hashed_index.hpp>
#include <boost/multi_index/sequenced_index.hpp>

namespace flg::smt {

class SmtSolver {
public:
    NO_COPY_OR_ASSIGN(SmtSolver);

    SmtSolver() = default;

    virtual SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) = 0;

    virtual ~SmtSolver() = default;
};

class TopLevelSmtSolver : public SmtSolver {
public:
    NO_COPY_OR_ASSIGN(TopLevelSmtSolver);

    TopLevelSmtSolver();

    SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) override;

    SmtResult check(term_ptr assertion) {
        return check({assertion}, false, std::numeric_limits<int>::max());
    }

private:
    std::unique_ptr<SmtSolver> m_delegate;
};

class MemoizingSmtSolver : public SmtSolver {
public:
    NO_COPY_OR_ASSIGN(MemoizingSmtSolver);

    explicit MemoizingSmtSolver(std::unique_ptr<SmtSolver> &&delegate);

    SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) override;

private:
    std::unique_ptr<SmtSolver> m_delegate;

    using sequenced_term_set =
    boost::multi_index_container<term_ptr,
            boost::multi_index::indexed_by<
                    boost::multi_index::sequenced<>,
                    boost::multi_index::hashed_unique<boost::multi_index::identity<term_ptr>>
            >
    >;

    static void break_into_conjuncts(term_ptr t, sequenced_term_set &acc, bool negated = false);

    static inline tbb::concurrent_unordered_map<std::vector<term_ptr>, SmtResult, boost::hash<std::vector<term_ptr>>> s_memo;
};

class AbstractSmtSolver : public SmtSolver {
public:
    NO_COPY_OR_ASSIGN(AbstractSmtSolver);

    explicit AbstractSmtSolver(std::unique_ptr<SmtShim> &&shim) : m_shim{std::move(shim)} {}

    using term_vector_pair = std::pair<std::vector<term_ptr>, std::vector<term_ptr>>;

    SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) override;

protected:
    virtual void initialize() = 0;

    virtual term_vector_pair make_assertions(const std::vector<term_ptr> &assertions) = 0;

    virtual void cleanup() = 0;

    std::unique_ptr<SmtShim> m_shim;

private:
    bool m_initialized{false};
};

class PushPopNaiveSolver : public AbstractSmtSolver {
public:
    NO_COPY_OR_ASSIGN(PushPopNaiveSolver);

    explicit PushPopNaiveSolver(std::unique_ptr<SmtShim> &&shim) : AbstractSmtSolver{std::move(shim)} {}

private:
    void initialize() override;

    term_vector_pair make_assertions(const std::vector<term_ptr> &assertions) override;

    void cleanup() override;
};

inline thread_local TopLevelSmtSolver smt_solver;

}

#endif //CODEGEN_SMT_SOLVER_H
