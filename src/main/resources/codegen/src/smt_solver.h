//
// Created by Aaron Bembenek on 8/9/22.
//

#ifndef CODEGEN_SMT_SOLVER_H
#define CODEGEN_SMT_SOLVER_H

#include "smt_shim.h"

#include <future>
#include <boost/container_hash/hash.hpp>
#include <boost/program_options.hpp>

namespace flg::smt {

enum class SmtSolverMode {
    naive, push_pop, check_sat_assuming
};

struct SmtResult {
    SmtStatus status;
    std::optional<Model> model;
};

class SmtSolver {
public:
    NO_COPY_OR_ASSIGN(SmtSolver);

    SmtSolver() = default;

    virtual SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int32_t timeout) = 0;

    virtual ~SmtSolver() = default;
};

class TopLevelSmtSolver : public SmtSolver {
public:
    NO_COPY_OR_ASSIGN(TopLevelSmtSolver);

    TopLevelSmtSolver();

    SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int32_t timeout) override;

    SmtResult check(term_ptr assertion);

private:
    std::unique_ptr<SmtSolver> m_delegate;

    static std::unique_ptr<SmtShim> make_shim();
};

class MemoizingSmtSolver : public SmtSolver {
public:
    NO_COPY_OR_ASSIGN(MemoizingSmtSolver);

    explicit MemoizingSmtSolver(std::unique_ptr<SmtSolver> &&delegate);

    SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int32_t timeout) override;

private:
    std::unique_ptr<SmtSolver> m_delegate;

    typedef std::tuple<std::set<term_ptr>, bool, int32_t> memo_key_t;
    static inline tbb::concurrent_unordered_map<memo_key_t, std::shared_future<SmtResult>, boost::hash<memo_key_t>> s_memo;
};

class AbstractSmtSolver : public SmtSolver {
public:
    NO_COPY_OR_ASSIGN(AbstractSmtSolver);

    explicit AbstractSmtSolver(std::unique_ptr<SmtShim> &&shim) : m_shim{std::move(shim)} {}

    using term_vector_pair = std::pair<std::vector<term_ptr>, std::vector<term_ptr>>;

    SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int32_t timeout) override;

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

class CheckSatAssumingSolver : public AbstractSmtSolver {
public:
    NO_COPY_OR_ASSIGN(CheckSatAssumingSolver);

    explicit CheckSatAssumingSolver(std::unique_ptr<SmtShim> &&shim) : AbstractSmtSolver{std::move(shim)} {}

private:
    std::unordered_map<term_ptr, term_ptr> m_conjuncts_to_vars;

    void initialize() override;

    term_vector_pair make_assertions(const std::vector<term_ptr> &assertions) override;

    void cleanup() override;
};

class PushPopSolver : public AbstractSmtSolver {
public:
    NO_COPY_OR_ASSIGN(PushPopSolver);

    explicit PushPopSolver(std::unique_ptr<SmtShim> &&shim) : AbstractSmtSolver{std::move(shim)} {}

private:
    std::vector<term_ptr> m_stack;
    std::unordered_set<term_ptr> m_set;

    void initialize() override;

    term_vector_pair make_assertions(const std::vector<term_ptr> &assertions) override;

    void cleanup() override;

    unsigned int find_diff_pos(const std::vector<term_ptr> &assertions);

    void shrink_cache(unsigned int num_to_pop);
};

class DoubleCheckingSolver : public SmtSolver {
public:
    NO_COPY_OR_ASSIGN(DoubleCheckingSolver);

    DoubleCheckingSolver(std::unique_ptr<SmtSolver> &&first, std::unique_ptr<SmtSolver> &&second) : m_first(
            std::move(first)), m_second(std::move(second)) {}

    SmtResult check(const std::vector<term_ptr> &assertions, bool get_model, int32_t timeout) override;

private:
    std::unique_ptr<SmtSolver> m_first;
    std::unique_ptr<SmtSolver> m_second;
};

extern inline TopLevelSmtSolver smt_solver;
#if defined(_OPENMP)
#pragma omp threadprivate(smt_solver)
#endif
TopLevelSmtSolver smt_solver;

}

namespace std {

inline std::istream &operator>>(std::istream &in, flg::smt::SmtSolverMode &mode) {
    std::string token;
    in >> token;

    if (token == "naive") {
        mode = flg::smt::SmtSolverMode::naive;
    } else if (token == "push-pop") {
        mode = flg::smt::SmtSolverMode::push_pop;
    } else if (token == "check-sat-assuming") {
        mode = flg::smt::SmtSolverMode::check_sat_assuming;
    } else {
        throw boost::program_options::validation_error(
                boost::program_options::validation_error::kind_t::invalid_option_value);
    }

    return in;
}

inline std::ostream &operator<<(std::ostream &out, const flg::smt::SmtSolverMode &mode) {
    switch (mode) {
        case flg::smt::SmtSolverMode::naive:
            out << "naive";
            break;
        case flg::smt::SmtSolverMode::push_pop:
            out << "push-pop";
            break;
        case flg::smt::SmtSolverMode::check_sat_assuming:
            out << "check-sat-assuming";
            break;
    }
    return out;
}

}

#endif //CODEGEN_SMT_SOLVER_H
