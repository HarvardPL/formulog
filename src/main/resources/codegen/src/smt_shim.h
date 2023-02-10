//
// Created by Aaron Bembenek on 8/9/22.
//

#ifndef CODEGEN_SMT_SHIM_H
#define CODEGEN_SMT_SHIM_H

#include <unordered_set>
#include <boost/process.hpp>
#include "Term.hpp"
#include "Type.hpp"

namespace flg::smt {

enum class SmtStatus {
    sat, unsat, unknown
};

class SmtShim {
public:
    NO_COPY_OR_ASSIGN(SmtShim);

    SmtShim() = default;

    virtual void make_declarations() = 0;

    virtual void make_assertion(term_ptr assertion) = 0;

    virtual void push() = 0;

    virtual void pop(unsigned int n) = 0;

    void pop() { pop(1); }

    virtual SmtStatus
    check_sat_assuming(const std::vector<term_ptr> &onVars, const std::vector<term_ptr> &offVars, int timeout) = 0;

    virtual Model get_model() = 0;

    virtual ~SmtShim() = default;
};

class SmtLibShim : public SmtShim {
public:
    NO_COPY_OR_ASSIGN(SmtLibShim);

    SmtLibShim(boost::process::child &&proc, boost::process::opstream &&in, boost::process::ipstream &&out);

    void make_declarations() override;

    void make_assertion(term_ptr assertion) override;

    void push() override;

    void pop(unsigned int n) override;

    SmtStatus
    check_sat_assuming(const std::vector<term_ptr> &onVars, const std::vector<term_ptr> &offVars, int timeout) override;

    Model get_model() override;

private:
    class Logger {
    public:
        explicit Logger(boost::process::opstream &&in) : m_in{std::move(in)} {}

        template<typename T>
        Logger &operator<<(const T &val) {
            m_in << val;
            /*
            std::cerr << val;
            std::cerr.flush();
            */
            return *this;
        }

        void flush() {
            m_in.flush();
            /*
            std::cerr.flush();
            */
        }

    private:
        boost::process::opstream m_in;
    };

    boost::process::child m_proc;
    Logger m_in;
    boost::process::ipstream m_out;

    std::unordered_map<term_ptr, string> m_solver_vars;
    std::unordered_map<string, term_ptr> m_solver_var_lookup;
    std::vector<term_ptr> m_solver_vars_in_order;
    std::vector<unsigned int> m_stack_positions;
    unsigned int m_cnt{0};
    std::deque<Type> m_annotations;

    Type next_annotation() {
        auto ty = m_annotations.front();
        m_annotations.pop_front();
        return ty;
    }

    void declare_vars(term_ptr t);

    std::string lookup_var(term_ptr var) {
        return m_solver_vars.find(var)->second;
    }

    void serialize(term_ptr t);

    static term_ptr argn(term_ptr t, size_t n) {
        return t->as_complex().val[n];
    }

    static term_ptr arg0(term_ptr t) {
        return argn(t, 0);
    }

    void serialize(const std::string &repr, const ComplexTerm &t);

    template<typename T, size_t N>
    void serialize_bit_string(T val);

    template<size_t From, size_t To, bool Signed>
    void serialize_bv_to_bv(term_ptr t);

    void serialize_bv_extract(term_ptr t);

    template<size_t E, size_t S>
    void serialize_bv_to_fp(term_ptr t);

    template<typename T, size_t E, size_t S>
    void serialize_fp(term_ptr t);

    template<size_t N, bool Signed>
    void serialize_fp_to_bv(term_ptr t);

    template<size_t S, size_t E>
    void serialize_fp_to_fp(term_ptr t);

    void serialize_let(term_ptr t);

    template<typename T>
    void serialize_int(term_ptr t);

    template<bool Exists>
    void serialize_quantifier(term_ptr t);

    std::string serialize_sym(Symbol sym);

    std::string serialize_tester(Symbol sym);

    template<size_t W>
    void serialize_int2bv(term_ptr t);
};

}

#endif //CODEGEN_SMT_SHIM_H
