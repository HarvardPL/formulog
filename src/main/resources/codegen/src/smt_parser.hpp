//
// Created by Aaron Bembenek on 1/23/23.
//

#ifndef CODEGEN_SMT_PARSER_HPP
#define CODEGEN_SMT_PARSER_HPP

#include <istream>
#include <optional>
#include "Term.hpp"

namespace flg {

class SmtLibTokenizer {
public:
    explicit SmtLibTokenizer(std::istream &is) : m_is(is) {}

    void ignore_whitespace(bool ignore) {
        m_ignore_whitespace = ignore;
    }

    bool ignoring_whitespace() {
        return m_ignore_whitespace;
    }

    const std::string &peek();

    std::string next();

    bool has_next();

    void consume(const std::string &s);

private:
    std::istream &m_is;
    bool m_ignore_whitespace{true};
    std::optional<std::string> m_next{};

    void load(bool allow_eof);

    static bool is_word_char(int ch) {
        return ch == '_' || std::isalnum(ch);
    }
};

class SmtLibParser {
public:
    explicit SmtLibParser(std::unordered_map<std::string, term_ptr> &vars) : m_vars(vars) {}

    Model get_model(std::istream &is) const;

private:
    const std::unordered_map<std::string, term_ptr> &m_vars;

    void consume_comment(SmtLibTokenizer &t) const;

    void parse_function_def(Model &m, SmtLibTokenizer &t) const;

    void parse_type(SmtLibTokenizer &t) const;

    bool should_record(Symbol sym) const;

    term_ptr parse_term(SmtLibTokenizer &t, Symbol sym) const;
};

}

#endif //CODEGEN_SMT_PARSER_HPP
