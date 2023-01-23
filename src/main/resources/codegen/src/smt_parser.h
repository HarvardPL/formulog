//
// Created by Aaron Bembenek on 1/23/23.
//

#ifndef CODEGEN_SMT_PARSER_H
#define CODEGEN_SMT_PARSER_H

#include <istream>
#include <optional>

class SmtTokenizer {
public:
    explicit SmtTokenizer(std::istream &is) : m_is(is) {}

    void ignore_whitespace(bool ignore) {
        m_ignore_whitespace = ignore;
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

#endif //CODEGEN_SMT_PARSER_H
