//
// Created by Aaron Bembenek on 1/23/23.
//

#include "smt_parser.hpp"
#include <sstream>

namespace flg {

void SmtLibTokenizer::load(bool allow_eof) {
    if (m_next.has_value()) {
        return;
    }
    int ch;
    while (std::isspace(ch = m_is.get()) && m_ignore_whitespace) {
        // keep looping
    }
    if (ch == std::char_traits<char>::eof()) {
        if (!allow_eof) {
            throw std::runtime_error("SMT-LIB tokenization error: unexpected EOF");
        }
    }
    std::string s;
    s.push_back((char) ch);
    if (is_word_char(ch)) {
        while ((ch = m_is.peek()) != std::char_traits<char>::eof() && is_word_char(ch)) {
            s.push_back((char) ch);
            m_is.get();
        }
    }
    m_next = std::move(s);
}

const std::string &SmtLibTokenizer::peek() {
    load(false);
    return *m_next;
}

std::string SmtLibTokenizer::next() {
    load(false);
    std::string s = *std::move(m_next);
    m_next.reset();
    return s;
}

bool SmtLibTokenizer::has_next() {
    load(true);
    return m_next.has_value();
}

void SmtLibTokenizer::consume(const std::string &s) {
    std::stringstream ss(s);
    SmtLibTokenizer t(ss);
    while (t.has_next()) {
        std::string expected = t.next();
        std::string found = next();
        if (expected != found) {
            std::stringstream msg;
            msg << "SMT-LIB tokenization error: tried to consume \"" << expected << "\" but found \"" << found << "\"";
            throw std::runtime_error(msg.str());
        }
    }
}

SmtLibParser::Model SmtLibParser::get_model(std::istream &is) const {
    SmtLibTokenizer t(is);
    t.consume("(");
    Model m;
    while (true) {
        const std::string &tok = t.peek();
        if (tok == ")") {
            break;
        } else if (tok == ";") {
            consume_comment(t);
        } else {
            parse_function_def(m, t);
        }
    }
    t.consume(")");
    t.ignore_whitespace(false);
    // Remove EOL
    t.next();
    return m;
}

void SmtLibParser::consume_comment(SmtLibTokenizer &t) const {
    t.consume(";;");
    t.ignore_whitespace(false);
    while (t.next() != "\n") {
        // Keep cruising
    }
    t.ignore_whitespace(true);
}

void SmtLibParser::parse_function_def(Model &m, SmtLibTokenizer &t) const {
    t.consume("(");
    auto tok = t.peek();
    if (tok == "forall" || tok == "declare") {
        skip_rest_of_s_exp(t);
        return;
    }
    t.consume("define-fun");
    std::string id = parse_identifier(t);

    // Ignore args
    t.consume("(");
    skip_rest_of_s_exp(t);

    // Ignore type
    parse_type(t);

    auto it = m_vars.find(id);
    if (it != m_vars.end()) {
        term_ptr x = it->second;
        if (should_record(x->sym)) {
            m.emplace(x, parse_term(t, x->sym));
        }
    }
    skip_rest_of_s_exp(t);
}

void SmtLibParser::skip_rest_of_s_exp(SmtLibTokenizer &t) const {
    unsigned depth = 1;
    while (depth > 0) {
        const std::string &tok = t.peek();
        if (tok == "(") {
            t.consume(tok);
            depth++;
        } else if (tok == ")") {
            t.consume(tok);
            depth--;
        } else if (tok == "\"") {
            parse_string_raw(t);
        } else if (tok == "|") {
            parse_identifier(t);
        }
    }
}

std::string SmtLibParser::parse_string_raw(SmtLibTokenizer &t) const {
    t.consume("\"");
    t.ignore_whitespace(false);
    std::string s;
    while (true) {
        std::string tok = t.next();
        if (tok == "\"") {
            // SMT-LIB uses "" to represent the character "
            if (t.peek() != "\"") {
                break;
            }
            t.consume(tok);
        }
        s += tok;
    }
    t.ignore_whitespace(true);
    return s;
}

std::string SmtLibParser::parse_identifier(SmtLibTokenizer &t) const {
    std::string s = t.next();
    if (s == "|") {
        t.ignore_whitespace(false);
        while (t.peek() != "|") {
            s += t.next();
        }
        t.ignore_whitespace(true);
    } else {
        while (true) {
            const std::string &tok = t.peek();
            if (is_ident_char(tok[0])) {
                t.consume(tok);
                s += tok;
            } else {
                break;
            }
        }
    }
    return s;
}

bool SmtLibParser::is_ident_char(int ch) {
    if (std::isalnum(ch)) {
        return true;
    }
    switch (ch) {
        case '~':
        case '!':
        case '@':
        case '%':
        case '^':
        case '&':
        case '*':
        case '_':
        case '-':
        case '+':
        case '=':
        case '<':
        case '>':
        case '.':
        case '?':
        case '/':
            return true;
    }
    return false;
}

void SmtLibParser::parse_type(SmtLibTokenizer &t) const {
    if (t.next() == "(") {
        skip_rest_of_s_exp(t);
    }
}

}