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
        if (allow_eof) {
            return;
        } else {
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

Model SmtLibParser::get_model(std::istream &is) const {
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

void skip_rest_of_s_exp(SmtLibTokenizer &t);
std::string parse_identifier(SmtLibTokenizer &t);

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

std::string parse_string_raw(SmtLibTokenizer &t) {
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

bool is_ident_char(int ch) {
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

std::string parse_identifier(SmtLibTokenizer &t) {
    std::string s = t.next();
    if (s == "|") {
        t.ignore_whitespace(false);
        while (t.peek() != "|") {
            s += t.next();
        }
        t.consume("|");
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


void skip_rest_of_s_exp(SmtLibTokenizer &t) {
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
        } else {
            t.consume(tok);
        }
    }
}

void SmtLibParser::parse_type(SmtLibTokenizer &t) const {
    std::string tok = t.next();
    if (tok == "(") {
        skip_rest_of_s_exp(t);
    }
}

bool SmtLibParser::should_record(Symbol sym) const {
    switch (sym) {
/* INSERT 0 */
    default: return false;
    }
}

term_ptr parse_string(SmtLibTokenizer &t) {
    return Term::make<std::string>(parse_string_raw(t));
}

uint64_t parse_bv(SmtLibTokenizer &t) {
    t.consume("#");
    std::string tok = t.next();
    std::string prefix = tok.substr(0, 1);
    std::string num = tok.substr(1);
    int base{0};
    if (prefix == "b") {
        base = 2;
    } else {
        assert(prefix == "x");
        base = 16;
    }
    return std::stoull(num, nullptr, base);
}

template<typename To, typename From>
To bit_cast(From from) {
    To dst;
    memcpy(&dst, &from, sizeof(To));
    return dst;
}

term_ptr parse_i32(SmtLibTokenizer &t) {
    return Term::make(bit_cast<int32_t>(parse_bv(t)));
}

term_ptr parse_i64(SmtLibTokenizer &t) {
    return Term::make(bit_cast<int64_t>(parse_bv(t)));
}

template<typename T, unsigned E, unsigned S>
term_ptr parse_fp(SmtLibTokenizer &t) {
    t.consume("(");
    T val;
    if (t.peek() == "fp") {
        t.consume("fp");
        uint64_t sign = parse_bv(t);
        uint64_t exp = parse_bv(t);
        uint64_t mant = parse_bv(t);
        uint64_t bits = sign << (E + S - 1);
        bits |=  exp << (S - 1);
        bits |= mant;
        val = bit_cast<T>(bits);
    } else {
        t.consume("_");
        std::string next = t.next();
        if (next == "NaN") {
            val = std::numeric_limits<T>::quiet_NaN();
        } else if (next == "+") {
            if (t.peek() == "oo") {
                t.consume("oo");
                val = +std::numeric_limits<T>::infinity();
            } else {
                t.consume("zero");
                val = +0.0f;
            }
        } else {
            assert(next == "-");
            if (t.peek() == "oo") {
                t.consume("oo");
                val = -std::numeric_limits<T>::infinity();
            } else {
                t.consume("zero");
                val = -0.0f;
            }
        }
    }
    skip_rest_of_s_exp(t);
    return Term::make<T>(val);
}

term_ptr parse_fp32(SmtLibTokenizer &t) {
    return parse_fp<float, 8, 24>(t);
}

term_ptr parse_fp64(SmtLibTokenizer &t) {
    return parse_fp<float, 11, 53>(t);
}

term_ptr parse_bool(SmtLibTokenizer &t) {
    std::string tok = t.next();
    if (tok == "true") {
        return Term::make(true);
    } else {
        assert(tok == "false");
        return Term::make(false);
    }
}

template<typename Fn>
term_ptr parse_adt(SmtLibTokenizer &t) {
    unsigned num_s_exps_to_skip = 0;
    if (t.peek() == "(") {
        t.consume("(");
        num_s_exps_to_skip++;
        if (t.peek() == "as") {
            t.consume("as");
            if (t.peek() == "(") {
                t.consume("(");
                num_s_exps_to_skip++;
            }
        }
    }
    Fn fn;
    term_ptr term = fn(t);
    for (unsigned i = 0; i < num_s_exps_to_skip; ++i) {
        skip_rest_of_s_exp(t);
    }
    return term;
}

/* INSERT 1 */
term_ptr SmtLibParser::parse_term(SmtLibTokenizer &t, Symbol sym) const {
    switch (sym) {
/* INSERT 2 */
    default: abort();
    }
}

}