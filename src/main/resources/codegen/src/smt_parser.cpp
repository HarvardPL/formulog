//
// Created by Aaron Bembenek on 1/23/23.
//

#include "smt_parser.hpp"
#include <sstream>

void SmtLibTokenizer::load(bool allow_eof) {
    if (m_next.has_value()) {
        return;
    }
    int ch;
    while ((ch = m_is.get()) != std::char_traits<char>::eof() && m_ignore_whitespace && std::isspace(ch)) {
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
