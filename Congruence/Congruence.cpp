#include <iostream>
#include <string>
#include <vector>
#include <memory>
#include <stdexcept>
#include <cctype>
#include <map>
#include <unordered_set>
struct Term
{
    std::string term_str;
    std::string label;
    std::vector<Term*> children;
    std::vector<Term*> parents;
};

class Parser
{
public:
    Parser(std::vector<std::unique_ptr<Term>>& terms, const std::string& str)
        : m_str(str)
        , m_terms(terms)
    {}
    
    void parse()
    {
        while (m_pos != m_str.size())
        {
            int term_start = m_pos;
            consumeTermName();
            int label_end = m_pos;
            auto t = std::make_unique<Term>();
            m_current_term = t.get();
            m_current_term->parents.push_back(m_parent_term);
            if (m_parent_term)
            {
                m_parent_term->children.push_back(m_current_term);
            }
            m_terms.push_back(std::move(t));
            if (m_pos > m_str.size())
            {
                return;
            }
            if (m_str[m_pos] == '(')
            {
                ++m_pos;
                m_parent_term = m_current_term;
                parse();
                m_current_term = m_parent_term;
                m_parent_term = m_current_term->parents.back();
            }
            m_current_term->label = m_str.substr(term_start, label_end - term_start);
            m_current_term->term_str = m_str.substr(term_start, m_pos - term_start);
            if (m_str[m_pos] == ')')
            {
                ++m_pos;
                return;
            }
            ++m_pos;
        }
    }

    void consumeTermName()
    {
        int i = m_pos;
        for (; i < m_str.size(); ++i)
        {
            if (m_str[i] == '(' || m_str[i] == ')' || m_str[i] == ',')
            {
                break;
            }
        }
        m_pos = i;
    }

    Term* m_current_term = nullptr;
    Term* m_parent_term = nullptr;
    const std::string& m_str;
    int m_pos = 0;
    std::vector<std::unique_ptr<Term>>& m_terms;
};

struct Identity
{
    std::string lhs;
    std::string rhs;
};



int main()
{
    
    std::vector<Identity> identities = {
        {"+(~a,~b)", "+(~b,~a)"},
        {"+(+(~a,~b),~c)", "+(~a,+(~b,~c))"},
        {"+(~a,+(~b,~c))", "+(+(~a,~b),~c)"},
        {"*(~a,~b)", "*(~b,~a)"},
        {"*(*(~a,~b),~c)", "*(~a,*(~b,~c))"},
        {"*(~a,*(~b,~c))", "*(*(~a,~b),~c)"},
        {"p(~a,2)", "*(~a,~a)"},
        {"*(+(~a,~b),~c)", "+(*(~a,~c),*(~b,~c))"},
        {"+(*(~a,~c),*(~b,~c))","*(+(~a,~b),~c)"},
        {"+(~a,~a)", "*(2,~a)"},

    };

    std::string lhs = "+(*(2,*(~a,~b)),+(*(~a,~a),*(~b,~b)))";
    std::string rhs = "p(+(*(a,b),e),2)";

    std::vector<std::unique_ptr<Term>> terms;
    Parser pr(terms, lhs);
    pr.parse();
    return 0;
}