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
    std::unordered_set<Term*> parents;
    std::vector<Term*> e_reps;
    Term* e_rep = nullptr;
};

class Parser
{
public:
    Parser(const std::string& str)
        : m_str(str)
    {}
    
    void parse()
    {
        while (m_pos != m_str.size())
        {
            int term_start = m_pos;
            consumeTermName();
            int label_end = m_pos;
            auto t = new Term();
            t->e_reps.push_back(t);
            t->e_rep = t;
            m_current_term = t;
            if (m_parent_term)
            {
                m_current_term->parents.insert(m_parent_term);
                m_parent_term->children.push_back(m_current_term);
            }
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
                m_parent_term = !m_current_term->parents.empty() ? *m_current_term->parents.begin() : nullptr;
            }
            m_current_term->label = m_str.substr(term_start, label_end - term_start);
            m_current_term->term_str = m_str.substr(term_start, m_pos - term_start);
            if (m_pos >= m_str.size())
            {
                return;
            }
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
};

struct Identity
{
    std::string lhs;
    std::string rhs;
    Term* t_lhs = nullptr;
    Term* t_rhs = nullptr;
};

void deleteRecursive(Term* term)
{
    for (auto ch : term->children)
    {
        deleteRecursive(ch);
    }
    delete term;
}

void compact(Term* term, int term_id, std::map<std::string, std::unique_ptr<Term>>& terms_map)
{
    auto found_term = terms_map.find(term->term_str);
    if (found_term == terms_map.end())
    {
        //in this case this means that this term and its parents are not in terms_map
        //therefor we just put it into map without changing its parents
        terms_map.emplace(term->term_str, std::unique_ptr<Term>(term));
    }
    else
    {
        //term already in map, this means, that it and its children are in terms_map
        //its parent still added into terms_map only once
        //but two identical terms could have same parent e.g. f(a,a)
        // so we need to add parent uniquely here
        // update this element in parent with found term
        //->delete this term recursively
        if(!term->parents.empty())
        {
            found_term->second->parents.insert(*term->parents.begin());
            (*term->parents.begin())->children[term_id] = found_term->second.get();
        }

        deleteRecursive(term);
        return;
    }
    int i = 0;
    for (auto ch : term->children)
    {
        compact(ch, i, terms_map);
        ++i;
    }
}

Term* find(Term* t)
{
    while (t->e_rep != t)
    {
        t = t->e_rep;
    }
    return t;
}

void unionTerms(Term* t1, Term* t2)
{
    t1 = find(t1);
    t2 = find(t2);
    Term* main_t = t1->e_reps.size() > t2->e_reps.size() ? t1 : t2;
    Term* sub_t = t1 == main_t ? t2 : t1;

    for(auto par : sub_t->parents)
    {
        main_t->parents.insert(par);
    }
    sub_t->parents.clear();
    main_t->e_reps.insert(main_t->e_reps.end(), sub_t->e_reps.begin(), sub_t->e_reps.end());
    sub_t->e_reps.clear();
    sub_t->e_rep = main_t;
}

bool cong(Term* t1, Term* t2)
{
    if (t1->label != t2->label)
    {
        return false;
    }
    for(int i = 0; i < t1->children.size(); ++i)
    {
        if (find(t1->children[i]) != find(t2->children[i]))
        {
            return false;
        }
    }
    return true;
}

void merge(Term* t1, Term* t2)
{
    t1 = find(t1);
    t2 = find(t2);
    auto pars1 = t1->parents;
    auto pars2 = t2->parents;
    unionTerms(t1, t2);
    for (auto par1 : pars1)
    {
        for (auto par2 : pars2)
        {
            if (par1 != par2 && cong(par1, par2))
            {
                merge(par1, par2);
            }
        }
    }
}

int main()
{
    
    std::vector<Identity> identities = {
        {"+(a,*(a,b))", "+(*(a,b),a)"},
        {"*(a,b)", "*(b,a)"},
    };

    std::string lhs = "+(a,*(a,b))";
    std::string rhs = "+(*(b,a),a)";

    std::map<std::string, std::unique_ptr<Term>> terms_map;

    {
        Parser pr(lhs);
        pr.parse();
        compact(pr.m_current_term, 0, terms_map);
    }

    {
        Parser pr(rhs);
        pr.parse();
        compact(pr.m_current_term, 0, terms_map);
    }

    for (auto& id : identities)
    {
        {
            Parser pr(id.lhs);
            pr.parse();
            compact(pr.m_current_term, 0, terms_map);
            id.t_lhs = terms_map.find(id.lhs)->second.get();
        }

        {
            Parser pr(id.rhs);
            pr.parse();
            compact(pr.m_current_term, 0, terms_map);
            id.t_rhs = terms_map.find(id.rhs)->second.get();
        }
        merge(id.t_lhs, id.t_rhs);
    }


    return 0;
}