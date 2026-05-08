#include <iostream>
#include <string>
#include <vector>
#include <memory>
#include <stdexcept>
#include <cctype>
#include <map>
#include <unordered_set>
#include <chrono>
struct Term
{
    std::string term_str;
    std::string label;
    std::vector<Term*> children;
    std::unordered_set<Term*> parents;
    std::vector<Term*> e_reps;
    Term* e_rep = nullptr;
    bool pat = false;
    std::vector<int> comp_order;
    bool pending_cong = false;
};

struct TermsStorage
{
    std::map<std::string, std::unique_ptr<Term>> terms_map;
    std::vector<std::unique_ptr<Term>> bin;
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

Term* find(Term* t)
{
    while (t->e_rep != t)
    {
        t = t->e_rep;
    }
    return t;
}

void compact(Term* term, int term_id, std::map<std::string, std::unique_ptr<Term>>& terms_map, bool before_merge = true)
{
    auto found_term = terms_map.find(term->term_str);
    if (found_term == terms_map.end())
    {
        //in this case this means that this term and its parents are not in terms_map
        //therefor we just put it into map without changing its parents
        term->pending_cong = !before_merge;
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
            find(found_term->second.get())->parents.insert(*term->parents.begin());
            (*term->parents.begin())->children[term_id] = found_term->second.get();
        }

        deleteRecursive(term);
        return;
    }
    int i = 0;
    for (auto ch : term->children)
    {
        compact(ch, i, terms_map, before_merge);
        ++i;
    }
}

bool cong(Term* t1, Term* t2)
{
    if (t1->label != t2->label)
    {
        return false;
    }
    for (int i = 0; i < t1->children.size(); ++i)
    {
        if (find(t1->children[i]) != find(t2->children[i]))
        {
            return false;
        }
    }
    return true;
}

void unionTerms(Term* t1, Term* t2, TermsStorage& storage, bool congruent = false)
{
    Term* main_t = find(t1);
    Term* sub_t = find(t2);
    if (main_t == sub_t)
    {
        return;
    }

    for(auto par : sub_t->parents)
    {
        main_t->parents.insert(par);
    }
    main_t->e_reps.insert(main_t->e_reps.end(), sub_t->e_reps.begin(), sub_t->e_reps.end());
    for (auto rep : main_t->e_reps)
    {
        rep->e_rep = main_t;
    }
    sub_t->e_reps.clear();
    sub_t->parents.clear();

    if (congruent)
    {
        for (auto par : main_t->parents)
        {
            for (int i = 0; i < par->children.size(); ++i)
            {
                if (par->children[i] == t2)
                {
                    par->children[i] = main_t;
                }
            }
        }
        for (auto ch : t2->children)
        {
            ch = find(ch);
            ch->parents.erase(t2);
            ch->parents.insert(main_t);
        }

        //opt: can be moved before e_reps.insert
        for (size_t i = 0; i < main_t->e_reps.size(); ++i)
        {
            if (main_t->e_reps[i] == t2)
            {
                std::swap(main_t->e_reps[i], main_t->e_reps.back());
                main_t->e_reps.pop_back();
                break;
            }
        }
        auto it = storage.terms_map.find(t2->term_str);

        if (it != storage.terms_map.end())
        {
            auto value = std::move(it->second);
            storage.terms_map.erase(it);
            storage.bin.push_back(std::move(value));
        }   
    }
}

void updateCongruence(Term* t, TermsStorage& storage);

void merge(Term* t1, Term* t2, TermsStorage& storage, bool rec = false)
{
    auto t1_top = find(t1);
    auto t2_top = find(t2);
    if (t1 == t2)
    {
        return;
    }
    auto pars1 = t1_top->parents;
    auto pars2 = t2_top->parents;
    unionTerms(t1, t2, storage, rec);
    for (auto par1 : pars1)
    {
        if (find(par1) == t1_top)
        {
            continue;
        }
        for (auto par2 : pars2)
        {
            if (find(par2) == t1_top)
            {
                continue;
            }
            if (cong(par1, par2))
            {
                merge(par1, par2, storage, true);
            }
        }
    }
}

void markPatternNodes(Term* t)
{
    bool pat_temp = false;
    for (auto ch : t->children)
    {
        markPatternNodes(ch);
        pat_temp |= ch->pat;
    }
    if (pat_temp)
    {
        t->pat = true;
        return;
    }
    if (t->label[0] == '`')
    {
        t->pat = true;
    }
}

void setupOrder(Term* t)
{
    for (int i = 0; i < t->children.size(); ++i)
    {
        if(!t->children[i]->pat)
        {
            t->comp_order.push_back(i);
        }
    }
    for (int i = 0; i < t->children.size(); ++i)
    {
        if (t->children[i]->pat)
        {
            t->comp_order.push_back(i);
        }
    }
    for (auto ch : t->children)
    {
        setupOrder(ch);
    }
}
struct Arg
{
    Term* term = nullptr;
    int node_id = 0;
};


class Matcher
{
    struct BStackEl
    {
        int parent_i = -1;
        int child_i = 0;
        int eq_i = -1;
        Term* lhs = nullptr;
        Term* rhs = nullptr;
        Term* rhs_main = nullptr;

        void nextRhs()
        {
            ++eq_i;
            if (lhs->label[0] == '`')
            {
                return;
            }
            for (; eq_i < rhs_main->e_reps.size(); ++eq_i)
            {
                if (rhs_main->e_reps[eq_i]->label == lhs->label)
                {
                    return;
                }
            }
        }
        bool updateEq()
        {
            nextRhs();
            if (eq_i >= rhs_main->e_reps.size())
            {
                return false;
            }
            rhs = rhs_main->e_reps[eq_i];
            child_i = 0;
            return true;
        }
        bool getChild(Term*& out_lhs, Term*& out_rhs)
        {
            if (rhs->children.empty())
            {
                return false;
            }
            if (child_i >= lhs->children.size())
            {
                return false;
            }
            out_lhs = lhs->children[lhs->comp_order[child_i]];
            out_rhs = rhs->children[lhs->comp_order[child_i]];
            return true;
        }
    };
public:

    bool match(Term* lhs, Term* rhs)
    {
        if (first_call)
        {
            first_call = false;
            BStackEl el;
            el.lhs = lhs;
            el.rhs_main = find(rhs);
            if (!el.updateEq())
            {
                return false;
            }
            bstack.push_back(el);
        }
        else if (!back())
        {
            return false;
        }
        while (true)
        {
            BStackEl& top = bstack.back();
            if (find(top.lhs) == find(top.rhs))
            {
                if (!next())
                {
                    return true;
                }
                BStackEl& new_top = bstack.back();
                if (!new_top.updateEq())
                {
                    if (!back())
                    {
                        return false;
                    }
                }
            }
            else if (top.lhs->label[0] == '`')
            {
                auto found_arg = args.find(top.lhs);
                if (found_arg == args.end())
                {
                    auto new_arg = args.emplace(top.lhs, Arg());
                    new_arg.first->second.node_id = bstack.size();
                    new_arg.first->second.term = top.rhs;
                    if (!next())
                    {
                        return true;
                    }
                    BStackEl& new_top = bstack.back();
                    if (!new_top.updateEq())
                    {
                        if (!back())
                        {
                            return false;
                        }
                    }
                }
                else if(find(found_arg->second.term) != find(top.rhs))
                {
                    if (!back())
                    {
                        return false;
                    }
                }
                else
                {
                    if (!next())
                    {
                        return true;
                    }
                    BStackEl& new_top = bstack.back();
                    if (!new_top.updateEq())
                    {
                        if (!back())
                        {
                            return false;
                        }
                    }
                }
            }
            else
            {
                if (!lhs->pat)
                {
                    if (!back())
                    {
                        return false;
                    }
                    continue;
                }
                if (!in())
                {
                    return true;
                }
                BStackEl& new_top = bstack.back();
                if (!new_top.updateEq())
                {
                    if (!back())
                    {
                        return false;
                    }
                }

            }
            
        }

    }

    // false means we finished comparisson
    bool next()
    {
        auto& top = bstack.back();
        int parent_i = top.parent_i;
        while (parent_i >= 0)
        {
            auto& par_el = bstack[parent_i];
            Term* lhs = nullptr;
            Term* rhs = nullptr;
            if (par_el.getChild(lhs, rhs))
            {
                ++par_el.child_i;
                BStackEl new_el;
                new_el.lhs = lhs;
                new_el.rhs_main = find(rhs);
                new_el.parent_i = parent_i;
                bstack.push_back(new_el);
                return true;
            }
            else
            {
                parent_i = par_el.parent_i;
            }
        }
        return false;
    }

    bool back()
    {
        for (int i = bstack.size() - 1; i >= 0; --i)
        {
            auto& top = bstack.back();
            if (top.updateEq())
            {
                // clear args
                for (auto it = args.begin(); it != args.end();)
                {
                    if (it->second.node_id > i)
                    {
                        it = args.erase(it); // returns next valid iterator
                    }
                    else
                    {
                        ++it;
                    }
                }
                return true;
            }
            if(top.parent_i >= 0)
            {
                auto& par = bstack[top.parent_i];
                --par.child_i;
            }
            bstack.pop_back();
        }
        return false;
    }

    bool in()
    {
        auto& top = bstack.back();
        Term* lhs = nullptr;
        Term* rhs = nullptr;
        
        if (!top.getChild(lhs, rhs))
        {
            return next();
        }
        ++top.child_i;
        BStackEl new_el;
        new_el.lhs = lhs;
        new_el.rhs_main = find(rhs);
        new_el.parent_i = bstack.size() - 1;
        bstack.push_back(new_el);
        return true;
    }

    std::vector<BStackEl> bstack;
    std::map<Term*, Arg> args;
    bool first_call = true;
};


void rewrite(Term* pat, std::map<Term*, Arg>& args, std::string& res)
{
    if (pat->label[0] == '`')
    {
        auto arg = args.find(pat);
        if (arg == args.end())
        {
            res += pat->label;
        }
        else
        {
            res += arg->second.term->term_str;
        }
        return;
    }
    res += pat->label;
    if (!pat->children.empty())
    {
        res += '(';
        for (auto& ch : pat->children)
        {
            rewrite(ch, args, res);
            res += ',';
        }
        res.back() = ')';
    }
}

Term* instantiate(Term* pat, std::map<Term*, Arg>& args, std::map<std::string, std::unique_ptr<Term>>& terms_map)
{
    std::string str;
    rewrite(pat, args, str);
    auto found = terms_map.find(str);
    if (found != terms_map.end())
    {
        return found->second.get();
    }
    Parser pr(str);
    pr.parse();
    compact(pr.m_current_term, 0, terms_map);

    return terms_map.find(str)->second.get();
}

void updateCongruence(Term* t, TermsStorage& storage)
{
    if (!t->pending_cong)
    {
        return;
    }
    t->pending_cong = false;
    if (t->children.empty())
    {
        return;
    }
    for (auto ch : t->children)
    {
        updateCongruence(ch, storage);
    }
    auto pars = find(t->children.back())->parents;
    for (auto par : pars)
    {
        if (find(t) != find(par) && cong(t, par))
        {
            //if found congruent parent, this means that this parent congruent to other parents and there is no need to continue
            unionTerms(par,t, storage, true);
            break;
        }
    }
}

struct TermView
{
    Term* t = nullptr;
    std::vector<TermView> children;
};

struct PathEl
{
    Term* t = nullptr;
    int pos = 0;
};

struct InvTree
{
    Term* t = nullptr;
    int pos = 0;
    std::vector<InvTree> parents;
};

void collectPaths(Term* t, int pos, std::vector<PathEl>& current, std::vector<std::vector<PathEl>>& result)
{
    auto& path_el = current.emplace_back();
    path_el.pos = pos;
    path_el.t = t;
    if (!t->pat || t->label[0] == '`')
    {
        result.push_back(current);
    }
    else
    {
        int i = 0;
        for (auto ch : t->children)
        {
            collectPaths(ch, i, current, result);
            ++i;
        }
    }
    current.pop_back();
}

bool makeInvPathTree(InvTree& tree, const std::vector<PathEl>& path, int path_i)
{
    if (path_i < 0)
    {
        return true;
    }
    auto t_top = find(tree.t);
    for (auto par : t_top->parents)
    {
        //iterate over parents
        if (par->label == path[path_i].t->label)
        {
            //parent have needed label
            int i = 0;
            if (find(par->children[tree.pos]) == t_top)
            {
                InvTree inv_el;
                inv_el.pos = path[path_i].pos;
                inv_el.t = par;
                tree.parents.push_back(inv_el);
                if (!makeInvPathTree(tree.parents.back(), path, path_i - 1))
                {
                    tree.parents.pop_back();
                }
            }
        }
    }
    return !tree.parents.empty();
}

void collectPathsPerTerm(InvTree& tree, std::vector<PathEl>& curr_path, std::map<Term*, std::vector<std::vector<PathEl>>>& paths_per_term)
{
    PathEl p_el;
    p_el.pos = tree.pos;
    p_el.t = tree.t;
    curr_path.push_back(p_el);

    if (p_el.pos == -1)
    {
        auto found = paths_per_term.find(tree.t);
        if (found == paths_per_term.end())
        {
            auto new_el = paths_per_term.emplace(tree.t, std::vector<std::vector<PathEl>>());
            new_el.first->second.push_back(curr_path);
        }
        else
        {
            found->second.push_back(curr_path);
        }
    }
    else
    {
        for (auto& par : tree.parents)
        {
            collectPathsPerTerm(par, curr_path, paths_per_term);
        }
    }
    curr_path.pop_back();
}

int main()
{
    
    std::vector<Identity> identities = {
        {"+(`a,`b)", "+(`b,`a)"},
        {"+(+(`a,`b),`c)", "+(`a,+(`b,`c))"},
        {"+(`a,+(`b,`c))", "+(+(`a,`b),`c)"},
        {"*(`a,`b)", "*(`b,`a)"},
        {"*(*(`a,`b),`c)", "*(`a,*(`b,`c))"},
        {"*(`a,*(`b,`c))", "*(*(`a,`b),`c)"},
        {"p(`a,2)", "*(`a,`a)"},
        {"*(+(`a,`b),`c)", "+(*(`a,`c),*(`b,`c))"},
        {"+(*(`a,`c),*(`b,`c))","*(+(`a,`b),`c)"},
        {"+(`a,`a)", "*(2,`a)"},
    };

    std::string lhs = "+(*(2,*(`a,`b)),+(*(`a,`a),*(`b,`b)))";//2ab + a*a + b*b
    std::string rhs = "p(+(*(a,c),*(c,d)),2)";//(e+a)^2

    Term* t_lhs = nullptr;
    Term* t_rhs = nullptr;
    TermsStorage ts;

    {
        Parser pr(lhs);
        pr.parse();
        compact(pr.m_current_term, 0, ts.terms_map);
        t_lhs = ts.terms_map.find(lhs)->second.get();
        markPatternNodes(t_lhs);
        setupOrder(t_lhs);
    }

    {
        Parser pr(rhs);
        pr.parse();
        compact(pr.m_current_term, 0, ts.terms_map);
        t_rhs = ts.terms_map.find(rhs)->second.get();
    }

    for (auto& id : identities)
    {
        {
            Parser pr(id.lhs);
            pr.parse();
            compact(pr.m_current_term, 0, ts.terms_map);
            id.t_lhs = ts.terms_map.find(id.lhs)->second.get();
            markPatternNodes(id.t_lhs);
            setupOrder(id.t_lhs);
        }

        {
            Parser pr(id.rhs);
            pr.parse();
            compact(pr.m_current_term, 0, ts.terms_map);
            id.t_rhs = ts.terms_map.find(id.rhs)->second.get();
            markPatternNodes(id.t_rhs);
            setupOrder(id.t_rhs);
        }
    }



    for (int i = 0; i < 30; ++i)
    {
        for (auto& id : identities)
        {
            std::vector<Identity> new_ids;
            for (auto& t : ts.terms_map)
            {
                if (t.second->pat)
                {
                    continue;
                }
                if (t.second->e_rep != t.second.get())
                {
                    continue;
                }
                Matcher mc;
                while (mc.match(id.t_lhs, t.second.get()))
                {
                    std::string str;
                    rewrite(id.t_rhs, mc.args, str);
                    auto& new_id = new_ids.emplace_back();
                    new_id.t_lhs = t.second.get();
                    new_id.rhs = std::move(str);
                }
            }

            for (auto& new_id : new_ids)
            {
                if (new_id.t_lhs->term_str == new_id.rhs)
                {
                    continue;
                }
                auto found = ts.terms_map.find(new_id.rhs);
                if (found != ts.terms_map.end())
                {
                    new_id.t_rhs = found->second.get();
                    //if rhs already exists
                    //if it congruent to lhs, then they are equal already
                    //synce system is closed on congruence
                    if (find(new_id.t_lhs) == find(new_id.t_rhs))
                    {
                        continue;
                    }
                }
                else
                {
                    Parser pr(new_id.rhs);
                    pr.parse();
                    compact(pr.m_current_term, 0, ts.terms_map, false);
                    new_id.t_rhs = ts.terms_map.find(new_id.rhs)->second.get();
                    //if new term
                    //update congruence
                    //if still different with lhs -> merge
                    updateCongruence(new_id.t_rhs, ts);
                }
                if (find(new_id.t_rhs) != find(new_id.t_lhs))
                {
                    merge(new_id.t_lhs, new_id.t_rhs, ts);
                }
                ts.bin.clear();
            }
            Matcher mc;
            if (mc.match(t_lhs, t_rhs))
            {
                std::cout << "match------------- \n";
                for (auto& arg : mc.args)
                {
                    std::cout << arg.first->label << " = " << arg.second.term->term_str << '\n';
                }
                for (auto& t : ts.terms_map)
                {
                    for (auto& rep : t.second->e_reps)
                    {
                        std::cout << t.second->term_str << "  " << rep->term_str << "\n";
                    }
                }
                return 0;
            }
        }
    }

    

    /*std::vector<PathEl> cur_path;
    std::vector<std::vector<PathEl>> paths;
    collectPaths(identities[5].t_lhs, -1, cur_path, paths);
    std::vector<std::vector<InvTree>> inv_trees;
    for(auto& path : paths)
    {
        inv_trees.emplace_back();
        for (auto& t : terms_map)
        {
            if (t.second->pat)
            {
                continue;
            }
            if (t.second->e_rep != t.second.get())
            {
                continue;
            }
            {
                InvTree tr;
                tr.t = t.second.get();
                tr.pos = path.back().pos;
                if (makeInvPathTree(tr, path, path.size() - 2))
                {
                    inv_trees.back().push_back(std::move(tr));
                }
            }

        }
    }
    std::map<Term*, std::vector<std::vector<PathEl>>> paths_per_term;
    for (auto& tr_arr : inv_trees)
    {
        for(auto& tr : tr_arr)
        {
            std::vector<PathEl> curr_path;
            collectPathsPerTerm(tr, curr_path, paths_per_term);
        }
    }*/
    /*for (auto& paths1 : paths_per_term)
    {
        if (paths1.second.size() < 3)
        {
            continue;
        }
        std::cout << "\n=========== \n";
        for (auto& path : paths1.second)
        {
            std::cout << "\n";
            for (int i = path.size() - 1; i >= 0; i--)
            {
                std::cout << path[i].t->term_str << " -> ";
            }
        }
    }*/
    return 0;
}