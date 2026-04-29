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
    std::vector<std::unique_ptr<Term>> children;
    Term* parent = nullptr;
    bool duplicate = false;
    bool templ = false;
};

class Parser
{
public:
    std::vector<std::unique_ptr<Term>> start(const std::string& str)
    {
        str_to_parse = str;
        main_term = std::make_unique<Term>();
        parent_term = main_term.get();
        parse();
        for (auto& child : main_term->children)
        {
            child->parent = nullptr;
        }
        return std::move(main_term->children);
    }

    void parse()
    {
        if (!startTerm())
        {
            return;
        }
        while (pos < str_to_parse.size())
        {
            if (str_to_parse[pos] == '(')
            {
                pos++;
                parent_term = current_term;
                int cache_pos = pos;
                parse();
                current_term = parent_term;
                parent_term = parent_term->parent;
                current_term->term_str += "(" + str_to_parse.substr(cache_pos, pos - cache_pos - 1) + ")";
                continue;
            }
            if (str_to_parse[pos] == ',')
            {
                pos++;
                if (!startTerm())
                {
                    return;
                }
                continue;
            }
            if (str_to_parse[pos] == ')')
            {
                pos++;
                break;
            }
        }
    }

    bool startTerm()
    {
        int start_pos = pos;
        // consume label
        while (pos < str_to_parse.size())
        {
            if (!isalpha(str_to_parse[pos]) && !isdigit(str_to_parse[pos]) && str_to_parse[pos] != '*' && str_to_parse[pos] != '+' && str_to_parse[pos] != '~')
            {
                break;
            }
            ++pos;
        }
        if (pos == start_pos)
        {
            return false;
        }
        current_term = parent_term->children.emplace_back(std::make_unique<Term>()).get();
        current_term->parent = parent_term;
        current_term->label = str_to_parse.substr(start_pos, pos - start_pos);
        current_term->term_str = current_term->label;
        return true;
    }

    Term* current_term = nullptr;
    Term* parent_term = nullptr;
    std::string str_to_parse;
    int pos = 0;
    std::unique_ptr<Term> main_term;
};

// helper: print one Term (recursively)
void print_term(const Term* term, int depth = 0)
{
    if (!term)
        return;

    // indentation
    std::cout << std::string(depth * 2, ' ') << "- " << term->term_str << "\n";

    // print children
    for (const auto& child : term->children)
    {
        print_term(child.get(), depth + 1);
    }
}

// main function: print vector of roots
void print_terms(const std::vector<std::unique_ptr<Term>>& terms)
{
    for (const auto& term : terms)
    {
        print_term(term.get());
    }
}

struct EquivalenceClass
{
    EquivalenceClass* getTop()
    {
        EquivalenceClass* eq = this;
        while (eq->parent_eq)
        {
            eq = eq->parent_eq;
        }
        return eq;
    }
    void attachTo(EquivalenceClass* other)
    {
        auto* top1 = getTop();
        auto* top2 = other->getTop();

        if (top1 == top2)
        {
            return;
        }

        top1->parent_eq = top2;
        // assume that top1 already in reps
        top2->representatives.insert(top2->representatives.end(),
            top1->representatives.begin(), top1->representatives.end());

        top1->representatives.clear();

        for (auto* pred : top1->preds)
        {
            top2->preds.insert(pred);
        }

        top1->preds.clear();
    }
    Term* representative = nullptr;
    std::unordered_set<Term*> preds;
    EquivalenceClass* parent_eq = nullptr;
    std::vector<EquivalenceClass*> representatives;
    std::unordered_set<int> identitites_hold;
};

void collectNodes(const std::vector<std::unique_ptr<Term>>& terms, std::map<std::string, EquivalenceClass>& out)
{
    for (auto& term : terms)
    {
        collectNodes(term->children, out);
        auto same_term = out.find(term->term_str);
        if (same_term != out.end())
        {
            term->duplicate = true;
            if (term->parent)
            {
                auto top = same_term->second.getTop();
                top->preds.insert(term->parent);
            }
        }
        else
        {
            auto pair = out.emplace(term->term_str, EquivalenceClass());
            pair.first->second.representative = term.get();
            pair.first->second.representatives.push_back(&pair.first->second);
            if (term->parent)
            {
                pair.first->second.preds.insert(term->parent);
            }
        }
    }
}

void collectNode(Term* term, std::map<std::string, EquivalenceClass>& out)
{
    collectNodes(term->children, out);
    auto same_term = out.find(term->term_str);
    if (same_term != out.end())
    {
        term->duplicate = true;
        if (term->parent)
        {
            auto top = same_term->second.getTop();
            top->preds.insert(term->parent);
        }
    }
    else
    {
        auto pair = out.emplace(term->term_str, EquivalenceClass());
        pair.first->second.representative = term;
        pair.first->second.representatives.push_back(&pair.first->second);
        if(term->parent)
        {
            pair.first->second.preds.insert(term->parent);
        }
    }
}

void removeDuplicatePreds(std::map<std::string, EquivalenceClass>& nodes)
{
    for (auto& pair : nodes)
    {
        auto& preds = pair.second.preds;

        for (auto it = preds.begin(); it != preds.end();)
        {
            Term* pred = *it;

            if (pred->duplicate || pred->label.empty())
            {
                it = preds.erase(it); // returns next iterator
            }
            else
            {
                ++it;
            }
        }
    }
}

struct Identity
{
    std::string lhs;
    std::string rhs;
};

EquivalenceClass* find(std::map<std::string, EquivalenceClass>& eq, const std::string& term)
{
    auto it = eq.find(term);
    if (it == eq.end())
    {
        return nullptr;
    }
    return it->second.getTop();
}
bool congruent(Term* t1, Term* t2, std::map<std::string, EquivalenceClass>& eq)
{
    if (t1->label == t2->label)
    {
        for (int i = 0; i < t1->children.size(); i++)
        {
            if (find(eq, t1->children[i]->term_str) != find(eq, t2->children[i]->term_str))
            {
                return false;
            }
        }
        return true;
    }
    return false;
}

bool merge(const std::string& lhs, const std::string& rhs, std::map<std::string, EquivalenceClass>& eq)
{
    // find representatives
    auto lhs_eq_it = eq.find(lhs);
    auto rhs_eq_it = eq.find(rhs);
    if (lhs_eq_it == eq.end() || rhs_eq_it == eq.end())
    {
        return false;
    }
    auto lhs_eq = lhs_eq_it->second.getTop();
    auto rhs_eq = rhs_eq_it->second.getTop();

    auto preds_lhs = lhs_eq->preds;
    auto preds_rhs = rhs_eq->preds;
    lhs_eq->attachTo(rhs_eq);

    for (auto pred_lhs : preds_lhs)
    {
        for (auto pred_rhs : preds_rhs)
        {
            if (pred_lhs != pred_rhs && congruent(pred_lhs, pred_rhs, eq))
            {
                merge(pred_lhs->term_str, pred_rhs->term_str, eq);
            }
        }
    }
    return true;
}

bool match(Term* templ, Term* node, std::map<std::string, Term*>& args, std::map<std::string, EquivalenceClass>& nodes)
{
    if (templ->label[0] == '~')
    {
        auto arg = args.find(templ->label);
        if (arg == args.end())
        {
            args.emplace(templ->label, node);
            return true;
        }
        auto cl_arg = find(nodes, arg->second->term_str);
        auto cl_node = find(nodes, node->term_str);
        if (!cl_arg || cl_arg != cl_node)
        {
            return false;
        }
        return true;
    }
    if (templ->label != node->label)
    {
        return false;
    }
    for (int i = 0; i < node->children.size(); ++i)
    {
        if (!match(templ->children[i].get(), node->children[i].get(), args, nodes))
        {
            return false;
        }
    }
    return true;
}

struct Arg
{
    Term* term = nullptr;
    int node_id = 0;
};

void rewrite(Term* templ_to, std::map<std::string, Arg>& args, std::string& res)
{
    if (templ_to->label[0] == '~')
    {
        auto arg = args.find(templ_to->label);
        if (arg == args.end())
        {
            res += templ_to->label;
        }
        else
        {
            res += arg->second.term->term_str;
        }
        return;
    }
    res += templ_to->label;
    if (!templ_to->children.empty())
    {
        res += '(';
        for (auto& ch : templ_to->children)
        {
            rewrite(ch.get(), args, res);
            res += ',';
        }
        res.back() = ')';
    }
}
class Matcher
{
public:
    Matcher(std::map<std::string, EquivalenceClass>& eq)
        : eq(eq)
    {
    }

    struct CompareStackEl
    {
        int parent_id = 0;
        int child_id = 0;
        Term* lhs = nullptr;
        Term* rhs = nullptr;
        EquivalenceClass* rhs_eq = nullptr;
        int eq_id = 0;
    };

    bool match(Term* lhs, Term* rhs)
    {
        CompareStackEl comp_stack_el;
        comp_stack_el.lhs = lhs;
        comp_stack_el.rhs = rhs;
        comp_stack_el.rhs_eq = find(eq, comp_stack_el.rhs->term_str);
        comp_stack_el.rhs = comp_stack_el.rhs_eq->representatives.front()->representative;
        comp_stack_el.parent_id = -1;
        comp_stack.push_back(comp_stack_el);

        while (true)
        {
            CompareStackEl& st_el = comp_stack.back();
            lhs = st_el.lhs;
            rhs = st_el.rhs;
            auto lhs_cl = find(eq, lhs->term_str);
            auto rhs_cl = find(eq, rhs->term_str);

            if (lhs_cl && lhs_cl == rhs_cl)
            {
                // compared subtrees by equivalence class
                // go to the next node
                if (!stepNext())
                {
                    return true;
                }
            }
            else if (lhs->label[0] == '~')
            {
                auto found_arg = args.find(lhs->label);
                if (found_arg == args.end())
                {
                    Arg new_arg;
                    new_arg.node_id = comp_stack.size();
                    new_arg.term = rhs;
                    args.emplace(lhs->label, new_arg);
                }
                else
                {
                    lhs_cl = find(eq, found_arg->second.term->term_str);
                    if (!lhs_cl || lhs_cl != rhs_cl)
                    {
                        if (!stepBack())
                        {
                            return false;
                        }
                        continue;
                    }
                }
                if (!stepNext())
                {
                    return true;
                }
            }
            else if (comp_stack.back().lhs->label != comp_stack.back().rhs->label)
            {
                if (!stepBack())
                {
                    return false;
                }
            }
            else
            {
                if (!stepIn())
                {
                    return true;
                }
            }
        }
        return false;
    }

    // false means we finished comparisson
    bool stepNext()
    {
        auto parent_id = comp_stack.back().parent_id;
        while (parent_id >= 0)
        {
            if (comp_stack[parent_id].child_id < int(comp_stack[parent_id].rhs->children.size()) - 1)
            {
                comp_stack[parent_id].child_id++;
                CompareStackEl comp_stack_el;
                comp_stack_el.lhs = comp_stack[parent_id].lhs->children[comp_stack[parent_id].child_id].get();
                comp_stack_el.rhs = comp_stack[parent_id].rhs->children[comp_stack[parent_id].child_id].get();
                comp_stack_el.rhs_eq = find(eq, comp_stack_el.rhs->term_str);
                comp_stack_el.rhs = comp_stack_el.rhs_eq->representatives.front()->representative;
                comp_stack_el.parent_id = parent_id;
                comp_stack.push_back(comp_stack_el);
                return true;
            }
            parent_id = comp_stack[parent_id].parent_id;
        }
        return false;
    }
    // false means we successfully finished comparisson
    bool stepIn()
    {
        auto& top = comp_stack.back();
        if (top.lhs->children.empty())
        {
            return stepNext();
        }
        CompareStackEl comp_stack_el;
        comp_stack_el.lhs = top.lhs->children[top.child_id].get();
        comp_stack_el.rhs = top.rhs->children[top.child_id].get();
        comp_stack_el.rhs_eq = find(eq, comp_stack_el.rhs->term_str);
        comp_stack_el.rhs = comp_stack_el.rhs_eq->representatives.front()->representative;
        comp_stack_el.parent_id = comp_stack.size() - 1;
        comp_stack.push_back(comp_stack_el);
        return true;
    }
    // false means all equivalence classes are over
    // true - we can continue comparing
    bool stepBack()
    {
        for (int i = int(comp_stack.size()) - 1; i >= 0; i--)
        {
            if (comp_stack[i].eq_id < int(comp_stack[i].rhs_eq->representatives.size()) - 1)
            {
                comp_stack[i].eq_id++;
                comp_stack[i].rhs = comp_stack[i].rhs_eq->representatives[comp_stack[i].eq_id]->representative;
                comp_stack[i].child_id = 0;

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
            if (comp_stack[i].parent_id >= 0)
            {
                comp_stack[comp_stack[i].parent_id].child_id--;
            }
            comp_stack.pop_back();
        }
        return false;
    }

    void pringArgs()
    {
        std::cout << "--------------Result-------------\n"
            << "Args : \n";
        for (auto arg : args)
        {
            std::cout << arg.first << " = " << arg.second.term->term_str << '\n';
        }
    }
    std::vector<CompareStackEl> comp_stack;
    std::map<std::string, EquivalenceClass>& eq;
    std::map<std::string, Arg> args;
};

void generateIdentities(const Identity& templ, std::map<std::string, EquivalenceClass>& nodes, std::vector<std::unique_ptr<Term>>& terms, int id_i)
{
    Parser pr;
    std::string all_terms;
    all_terms += templ.lhs + "," + templ.rhs;
    auto res = pr.start(all_terms);
    std::map<std::string, std::string> identities;
    int terms_size_old = terms.size();
    for (auto& node : nodes)
    {
        if (node.second.identitites_hold.contains(id_i))
        {
            continue;
        }
        if (node.second.representative->templ || node.second.representatives.empty())
        {
            continue;
        }
        std::map<std::string, Term*> args;
        Matcher mc(nodes);
        if (mc.match(res[0].get(), node.second.representative))
        {
            node.second.identitites_hold.insert(id_i);
            std::string lhs_str;
            rewrite(res[1].get(), mc.args, lhs_str);
            if (lhs_str == node.second.representative->term_str)
            {
                continue;
            }
            auto pair = identities.emplace(node.second.representative->term_str, lhs_str);
            Parser pr2;
            auto new_term = pr2.start(pair.first->second);
            terms.push_back(std::move(new_term.back()));
        }
    }
    for (int i = terms_size_old; i < terms.size(); ++i)
    {
        collectNode(terms[i].get(), nodes);
    }
    removeDuplicatePreds(nodes);
    for (auto pair : identities)
    {
        if (pair.first == pair.second)
        {
            continue;
        }
        merge(pair.first, pair.second, nodes);
    }
}

void makeTemplate(Term* term, bool& has_var)
{
    bool has_var_temp = false;
    for (auto& child : term->children)
    {
        makeTemplate(child.get(), has_var_temp);
    }
    if (term->label[0] == L'~')
    {
        has_var_temp = true;
    }
    if (has_var_temp)
    {
        term->templ = true;
    }
    has_var = has_var_temp;
}

int main()
{

    Parser pr;
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

    std::string lhs = "+(*(2,*(~a,~b)),+(*(~a,~a),*(~b,~b)))";//2ab + a*a + b*b
    std::string rhs = "p(+(*(a,b),e),2)";//(e+a)^2

    std::cout << "Check equality: " << lhs << " = " << rhs << '\n';
    std::cout << "Identities: \n";
    for (auto& id : identities)
    {
        std::cout << id.lhs << " = " << id.rhs << '\n';
    }
    std::string all_terms;
    all_terms += lhs + "," + rhs;
    std::vector<std::unique_ptr<Term>> res = pr.start(all_terms);
    auto lhs_term = res[0].get();
    auto rhs_term = res[1].get();

    bool has_var = false;
    makeTemplate(lhs_term, has_var);
    std::map<std::string, EquivalenceClass> nodes;
    collectNodes(res, nodes);
    bool res1 = false;
    for (int i = 0; i < 15; i++)
    {
        int id_i = 0;
        for (auto& id : identities)
        {
            generateIdentities(id, nodes, res, id_i);
            Matcher mc(nodes);
            if (mc.match(lhs_term, rhs_term))
            {
                mc.pringArgs();
                res1 = true;
                break;
            }
            id_i++;
        }
        std::cout << (res1 ? "-----------------------Found \n" : "");
        if (res1)
        {
            break;
        }
    }
    std::cout << '\n';

    for (auto nd : nodes)
    {
        if (nd.second.representative->templ)
        {
            continue;
        }
        std::cout << nd.first << "\n";
        /*for (auto& ch : nd.second.representatives)
        {
            std::cout << nd.first << "  " << ch->representative->term_str << '\n';
        }*/
    }

    return 0;
}