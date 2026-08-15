#include "Class.h"
#include <iostream>
#include <chrono>
namespace NewTrs
{
	void Trs::run()
	{
		struct StrId
		{
			std::string lhs;
			std::string rhs;
		};

		std::vector<StrId> identities = {
		{"+(`a,`b)", "+(`b,`a)"},
		{"+(+(`a,`b),`c)", "+(`a,+(`b,`c))"},
		{"+(`a,+(`b,`c))", "+(+(`a,`b),`c)"},
		{"*(`a,`b)", "*(`b,`a)"},
		{"*(*(`a,`b),`c)", "*(`a,*(`b,`c))"},
		{"*(`a,*(`b,`c))", "*(*(`a,`b),`c)"},
		{"p(`a,2)", "*(`a,`a)"},
		{"*(`a,`a)","p(`a,2)"},
		{"*(+(`a,`b),`c)", "+(*(`a,`c),*(`b,`c))"},
		{"+(*(`a,`c),*(`b,`c))","*(+(`a,`b),`c)"},
		{"+(`a,`a)", "*(2,`a)"},
		};

		std::string lhs = "p(+(`a,`a),2)";//*(a*(a,b),b)
		std::string rhs = "+(p(*(a,+(b,c)),2),+(p(*(a,+(b,c)),2),*(2,*(*(+(b,c),a),*(a,+(c,b))))))";//(e+a)^2

		std::cout << "Find solution: \n";
		std::cout << lhs << " = " << rhs << "\n\n";
		std::cout << "Identities: \n";

		for (auto id : identities)
		{
			std::cout << id.lhs << " = " << id.rhs << "\n";
		}
		std::cout << "\n";

		{
			Parser pr(lhs);
			pr.parse();
			compact(pr.m_current_term);
			m_id.lhs = pr.m_current_term;
			m_id.lhs->persistent = true;
			m_id.variablesOrder = setupVariablesOrder(m_id.lhs);
			markPatternNodes(m_id.lhs);
			initCompOrder(m_id.lhs);
		}

		{
			Parser pr(rhs);
			pr.parse();
			compact(pr.m_current_term);
			m_id.rhs = pr.m_current_term;
			m_id.rhs->persistent = true;
		}

		for (auto& id : identities)
		{
			auto& newId = m_ids.emplace_back();
			{
				Parser pr(id.lhs);
				pr.parse();
				compact(pr.m_current_term);
				newId.lhs = pr.m_current_term;
				newId.lhs->persistent = true;
				newId.variablesOrder = setupVariablesOrder(newId.lhs);
				markPatternNodes(newId.lhs);
				initCompOrder(newId.lhs);
			}

			{
				Parser pr(id.rhs);
				pr.parse();
				compact(pr.m_current_term);
				newId.rhs = pr.m_current_term;
				newId.rhs->persistent = true;
				markPatternNodes(newId.rhs);
			}
		}
		struct NewIdentity
		{
			Term* lhs = nullptr;
			Term* rhs = nullptr;
		};
		auto start = std::chrono::high_resolution_clock::now();
		for (int i = 0; i < 7; ++i)
		{
			std::vector<NewIdentity> newIdentities;
			for (auto& id : m_ids)
			{
				for (auto& [str, trm] : m_storage)
				{
					if (trm->isPat)
					{
						continue;
					}
					if (trm->eRep != trm.get())
					{
						continue;
					}
					Matcher matcher(id.variablesOrder);
					if (matcher.match(id.lhs, trm.get()))
					{
						matcher.genSub([this, &newIdentities, &id, &trm]()
							{
								Term* newTerm = nullptr;
								Trs::rewrite(id.rhs, newTerm);
								newIdentities.emplace_back(trm.get(), newTerm);
							});
					}
				}

			}
			for (auto& newId : newIdentities)
			{
				generateTermStr(newId.rhs);
				updateCongruence(newId.rhs);
				setupParent(newId.rhs);
				if (find(newId.lhs) != find(newId.rhs))
				{
					merge(newId.lhs, newId.rhs);
				}
			}
			for (auto* t : m_cong)
			{
				if (find(t)->eReps.size() > 1)
				{
					remove(t);
				}
			}
			m_cong.clear();
			{
				Matcher matcher(m_id.variablesOrder);
				if (matcher.match(m_id.lhs, m_id.rhs))
				{

					std::cout << "SUCCEDED\n";
					auto end = std::chrono::high_resolution_clock::now();

					auto duration =
						std::chrono::duration<double, std::milli>(end - start);

					std::cout << duration.count() << " ms\n";
					matcher.genSub([this]()
						{
							std::cout << "===";
							std::cout << m_id.lhs->termString << "->" << m_id.rhs->termString << "\n";
							Trs::printVars(m_id.lhs);

							//Term* newTerm = nullptr;
							//Trs::rewrite(id.rhs, newTerm);
							//newIdentities.emplace_back(trm.get(), newTerm);
						});

					for (auto& el : m_storage)
					{
						if (el.second->eRep == el.second.get())
						{
							auto& reps = el.second->eReps;
							for (int i = 0; i < reps.size(); ++i)
							{
								for (int j = i + 1; j < reps.size(); ++j)
								{
									if (cong(reps[i], reps[j]))
									{
										std::cout << reps[i]->termString << "=== " << reps[j]->termString << "\n";
									}
								}
							}
						}
					}
					return;
				}
			}

		}
		for (auto& el : m_storage)
		{
			if (el.second->eRep == el.second.get())
			{
				auto& reps = el.second->eReps;
				for (int i = 0; i < reps.size(); ++i)
				{
					for (int j = i + 1; j < reps.size(); ++j)
					{
						if (cong(reps[i], reps[j]))
						{
							std::cout << reps[i]->termString << "=== " << reps[j]->termString << "\n";
						}
					}
				}
			}
		}

	}
	bool Trs::cong(Term* t1, Term* t2)
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
	void Trs::unionTerms(Term* t1, Term* t2)
	{
		//move t1 into t2
		auto* topT1 = find(t1);
		auto* topT2 = find(t2);
		topT1->eRep = topT2;
		topT2->eReps.insert(topT2->eReps.end(), topT1->eReps.begin(), topT1->eReps.end());
		topT2->parents.merge(topT1->parents);
		topT1->parents.clear();
		topT1->eReps.clear();
	}

	void Trs::remove(Term* tToRemove)
	{
		auto tTop = find(tToRemove);
		//remove from reps
		std::erase(tTop->eReps, tToRemove);

		if (tTop == tToRemove)
		{
			//want to remove top
			//find new top
			Term* newTop = *tTop->eReps.begin();
			for (Term* rep : tTop->eReps)
			{
				//set new top for reps
				rep->eRep = newTop;
			}
			//move all information to the newTop
			newTop->eReps = std::move(tTop->eReps);
			newTop->parents = std::move(tTop->parents);
			tTop = newTop;
		}
		else
		{
			for (Term* rep : tTop->eReps)
			{
				//set new top for reps
				rep->eRep = tTop;
			}
		}

		//replace itself in parents with the newTop
		for (Term* parent : tTop->parents)
		{
			for (Term*& sibling : parent->children)
			{
				if (sibling == tToRemove)
				{
					sibling = tTop;
				}
			}
		}
		//replace remove itself from parents
		for (Term* child : tToRemove->children)
		{
			find(child)->parents.erase(tToRemove);
		}
		m_storage.erase(tToRemove->termString);
	}

	void Trs::mergeCong(Term* t1, Term* t2)
	{
		//collect congruent
		if (t1->persistent && !t2->persistent)
		{
			m_cong.insert(t2);
		}
		else if (!t1->persistent && t2->persistent)
		{
			m_cong.insert(t1);
		}
		else if (!t1->persistent)
		{
			m_cong.insert(t1);
		}

		//if they are congruent but in the same e-class
		//all their parents already were congruent at this point
		if (find(t1) == find(t2))
		{
			return;
		}
		auto parents1 = find(t1)->parents;
		auto parents2 = find(t2)->parents;
		unionTerms(t1, t2);
		for (auto* parent1 : parents1)
		{
			for (auto* parent2 : parents2)
			{
				if (parent1 != parent2 && cong(parent1, parent2))
				{
					mergeCong(parent1, parent2);
				}
			}
		}
	}

	void Trs::merge(Term* t1, Term* t2)
	{
		auto parents1 = find(t1)->parents;
		auto parents2 = find(t2)->parents;
		//t1.eReps !cong t2.eReps
		unionTerms(t1, t2);

		for (auto* parent1 : parents1)
		{
			for (auto* parent2 : parents2)
			{
				if (parent1 != parent2 && cong(parent1, parent2))
				{
					mergeCong(parent1, parent2);
				}
			}
		}
	}

	void Trs::compact(Term*& t)
	{
		if (t->stored)
		{
			return;
		}
		auto [it, inserted] = m_storage.emplace(t->termString, t);
		if (!inserted)
		{
			it->second->parents.merge(t->parents);
			deleteRec(t);
			t = it->second.get();
			//element already in the map, therefore its children are as well
			return;
		}
		else
		{
			it->second->stored = true;
			for (auto*& ch : t->children)
			{
				compact(ch);
			}
		}
	}

	void Trs::setupParent(Term* t, Term* parent)
	{
		if (parent)
		{
			find(t)->parents.insert(parent);
		}
		for (Term* ch : t->children)
		{
			setupParent(ch, t);
		}
	}

	Term* Trs::find(Term* t)
	{
		while (t->eRep != t)
		{
			t = t->eRep;
		}
		return t;
	}

	std::map<std::vector<int>, int> Trs::setupVariablesOrder(Term* t)
	{
		std::map<std::vector<int>, int> res;
		std::vector<int> path = { 0 };
		int id = 0;
		setupVariablesOrder(t, path, id, res);
		return res;
	}

	void Trs::setupVariablesOrder(Term* t, std::vector<int>& pos, int& id, std::map<std::vector<int>, int>& res)
	{
		if (t->isVariable)
		{
			res[pos] = id;
			++id;
			return;
		}
		for (int i = 0; i < t->children.size(); ++i)
		{
			pos.push_back(i);
			setupVariablesOrder(t->children[i], pos, id, res);
			pos.pop_back();
		}
	}

	void Trs::printVars(Term* t)
	{
		if (t->isVariable)
		{
			std::cout << t->termString << " = " << t->capture->termString << "\n";
			return;
		}
		for (auto* ch : t->children)
		{
			printVars(ch);
		}
	}

	void Trs::rewrite(Term* t, Term*& res)
	{
		if (t->isVariable)
		{
			res = t->capture;
			return;
		}
		res = new Term;
		res->label = t->label;
		res->eRep = res;
		res->eReps.push_back(res);

		for (Term* ch : t->children)
		{
			Term*& newCh = res->children.emplace_back();
			rewrite(ch, newCh);
		}
	}

	void Trs::markPatternNodes(Term* t)
	{
		bool pat_temp = false;
		for (auto ch : t->children)
		{
			markPatternNodes(ch);
			pat_temp |= ch->isPat;
		}
		if (pat_temp)
		{
			t->isPat = true;
			return;
		}
		if (t->isVariable)
		{
			t->isPat = true;
		}
	}

	void Trs::deleteRec(Term* t)
	{
		if (t->stored)
		{
			return;
		}
		for (auto* ch : t->children)
		{
			deleteRec(ch);
		}
		delete t;
	}

	bool Trs::updateCongruence(Term*& t)
	{
		if (t->stored)
		{
			return false;
		}
		bool createdNewTerm = false;
		for (Term*& ch : t->children)
		{
			if (updateCongruence(ch))
			{
				t->stored = true;
				m_storage.emplace(t->termString, t);
				createdNewTerm = true;
			}
		}
		if (createdNewTerm)
		{
			return true;
		}

		auto found = m_storage.find(t->termString);
		if (found != m_storage.end())
		{
			delete t;
			t = found->second.get();
			//element already in the map, therefore its children are as well
			return false;
		}
		if (t->children.empty())
		{
			t->stored = true;
			m_storage.emplace(t->termString, t);
			return true;
		}
		auto* ch = t->children.back();
		auto& siblings = find(ch)->parents;
		for (Term* sib : siblings)
		{
			if (cong(sib, t))
			{
				delete t;
				t = sib;
				return false;
			}
		}
		t->stored = true;
		m_storage.emplace(t->termString, t);
		return true;
	}

	inline void Trs::generateTermStr(Term* t)
	{
		if (!t->termString.empty())
		{
			return;
		}
		t->termString = t->label;
		if (t->children.empty())
		{
			return;
		}
		t->termString += "(";
		for (int i = 0; i < t->children.size(); ++i)
		{
			auto* ch = t->children[i];
			generateTermStr(ch);
			t->termString += ch->termString;
			if (i != t->children.size() - 1)
			{
				t->termString += ',';
			}
		}
		t->termString += ")";
	}

	void Trs::initCompOrder(Term* t)
	{
		for (Term* ch : t->children)
		{
			initCompOrder(ch);
		}

		for (int i = 0; i < t->children.size(); ++i)
		{
			if (!t->children[i]->isPat)
			{
				t->compOrder.push_back(i);
			}
		}
		for (int i = 0; i < t->children.size(); ++i)
		{
			if (t->children[i]->isVariable)
			{
				t->compOrder.push_back(i);
			}
		}
		for (int i = 0; i < t->children.size(); ++i)
		{
			if (t->children[i]->isPat && !t->children[i]->isVariable)
			{
				t->compOrder.push_back(i);
			}
		}
	}

	void Parser::parse()
	{
		while (m_pos != m_str.size())
		{
			int term_start = m_pos;
			consumeTermName();
			int label_end = m_pos;
			auto t = new Term();
			t->eReps.push_back(t);
			t->eRep = t;
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
			if (m_current_term->label[0] == '`')
			{
				m_current_term->isVariable = true;
			}
			m_current_term->termString = m_str.substr(term_start, m_pos - term_start);
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
	void Parser::consumeTermName()
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

	bool Matcher::match(Term* pat, Term* subj, int pos)
	{
		m_path.posPath.push_back(pos);
		m_path.repPath.push_back(0);
		if (!pat->isPat)
		{
			bool res = Trs::find(pat) == Trs::find(subj);
			m_path.posPath.pop_back();
			m_path.repPath.pop_back();
			return res;
		}
		if (pat->isVariable)
		{
			bool res = addSub(&m_subRoot, m_path, pat, subj, getVarId(m_path.posPath));
			m_path.posPath.pop_back();
			m_path.repPath.pop_back();
			return res;
		}

		auto& reps = Trs::find(subj)->eReps;
		bool repSucceded = false;
		for (auto* rep : reps)
		{
			if (pat->label != rep->label)
			{
				continue;
			}
			bool result = true;
			auto& compOrder = pat->compOrder;
			for (int i = 0; i < compOrder.size(); ++i)
			{
				if (!match(pat->children[compOrder[i]], rep->children[compOrder[i]], compOrder[i]))
				{
					result = false;
				}
			}
			/*for (int i = 0; i < pat->children.size(); ++i)
			{
				if (!match(pat->children[i], rep->children[i], i))
				{
					result = false;
				}
			}*/
			repSucceded |= result;
			m_path.repPath.back()++;
		}
		m_path.posPath.pop_back();
		m_path.repPath.pop_back();
		return repSucceded;
	}

	bool Matcher::addSub(Sub* sub, const Path& path, Term* var, Term* subj, int id)
	{
		if (id == 0)
		{
			auto& newSub = sub->next.emplace_back();
			newSub.path = path;
			newSub.subj = subj;
			newSub.var = var;
			return true;
		}
		for (auto& next : sub->next)
		{
			if (next.var == var && Trs::find(next.subj) != Trs::find(subj))
			{
				continue;
			}
			if (!pathsCompatible(next.path, path))
			{
				continue;
			}
			return addSub(&next, path, var, subj, id - 1);
		}
		return false;
	}

	bool Matcher::pathsCompatible(const Path& p1, const Path& p2)
	{
		for (int i = 0; i < std::min(p1.posPath.size(), p2.posPath.size()); ++i)
		{
			if (p1.posPath[i] == p2.posPath[i])
			{
				if (p1.repPath[i] != p2.repPath[i])
				{
					return false;
				}
			}
			else
			{
				return true;
			}
		}
		return true;
	}

	int Matcher::getVarId(const std::vector<int>& posPath)
	{
		return m_variablesOrder.find(posPath)->second;
	}

	void Matcher::genSub(Sub* sub, const std::function<void()>& callback, int depth)
	{
		for (auto& next : sub->next)
		{
			next.var->capture = next.subj;
			if (depth == m_variablesOrder.size() - 1)
			{
				callback();
			}
			else
			{
				genSub(&next, callback, depth + 1);
			}
		}
	}

	void Matcher::genSub(const std::function<void()>& callback)
	{
		genSub(&m_subRoot, callback);
	}

}
