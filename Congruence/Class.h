#pragma once
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <memory>
#include <map>
#include <functional>

namespace NewTrs
{
	struct Term
	{
		bool stored = false;
		std::string label;
		std::string termString;
		std::vector<Term*> children;
		std::vector<Term*> eReps;
		Term* eRep = nullptr;
		std::unordered_set<Term*> parents;
		bool isVariable = false;
		bool isPat = false;
		bool deleteByCong = false;
		Term* capture = nullptr;
		//term is used in identities
		bool persistent = false;
		std::vector<int> compOrder;
	};

	class Parser
	{
	public:
		Parser(const std::string& str)
			: m_str(str)
		{
		}

		void parse();

		void consumeTermName();

		Term* m_current_term = nullptr;
		Term* m_parent_term = nullptr;
		const std::string& m_str;
		int m_pos = 0;
	};

	struct Identity
	{
		std::map<std::vector<int>, int> variablesOrder;
		std::unordered_set<Term*> variables;
		Term* lhs = nullptr;
		Term* rhs = nullptr;
	};

	class Matcher
	{
		struct Path
		{
			std::vector<int> posPath;
			std::vector<int> repPath;
		};
		struct Sub
		{
			Term* var = nullptr;
			Term* subj = nullptr;
			std::vector<Sub> next;
			Path path;
		};

	public:
		Matcher(const std::map<std::vector<int>, int>& variablesOrder)
			:m_variablesOrder(variablesOrder)
		{

		}
		bool match(Term* pat, Term* subj, int pos = 0);
		bool addSub(Sub* sub, const Path& path, Term* var, Term* subj, int id);
		bool pathsCompatible(const Path& p1, const Path& p2);
		int getVarId(const std::vector<int>& posPath);
		void genSub(const std::function<void()>& callback);
	private:
		void genSub(Sub* sub, const std::function<void()>& callback, int depth = 0);
		Path m_path;
		Sub m_subRoot;
		const std::map<std::vector<int>, int>& m_variablesOrder;
	};

	class Trs
	{
	public:
		void run();
		bool cong(Term* t1, Term* t2);
		void unionTerms(Term* t1, Term* t2);
		void remove(Term* t1);
		void mergeCong(Term* t1, Term* t2);
		void merge(Term* t1, Term* t2);
		void compact(Term*& t);
		void setupParent(Term* t, Term* parent = nullptr);
		void markPatternNodes(Term* t);
		void deleteRec(Term* t);
		//returns true if created new term(not equal and not congruent to other terms)
		//this would imply that all parent terms also will be unique
		bool updateCongruence(Term*& t);
		void generateTermStr(Term* t);
		void initCompOrder(Term* t);
		static Term* find(Term* t);
		static std::map<std::vector<int>, int> setupVariablesOrder(Term* t);
		static void setupVariablesOrder(Term* t, std::vector<int>& pos, int& id, std::map<std::vector<int>, int>& res);
		static void printVars(Term* t);
		static void rewrite(Term* t, Term*& res);
		Identity m_id;
		std::vector<Identity> m_ids;
		std::map<std::string, std::unique_ptr<Term>> m_storage;

		std::unordered_set<Term*> m_cong;
	};
}