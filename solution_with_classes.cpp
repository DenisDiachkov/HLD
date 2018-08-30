#pragma comment(linker, "/STACK:10000000000")
#include <vector>
#include <map>
#include <cstdio>
#include <cmath>
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <set>
#include <sstream>
#include <functional>
#include <iterator>
#include <random>
#include <list>
#include <queue>
#include <cstdlib>
#include <string>
#include <memory.h>
#include <cstdint>
#include <unordered_map>
#include <unordered_set>
#include <cassert>
#include <bitset>
#include <fstream>
#include <deque>
#include <cmath>
#include <numeric>
#include <stack>
#include <stdarg.h>
using namespace std;
#pragma region custom templates
#define break(x)    {x;break;}
#define continue(x) {x;continue;}
#define _sort(x)    sort(x.begin(), x.end())
#define r_sort(x)   sort(x.rbegin(), x.rend())
#define INT_INFINITY 2'000'000'000
typedef long long ll;
typedef unsigned long long ull;
typedef long double ld;
const ll MOD = 1000000007LL;
enum class START_OPTION {NOTHING=0, FILE_INPUT=1, FILE_OUTPUT=2, FILE_OUTHERE = 4};

inline                             START_OPTION operator|   (START_OPTION a, START_OPTION b)
{
	return static_cast<START_OPTION>(static_cast<int>(a) | static_cast<int>(b));
}
inline                             int          operator&   (START_OPTION a, START_OPTION b)
{
	return static_cast<int>(a) & static_cast<int>(b);
}


template<typename T>               istream&     operator>>  (istream&i, vector<T>&v)
{
	for (auto&e : v)i >> e;
	return i;
}
template<typename T>               ostream&	    operator<<  (ostream&i, vector<T>&v)
{
	for (auto&e : v)i << e << " ";
	return i;
}
template<typename T1, typename T2> istream&     operator>>  (istream&i, vector<pair<T1, T2>>&v)
{
	for (auto&e : v)i >> e.first >> e.second;
	return i;
}
template<typename T1, typename T2> ostream&     operator<<  (ostream&i, vector<pair<T1, T2>>&v)
{
	for (auto&e : v)i << e.first << " " << e.second << endl;
	return i;
}
								   void			readUndirGraph  (int n, int w, vector<vector<int> >&v)
								   {
									   v = vector<vector<int> >(n + 1LL);
									   while (w--)
									   {
										   int x, y; 
										   cin >> x >> y;
										   v[x].push_back(y);
										   v[y].push_back(x);
									   }
								   }

								   bool         isVowel     (char x)
{
	return x == 'a' || x == 'e' || x == 'o' || x == 'u' || x == 'i';
}
								   bool         isConsonant (char x) 
{
	return !isVowel(x);
}


								   void         _start      (START_OPTION opt = START_OPTION::NOTHING, string fileIn = "input.txt", string fileOut = "output.txt")
{
#ifdef LOCAL_FREOPEN
	if (opt & START_OPTION::FILE_INPUT)  freopen(fileIn.c_str(), "r", stdin);
	if (opt & START_OPTION::FILE_OUTPUT) freopen(fileOut.c_str(), "w", stdout);
#endif
	if ((opt & START_OPTION::FILE_OUTHERE) && (opt & START_OPTION::FILE_INPUT))  freopen(fileIn.c_str(), "r", stdin);
	if ((opt & START_OPTION::FILE_OUTHERE) && (opt & START_OPTION::FILE_OUTPUT)) freopen(fileOut.c_str(), "w", stdout);
	cin.sync_with_stdio(false);
	cout.sync_with_stdio(false);
	cin.tie(0);
}
template<typename T>               void         _end        (T out, int returnValue = 0)
{
	cout << out;
#ifdef LOCAL_FREOPEN
	cerr << endl << "Time elapsed: " << 1.0 * clock() / CLOCKS_PER_SEC * 1000 << " ms." << endl;
#endif
	exit(returnValue);
}
template<typename T>
class SegmentTree
{
private:
	vector<T> tree, //Segment tree 
			  mem_add,//Data for pushing adding
			  mem_change;  //Data for pushing changing
	vector<bool> is_mem_change; //Data to find out is there pushing changing
	int n;			//Array size
	string string_f; //String name for binary function(max, min, sum)
	
	//Calculate max or min or sum
	T  f(T a, T b)
	{
		if (string_f == "max")
			return a > b ? a : b;
		else if (string_f == "min")
			return a < b ? a : b;
		else if (string_f == "sum")
			return a + b;
		else throw("segment tree has wrong func");
	}
	//Push data of mem_add down
	void push_add(int idx)
	{
		if (mem_add[idx] == 0) return;
		tree[idx] += mem_add[idx];
		if (mem_add.size() > idx << 1) mem_add[idx << 1] += mem_add[idx];
		if (mem_add.size() > (idx << 1) + 1) mem_add[(idx << 1) + 1] += mem_add[idx];
		mem_add[idx] = 0;
	}
	//Push data of mem_change down
	void push_change(int idx)
	{
		if (!is_mem_change[idx]) return;
		tree[idx] = mem_change[idx];
		if (mem_change.size() > idx << 1) mem_change[idx << 1] = mem_change[idx];
		if (mem_change.size() > (idx << 1) + 1) mem_add[(idx << 1) + 1] = mem_change[idx];
		is_mem_change[idx] = 0;
	}
	//Default vals for every f
	T val_default()
	{
		if (string_f == "sum") return 0;
		if (string_f == "max") return -INT_INFINITY;
		if (string_f == "min") return INT_INFINITY;
	}
public:
	//Query to change element of array
	T changePos(int pos, T val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		push_add(idx);
		push_change(idx);
		if (tl == tr)
			return tree[idx] = val;
		int m = (tl + tr) >> 1;
		if (pos <= m)
			return tree[idx] = f(changePos(pos, val, tl, m, idx << 1), tree[(idx << 1) + 1]);
		else return tree[idx] = f(changePos(pos, val, m + 1, tr, (idx << 1) + 1), tree[idx << 1]);
	}
	//Query to increase element of array
	T incPos(int pos, T val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		push_add(idx);
		push_change(idx);
		if (tl == tr)
		{
			tree[idx] += val;
			return tree[idx];
		}
		int m = (tl + tr) >> 1;
		if (pos <= m)
			return tree[idx] = f(incPos(pos, val, tl, m, idx << 1), tree[(idx << 1) + 1]);
		else return tree[idx] = f(incPos(pos, val, m + 1, tr, (idx << 1) + 1), tree[idx << 1]);
	}
	//Query to get f on segment l-r
	T get(int l, int r, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		push_add(idx);
		push_change(idx);
		if (tl > r || tr < l)
			return val_default();
		int m = (tl + tr) >> 1;
		if (tl >= l && tr <= r)
			return tree[idx];
		return f(get(l, r, tl, m, idx << 1), get(l, r, m + 1, tr, (idx << 1) + 1));
	}
	//Query to change all elements on segment l-r
	T changeSegment(int l, int r, T val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		push_add(idx);
		push_change(idx);
		if (tl > r || tr < l)
			return tree[idx];
		int m = (tl + tr) >> 1;
		if (tl >= l && tr <= r)
		{
			mem_change[idx] = val;
			is_mem_change[idx] = true;
			push_change(idx);
			return tree[idx];
		}
		else return tree[idx] = f(incSegment(l, r, val, tl, m, idx << 1), incSegment(l, r, val, m + 1, tr, (idx << 1) + 1));
	}
	//Query to increase all elements on segment l-r
	T incSegment(int l, int r, T val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		push_add(idx);
		push_change(idx);
		if (tl > r || tr < l)
			return tree[idx];
		int m = (tl + tr) >> 1;
		if (tl >= l && tr <= r)
		{
			mem_add[idx] = val;
			push_add(idx);
			return tree[idx];
		}
		else return tree[idx] = f(incSegment(l, r, val, tl, m, idx << 1), incSegment(l, r, val, m + 1, tr, (idx << 1) + 1));
	}
	//constructor
	SegmentTree(const vector<T> &mas, const string &string_f, bool emptyArr=0)
	{
		this->string_f = string_f;
		n = mas.size();
		tree = mem_add = mem_change = vector<T>(n << 2);
		is_mem_change = vector<bool>(n << 2);
		if(!emptyArr)
			for (int i = 0; i < n; i++)
				changePos(i, mas[i]);
	}
	SegmentTree() {}
};
class LCA
{
private:
	vector<int> tin, //Time in of vertex
				tout; //Time out of vertex
	vector<vector<int> > ancs; //1, 2, 4, and so on ancestors list for every vertex 
	//LCA Preprocessing
	int timer = 1; 
	void LCA_prep(const vector<vector<int> > &tree, int v, vector<int> &ancestors, int prev=-1)
	{
		tin[v] = timer++;
		int start = 0LL;
		while (start < ancestors.size())
		{
			ancs[v].push_back(ancestors[ancestors.size() - start - 1LL]);
			start = ((start + 1LL) << 1LL) - 1LL;
		}
		ancestors.push_back(v);
		for (auto&i : tree[v])
			if (i != prev)
				LCA_prep(tree, i, ancestors, v);
		ancestors.pop_back();
		tout[v] = timer++;
	}
public:
	bool isParent(int v1, int v2)
	{
		if (tin[v1] > tin[v2] && tout[v1] < tout[v2]) return 1;
		return 0;
	}
	//constructor
	LCA(const vector<vector<int> > &tree, int v) : tin(tree.size()), tout(tree.size()), ancs(tree.size())
	{
		vector<int> trash;
		LCA_prep(tree, v, trash);
	}
	//Query to get LCA for 2 vertices
	int get(int v1, int v2)
	{
		if (v1 == v2) return v1;
		if (isParent(v1, v2)) return v2;
		if (isParent(v2, v1)) return v1;
		int start = -1;
		for (; start < int(ancs[v1].size() - 1LL) && !isParent(ancs[v1][start + 1LL], v2) && !isParent(v2, ancs[v1][start + 1LL]); start++);
		if (start != -1)
			v1 = ancs[v1][start];
		else return ancs[v1][0];

		if (v1 == v2) return v1;
		start = -1LL;
		for (; start < int(ancs[v2].size() - 1LL) && !isParent(ancs[v2][start + 1LL], v1) && !isParent(v1, ancs[v2][start + 1LL]); start++);
		if (start != -1LL)
			v2 = ancs[v2][start];
		else return ancs[v2][0];

		return get(v1, v2);
	}
};

template<typename T>
class HeavyLightDecomposition
{
private:
	vector<vector<int> > tree, //tree itself
						 ways; //decomposed tree
	vector<int> endsW, //Ends of ways
			    sizes, //sizes of subtrees
				depth, //depth of vertices
				myWay, //Way number for each vertex
				myPos; //position of vertex in it's way
	map<pair<int, int>, bool> heavy; //is edge heavy
	vector<SegmentTree<T>> seg_trees; //segment trees for ways
	LCA lca; //Least Common Ancestor finder
	string string_f; //String name for binary function(max, min, sum)

	//Calculate max or min or sum
	T  f(T a, T b)
	{
		if (string_f == "max")
			return a > b ? a : b;
		else if (string_f == "min")
			return a < b ? a : b;
		else if (string_f == "sum")
			return a + b;
		else throw("segment tree has wrong func");
	}
	//Finds depth of vertices and heavy edges
	int HeavyDfs(int v = 1, int d = 1, int prev = 0) 
	{
		depth[v] = d;
		int c = 1;
		for (auto&i : tree[v])
			if (i != prev)
				c += sizes[i] = HeavyDfs(i, d + 1LL, v);
		for (auto&i : tree[v])
			if (i != prev && sizes[i] >= (c + 1LL) / 2LL)
				heavy[make_pair(v, i)] = true;
		return c;
	}
	//splits tree into ways of heavy edges and 1 light edge at the end of way
	int make_ways(int v = 1, int prev = 0)
	{
		int res = 0;
		for (auto&i : tree[v])
		{
			if (i != prev)
			{
				int w = make_ways(i, v);
				ways[w].push_back(v);
				endsW[w] = v;
				if (heavy[make_pair(v, i)])
				{
					res = w;
					myWay[v] = w;
					myPos[v] = ways[w].size() - 1LL;
				}
			}
		}
		if (res == 0)
		{
			res = v;
			myWay[v] = v;
			myPos[v] = 0LL;
			ways[v].push_back(res);
			endsW[v] = v;
		}
		return res;
	}
	//initializes segment trees for ways
	void createSegs()
	{
		for (ll i = 0LL; i < seg_trees.size(); i++)
			if (ways[i].size())
				seg_trees[i] = SegmentTree<int>(vector<int> (ways[i].size()), string_f, true);
	}

public:
	vector<int> vals; //values of vertices
	//Query to get f on way a-b
	int get(int a, int b, int lca = -1)
	{
		if (lca == -1) lca = this->lca.get(a, b);

		int res = 0LL;
		SegmentTree<T> &aSeg = seg_trees[myWay[a]],
					   &bSeg = seg_trees[myWay[b]];
		int  aEnd = ways[myWay[a]].size() - 1LL,
			 bEnd = ways[myWay[b]].size() - 1LL;

		if (depth[a] >= depth[lca])
			if (depth[endsW[myWay[a]]] >= depth[lca])
			{
				res = f(res, aSeg.get(myPos[a], aEnd-1));
				a = endsW[myWay[a]];
			}
			else
			{
				res = f(res, aSeg.get(myPos[a], myPos[lca] -1));
				a = lca;
			}

		if (depth[b] >= depth[lca])
			if (depth[endsW[myWay[b]]] >= depth[lca])
			{
				res = f(res, bSeg.get(myPos[b], bEnd-1));
				b = endsW[myWay[b]];
			}
			else
			{
				res = f(res, bSeg.get(myPos[b], myPos[lca] -1));
				b = lca;
			}

		if (depth[b] <= depth[lca] && depth[a] <= depth[lca])
			return f(vals[lca], res);
		return f(res, get(a, b, lca));
	}
	//Query to change vertex value
	void changeVertex(int v, int val)
	{
		vals[v] = val;
		seg_trees[myWay[v]].changePos(myPos[v], vals[v]);
	}
	//Query to increase vertex value
	void incVertex(int v, int val)
	{
		vals[v] += val;
		seg_trees[myWay[v]].incPos(myPos[v], val);
	}

	//constructor
	HeavyLightDecomposition(const vector<vector<int> > &t, string string_f) :
		lca(t, 1),seg_trees(vector<SegmentTree<T>>(t.size() + 1)),
		tree(t), ways(t.size() + 1), string_f(string_f)
	{
		sizes = endsW = depth = vals = myWay = myPos = vector<int>(t.size() + 1LL);
		HeavyDfs(); make_ways(); createSegs();
	}
};
#pragma endregion custom templates

int main()
{ 
	_start(START_OPTION::FILE_INPUT /*
		| START_OPTION::FILE_OUTPUT 
		| START_OPTION::FILE_OUTHERE, 
		"bigwall.in", 
		"bigwall.out"*/);
	int n; cin >> n;
	vector<vector<int> > tree;
	readUndirGraph(n, n - 1, tree);
	HeavyLightDecomposition<int> hld(tree, "max");

	int q; cin >> q;
	while (q--)
	{
		string c; cin >> c;
		if (c == "I")
		{
			int x; cin >> x;
			int val; cin >> val;
			hld.incVertex(x, val);
		}
		else
		{
			int a, b;
			cin >> a >> b;
			cout << hld.get(a, b) << endl;
		}
	}
	_end("");
}
