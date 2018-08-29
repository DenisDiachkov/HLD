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


class SegmentTree
{
private:
	vector<int> treeMx, treeMn, treeSm, pushMx, pushMn, pushSm;
	int n; 

	void pushMax(int idx)
	{
		if (pushMx[idx] == 0) return;
		treeMx[idx] += pushMx[idx];
		if (pushMx.size() > idx * 2) pushMx[idx * 2] += pushMx[idx];
		if (pushMx.size() > idx * 2 + 1) pushMx[idx * 2 + 1] += pushMx[idx];
		pushMx[idx] = 0;
	}
	void pushMin(int idx)
	{
		if (pushMn[idx] == 0) return;
		treeMn[idx] += pushMn[idx];
		if (pushMn.size() > idx * 2) pushMn[idx * 2] += pushMn[idx];
		if (pushMn.size() > idx * 2 + 1) pushMn[idx * 2 + 1] += pushMn[idx];
		pushMn[idx] = 0;
	}
	void pushSum(int idx)
	{
		if (pushSm[idx] == 0) return;
		treeSm[idx] += pushSm[idx];
		if (pushSm.size() > idx * 2) pushSm[idx * 2] += pushSm[idx];
		if (pushSm.size() > idx * 2 + 1) pushSm[idx * 2 + 1] += pushSm[idx];
		pushSm[idx] = 0;
	}

public:
	int RMxQChangePos(int pos, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMax(idx);
		if (tl == tr)
			return treeMx[idx] = val;
		int m = (tl + tr) / 2;
		if (pos <= m)
			return treeMx[idx] = max(RMxQChangePos(pos, val, tl, m, idx * 2), treeMx[idx * 2 + 1]);
		else return treeMx[idx] = max(RMxQChangePos(pos, val, m + 1, tr, idx * 2 + 1), treeMx[idx * 2]);
	}
	int RMnQChangePos(int pos, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMin(idx);
		if (tl == tr)
			return treeMn[idx] = val;
		int m = (tl + tr) / 2;
		if (pos <= m)
			return treeMn[idx] = min(RMnQChangePos(pos, val, tl, m, idx * 2), treeMn[idx * 2 + 1]);
		else return treeMn[idx] = min(RMnQChangePos(pos, val, m + 1, tr, idx * 2 + 1), treeMn[idx * 2]);
	}
	int RSQChangePos(int pos, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushSum(idx);
		if (tl == tr)
			return treeSm[idx] = val;
		int m = (tl + tr) / 2;
		if (pos <= m)
			return treeSm[idx] = RSQChangePos(pos, val, tl, m, idx * 2) + treeSm[idx * 2 + 1];
		else return treeSm[idx] = RSQChangePos(pos, val, m + 1, tr, idx * 2 + 1) + treeSm[idx * 2];
	}

	int RMxQIncPos(int pos, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMax(idx);
		if (tl == tr)
		{
			treeMx[idx] += val;
			pushMax(idx);
			return treeMx[idx];
		}
		int m = (tl + tr) / 2;
		if (pos <= m)
			return treeMx[idx] = max(RMxQChangePos(pos, val, tl, m, idx * 2), treeMx[idx * 2 + 1]);
		else return treeMx[idx] = max(RMxQChangePos(pos, val, m + 1, tr, idx * 2 + 1), treeMx[idx * 2]);
	}
	int RMnQIncPos(int pos, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMin(idx);
		if (tl == tr)
		{
			treeMn[idx] += val;
			pushMin(idx);
			return treeMn[idx];
		}
		int m = (tl + tr) / 2;
		if (pos <= m)
			return treeMn[idx] = min(RMnQChangePos(pos, val, tl, m, idx * 2), treeMn[idx * 2 + 1]);
		else return treeMn[idx] = min(RMnQChangePos(pos, val, m + 1, tr, idx * 2 + 1), treeMn[idx * 2]);
	}
	int RSQIncPos(int pos, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushSum(idx);
		if (tl == tr)
		{
			treeSm[idx] += val;
			pushSum(idx);
			return treeSm[idx];
		}
		int m = (tl + tr) / 2;
		if (pos <= m)
			return treeSm[idx] = RSQChangePos(pos, val, tl, m, idx * 2) + treeSm[idx * 2 + 1];
		else return treeSm[idx] = RSQChangePos(pos, val, m + 1, tr, idx * 2 + 1) + treeSm[idx * 2];
	}

	int getMax(int l, int r, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMax(idx);
		if (tl > r || tr < l)
			return -INT_INFINITY;
		int m = (tl + tr) >> 1;
		if (tl >= l && tr <= r)
			return treeMx[idx];
		return max(getMax(l, r, tl, m, idx << 1), getMax(l, r, m + 1, tr, (idx << 1) + 1));
	}
	int getMin(int l, int r, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMin(idx);
		if (tl > r || tr < l)
			return INT_INFINITY;
		int m = (tl + tr) / 2;
		if (tl >= l && tr <= r)
			return treeMn[idx];
		return min(getMin(l, r, tl, m, idx * 2), getMin(l, r, m + 1, tr, idx * 2 + 1));
	}
	int getSum(int l, int r, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushSum(idx);
		if (tl > r || tr < l)
			return 0;
		int m = (tl + tr) / 2;
		if (tl >= l && tr <= r)
			return treeSm[idx];
		return getSum(l, r, tl, m, idx * 2) + getSum(l, r, m + 1, tr, idx * 2 + 1);
	}

	//TODO: ChangeSegment

	int RMxQIncSegment(int l, int r, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMax(idx);
		if (tl > r || tr < l)
			return treeMx[idx];
		int m = (tl + tr) >> 1;
		if (tl >= l && tr <= r)
		{
			pushMx[idx] = val;
			pushMax(idx);
			return treeMx[idx];
		}
		else return treeMx[idx] = max(RMxQIncSegment(l, r, val, tl, m, idx * 2), RMxQIncSegment(l, r, val, m + 1, tr, idx * 2 + 1));
	}
	int RMnQIncSegment(int l, int r, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushMin(idx);
		if (tl > r || tr < l)
			return treeMn[idx];
		int m = (tl + tr) / 2;
		if (tl >= l && tr <= r)
		{
			pushMn[idx] = val;
			pushMin(idx);
			return treeMn[idx];
		}
		else return treeMn[idx] = min(RMnQIncSegment(l, r, val, tl, m, idx * 2), RMnQIncSegment(l, r, val, m + 1, tr, idx * 2 + 1));
	}
	int RSQIncSegment(int l, int r, int val, int tl = 0, int tr = -1, int idx = 1)
	{
		if (tr == -1) tr += n;

		pushSum(idx);
		if (tl > r || tr < l)
			return treeSm[idx];
		int m = (tl + tr) / 2;
		if (tl >= l && tr <= r)
		{
			pushSm[idx] = val;
			pushSum(idx);
			return treeSm[idx];
		}
		else return treeSm[idx] = RSQIncSegment(l, r, val, tl, m, idx * 2) + RSQIncSegment(l, r, val, m + 1, tr, idx * 2 + 1);
	}

	SegmentTree(vector<int> mas, bool RMxQ, bool RMnQ, bool RSQ)
	{
		n = mas.size();
		if (RMxQ) treeMx = pushMx = vector<int>(n * 4);
		if (RMnQ) treeMn = pushMn = vector<int>(n * 4);
		if (RSQ)  treeSm = pushSm = vector<int>(n * 4);
		for (int i = 0; i < mas.size(); i++)
		{
			if (RMxQ)RMxQChangePos(i, mas[i], 0, n - 1, 1);
			if (RMnQ)RMnQChangePos(i, mas[i], 0, n - 1, 1);
			if (RSQ) RSQChangePos(i, mas[i], 0, n - 1, 1);
		}
	}
	SegmentTree() {}
};
class LCA
{
private:
	vector<int> tin, tout;
	vector<vector<int> > ancs;
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
	LCA(const vector<vector<int> > &tree, int v) : tin(tree.size()), tout(tree.size()), ancs(tree.size())
	{
		vector<int> trash;
		LCA_prep(tree, v, trash);
	}
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
class HeavyLightDecomposition
{
private:
	vector<vector<int> > tree, ways, myEnds;
	vector<int> endsW, sizes, depth, myWay, myPos;
	map<pair<int, int>, bool> heavy;
	vector<SegmentTree> seg_trees;
	LCA lca;
	int HeavyDfs(int v, int d = 1LL, int prev = 0LL)
	{
		depth[v] = d;
		int c = 1LL;
		for (auto&i : tree[v])
			if (i != prev)
				c += sizes[i] = HeavyDfs(i, d + 1LL, v);
		for (auto&i : tree[v])
			if (i != prev && sizes[i] >= (c + 1LL) / 2LL)
				heavy[make_pair(v, i)] = true;
		return c;
	}
	int make_ways(int v, int prev = 0LL)
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
	void createSegs(bool mx=1, bool mn=1, bool sm=1)
	{
		for (ll i = 0LL; i < seg_trees.size(); i++)
			if (ways[i].size())
				seg_trees[i] = SegmentTree(vector<int> (ways[i].size()), mx, mn, sm);
	}

public:
	vector<int> vals;
	int getTreeMax(int a, int b, int lca = -1)
	{
		if (lca == -1) lca = this->lca.get(a, b);

		int res = 0LL;
		SegmentTree &aSeg = seg_trees[myWay[a]],
			&bSeg = seg_trees[myWay[b]];
		int  aPos = myPos[a],
			bPos = myPos[b],
			lcaPos = myPos[lca],
			aEnd = ways[myWay[a]].size() - 2LL,
			bEnd = ways[myWay[b]].size() - 2LL;

		if (depth[a] >= depth[lca])
			if (depth[endsW[myWay[a]]] >= depth[lca])
			{
				res = max(res, aSeg.getMax(aPos, aEnd));
				a = endsW[myWay[a]];
			}
			else
			{
				res = max(res, aSeg.getMax(aPos, lcaPos));
				a = lca;
			}

		if (depth[b] >= depth[lca])
			if (depth[endsW[myWay[b]]] >= depth[lca])
			{
				res = max(res, bSeg.getMax(bPos, bEnd));
				b = endsW[myWay[b]];
			}
			else
			{
				res = max(res, bSeg.getMax(bPos, lcaPos));
				b = lca;
			}

		if (depth[b] <= depth[lca] && depth[a] <= depth[lca])
			return max(vals[lca], res);
		return max(res, getTreeMax(a, b, lca));
	}
	void changeVertex(int v, int val)
	{
		vals[v] = val;
		seg_trees[myWay[v]].RMxQChangePos(myPos[v], vals[v]);
	}
	void incVertex(int v, int val)
	{
		vals[v] += val;
		seg_trees[myWay[v]].RMxQChangePos(myPos[v], vals[v]);
	}
	HeavyLightDecomposition(vector<vector<int> > &t) :
		lca(t, 1),
		seg_trees(vector<SegmentTree>(t.size() + 1)),
		tree(t),
		ways(t.size() + 1)
	{
		sizes = endsW = depth = vals = myWay = myPos = vector<int>(t.size() + 1LL);
		HeavyDfs(1);
		make_ways(1);
		vector<int> trash;
		createSegs(1,0,0);
	}
};
#pragma endregion custom templates

int main()
{ 
	_start(START_OPTION::FILE_INPUT/* | START_OPTION::FILE_OUTPUT | START_OPTION::FILE_OUTHERE, "bigwall.in", "bigwall.out"*/);
	int n; cin >> n;
	vector<vector<int> > tree;
	readUndirGraph(n, n - 1, tree);
	HeavyLightDecomposition hld(tree);


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
			cout << hld.getTreeMax(a, b) << endl;
		}
	}
	_end("");
}