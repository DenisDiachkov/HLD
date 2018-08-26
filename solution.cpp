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
typedef long long ll;
typedef unsigned long long ull;
typedef long double ld;
const ll MOD = 1000000007LL;
enum class START_OPTION {NOTHING=0, FILE_INPUT=1, FILE_OUTPUT=2};

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


								   void         _start      (START_OPTION opt = START_OPTION::NOTHING)
{
#ifdef LOCAL_FREOPEN
	if (opt & START_OPTION::FILE_INPUT)  freopen("input.txt", "r", stdin);
	if (opt & START_OPTION::FILE_OUTPUT) freopen("output.txt", "w", stdout);
#endif
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
#pragma endregion custom templates


vector<vector<int> > tree, ways, seg_trees, myEnds;
vector<int> endsW, sizes, depth, tin, tout, vals, myWay, myPos, par;
vector<vector<int> > ancs;
map<pair<int, int>, bool> heavy;

int HeavyDfs(int v, int d = 1LL, int prev = 0LL)
{
	par[v] = prev;
	depth[v] = d;
	int c = 1LL;
	for (auto&i : tree[v])
		if (i != prev)
			c += sizes[i] = HeavyDfs(i, d+1LL, v);
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


int timer = 1;
void LCA_prep(int v, vector<int> &ancestors, int prev = -1LL)
{
	tin[v] = timer++;
	int start = 0LL;
	while (start < ancestors.size())
	{
		ancs[v].push_back(ancestors[ancestors.size() - start - 1LL]);
		start = ((start+1LL) << 1LL)-1LL;
	}
	ancestors.push_back(v);
	for (auto&i : tree[v])
		if(i != prev)
			LCA_prep(i, ancestors, v);
	ancestors.pop_back();
	tout[v] = timer++;
}
bool isParent(int v1, int v2)
{
	if (tin[v1] > tin[v2] && tout[v1] < tout[v2]) return 1;
	return 0;
}
int LCA(int v1, int v2)
{
	if (v1 == v2) return v1;
	if (isParent(v1, v2)) return v2;
	if (isParent(v2, v1)) return v1;
	int start = -1;
	for (; start < int(ancs[v1].size() - 1LL) && !isParent(ancs[v1][start + 1LL], v2) && !isParent(v2, ancs[v1][start + 1LL]); start++);
	if(start != -1)
		v1 = ancs[v1][start];
	else return ancs[v1][0];

	if (v1 == v2) return v1;
	start = -1LL;
	for (; start < int(ancs[v2].size() - 1LL) && !isParent(ancs[v2][start + 1LL], v1) && !isParent(v1, ancs[v2][start + 1LL]); start++);
	if (start != -1LL)
		v2 = ancs[v2][start];
	else return ancs[v2][0];

	return LCA(v1, v2);
}


int changeSum(vector<int> &sgt, int pos, int val, int tl, int tr, int idx)
{
	if (tl == tr) return sgt[idx] = val;
	int m = (tl + tr) / 2;
	if (m >= pos) return sgt[idx] = changeSum(sgt, pos, val, tl,  m,  idx * 2) + sgt[idx*2+1];
	else		  return sgt[idx] = changeSum(sgt, pos, val, m + 1, tr, idx * 2 + 1) + sgt[idx * 2];
}
int getSum(vector<int> &sgt, int l, int r, int tl, int tr, int idx)
{
	if (tl > r || tr < l) return 0;
	int m = (tl + tr) / 2;
	if (tl >= l && tr <= r) return sgt[idx];
	return getSum(sgt, l, r, tl, m, idx * 2) + getSum(sgt, l, r, m + 1, tr, idx * 2 + 1);
}
int changeMax(vector<int> &sgt, int pos, int val, int tl, int tr, int idx)
{
	if (tl == tr) return sgt[idx] = val;
	int m = (tl + tr) / 2LL;
	if (m >= pos) return sgt[idx] = max(changeMax(sgt, pos, val, tl, m, idx * 2LL), sgt[idx * 2LL + 1LL]);
	else		  return sgt[idx] = max(changeMax(sgt, pos, val, m + 1, tr, idx * 2LL + 1LL), sgt[idx * 2LL]);
}
int getMax(vector<int> &sgt, int l, int r, int tl, int tr, int idx)
{
	if (tl > r || tr < l) return 0LL;
	int m = (tl + tr) / 2LL;
	if (tl >= l && tr <= r) return sgt[idx];
	return max(getMax(sgt, l, r, tl, m, idx * 2LL), getMax(sgt, l, r, m + 1LL, tr, idx * 2LL + 1LL));
}

int getTreeSum(int a, int b, int lca)
{
	int res = 0LL;
	vector<int> &aSeg = seg_trees[myWay[a]],
		&bSeg = seg_trees[myWay[b]];
	int  aPos = myPos[a],
		bPos = myPos[b],
		lcaPos = myPos[lca],
		aEnd = ways[myWay[a]].size() - 2LL,
		bEnd = ways[myWay[b]].size() - 2LL;

	if (depth[a] >= depth[lca])
		if (depth[endsW[myWay[a]]] >= depth[lca])
		{
			res = res + getSum(aSeg, aPos, aEnd, 0LL, aEnd + 1, 1LL);
			a = endsW[myWay[a]];
		}
		else
		{
			res = res + getSum(aSeg, aPos, lcaPos, 0LL, aEnd + 1, 1LL);
			a = lca;
		}

	if (depth[b] >= depth[lca])
		if (depth[endsW[myWay[b]]] >= depth[lca])
		{
			res = res + getSum(bSeg, bPos, bEnd, 0LL, bEnd + 1, 1LL);
			b = endsW[myWay[b]];
		}
		else
		{
			res = res + getSum(bSeg, bPos, lcaPos, 0LL, bEnd + 1, 1LL);
			b = lca;
		}

	if (depth[b] <= depth[lca] && depth[a] <= depth[lca])
		return res;
	return res + getTreeSum(a, b, lca);
}
int getTreeMax(int a, int b, int lca)
{
	int res = 0LL;
	vector<int> &aSeg = seg_trees[myWay[a]],
				&bSeg = seg_trees[myWay[b]];
	int  aPos = myPos[a],
		bPos = myPos[b],
		lcaPos = myPos[lca],
		aEnd = ways[myWay[a]].size() - 2LL,
		bEnd = ways[myWay[b]].size() - 2LL;

	if (depth[a] >= depth[lca])
		if (depth[endsW[myWay[a]]] >= depth[lca])
		{
			res = max(res, getMax(aSeg, aPos, aEnd, 0LL, aEnd+1, 1LL));
			a = endsW[myWay[a]];
		}
		else
		{
			res = max(res, getMax(aSeg, aPos, lcaPos, 0LL, aEnd+1, 1LL));
			a = lca;
		}

	if (depth[b] >= depth[lca])
		if (depth[endsW[myWay[b]]] >= depth[lca])
		{
			res = max(res, getMax(bSeg, bPos, bEnd, 0LL, bEnd+1, 1LL));
			b = endsW[myWay[b]];
		}
		else
		{
			res = max(res, getMax(bSeg, bPos, lcaPos, 0LL, bEnd+1, 1LL));
			b = lca;
		}

	if (depth[b] <= depth[lca] && depth[a] <= depth[lca])
		return res;
	return max(res,getTreeMax(a, b, lca));
}
void createSegs()
{
	for (ll i = 0LL; i < seg_trees.size(); i++)
		if (ways[i].size())
			seg_trees[i] = vector<int>(ways[i].size() * 4LL + 10LL);
}
int main()
{ 
	_start(START_OPTION::FILE_INPUT);
	int n; cin >> n;
	readUndirGraph(n, n - 1, tree);
	sizes = endsW = depth = tin = tout = vals = myWay = myPos = par = vector<int>(n + 1LL);
	ways = ancs = seg_trees = vector<vector<int> >(n + 1LL);
	HeavyDfs(1);
	make_ways(1);
	vector<int> useless;
	LCA_prep(1LL, useless);
	createSegs();


	int q; cin >> q;
	while (q--)
	{ 
		string c; cin >> c;
		if (c == "I")
		{
			int x; cin >> x;
			int val; cin >> val;
			vals[x] += val;
			changeMax(seg_trees[myWay[x]], myPos[x], vals[x], 0LL, ways[myWay[x]].size() - 1LL, 1LL);
		}
		else
		{
			int a,b;
			cin >> a >> b;
			int lca = LCA(a, b);
			cout << max(vals[lca], getTreeMax(a,b,lca)) << endl;
		}
	}
	_end("");
}