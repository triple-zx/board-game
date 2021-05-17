//#pragma GCC optimize("Ofast")
//#pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx")
//#pragma GCC optimize("unroll-loops")
#include<bits/stdc++.h>
//#define int long long
using namespace std;
 
#define rep(i,n) for (int i=0;i<(int)(n);++i)
#define rep1(i,n) for (int i=1;i<=(int)(n);++i)
#define range(x) begin(x), end(x)
#define sz(x) (int)(x).size()
#define pb push_back
#define F first
#define S second
 
typedef long long ll;
typedef unsigned long long ull;
typedef long double ld;
typedef pair<int, int> pii;
typedef vector<int> vi;

//mincostmaxflow algorithm, copied from atcoder library.

namespace internal {

template <class T> struct simple_queue {
    std::vector<T> payload;
    int pos = 0;
    void reserve(int n) { payload.reserve(n); }
    int size() const { return int(payload.size()) - pos; }
    bool empty() const { return pos == int(payload.size()); }
    void push(const T& t) { payload.push_back(t); }
    T& front() { return payload[pos]; }
    void clear() {
        payload.clear();
        pos = 0;
    }
    void pop() { pos++; }
};

}  // namespace internal

template <class Cap, class Cost> struct mcf_graph {
  public:
    mcf_graph() {}
    mcf_graph(int n) : _n(n), g(n) {}

    int add_edge(int from, int to, Cap cap, Cost cost) {
        assert(0 <= from && from < _n);
        assert(0 <= to && to < _n);
        int m = int(pos.size());
        pos.push_back({from, int(g[from].size())});
        g[from].push_back(_edge{to, int(g[to].size()), cap, cost});
        g[to].push_back(_edge{from, int(g[from].size()) - 1, 0, -cost});
        return m;
    }

    struct edge {
        int from, to;
        Cap cap, flow;
        Cost cost;
    };

    edge get_edge(int i) {
        int m = int(pos.size());
        assert(0 <= i && i < m);
        auto _e = g[pos[i].first][pos[i].second];
        auto _re = g[_e.to][_e.rev];
        return edge{
            pos[i].first, _e.to, _e.cap + _re.cap, _re.cap, _e.cost,
        };
    }
    std::vector<edge> edges() {
        int m = int(pos.size());
        std::vector<edge> result(m);
        for (int i = 0; i < m; i++) {
            result[i] = get_edge(i);
        }
        return result;
    }

    std::pair<Cap, Cost> flow(int s, int t) {
        return flow(s, t, std::numeric_limits<Cap>::max());
    }
    std::pair<Cap, Cost> flow(int s, int t, Cap flow_limit) {
        return slope(s, t, flow_limit).back();
    }
    std::vector<std::pair<Cap, Cost>> slope(int s, int t) {
        return slope(s, t, std::numeric_limits<Cap>::max());
    }
    std::vector<std::pair<Cap, Cost>> slope(int s, int t, Cap flow_limit) {
        assert(0 <= s && s < _n);
        assert(0 <= t && t < _n);
        assert(s != t);
        // variants (C = maxcost):
        // -(n-1)C <= dual[s] <= dual[i] <= dual[t] = 0
        // reduced cost (= e.cost + dual[e.from] - dual[e.to]) >= 0 for all edge
        std::vector<Cost> dual(_n, 0), dist(_n);
        std::vector<int> pv(_n), pe(_n);
        std::vector<bool> vis(_n);
        auto dual_ref = [&]() {
            std::fill(dist.begin(), dist.end(),
                      std::numeric_limits<Cost>::max());
            std::fill(pv.begin(), pv.end(), -1);
            std::fill(pe.begin(), pe.end(), -1);
            std::fill(vis.begin(), vis.end(), false);
            struct Q {
                Cost key;
                int to;
                bool operator<(Q r) const { return key > r.key; }
            };
            std::priority_queue<Q> que;
            dist[s] = 0;
            que.push(Q{0, s});
            while (!que.empty()) {
                int v = que.top().to;
                que.pop();
                if (vis[v]) continue;
                vis[v] = true;
                if (v == t) break;
                // dist[v] = shortest(s, v) + dual[s] - dual[v]
                // dist[v] >= 0 (all reduced cost are positive)
                // dist[v] <= (n-1)C
                for (int i = 0; i < int(g[v].size()); i++) {
                    auto e = g[v][i];
                    if (vis[e.to] || !e.cap) continue;
                    // |-dual[e.to] + dual[v]| <= (n-1)C
                    // cost <= C - -(n-1)C + 0 = nC
                    Cost cost = e.cost - dual[e.to] + dual[v];
                    if (dist[e.to] - dist[v] > cost) {
                        dist[e.to] = dist[v] + cost;
                        pv[e.to] = v;
                        pe[e.to] = i;
                        que.push(Q{dist[e.to], e.to});
                    }
                }
            }
            if (!vis[t]) {
                return false;
            }

            for (int v = 0; v < _n; v++) {
                if (!vis[v]) continue;
                // dual[v] = dual[v] - dist[t] + dist[v]
                //         = dual[v] - (shortest(s, t) + dual[s] - dual[t]) + (shortest(s, v) + dual[s] - dual[v])
                //         = - shortest(s, t) + dual[t] + shortest(s, v)
                //         = shortest(s, v) - shortest(s, t) >= 0 - (n-1)C
                dual[v] -= dist[t] - dist[v];
            }
            return true;
        };
        Cap flow = 0;
        Cost cost = 0, prev_cost = -1;
        std::vector<std::pair<Cap, Cost>> result;
        result.push_back({flow, cost});
        while (flow < flow_limit) {
            if (!dual_ref()) break;
            Cap c = flow_limit - flow;
            for (int v = t; v != s; v = pv[v]) {
                c = std::min(c, g[pv[v]][pe[v]].cap);
            }
            for (int v = t; v != s; v = pv[v]) {
                auto& e = g[pv[v]][pe[v]];
                e.cap -= c;
                g[v][e.rev].cap += c;
            }
            Cost d = -dual[s];
            flow += c;
            cost += c * d;
            if (prev_cost == d) {
                result.pop_back();
            }
            result.push_back({flow, cost});
            prev_cost = cost;
        }
        return result;
    }

  private:
    int _n;

    struct _edge {
        int to, rev;
        Cap cap;
        Cost cost;
    };

    std::vector<std::pair<int, int>> pos;
    std::vector<std::vector<_edge>> g;
};

//mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
mt19937 rng(12345678);
//cells 0 left, 1 right, 2 up, 3 down

const int tries=10000;
int check(vi &res,vector<vi>& cells,int n,int m){
    assert(n*m==sz(cells));
    int score=0;
    auto f=[&](int u,int v){
        return u*m+v;
    };
    rep(i,n) rep(j,m-1) if (cells[res[f(i,j)]][1]==cells[res[f(i,j+1)]][0]) score++;
    rep(i,n-1) rep(j,m) if (cells[res[f(i,j)]][3]==cells[res[f(i+1,j)]][2]) score++;
    return score;
}


vector<vi> gen(int n,int m){
    vector<vi> ret;
    ret.clear();
    ret.resize(n*m,vi(4,-1));
    auto f=[&](int u,int v){
        return u*m+v;
    };
    rep(i,n) rep(j,m-1) ret[f(i,j)][1]=ret[f(i,j+1)][0]=rng()%4;
    rep(i,n-1) rep(j,m) ret[f(i,j)][3]=ret[f(i+1,j)][2]=rng()%4;
    rep(i,n*m) rep(k,4) if (ret[i][k]==-1) ret[i][k]=rng()%4;
    vi res(n*m,0);
    rep(i,n*m) res[i]=i;
    assert(check(res,ret,n,m)==n*(m-1)+(n-1)*m);
    shuffle(range(ret),rng);
    return ret; 
}

vi solve(vector<vi>& cells,int n,int m){
    vi attempt;
    attempt.clear();
    attempt.resize(n*m,-1);
    rep(i,n*m) attempt[i]=i;
    int score=0;
    rep(_,tries){
        if (_%1000==0) cout<<_<<" tries, current score: "<<score<<endl;
        int u,v;
        while (1){
            u=rng()%(n*m), v=rng()%(n*m);
            if (u==v) continue;
            if ((u*v)&1) continue;
            break; 
        }
        swap(attempt[u],attempt[v]);
        mcf_graph<int,int> mfg(n*m+5);
        vi black,white;
        black.clear(), white.clear();
        rep(i,n*m){
            int x=i/m, y=i%m;
            if ((x+y)&1) mfg.add_edge(sz(black),n*m,1,0), black.pb(i);
            else mfg.add_edge(n*m+1,n*m/2+sz(white),1,0), white.pb(i);
        } 
        auto check=[&](int nc1,int nc2,int l,int r){
            return cells[attempt[nc1]][l]==cells[attempt[nc2]][r];
        };
        int hii=2*n*m;
        rep(i,n*m/2) rep(j,n*m/2){
            int cnt=0, nc=white[i], pos=white[j];
            if (pos%m&&check(pos-1,nc,1,0)) cnt++;
            if ((pos+1)%m&&check(nc,pos+1,1,0)) cnt++;
            if (pos-m>=0&&check(nc,pos-m,2,3)) cnt++;
            if (pos+m<n*m&&check(nc,pos+m,3,2)) cnt++;
            mfg.add_edge(j+n*m/2,i,1,4-cnt);
        }
        auto qaq=mfg.flow(n*m+1,n*m);
        assert(qaq.F==n*m/2);
        int xd=hii-qaq.S;
        if (score>xd) swap(attempt[u],attempt[v]);
        else {
            score=xd;
            vi tmp;
            tmp.clear();
            tmp.resize(n*m,-1);
            int test=0;
            for (auto e:mfg.edges()){
                if (e.flow&&max(e.from,e.to)<n*m&&(e.to<e.from)){
//                    cout<<e.from<<" "<<e.to<<endl;
                    tmp[white[e.from-n*m/2]]=attempt[white[e.to]];
                    test+=e.cost;
                }
            }
//            cout<<"TEST:"<<hii-test<<endl;
            assert(test+score == hii);
            rep(i,n*m) if (tmp[i]!=-1){
                attempt[i]=tmp[i];
            }
        }
        assert(::check(attempt,cells,n,m)==score);
    }
    return attempt;
}
signed main(){
    ios::sync_with_stdio(false);
    cin.tie(0);
    map<int,int> cnt;
    cnt.clear();
    rep1(_,20){
        auto puz=gen(8,12);
        auto sol=solve(puz,8,12);    
        cout<<"permutation: ";
        for (auto c:sol) cout<<c<<" ";
        cout<<endl;
        int tmp=check(sol,puz,8,12);
        cout<<"score: "<<tmp<<endl;
        cnt[tmp]++;
    }
    cout<<"stat:"<<endl;
    for (auto c:cnt){
        cout<<"Score: "<<c.F<<" Times: "<<c.S<<endl;
    } 
    return 0;
}
