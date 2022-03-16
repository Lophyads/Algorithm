namespace G{
    struct edge{// 费用流
        int v;
        ll w, c;
        edge(int v, ll w, ll c) : v(v), w(w), c(c){}
    };
    VII flow_g;//网络流图
    VII cost_g;// 费用流图
    vector<pair<int,ll>> flow_e;//网络流边
    vector<edge> cost_e;// 费用流边
    vector<vector<pair<int,ll>>> tr;// 最小割树
    VI pdx, tdx, idx;
    int N, S, T;
    VI cur;
    ll cost;//费用
    VI vis;
    VL d;
    void flow_init(int n){// 网络流初始化图
        N = n;
        flow_g = VII(N);
        flow_e.clear();
    }
    void flow_add(int u, int v, int w){
        flow_g[u].eb(flow_e.size());
        flow_e.eb(v, w);
        flow_g[v].eb(flow_e.size());
        flow_e.eb(u, 0);
    }
    bool bfs(){
        d.assign(N, 0);
        d[S] = 1;
        queue<int> q;
        q.push(S);
        while(!q.empty()){
            int u = q.front();
            q.pop();
            for(int& id : flow_g[u]){
                auto& [v, w] = flow_e[id];
                if(!w || d[v]) continue;
                d[v] = d[u] + 1;
                if(v == T) return true;
                q.push(v);
            }
        }
        return false;
    }
    ll flow_dinic(int u, ll lim){
        if(u == T || !lim) return lim;
        ll tot = 0;
        for(int& i = cur[u]; i < (int)flow_g[u].size(); ++i){
            int id = flow_g[u][i];
            auto& [v, w] = flow_e[id];
            if(!w || d[v] != d[u] + 1) continue;
            ll f = flow_dinic(v, min(w, lim));
            if(!f){
                d[v] = 0;
                continue;
            }
            flow_e[id].se -= f;
            flow_e[id ^ 1].se += f;
            tot += f;
            lim -= f;
            if(!lim) break;
        }
        return tot;
    }
    ll maxflow(int s, int t){
        S = s, T = t;
        ll ans = 0;
        while(bfs()){
            cur.assign(N, 0);
            ans += flow_dinic(S, KINF);
        }
        return ans;
    }
    void cost_init(int n){// 费用流初始化图
        N = n;
        cost_g = VII(N);
        cost_e.clear();
        cost = 0;
    }
    void cost_add(int u, int v, ll w, ll c){// 费用流
        cost_g[u].eb(cost_e.size());
        cost_e.eb(v, w, c);
        cost_g[v].eb(cost_e.size());
        cost_e.eb(u, 0, -c);
    }
    bool spfa(){
        vis.assign(N, 0);
        d.assign(N, KINF);//最小费用流初始正无穷,反之负无穷
        d[S] = 0;
        queue<int> q;
        q.push(S);     
        vis[S] = 1;
        while(!q.empty()){
            int u = q.front();
            vis[u] = 0;
            q.pop();
            for(int& id : cost_g[u]){
                auto E = cost_e[id];
                int v = E.v;
                ll w = E.w, c = E.c;
                if(w && d[v] > d[u] + c){// 最小费用流大于号，反之小于号
                    d[v] = d[u] + c;
                    if(vis[v]) continue;
                    q.push(v);
                    vis[v] = 1;
                }
            }
        }
        return d[T] != KINF;
    }
    ll cost_dinic(int u, ll lim){
        if(u == T || !lim) return lim;
        vis[u] = 1;// 防止因费用为0的边导致死循环
        ll tot = 0;
        for(int& i = cur[u]; i < (int)cost_g[u].size(); ++i){
            int id = cost_g[u][i];
            auto E = cost_e[id];
            int v = E.v;
            ll w = E.w, c = E.c;
            if(!w || d[v] != d[u] + c || vis[v]) continue;
            ll f = cost_dinic(v, min(lim, w));
            if(!f) continue;
            cost += f * c;
            // 每增加1流量,费用就会加d[T]
            cost_e[id].w -= f;
            cost_e[id ^ 1].w += f;
            tot += f;
            lim -= f;
            if(!lim) break;
        }
        vis[u] = 0;
        return tot;
    }
    pair<ll,ll> mcmf(int s, int t){
        S = s, T = t;
        ll flow = 0;//最大流
        while(spfa()){
            cur.assign(N, 0);
            vis.assign(N, 0);
            flow += cost_dinic(S, KINF);
        }
        return {flow, cost};// 最大流和费用
    }
    void mincut_init(){
        tr = vector<vector<pair<int,ll>>> (N);
        pdx.assign(N, 0);
        tdx.assign(N, 0);
        idx.assign(N, 0);
        iota(all(pdx), 0);
    }
    void dfs(int l, int r){//建最小割树
        if(l >= r) return;
        int x = pdx[l], y = pdx[l + 1];
        S = x, T = y;
        // 求最小割前要把图恢复回初始状态
        for(int i = 0; i < (int)flow_e.size(); i += 2) flow_e[i].se += flow_e[i ^ 1].se, flow_e[i ^ 1].se = 0;
        ll cut = maxflow(S, T);
        tr[x].eb(y, cut);
        tr[y].eb(x, cut);//添加最小割边到树上
        int p = l, t = r;
        rep(i, l, r + 1){
            if(d[pdx[i]]) tdx[p ++] = pdx[i];//最后一次bfs有深度,说明与x相连
            else tdx[t--] = pdx[i];
        }
        rep(i, l, r + 1) pdx[i] = tdx[i];
        dfs(l, p - 1);
        dfs(t + 1, r);
    }
    VII fa;
    VLL mi;
    VI h;
    void Bfs(int rt){//倍增预处理树上路径
        queue<int> q;
        q.push(rt);
        h[rt] = 1;
        fa[rt][0] = -1;
        while(!q.empty()){
            int u = q.front();
            q.pop();
            for(auto& [v, w] : tr[u]){
                if(v != fa[u][0]){
                    fa[v][0] = u;
                    mi[v][0] = w;
                    h[v] = h[u] + 1;
                    for(int j = 1; (1 << j) <= h[u]; j ++){
                        fa[v][j] = fa[fa[v][j - 1]][j - 1];
                        mi[v][j] = min(mi[v][j - 1], mi[fa[v][j - 1]][j - 1]);
                    }
                    q.push(v);
                }
            }
        }
    }
    void build(int s, int t){// 最小割树
    	S = s, T = t;
        mincut_init();
        dfs(s, t);// 递归建最小割树
        int M = __lg(N) + 2;
        fa = VII(N, VI(M));
        mi = VLL(N, VL(M, KINF));       
        h.assign(N, 0);	
        Bfs(S);      
    }
    ll query(int u, int v){// 查询无向图中两点之间的最小割
        ll ans = KINF;
        if(h[u] > h[v]) swap(u, v);
        int M = __lg(N) + 2;
        _rep(i, M - 1, -1){
            if(h[fa[v][i]] >= h[u]){
                ans = min(ans, mi[v][i]);
                v = fa[v][i];
            }
            if(v == u) return ans;
        }
        _rep(i, M - 1, -1){
            if(fa[u][i] != fa[v][i]){
                ans = min({ans, mi[u][i], mi[v][i]});
                u = fa[u][i];
                v = fa[v][i];
            }
        }
        ans = min({ans, mi[u][0], mi[v][0]});
        return ans;
    }
}