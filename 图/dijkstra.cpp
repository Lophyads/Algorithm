namespace Dij{
	VL d;
	VI vis;
	int N;
	vector<vector<PII>> g;
	void init(int n){
		N = n;
		g = vector<vector<PII>>(N);
	}
	void add(int u ,int v, int w){
		g[u].eb(v, w);
	}
	void dij(int s){
		d.assign(N, KINF);
		vis.assign(N, 0);
		d[s] = 0;
		PQ<pair<ll,int>> pq;
		pq.push({0, s});
		while(!pq.empty()){
			auto [w, u] = pq.top();
			pq.pop();
			w = -w;
			if(vis[u] ++) continue;
			for(auto& [v, ww] : g[u]){	
				if(vis[v]) continue;		
				if(d[v] > w + ww){
					d[v] = w + ww;
					pq.push({-d[v], v});
				}
			}
		}
		return ;
	}
}