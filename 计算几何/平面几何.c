using db = long double;
const db eps = 1e-6;
const db pi = acosl(-1.0);
inline int sgn(db x){ return x < -eps ? -1 : x > eps;}
inline int cmp(db a, db b){ return sgn(a-b); }
struct P{ // 点
	db x, y;
	P(db _x, db _y): x(_x), y(_y){}
	P operator-(P p) { return {x - p.x, y - p.y}; }
	P(){}
	db dot(P p) { return x * p.x + y * p.y; }
    db det(P p) { return x * p.y - y * p.x; }
    db distTo(P p) { return (*this - p).abs(); }
    db abs() { return sqrt(abs2());}
    db abs2() { return x * x + y * y; }
    bool operator < (const P& p) const { 
        int c = cmp(x, p.x);
        if (c) return c == -1;
        return cmp(y, p.y) == -1;
    }
    bool operator == (const P& o) const{
        return cmp(x,o.x) == 0 && cmp(y,o.y) == 0;
    }
};

P operator + (const P& a, const P& b){
	return {a.x + b.x, a.y + b.y};
}
P operator - (const P& a, const P& b){
	return {a.x - b.x, a.y - b.y};
}
P operator * (const P& a, db b){
	return {a.x * b, a.y * b};
}
P operator * (const db k, const P& p){
	return {p.x * k, p.y * k};
}
P operator / (const P& a, db b){
	return {a.x / b, a.y / b};
}
db operator ^ (const P& a, const P& b){ // 叉积
	return a.x * b.y - a.y * b.x;
}
db operator * (const P& a, const P& b){ // 点积
	return a.x * b.x + a.y * b.y;
}
db rad(const P& p, const P& a, const P& b){// pa 与 pb 的夹角
	return fabs(atan2(fabs((a - p) ^ (b - p)),(a - p) * (b - p)));
}
db cross(const P& a, const P& b, const P& c){return (b.x - a.x) * (c.y - a.y) - (c.x - a.x) * (b.y - a.y);}
int crossOp(const P& a, const P& b, const P& c){return sgn(cross(a, b, c));}
db len(const P& a, const P& b) {return sqrt((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y));} // 向量长度
db len2(const P& a, const P& b){return (a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y);}
db len(const P& a){ return sqrt(a * a);}
db len2(const P& a){ return a * a;}
P r90c(P v) { return {v.y, -v.x}; }// 顺时针旋转90度 
P l90c(P v) { return {-v.y, v.x}; }// 逆时针旋转90度
P rrota(P v, db a){// 逆时针旋转a度
	return {v.x * cosl(a) - v.y * sinl(a), v.x * sinl(a) + v.y * cosl(a)};
}
P lrota(P v, db a){// 顺时针旋转a度
	return {v.x * cosl(a) + v.y * sinl(a), -v.x * sinl(a) + v.y * cosl(a)};
}
bool eq(db a, db b) { return fabs(a - b) < eps; } // ==
bool eq(const P& a, const P& b){return eq(a.x, b.x) && eq(a.y, b.y);}
bool gt(db a, db b) { return a - b > eps; }      // >
bool lt(db a, db b) { return a - b < -eps; }     // <
bool ge(db a, db b) { return a - b > -eps; }     // >=
bool le(db a, db b) { return a - b < eps; }    // <= 
db area(vector<P>& a){ //有向面积
	db sum = 0;
	int n = a.size();
	for(int i = 1; i < n - 1; i ++)
		sum += 1.0 / 2.0 * ((a[i] - a[0]) ^ (a[i + 1] - a[i]));
	return sum;
}

// 判断点的上下位置
int quad(const P& p) { return sgn(p.y) == 1 || (sgn(p.y) == 0 && sgn(p.x) >= 0); }
void psort(vector<P> &ps, P c = {0, 0}){// (-pi开始)逆时针极角排序
    sort(ps.begin(), ps.end(), [&](auto v1, auto v2) {
        return quad(v1 - c) < quad(v2 - c) || (quad(v1 - c) == quad(v2 - c) && gt((v1 - c) ^ (v2 - c), 0));
    });
}

P unit(const P& p) { return p / len(p); }// 单位化
struct L { // ps[0] -> ps[1] 线
	P ps[2];
    P& operator[](int i) { return ps[i]; }
    L (){}
    P dir() { return ps[1] - ps[0]; }
    db K;
    L (P a,P b) {
        ps[0] = a;
        ps[1] = b;
        K = atan2((b - a).y, (b - a).x);
    }
    bool include(P p) { return sgn((ps[1] - ps[0]) ^ (p - ps[0])) > 0; }
    L push(){ // push eps outward
        const double eps = 1e-8;
        P delta = unit(r90c((ps[1] - ps[0]))) * eps;
        return {ps[0] + delta, ps[1] + delta};
    }
};

P isLL(const P& p1,const P& p2,const P& q1,const P& q2) {// 直线交点
    db a1 = cross(q1, q2, p1), a2 = -cross(q1, q2, p2);
    return (p1 * a2 + p2 * a1) / (a1 + a2);
}
P isLL(L& l1, L& l2){ return isLL(l1[0],l1[1],l2[0],l2[1]); }
bool parallel(L l0, L l1) { return sgn( l0.dir() ^  l1.dir()) == 0; }
db toline(const P& p,const P& s, const P& e){// 点到直线的距离
	return fabs((p - s) ^ (e - s)) / len(s, e);
}
db toseg(P p, P s, P e){ // 点到线段的距离
	if(sgn((p - s) * (e - s)) < 0 || sgn((p - e) * (s - e)) < 0)
		return min(len(s, p),len(e, p));
	return toline(p, s, e);
}
P pedal(const P& p, const L& l){ // 点到直线的垂足
	P v;
	if(sgn(cross(p, l.ps[0], l.ps[1])) >= 0) v = r90c(l.ps[1] - l.ps[0]);
	else v = l90c(l.ps[1] - l.ps[0]);
	v = unit(v);
	return p + v * toline(p, l.ps[0], l.ps[1]);
}
bool intersect(db l1, db r1,db l2,db r2){//同一直线上两线段相交
    if(l1 > r1) swap(l1,r1); 
    if(l2 > r2) swap(l2,r2); 
    return !(lt(r1, l2) || lt(r2, l1));
}  
// 直线相交只需一次跨立实验
bool isSS(const P& p1,const P& p2, const P& q1, const P& q2){// 线段相交
    return intersect(p1.x, p2.x, q1.x, q2.x) && intersect(p1.y, p2.y, q1.y, q2.y) && 
    crossOp(p1, p2, q1) * crossOp(p1, p2, q2) <= 0 && crossOp(q1, q2, p1)
            * crossOp(q1, q2, p2) <= 0;
}
  
bool isSS_strict(P p1, P p2, P q1, P q2){ // 线段严格相交
    return crossOp(p1,p2,q1) * crossOp(p1,p2,q2) < 0 && crossOp(q1,q2,p1)
            * crossOp(q1,q2,p2) < 0;
}
  
bool sameDir(L l0, L l1) { return parallel(l0, l1) && sgn(l0.dir() * l1.dir()) == 1; }

bool cmp(const P& a, const P& b) {
    if (quad(a) != quad(b)) {
        return quad(a) < quad(b);
    } else {
        return sgn(a ^ b) > 0;
    }
}

bool operator < (L l0, L l1) {
    if (sameDir(l0, l1)) {
        return l1.include(l0[0]);
    } else {
        return cmp(l0.dir(), l1.dir());
    }
}

bool check(L u, L v, L w) { 
    return w.include(isLL(u,v)); 
}

bool isMiddle(db a, db m, db b) {
    return sgn(a - m) == 0 || sgn(b - m) == 0 || ((a < m) != (b < m));
}
  
bool isMiddle(P a, P m, P b) {
    return isMiddle(a.x, m.x, b.x) && isMiddle(a.y, m.y, b.y);
}
bool onSeg(P p1, P p2, P q){
    return crossOp(p1,p2,q) == 0 && isMiddle(p1, q, p2);
}
 
bool onSeg_strict(P p1, P p2, P q){
    return crossOp(p1,p2,q) == 0 && sgn((q-p1).dot(p1-p2)) * sgn((q-p2).dot(p1-p2)) < 0;
}

// polygon
vector<P> halfPlaneIS(vector<L> &l) {// 半平面交
	sort(all(l));// 从pi(-pi)开始顺时针排序
    deque<L> q;
    for (int i = 0; i < (int)l.size(); ++i) {
        if (i && sameDir(l[i], l[i - 1])) continue;
        while (q.size() > 1 && !check(q[q.size() - 2], q[q.size() - 1], l[i])) q.pop_back();
        while (q.size() > 1 && !check(q[1], q[0], l[i])) q.pop_front();
        q.push_back(l[i]);
    }
    while (q.size() > 2 && !check(q[q.size() - 2], q[q.size() - 1], q[0])) q.pop_back();
    while (q.size() > 2 && !check(q[1], q[0], q[q.size() - 1])) q.pop_front();
    vector<P> ret;
    for (int i = 0; i < (int)q.size(); ++i) ret.push_back(isLL(q[i], q[(i + 1) % q.size()]));
    return ret;
}

vector<P> convexHull(vector<P> ps) {//从左边逆时针
    int n = ps.size(); if(n <= 1) return ps;
    sort(ps.begin(), ps.end());
    vector<P> qs(n * 2); int k = 0;
    for (int i = 0; i < n; qs[k++] = ps[i++]) 
        while (k > 1 && crossOp(qs[k - 2], qs[k - 1], ps[i]) <= 0) --k; // 内角 < 180
    for (int i = n - 2, t = k; i >= 0; qs[k++] = ps[i--])
        while (k > t && crossOp(qs[k - 2], qs[k - 1], ps[i]) <= 0) --k;
    qs.resize(k - 1);
    return qs;
}
db RotateCalipers(vector<P>& c){ // 旋转卡壳(求凸包直径平方)
	c.emplace_back(c[0]);
	int n = c.size();
	db ans = 0;
	int j = 2;
	for(int i = 0; i < n; i ++){
		// 枚举每条线段,j作为顶点,通过叉积求顶点到与边的三角面积来判断点到边距离的大小
		while(lt((c[i] - c[i + 1]) ^ (c[i + 1] - c[j]), (c[i] - c[i + 1]) ^ (c[i + 1] - c[j + 1]))) j = (j + 1) % n;
		ans = max(ans, max(len2(c[i], c[j]), len2(c[i + 1], c[j]))); // 左右端点之一到j的距离
	}
	return ans;
}
bool checkconvex(vector<P>& a){ // 判断多边形是否为凸包！
	int n = a.size();
	psort(a);
	for(int i = 2; i < n; i ++){
		if(crossOp(a[i - 2], a[i - 1], a[i]) < 0) return false;
	}
	if(crossOp(a[n - 2], a[n - 1], a[0]) < 0) return false;
	return true;
}
vector<P> convexCut(const vector<P>&ps, P q1, P q2) {// 线对应的半平面与多边形的交
    vector<P> qs;
    int n = ps.size();
    for(int i = 0; i < n; i ++){
        P p1 = ps[i], p2 = ps[(i+1)%n];
        int d1 = crossOp(q1,q2,p1), d2 = crossOp(q1,q2,p2);
        if(d1 >= 0) qs.push_back(p1);
        if(d1 * d2 < 0) qs.push_back(isLL(p1,p2,q1,q2));
    }
    return qs;
}
int contain(const vector<P>& ps,const P& p){ //2:inside,1:on_seg,0:outside
	// 点引一条射线,奇内偶外
    int n = ps.size(), ret = 0; 
    for(int i = 0; i < n; i ++){
        P u = ps[i],v = ps[(i + 1) % n];
        if(onSeg(u, v, p)) return 1;
        if(cmp(u.y, v.y) <= 0) swap(u, v);
        if(cmp(p.y, u.y) > 0 || cmp(p.y, v.y) <= 0) continue; //上闭下开
        ret ^= crossOp(p,u,v) > 0;
    }
    return ret * 2;
}


struct Circle { 
	P O; 
	db r; 
	Circle(){}
	Circle(P _o, db _r):O(_o),r(_r){}
}; 
//`0 圆外`
//`1 圆上`
//`2 圆内`
db area(const Circle& c){ return pi * c.r * c.r;}
int relation(const P& b, const Circle& c){//点与圆的关系
	db dst = len(b - c.O);
	if(sgn(dst - c.r) < 0) return 2;
	else if(sgn(dst - c.r) == 0) return 1;
	return 0;
}
int relationcircle(const Circle& a, const Circle& b){// 两圆关系
	db d = len(a.O, b.O);
	if(sgn(d - a.r - b.r) > 0) return 5; // 相离
	if(sgn(d - a.r - b.r) == 0) return 4; // 外切
	db l = fabs(a.r - b.r);
	if(sgn(d - a.r - b.r) < 0 && sgn(d - l) > 0) return 3; // 相交
	if(sgn(d - l) == 0) return 2; // 内切
	if(sgn(d - l) < 0) return 1; // 内含
	return 0;
}

vector<P> inter(Circle C1, Circle C2){ // 求两圆交点
    P v1 = C2.O - C1.O, v2 = r90c(v1);
    db d = len(v1);
    if (gt(d, C1.r + C2.r) || gt(abs(C1.r - C2.r), d)) return {};
    if (eq(d, C1.r + C2.r) || eq(d, abs(C1.r - C2.r))) return {C1.O + C1.r / d * v1};
    db a = ((C1.r * C1.r - C2.r * C2.r) / d + d) / 2;
    db h = sqrt(C1.r * C1.r - a * a);
    P av = a / len(v1) * v1, hv = h / len(v2) * v2;
    return {C1.O + av + hv, C1.O + av - hv};
}
vector<P> inter(L l, Circle C){// 直线与圆的交点
    P p = pedal(C.O, l);
    db h = len(p - C.O);
    if (gt(h, C.r)) return {};
    if (eq(h, C.r)) return {p};
    double d = sqrt(C.r * C.r - h * h);
    P vec = (d / len(l.ps[1] - l.ps[0])) * (l.ps[1] - l.ps[0]);
    return {p + vec, p - vec};
}

Circle Circumscribed_triangl(const P& a, const P& b, const P& c){// 三角形的外接圆
	// 中垂线
	L u = L((a + b) / 2,((a + b) / 2) + (r90c(b - a)));
	L v = L((b + c) / 2,((b + c) / 2) + (r90c(c - b)));
	// 两条中垂线交点为圆心
	P p = isLL(u, v);
	db r = len(p, a);
	return Circle(p, r);
}

Circle Incircle_triangle(const P& a, const P& b, const P& c){// 三角形的内接圆
	L u,v;
	db m = atan2(b.y - a.y,b.x - a.x), n = atan2(c.y - a.y,c.x - a.x);
	u.ps[0] = a;
	u.ps[1] = u.ps[0] + P(cosl((n + m) / 2),sinl((n + m) / 2));
	v.ps[0] = b;
	m = atan2(a.y - b.y,a.x - b.x) , n = atan2(c.y - b.y,c.x - b.x);
	v.ps[1] = v.ps[0] + P(cosl((n + m) / 2),sinl((n + m) / 2));
	P p = isLL(u, v);
	db r = toseg(p, a, b);
	return {p, r};
}
vector<L> tangentline(const P& p, const Circle& c){// 过一点作圆的切线
	// 点一定在圆外
	db d = len(p, c.O);
	P v1 = p - c.O;
	db ang = acosl(c.r / d);
	P v2 = rrota(v1, ang);
	P v3 = lrota(v1, ang);
	v2 = unit(v2);
	v3 = unit(v3);
	vector<L> res;
	res.pb(L(p, c.O + v2 * c.r));
	res.pb(L(p, c.O + v3 * c.r));
	return res;
}
vector<P> commonTangents(const Circle& o1, const Circle& o2){// 求两圆公切线在圆o1上的切点
	db rdif = o1.r - o2.r, rsum = o1.r + o2.r;
	P a = o2.O - o1.O, b = a / len(a) * o1.r;
	vector<P> res;
	db alpha;
 	if(abs(abs(rdif) - len(a)) < eps){ // 两圆内切
		if(rdif < 0) alpha = acosl(-1);
		else alpha = acosl(1);
		res.push_back(o1.O + rrota(b,alpha));
	}else if(abs(rdif) < len(a) - eps){ // 两圆相交
		alpha = acosl(rdif / len(a));
		res.push_back(o1.O + rrota(b,alpha));
		res.push_back(o1.O + rrota(b,-alpha));
	}
	if(abs(rsum - len(a)) < eps){ // 两圆相切
		alpha = acosl(1);
		res.push_back(o1.O + rrota(b,alpha));
	}else if(rsum < len(a) - eps){ // 两圆相离
		alpha = acos(rsum / len(a));
		res.push_back(o1.O + rrota(b,alpha));
		res.push_back(o1.O + rrota(b,-alpha));
	}
	return res;
}

double areatriangle(const P& a, const P& b, const Circle& c){
	// 圆心O与a,b围成的三角形与圆的面积交
	P p = c.O; 
	if(sgn((p - a) ^ (p - b)) == 0)return 0.0;
	P q[5];
	int len = 0;
	q[len++] = a;
	L l(a, b);
	vector<P> tmp = inter(l, c);
	if(SZ(tmp) == 2){
		q[1] = tmp[0], q[2] = tmp[1];
		if(sgn((a - q[1]) * (b - q[1])) < 0) q[len++] = q[1];
		if(sgn((a - q[2]) *(b - q[2])) < 0) q[len++] = q[2];
	}
	q[len++] = b;
	if(len == 4 && sgn((q[0] - q[1]) * (q[2] - q[1])) > 0) swap(q[1], q[2]);
	db res = 0;
	for(int i = 0;i < len - 1; i++){
		if(relation(q[i], c) == 0 || relation(q[i + 1], c) == 0){
			db arg = rad(p, q[i], q[i + 1]);
			res += c.r * c.r * arg / 2.0;
		}
		else{
			res += fabs((q[i] - p) ^ (q[i + 1] - p)) / 2.0;
		}
	}
	return res;
}
Circle get_minCircle(vector<P> ps){// 最小圆覆盖
	random_shuffle(ps.begin(), ps.end());
	P o(0, 0);
	db r2 = 0;
	int n = ps.size();
	rep(i, 0, n){
		if(len2(ps[i] - o) > r2){
			o = ps[i], r2 = 0;
			rep(j, 0, i){
				if(len2(ps[j] - o) > r2){
					o = (ps[i] + ps[j]) / 2, r2 = len2(ps[j] - o);
					rep(k, 0, j){
						if(len2(ps[k] - o) > r2){
							Circle c = Circumscribed_triangl(ps[i], ps[j], ps[k]);
							o = c.O, r2 = c.r * c.r;
						}
					}
				}
			}
		}
	}
	return Circle(o, sqrt(r2));
}
db areacircle(const Circle& c, vector<P>& pyg){// 多边形与圆的面积交
	db ans = 0;
	int n = pyg.size();
	for(int i = 0;i < n;i++){
		int j = (i + 1) % n;
		if(sgn((pyg[j] - c.O) ^ (pyg[i] - c.O)) >= 0)
			ans += areatriangle(pyg[i], pyg[j], c);
		else ans -= areatriangle(pyg[i], pyg[j], c);
	}
	return fabs(ans);
}

db areacircle(const Circle& a, const Circle& b){ // 圆与圆的面积交
	int rel = relationcircle(a, b);
	if(rel >= 4) return 0.0;
	if(rel <= 2) return min(area(a), area(b));
	db d = len(a.O, b.O);
	db hf = (a.r + b.r + d) / 2.0;
	db ss = 2 * sqrt(hf *(hf - a.r) * (hf - b.r) * (hf - d));
	db a1 = acosl((a.r * a.r + d * d - b.r * b.r) / (2.0 * a.r * d));
	a1 = a1 * a.r * a.r;
	db a2 = acosl((b.r * b.r + d * d - a.r * a.r) / (2.0 * b.r * d));
	a2 = a2 * b.r * b.r;
	return a1 + a2 - ss;
}

//min_dist

// 二维平面最近点对
db min_dist(const vector<P>&ps, int l, int r){//左闭右开	
	// 调用前先进行x排序
	//sort(all(a), [&](P a,P b){return (a.x == b.x ? a.y < b.y : a.x < b.x);});
    if(r - l <= 5){
        db ret = 1e100;
        rep(i, l, r) rep(j, l, i) ret = min(ret, len(ps[i], ps[j]));
        return ret;
    }
    int m = (l + r) >> 1;
    db ret = min(min_dist(ps,l,m), min_dist(ps,m,r));
    vector<P> qs; rep(i, l, r) if(abs(ps[i].x - ps[m].x) <= ret) qs.pb(ps[i]);
    sort(qs.begin(), qs.end(),[&](const P& a, const P& b){
    	return (a.y == b.y ? a.x < b.x : a.y < b.y); });
    rep(i, 1, qs.size()) for(int j = i - 1; j >= 0 && qs[j].y >= qs[i].y - ret; --j)
        ret = min(ret,len(qs[i], qs[j]));
    return ret;
}