// BFS solver mirroring tools/rules.py.  stdin: level rows (one per line).  argv[1]: state cap.
// stdout: "OPT <len> <states> <moves>" | "NONE <states>" (exhausted) | "CAP <states>"
#include <algorithm>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
typedef pair<int,int> P;
struct En { int r, c, d; bool hunt; };
struct S { int pr, pc; bool dead; vector<P> bl, he, wa; vector<En> en; };
static int H, W, SIGHT = 6; static set<P> walls; static P EX{-1,-1};
static const int DR[4] = {-1,1,0,0}, DC[4] = {0,0,-1,1}; // U D L R
static const int OPP[4] = {1,0,3,2};
static const char NAME[5] = {'U','D','L','R','S'};
static bool inb(int r, int c){ return r>=0&&r<H&&c>=0&&c<W; }
static bool has(const vector<P>& v, P p){ for(auto&x:v) if(x==p) return true; return false; }
static string enc(const S& s){
  string k; k.push_back(s.pr); k.push_back(s.pc); k.push_back(s.dead);
  k.push_back(s.bl.size()); for(auto&p:s.bl){k.push_back(p.first);k.push_back(p.second);}
  k.push_back(s.he.size()); for(auto&p:s.he){k.push_back(p.first);k.push_back(p.second);}
  k.push_back(s.wa.size()); for(auto&p:s.wa){k.push_back(p.first);k.push_back(p.second);}
  for(auto&e:s.en){k.push_back(e.r);k.push_back(e.c);k.push_back(e.d);}
  return k;
}
static int sees(const S& s, const En& e){
  int r=e.r,c=e.c; if(r==s.pr&&c==s.pc) return -1; int d,dist;
  if(r==s.pr){ d = s.pc>c?3:2; dist=abs(s.pc-c);} else if(c==s.pc){ d = s.pr>r?1:0; dist=abs(s.pr-r);} else return -1;
  if(dist>SIGHT) return -1;
  for(int i=1;i<dist;i++){ P q{r+DR[d]*i,c+DC[d]*i}; if(walls.count(q)||has(s.bl,q)||q==EX) return -1; }
  return d;
}
static S worldTurn(const S& s0){
  S s=s0; size_t n=s.en.size();
  for(size_t i=0;i<n;i++){
    En e=s.en[i];
    auto freeq=[&](P q){
      if(!inb(q.first,q.second)||walls.count(q)||has(s.wa,q)||has(s.bl,q)||q==EX) return false;
      for(size_t j=0;j<n;j++) if(j!=i && s.en[j].r==q.first && s.en[j].c==q.second) return false;
      return true; };
    int sd = e.hunt ? sees(s,e) : -1; En m=e;
    if(sd>=0){ m.d=sd; P q{e.r+DR[sd],e.c+DC[sd]}; if(freeq(q)){m.r=q.first;m.c=q.second;} }
    else { P q{e.r+DR[e.d],e.c+DC[e.d]}; if(freeq(q)){m.r=q.first;m.c=q.second;} else m.d=OPP[e.d]; }
    s.en[i]=m;
    if(m.r==s.pr&&m.c==s.pc){ s.dead=true; return s; }
  }
  return s;
}
static bool playerMove(const S& s, int d, S& out){
  out=s; P t{s.pr+DR[d],s.pc+DC[d]};
  if(!inb(t.first,t.second)||walls.count(t)||has(s.wa,t)) return false;
  bool eHere=false; for(auto&e:s.en) if(e.r==t.first&&e.c==t.second) eHere=true;
  if(t==EX){ if(!s.he.empty()) return false; out.pr=t.first; out.pc=t.second; return true; }
  if(has(s.bl,t)){
    P u{t.first+DR[d],t.second+DC[d]};
    if(!inb(u.first,u.second)||walls.count(u)||u==EX||has(s.bl,u)||has(s.he,u)) return false;
    for(auto&e:s.en) if(e.r==u.first&&e.c==u.second) return false;
    out.bl.erase(find(out.bl.begin(),out.bl.end(),t));
    if(has(s.wa,u)) out.wa.erase(find(out.wa.begin(),out.wa.end(),u));
    else { out.bl.push_back(u); sort(out.bl.begin(),out.bl.end()); }
    out.pr=t.first; out.pc=t.second; return true;
  }
  auto it=find(out.he.begin(),out.he.end(),t); if(it!=out.he.end()) out.he.erase(it);
  out.pr=t.first; out.pc=t.second; out.dead=eHere; return true;
}
static bool step(const S& s, int a, S& out){
  if(s.dead || (s.pr==EX.first&&s.pc==EX.second)) return false;
  if(a==4){ out=worldTurn(s); return true; }
  S m; if(!playerMove(s,a,m)) return false;
  if((m.pr==EX.first&&m.pc==EX.second)||m.dead){ out=m; return true; }
  out=worldTurn(m); return true;
}
int main(int argc,char**argv){
  size_t cap = argc>1? stoull(argv[1]) : 2000000;
  vector<string> rows; string line; while(getline(cin,line)) if(!line.empty()) rows.push_back(line);
  H=rows.size(); W=rows[0].size(); S s0{0,0,false,{},{},{},{}};
  for(int r=0;r<H;r++) for(int c=0;c<W;c++){ char ch=rows[r][c]; P p{r,c};
    if(ch=='#'||ch=='N') walls.insert(p); else if(ch=='B') s0.bl.push_back(p); else if(ch=='H') s0.he.push_back(p);
    else if(ch=='~') s0.wa.push_back(p); else if(ch=='P'){s0.pr=r;s0.pc=c;} else if(ch=='E') EX=p;
    else if(strchr("^v<>",ch)){ int d= ch=='^'?0:ch=='v'?1:ch=='<'?2:3; s0.en.push_back({r,c,d,false}); }
    else if(strchr("udlr",ch)){ int d= ch=='u'?0:ch=='d'?1:ch=='l'?2:3; s0.en.push_back({r,c,d,true}); } }
  unordered_map<string,pair<int,char>> parent; // key -> (parent index, move)
  vector<S> nodes; vector<string> keys; unordered_map<string,int> idx;
  nodes.push_back(s0); keys.push_back(enc(s0)); idx[keys[0]]=0; parent[keys[0]]={-1,0};
  vector<int> par{-1}; vector<char> mv{0};
  for(size_t i=0;i<nodes.size();i++){
    S s=nodes[i];
    if(s.pr==EX.first&&s.pc==EX.second&&!s.dead){
      string out; for(int k=i;par[k]>=0;k=par[k]) out.push_back(mv[k]); reverse(out.begin(),out.end());
      printf("OPT %zu %zu %s\n",out.size(),nodes.size(),out.c_str()); return 0; }
    for(int a=0;a<5;a++){ S n; if(!step(s,a,n)) continue; string k=enc(n);
      if(idx.count(k)) continue; idx[k]=nodes.size(); nodes.push_back(n); par.push_back(i); mv.push_back(NAME[a]);
      if(nodes.size()>cap){ printf("CAP %zu\n",nodes.size()); return 0; } }
  }
  printf("NONE %zu\n",nodes.size());
}
