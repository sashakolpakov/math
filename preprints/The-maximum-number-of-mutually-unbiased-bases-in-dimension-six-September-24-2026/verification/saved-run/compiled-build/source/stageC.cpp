#define REFINE_HEADER
#include "stageB.cpp"
#define FOR(i,n) for(int i=0;i<int(n);++i)
const int d=6;
const double inv=1./sqrt(6.);
double TT[maxK][6][6];
int tk=0;
struct cx {
 double a,b;
 cx operator+(cx x)const{return{a+x.a,b+x.b};}
 cx operator-(cx x)const{return{a-x.a,b-x.b};}
 cx& operator+=(cx x){a+=x.a;b+=x.b;return *this;}
};
inline double imagconj(cx s,cx q){return s.a*q.b-s.b*q.a;}
inline double norm(cx x){return x.a*x.a+x.b*x.b;}
inline double sq(double x){return x*x;}
using bin=array<int,6>;
                                                                                  
template<int n> inline void solve(double (&A)[n][n],double (&x)[n]){
 double D[n];
 FOR(i,n){
   D[i]=1./A[i][i];
   for(int j=i+1;j<n;j++){
      double l=A[j][i]*D[i];
      for(int k=j;k<n;k++)A[k][j]-=A[k][i]*l;
      x[j]-=x[i]*l;
   }
   x[i]*=D[i];                    
 }
 for(int j=n-1;j>0;j--)FOR(i,j)x[i]-=A[j][i]*D[i]*x[j];
}
struct Layer{
 double p[6][6],r,rt,K,w,half,rn,xnorm,xone,xinf;
 bool overflow=false;
 static constexpr size_t binCap=2000000;
 int N,linear;
 vector<array<cx,6>> tab[6];
 vector<bin> bins;
 uint64_t count1=0,count2=0,count3=0,count4=0;
 array<array<cx,6>,6> q;
 double J[6][6],jj[6],c[6],A[6][6];
 void init(){
   w=1./N; half=.5/N+1e-12;
   xnorm=sqrt(5-1./6)*half+1e-12; xone=5*half+1e-12; xinf=1.5*half+1e-12;                                                                                                           
   FOR(j,d){
     tab[j].resize(N);
     FOR(b,N) FOR(i,d){
       double ph=(j==0?0:(b+.5)*w)-p[j][i];
       V z=expair(ph);tab[j][b][i]={z[0]*inv,z[1]*inv};
     }
   }
 }
 void test(bin b){
                              
   count1++;
   FOR(j,d)q[j]=tab[j][b[j]];
   cx S[d]; double Sm=0,dist=0;
   double magtol=2*pi*(xone*inv+r);
   FOR(i,d){
     cx z{0,0};
     FOR(j,d)z+=q[j][i];
     double s=norm(z);
     if((magtol<1 && s<sq(1-magtol)-2e-7) || s>sq(1+magtol)+2e-7)return;
     s=sqrt(s);
     dist+=sq(s-1);
     Sm=max(Sm,s);
     S[i]=z;
     c[i]=(norm(z)-1)/(4*pi);
   }
   if(dist>sq(2*pi*(K*xnorm+r))+2e-7)return;
   count2++;
   double jmax=0;
   double rho=pi*(sq(K*xnorm+r) + Sm*(K*xinf*xnorm+inv*(2*xnorm*r + r*r)));
   FOR(i,d){
     double one=0, two=0;
     FOR(j,d){
       double a=-imagconj(S[i],q[j][i]);
       if(j)one+=abs(a);
       J[i][j]=a;
       two+=a*a;
     }
     jj[i]=two;
     two=sqrt(two);
     jmax=max(jmax,two);
     if(abs(c[i])>one*half+two*r+min(rho,pi*(sq(xone*inv+r)+Sm*inv*sq(xnorm+r)))+2e-7)return;                                                                                                                                                                                                                                                                                                                
   }
   count3++;
   if(!linear)goto keep;
   {
     double M[d][d],y[d],B[d][maxK]{},G[d][d],aa[d],Dreal[d][d];
     double normB=0, extra=rho+jmax*rn;
     FOR(i,d){
       aa[i]=norm(S[i]);
       FOR(j,d){
         FOR(k,tk) B[i][k]+=J[i][j]*TT[k][j][i];
         Dreal[i][j]=S[i].a*q[j][i].a+S[i].b*q[j][i].b;
       }
       FOR(k,tk)normB+=sq(B[i][k]);
     }
     FOR(i,d) FOR(k,i+1) {
       double val=0;
       FOR(j,d)val+=J[i][j]*J[k][j];
       A[i][k]=val;
       val=0;
       FOR(j,tk)val+=B[i][j]*B[k][j];
       G[i][k]=val;
     }
     double fJ=xnorm/max(1e-6,Sm), fB=rt/sqrt(max(1e-6,normB/4)), fE=extra;
     FOR(it,linear){
     FOR(i,d)y[i]=c[i];
     FOR(i,d){FOR(k,i+1)M[i][k]=A[i][k]*fJ+G[i][k]*fB; M[i][i]+=fE;}
     solve(M,y);
     double my=0;bool good=true;FOR(i,d){if(!isfinite(y[i]))good=false;else my=max(my,abs(y[i]));}
     if(!good || !(my>1e-100 && my<1e100))break;
     FOR(i,d)y[i]/=my;                                                             
     double a=0,ny=0, nh=0, zb[d]{},zr[d]{},hb[maxK]{},mY=0,mYS=0, nYS=0;
     FOR(i,d){
       a+=c[i]*y[i];ny+=sq(y[i]);nh+=sq(y[i])*jj[i];
       FOR(j,d){
         zb[j]+=y[i]*J[i][j];
         zr[j]+=y[i]*Dreal[i][j];
       }
       FOR(j,tk)hb[j]+=y[i]*B[i][j];
       mY=max(mY,abs(y[i]));
       mYS=max(mYS,sq(y[i])*aa[i]);
       nYS+=sq(y[i])*aa[i];
     }
     double one=0,two=0,m_s=0,h_s=0; FOR(j,d){
       if(j)one+=abs(zb[j]);
       two+=sq(zb[j]);
       m_s=max(m_s,sq(zb[j])+sq(zr[j]));
     }
     FOR(j,tk)h_s+=sq(hb[j]);
     double bJ=one*half, bB=rt*sqrt(h_s), 
       bE=rn*sqrt(nh) + pi*(mY*sq(K*xnorm+r)
          +min(sqrt(m_s)*xnorm,K*sqrt(nYS)*xinf)*xnorm
          +2*inv*sqrt(nYS)*xnorm*r +inv*sqrt(mYS)*r*r);
     if(abs(a)>bJ+bB+bE+2e-7)return;
     fJ=xnorm*sqrt(ny/max(two,1e-5*ny));
     fB=rt*sqrt(ny/max(h_s,1e-5*ny));
     fE=bE/sqrt(ny+1e-300);
     if(!ny)break;
     }
   }
   keep:
   count4++;
   if(bins.size()>=binCap){overflow=true;return;}
   bins.push_back(b);
 }
 void gen0(){
   FOR(a,N)FOR(b,N)FOR(c,N)FOR(e,N)FOR(f,N){test({0,a,b,c,e,f});if(overflow)return;}
 }
 void gen1(const vector<bin>&prev){
   for(auto&x:prev)FOR(b,32){
     bin v{};
     FOR(j,5)v[j+1]=2*x[j+1]+((b>>j)&1);
     test(v);if(overflow)return;
   }
 }
 void report(){fprintf(stdout,"N%d r%.4f K%.3f %lu/%lu/%lu/%lu\n",N,r,K,count4,count3,count2,count1);}
} layer;

using pt=array<double,6>;
struct ball {pt v{}; double s=0; int n=0;};
vector<ball> balls;
inline pt diff(const pt&v,const pt&cent, bool &far,double cut){
  pt r{};
  double a=0;
  FOR(i,d){
    double z=v[i]-cent[i];                      
    z-=nearbyint(z);
    if(abs(z)>=cut){far=true;return r;}
    a+=(r[i]=z);
  }
  FOR(i,d)r[i]-=a/6;
  far=false;
  return r;
}
inline double len(const pt&v){
 double x=0; for(auto z:v)x+=z*z;return x;
}
bool cluster(const vector<bin>& bins,double R,int iters){
 double w=layer.w, tol2=sq(R-w*1.11),cut=sqrt(2*tol2)+1e-10;
                                                    
 balls.clear();
 FOR(it,iters){
 vector<ball> next(balls.size());
 for(bin b:bins){
   pt u;
   FOR(i,d)u[i]=i?(b[i]+.5)*w:0;
   int ix=-1;
   pt delta{};
   double dst=tol2;
   FOR(j,(int)balls.size()){
     bool far;
     pt x=diff(u,balls[j].v,far,cut);
     if(far)continue;
     double y=len(x);
     if(y<=dst){
       dst=y; ix=j; delta=x;
     }
   }
   if(ix<0){
     if(balls.size()>=2048)return false;
     ix=balls.size(); balls.push_back({u});next.emplace_back();dst=0;
   }
   FOR(i,d)next[ix].v[i]+=delta[i]-delta[0];
   next[ix].n++;
   next[ix].s=max(next[ix].s,sqrt(dst)+layer.xnorm+1e-9);
 }
 vector<ball> b;
 FOR(j,(int)balls.size()){
   if(next[j].n==0)continue;
   pt u=balls[j].v;
   if(it+1<iters){
     FOR(i,d)u[i]+=next[j].v[i]/next[j].n;
   }
   
   FOR(i,d)if(!(abs(u[i])<=2.))return false;
   if(!(next[j].s<.1 && next[j].s>=0))return false;
   b.push_back({u,next[j].s,next[j].n});
 }
 balls=move(b);
 }
 return true;
}
double RB=.04;

struct single {
 double s, e0;
 cx v[d],S[d],R[d][d];
 double J[d][d],jj[d],Sm,B[d][maxK]{},c[d];
 void init(ball b){
   s=b.s;
   Sm=0;
   double jjmax=0;
   const auto &p=layer.p;
   double K=layer.K,r=layer.r, n=layer.rn;
   FOR(i,d){
     V ev=expair(b.v[i]);v[i]={ev[0],ev[1]};
     cx q[d],sum{};
     FOR(j,d){
       double ph=b.v[j]-p[j][i];V evj=expair(ph);
       sum+=(q[j]={evj[0]*inv,evj[1]*inv});
     }
     S[i]=sum;
     FOR(j,d){
       R[i][j]={S[i].a*q[j].a+S[i].b*q[j].b, imagconj(S[i],q[j])};
       J[i][j]=-R[i][j].b;
     }
     jj[i]=0;
     FOR(j,d)jj[i]+=sq(J[i][j]);
     jjmax=max(jjmax,jj[i]);
     FOR(k,tk){B[i][k]=0;FOR(j,d)B[i][k]+=J[i][j]*TT[k][j][i];}
     Sm=max(Sm,sqrt(norm(S[i])));
     c[i]=(norm(sum)-1)/(4*pi);
   }
   e0=pi*(sq(K*s+r)+Sm*(K*s*s+inv*(2*s*r+r*r)))+n*sqrt(jjmax);
 }
 void support(const double*y,double*b,double*z,double &error)const{
   double ym=0,nS=0,mS=0,nJ=0;
   double zz[d]{};
   FOR(i,d){
     FOR(k,tk)b[k]-=y[i]*B[i][k];
     FOR(k,d){z[k]+=y[i]*J[i][k];zz[k]+=y[i]*R[i][k].a;}
     double y2S=sq(y[i])*norm(S[i]);
     ym=max(ym,abs(y[i]));
     nJ+=sq(y[i])*jj[i];
     nS+=y2S;
     mS=max(mS,y2S);
   }
   double mz=0;
   FOR(j,d)mz=max(mz,sq(zz[j])+sq(z[j]));
   double K=layer.K,r=layer.r,n=layer.rn;
   error=pi*(sq(K*s+r)*ym + s*s*sqrt(mz)
              + 2*s*r*inv*sqrt(nS)+ r*r*inv*sqrt(mS))
            +n*sqrt(nJ);
 }
};
int words=0;
struct BS {
 static const int L=32;
 uint64_t data[L]{};
 inline void set(int i){data[i/64]|=uint64_t(1) << (i%64);}
 inline void del(int i){data[i/64]&=~(uint64_t(1) << (i%64));}
 BS operator&(const BS&o)const{
   BS b; FOR(i,words)b.data[i]=data[i]&o.data[i]; return b;
 }
 int count()const{
   int n=0; FOR(i,words)n+=__builtin_popcountll(data[i]);return n;
 }
 inline bool empty()const{FOR(i,words)if(data[i])return false;return true;}
 inline int first()const{
   FOR(i,words)if(data[i])return i*64+__builtin_ctzll(data[i]);abort();
 }
};
struct node{
 BS O,U;
 single v;
};
vector<node> nodes;
int detail=2, searchMode=1;
uint64_t capSteps=5000000;
struct graph{
 int ol,ul;
 static uint64_t steps;
 static bool gaveup;
 template<int k> inline bool joint(const single& a,const single& b,const double D[][6], const double *q, double ed)const{
    if(!detail)return true;
    const int m=12+k;
    const single*X[2]={&a,&b};
    double J[2][m][6]{}, B[m][maxK]{}, c[m]{}, M[m][m],G[2][m][m]{},GB[m][m]{};
    FOR(t,2){
      int o=t*d;
      FOR(i,d){
        c[o+i]=X[t]->c[i];
        FOR(j,d)J[t][o+i][j]=X[t]->J[i][j];
        FOR(l,tk)B[o+i][l]=-X[t]->B[i][l];
      }
      FOR(i,k)FOR(j,d)J[t][12+i][j]=(t?-1:1)*D[i][j];
      FOR(i,6+k){
        int g=(i<6?i+o:6+i);
        FOR(j,i+1){
          int h=(j<6?j+o:6+j);
          FOR(l,d)G[t][g][h]+=J[t][g][l]*J[t][h][l];
        }
      }
    }
    FOR(i,k)c[12+i]=q[i];
    FOR(i,12)FOR(j,i+1)FOR(l,tk)GB[i][j]+=B[i][l]*B[j][l];
    double s[2]={a.s,b.s}, e[2]={a.e0,b.e0}, r=layer.r,
       rt=layer.rt, f[2]={s[0],s[1]}, fE[2]={e[0],e[1]}, fD=ed,fB=2*rt;
    FOR(it,detail){
      FOR(i,m){
        FOR(j,i+1) M[i][j]=G[0][i][j]*f[0]+G[1][i][j]*f[1]+GB[i][j]*fB;
        M[i][i]+=(i>=12?fD:fE[i/d])+.000001;
      }
      double y[m];
      FOR(i,m)y[i]=c[i];
      solve(M,y);
      double my=0;bool good=true;FOR(i,m){if(!isfinite(y[i]))good=false;else my=max(my,abs(y[i]));}
      if(!good || !(my>1e-100 && my<1e100))return true;
      FOR(i,m)y[i]/=my;
      double yc=0,yn=0;
      FOR(i,m){yc+=c[i]*y[i];yn+=sq(y[i]);}
      if(yn<1e-100)return true;               
      double en=0,sup,zB[maxK]{},zx[2][d]{};
      FOR(i,k)en+=sq(y[12+i]);
      double err=ed*sqrt(en);
      sup=err;
      fD=ed*sqrt(yn/max(en,1e-6*yn));
      FOR(t,2){
        X[t]->support(y+t*d,zB,zx[t],err);
        FOR(i,k)FOR(j,d)zx[t][j]+=(t?-1:1)*y[12+i]*D[i][j];
        en=0;double l2=0;
        FOR(j,d){l2+=sq(zx[t][j]);en+=sq(y[t*d+j]);}
        sup+=s[t]*sqrt(l2)+err;
        f[t]=s[t]*sqrt(yn/max(l2,1e-6*yn));
        fE[t]=e[t]*sqrt(yn/max(en,1e-6*yn));
      }
      en=0; FOR(i,tk)en+=sq(zB[i]);
      sup+=rt*sqrt(en);
      fB=rt*sqrt(yn/max(en,1e-6*yn));
      if(abs(yc)>sup+3e-7)return false;
    }
    return true;
 }
 void pairtest(int i,int j){
   auto &a=nodes[i].v, &b=nodes[j].v;
   cx Q[d], S{};
   double r=a.s+b.s+1e-10;
   FOR(k,d){
     Q[k]={a.v[k].a*b.v[k].a+a.v[k].b*b.v[k].b,imagconj(b.v[k],a.v[k])};
     S+=Q[k];
   }
   double mag=sqrt(norm(S));
   double disto=mag/(2*pi)*inv, distu=abs(mag*inv-1)/(2*pi);
   if(min(disto,distu)>r+2e-7)return;
   double A[2][d]{},J[2][d]{},q[2]{},jj=0,eps;
   FOR(k,d){
     A[0][k]=-Q[k].b; A[1][k]=Q[k].a;
     J[0][k]=(S.a*A[0][k]+S.b*A[1][k])/6;
     jj+=sq(J[0][k]);
   }
   if(disto<=r+2e-7){
                       
     q[0]=S.a/(2*pi); q[1]=S.b/(2*pi);
     eps=pi*r*r+2e-8;
     if(norm(S)/(2*pi)>r*6*sqrt(jj)+eps*mag+2e-7)goto ut;
     if(!joint<2>(a,b,A,q,eps))goto ut;
     nodes[i].O.set(j);nodes[j].O.set(i);ol++;
   }
ut:
   if(distu>r+2e-7)return;
   q[0]=(norm(S)/6-1)/(4*pi);
   eps=pi*r*r*(1+mag/6)+2e-8;
   if(abs(q[0])>r*sqrt(jj)+eps+2e-7)return;
   if(!joint<1>(a,b,J,q,eps))return;
   nodes[i].U.set(j);nodes[j].U.set(i);ul++;
 }
 BS init(){
   nodes.clear();nodes.resize(balls.size());
   ol=ul=0;words=(int(nodes.size())+63)/64;
   if(words>BS::L)abort();
   BS p;
   FOR(i,nodes.size()){
     p.set(i);nodes[i].v.init(balls[i]);
   }
   FOR(i,nodes.size())FOR(j,i)pairtest(i,j);
   return p;
 }
 static inline bool tick(){
   if(++steps>capSteps){gaveup=true;return true;}
   return false;
 }
 static inline bool clique(BS o,int n){                            
   if(n<=0)return true;
   if(n==1)return !o.empty();
   while(o.count()>=n){
     if(tick())return true;
     int i=o.first();
     o.del(i);
     BS v=o&nodes[i].O;
     if(n==2?!v.empty():clique(v,n-1))return true;
   }
   return false;
 }
 static bool exist(BS o,BS u,int n){
   while(o.count()>=n){
     if(tick())return true;
     int i=o.first();
     o.del(i);
     if(n==6)u.del(i);                                                              
     BS pool=u&nodes[i].U;
     if(pool.count()<6)continue;
     if(n==1){if(clique(pool,6))return true;continue;}
     BS v=o&nodes[i].O;
     if(v.count()<n-1)continue;
     if(searchMode>=1 && !clique(pool,6))continue;                        
     if(gaveup)return true;
     if(exist(v,pool,n-1))return true;
   }
   return false;
 }
 static bool duo(BS a,BS b,int na,int nb){
   if(na==0)return clique(b,nb);
   if(nb==0)return clique(a,na);
   int ca=a.count(),cb=b.count();
   if(ca<na || cb<nb)return false;
   if(!clique(a,na) || !clique(b,nb))return false;                                  
   if(gaveup)return true;
                                                                  
   auto weight=[](int count,int need){
     double z=1.,f=1.;
     for(int j=0;j<need;j++){z*=double(count-j)*f/(j+1); f*=.22;}
     return z;
   };
   bool pick=weight(ca,na)<=weight(cb,nb);
   BS x=pick?a:b, y=pick?b:a;
   int nx=pick?na:nb, ny=pick?nb:na;
   while(x.count()>=nx){
     if(tick())return true;
     int i=x.first();x.del(i);
     BS xx=x&nodes[i].O;
     if(xx.count()<nx-1)continue;
     BS yy=y&nodes[i].U;
     if(yy.count()<ny)continue;
     if(pick?duo(xx,yy,na-1,nb):duo(yy,xx,na,nb-1))return true;
     if(gaveup)return true;
   }
   return false;
 }
 static bool startDuo(BS p){
   while(p.count()>=12){
     if(tick())return true;
     int i=p.first();p.del(i);
     BS a=p&nodes[i].O, b=p&nodes[i].U;
     if(duo(a,b,5,6))return true;
     if(gaveup)return true;
   }
   return false;
 }
 bool candidate(){
   steps=0;gaveup=false;
   BS p=init();
   bool q= searchMode>=2 ? startDuo(p) : exist(p,p,6);
   return q || gaveup;
 }
};
uint64_t graph::steps=0;
bool graph::gaveup=false;
struct paramsC{int M=12,layers=4,linear=1,lloyd=2;};
struct statC{
 uint64_t done=0,negative=0,overflow=0,clusterFail=0,cap=0,positive=0,totalBins=0,totalBalls=0;
};
bool negative(const Record&z,const paramsC& par,statC &stats){
 validate(z,.03);
 stats.done++;
 const Root&R=z.R;
 FOR(i,d)FOR(j,d)layer.p[i][j]=R.p[6*i+j];
 tk=R.k;FOR(a,tk)FOR(i,d)FOR(j,d)TT[a][i][j]=R.T[a][6*i+j];
 layer.K=1.00001;
 layer.r=z.radius;
 layer.rt=sqrt(1+R.ort)*layer.r+1e-9;
 layer.rn=R.n0+R.id*layer.r+R.C*layer.r*layer.r+1e-9;
 layer.linear=par.linear;
 vector<bin> prev;
 int M=par.M;
 FOR(k,par.layers){
   if(M<=0 || M>1024)abort();
   layer.N=M;
   layer.count1=layer.count2=layer.count3=layer.count4=0;
   layer.overflow=false;
   layer.bins.clear();
   layer.init();
   if(k==0)layer.gen0();
   else layer.gen1(prev);
   if(layer.overflow){stats.overflow++;return false;}
   layer.bins.swap(prev);
   if(prev.empty()){stats.negative++;return true;}
   M*=2;
 }
 stats.totalBins+=prev.size();
 if(!cluster(prev,RB,par.lloyd)){stats.clusterFail++;return false;}
 stats.totalBalls+=balls.size();
 graph g{};
 if(!g.candidate()){stats.negative++;return true;}
 if(graph::gaveup)stats.cap++;
 else stats.positive++;
 return false;
}
                                                                   
#ifndef STAGEC_HEADER
int main(int argc,char**argv){
 checkcpu();if(argc<12)abort();
 paramsC par;par.M=atoi(argv[1]);par.layers=atoi(argv[2]);par.linear=atoi(argv[3]);
 RB=atof(argv[4]);detail=atoi(argv[5]);searchMode=atoi(argv[6]);
 capSteps=strtoull(argv[7],nullptr,10);
 int part=atoi(argv[8]),parts=atoi(argv[9]);
 if(par.M<6 || par.M>24 || par.layers<1 || par.layers>6 ||
    par.linear<0 || par.linear>10 || !(RB>=.012 && RB<=.09) ||
    detail<0 || detail>10 || searchMode<0 || searchMode>2 ||
    capSteps<100 || capSteps>1000000000ull || parts<1 || part<0 || part>=parts)abort();
 vector<Record> bad;
 statC st{};
 size_t offset=0;
 auto start=chrono::steady_clock::now();
 for(int arg=11;arg<argc;arg++){
   auto v=readRecords(argv[arg]);
   for(size_t i=0;i<v.size();i++)if((offset+i)%size_t(parts)==size_t(part)){
     if(!negative(v[i],par,st))bad.push_back(v[i]);
     if(st.done%100==0){
       printf("done%lu bad%zu (graph%lu cap%lu over%lu cluster%lu) avg bins%.0f balls%.0f time %.1f\n",
        st.done,bad.size(),st.positive,st.cap,st.overflow,st.clusterFail,
        st.totalBins/double(st.done),st.totalBalls/double(st.done),
        chrono::duration<double>(chrono::steady_clock::now()-start).count());fflush(stdout);
     }
   }
   offset+=v.size();if(offset>8000000 || bad.size()>2000000)abort();
 }
 printf("result done%lu bad%zu (graph%lu cap%lu over%lu cluster%lu) time %.2f\n",
    st.done,bad.size(),st.positive,st.cap,st.overflow,st.clusterFail,
    chrono::duration<double>(chrono::steady_clock::now()-start).count());
 saveRecords(argv[10],bad);
 return bad.empty()?0:1;
}
#endif
