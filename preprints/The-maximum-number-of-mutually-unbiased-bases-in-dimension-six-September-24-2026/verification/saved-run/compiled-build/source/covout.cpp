#define HEADER
#include "seed.cpp"
#include <cstdint>
#include <cstring>
#include <chrono>
using i4=array<int,4>;

struct SI{xy p; double lo,hi; double J[2][5];};
SI extend(xy p,int s){
 SI o{};o.p=p;
 F(a,2)F(j,5)o.J[a][j]=tab[p.b[j]][a];
 double err=pi*(w/4)*5.;         
 o.lo=-.5; o.hi=.5;
 auto clip=[&](double x,double y){
   double v=(x*p.c[0]+y*p.c[1])*n, a=x*o.J[0][s]+y*o.J[1][s];
   if(abs(a)<1e-6)return;
   double r=hp(x,y)*err;
   F(j,5)if(j!=s)r+=.5*abs(x*o.J[0][j]+y*o.J[1][j]);
   double mid=-v/a; r=(r+1e-7)/abs(a);
   o.lo=max(o.lo,mid-r-1e-5);o.hi=min(o.hi,mid+r+1e-5);
 };
 clip(o.J[0][s],o.J[1][s]);
 F(j,5)if(j!=s)clip(-o.J[1][j],o.J[0][j]);
 return o;
}
struct cent{int ix; i4 y;};
struct RX{i4 x; int dummy;};      
struct indexed{array<int8_t,5> k; i4 y; int xsq,xab;};
int sq(int x){return x*x;}

struct coverSeeds{
 int K,m,dual;
 double R,RN2,T;
 vector<SI> X;
 vector<vector<SI>> Y;
 vector<vector<cent>> byX;
 vector<cent> all;
 vector<vector<indexed>> buckets;
 uint64_t checked=0,ncover=0,ncheap=0,nlp=0,nvisit=0;
 static double supdual(array<int,9> k,const SI&A,const SI&B,int iters){
                                                                                                      
   int s=A.p.s;
   double rows[9][4]{};
   F(j,5){rows[j][0]=A.J[0][j];rows[j][1]=A.J[1][j];}
   F(j,5){int h=j?4+j:s;rows[h][2]=B.J[0][j];rows[h][3]=B.J[1][j];}
   double rhs[4]={-n*A.p.c[0],-n*A.p.c[1],-n*B.p.c[0],-n*B.p.c[1]};
   double err=1.251*pi*w;
   double y[4]{}, reg[2]={.2,.2}, ww[9]={1.,1.,1.,1.,1.,1.,1.,1.,1.};
   double best=1e10;
   F(loop,iters){
     double M[4][4]{},v[4]{};
     F(j,9)F(a,4){
       double p=rows[j][a]*ww[j];
       v[a]+=p*k[j];
       F(b,a+1)M[a][b]+=p*rows[j][b];
     }
     F(a,4){M[a][a]+=reg[a/2]; v[a]-=2*rhs[a];}
     double D[4];
     F(i,4){D[i]=1./M[i][i];for(int j=i+1;j<4;j++){
       double l=M[j][i]*D[i]; for(int b=j;b<4;b++)M[b][j]-=l*M[b][i];v[j]-=l*v[i];
     }v[i]*=D[i];}
     for(int j=3;j>0;j--)F(i,j)v[i]-=M[j][i]*D[i]*v[j];
     bool usable=true;F(a,4)if(!(abs(v[a])<=1e4))usable=false;
     if(!usable)break;
     double u=0;
     F(a,4)u+=2*v[a]*rhs[a];
     F(e,2){double q=hp(v[2*e],v[2*e+1]); u+=2*err*q; reg[e]=2*err/max(.02,q);}
     F(j,9){double z=k[j];F(a,4)z-=rows[j][a]*v[a]; u+=abs(z);ww[j]=1./max(abs(z),.03);}
     best=min(best,u);
   }
   return best+.01;
 }
 bool testBucket(const vector<indexed>&pool,const SI&A,const SI&B){
   const ar &y=B.p.b;
   nvisit+=pool.size();
   for(auto &e:pool){
     array<int,9> k={e.k[0],e.k[1],e.k[2],e.k[3],e.k[4], y[1]-e.y[0],y[2]-e.y[1],y[3]-e.y[2],y[4]-e.y[3]};
     int s=e.xsq+sq(k[5])+sq(k[6])+sq(k[7])+sq(k[8]);
     if(s > int(T))continue;
     ncover++;
     int a=e.xab+abs(k[5])+abs(k[6])+abs(k[7])+abs(k[8]);
     if(s+a+2.25 < RN2){ncheap++;return true;}
     if(!dual || s-a > RN2)continue;
     nlp++;
     if(s+2.25+supdual(k,A,B,dual)<RN2) return true;
   }
   return false;
 }
 bool covered(const SI&A,const SI&B){
   int a=B.p.b[1]/K,b=B.p.b[2]/K,c=B.p.b[3]/K;
   for(int i=max(0,a-1);i<=min(m-1,a+1);i++)for(int j=max(i,b-1);j<=min(m-1,b+1);j++)
     for(int l=max(j,c-1);l<=min(m-1,c+1);l++)
       if(testBucket(buckets[(i*m+j)*m+l],A,B))return true;
   return false;
 }
 void insert(indexed u){
   int i=u.y[0]/K,j=u.y[1]/K,k=u.y[2]/K;buckets[(i*m+j)*m+k].push_back(u);
 }
 void run(seeds&S,double r,int d){
   R=r;dual=d; RN2=sq(1)*pow(R*n,2)-.0001;
   T=pow(sqrt(RN2)+1.5,2);
   K=int(R*n+.51); K=max(1,K);                                                      
   m=(n+K-1)/K;
   buckets.resize(m*m*m);
   for(auto p:S.xs)X.push_back(extend(p,p.s));
   Y.resize(n);F(i,n)for(auto p:S.ys[i])Y[i].push_back(extend(p,0));
   byX.resize(X.size());
   F(t,X.size()){
     const SI&A=X[t];
     for(auto&L:buckets)L.clear();
     F(h,t){
       const xy&p=X[h].p;
       if(p.s!=A.p.s)continue;
       indexed u{};
       int s=0,ab=0;
       F(j,5){int k=A.p.b[j]-p.b[j];u.k[j]=k;s+=sq(k);ab+=abs(k);}
       u.xsq=s;u.xab=ab;
       if(s>int(T) || s-ab > RN2)continue;
       for(auto cent:byX[h]){u.y=cent.y;insert(u);}
     }
     for(auto &B:Y[A.p.b[A.p.s]]){
       if(B.p.g+1e-8<1.-(A.p.b[4]+2)*w)continue;
       if(B.hi<A.lo || B.lo>A.hi)continue;
       checked++;
       if(covered(A,B))continue;
       cent c{t,{B.p.b[1], B.p.b[2], B.p.b[3], B.p.b[4]}};
       all.push_back(c); byX[t].push_back(c);
       indexed u{};u.y=c.y;insert(u);
     }
     if(!(t%10000))printf(" t%d/%zu cells%lu centers%zu\n",t,X.size(),checked,all.size());
   }
   printf("N%d r%.4f dual%d checked%lu centers%zu visit%lu near%lu cheap%lu lp%lu\n",n,R,dual,checked,all.size(),nvisit,ncover,ncheap,nlp);
 }
};
int main(int argc,char**argv){
 environment(); if(argc!=2)abort();
 auto st=chrono::steady_clock::now();
 seeds S;S.build(112);
 printf("xs%zu build%.2f\n",S.xs.size(),chrono::duration<double>(chrono::steady_clock::now()-st).count());
 coverSeeds C;C.run(S,.032,2);
 if(true){FILE*f=fopen(argv[1],"w"); if(!f)abort(); fprintf(f,"%d %zu\n",n,C.all.size());for(auto u:C.all){auto &p=C.X[u.ix].p;for(int b:p.b)fprintf(f,"%d ",b);fprintf(f,"%d ",p.s);for(int b:u.y)fprintf(f,"%d ",b);fprintf(f,"\n");}if(ferror(f)||fclose(f)!=0)abort();}
 printf("time %.2f\n",chrono::duration<double>(chrono::steady_clock::now()-st).count());
}
