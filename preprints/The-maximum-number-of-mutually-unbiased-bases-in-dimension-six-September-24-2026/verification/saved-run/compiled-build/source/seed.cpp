#include <cmath>
#include <cstdio>
#include <vector>
#include <array>
#include <algorithm>
#include <random>
#include <cfenv>
#include <limits>
#pragma STDC FENV_ACCESS ON
using namespace std;
#define F(i,n) for(int i=0;i<int(n);++i)
const double pi=0x1.921fb54442d18p+1;
inline void environment(){
 static_assert(numeric_limits<double>::is_iec559 && numeric_limits<double>::digits==53);
 if(fesetround(FE_TONEAREST)!=0 || fegetround()!=FE_TONEAREST) abort();
}


using ar=array<int,5>;
using V=array<double,2>;
inline V expair(double x){
 if(!(abs(x)<=16.))return {NAN,NAN};
 int k=int(nearbyint(4*x));
 double y=(x-.25*k)*(2*pi), yy=-y*y;
 double a=1.,b=y,ta=1.,tb=y;
 for(int j=1;j<=9;j++){
   ta=(ta*yy)/((2*j-1.)*(2*j)); tb=(tb*yy)/((2*j)*(2*j+1.));
   a+=ta; b+=tb;
 }
 switch((k%4+4)%4){case 0:return {a,b};case 1:return {-b,a};case 2:return {-a,-b};default:return {b,-a};}
}
inline double hp(double x,double y){return sqrt(x*x+y*y);}
struct xy{ar b; int s; double g,c[2];};
int n;double w;vector<V> tab;
bool sumok(xy&p){
 double c[2]={0.,-1./(2*pi)};
 for(auto b:p.b){
  c[0]+=tab[b][1]/(2*pi);c[1]-=tab[b][0]/(2*pi);
 }
 p.c[0]=c[0];p.c[1]=c[1];
 double err=pi*(w*w/4)*5.;
                          
 auto chk=[&](double x,double y){
   double l=abs(x*c[0]+y*c[1]),r=hp(x,y)*err;
   for(auto b:p.b)r+=(w/2)*abs(x*tab[b][0]+y*tab[b][1]);
   return !(l>r+1e-8);
 };
 if(!chk(c[0],c[1]))return false;
 for(auto b:p.b)if(!chk(-tab[b][1],tab[b][0]))return false;
 return true;
}
                                                            
bool share(const xy &X,const xy &Y){
 int b=Y.b[0], skip[2]={X.s,0};
 double low=-w/2,up=w/2;
 F(t,2){
   auto &p=t?Y:X;
   double err=pi*(w*w/4)*5.;
   auto clip=[&](double x,double y){
     double v=x*p.c[0]+y*p.c[1], a=x*tab[b][0]+y*tab[b][1];
     if(abs(a)<1e-6)return;
     double r=hp(x,y)*err;
     F(j,5)if(j!=skip[t])r+=(w/2)*abs(x*tab[p.b[j]][0]+y*tab[p.b[j]][1]);
     double mid=-v/a; r/=abs(a);
     low=max(low,mid-r-1e-10); up=min(up,mid+r+1e-10);
   };
   clip(tab[b][0],tab[b][1]);
   F(j,5)if(j!=skip[t]){int d=p.b[j]; clip(-tab[d][1],tab[d][0]);}
 }
 return low<=up;
}
struct seeds{
 vector<xy> xs; vector<vector<xy>> ys;
 static xy mk(ar b,bool sorted){
   xy p{};p.b=b;
   F(j,5)if(abs(b[j]*2+1-n)<abs(b[p.s]*2+1-n))p.s=j;
   if(!sorted)std::sort(b.begin(),b.end());
   p.g=.5*max(2*b[0]+1,2*n-(2*b[4]+1));
   F(j,4)p.g=max(p.g,double(b[j+1]-b[j]));
   p.g*=w;
   return p;
 }
 void build(int nn){
   n=nn;w=1./n;tab.clear();F(i,n)tab.push_back(expair((i+.5)/n));
   F(e,n)F(d,e+1)F(c,d+1)F(b,c+1)F(a,b+1){
     if(a>e-d+1)continue;
     xy p=mk({a,b,c,d,e},true);
     if(p.g>1.-(e-1)*w+1e-8)continue;
     if(sumok(p)) xs.push_back(p);
   }
   ys.resize(n);
   F(a,n)F(e,n)F(d,e+1)F(c,d+1)F(b,c+1){
     xy p=mk({a,b,c,d,e},false);
     if(sumok(p)) ys[a].push_back(p);
   }
 }
 vector<pair<xy,xy>> list(int samples=1000){
   vector<pair<xy,xy>> out;
   mt19937_64 rng(42);
   uint64_t m=0,h=0,ym=0,v=0;
   for(auto X:xs)for(auto Y:ys[X.b[X.s]]){
     ++ym;
     if(Y.g<1.-(X.b[4]+2.0001)*w)continue;
     ++h;
     if(!share(X,Y))continue;
     m++;
     if(out.size()<samples)out.emplace_back(X,Y);
     else if(samples>0){
       auto j=rng()%m;
       if(j<samples)out[j]={X,Y};
     }
   }
   printf("%d xs%zu avg y %.1f counts gap %lu share %lu out %zu\n",n,xs.size(),ym/double(xs.size()),h,m,out.size());
   return out;
 }
};
#ifndef HEADER
int main(int argc,char**argv){ F(i,argc-1){seeds s;s.build(atoi(argv[i+1]));s.list(0);} }
#endif
