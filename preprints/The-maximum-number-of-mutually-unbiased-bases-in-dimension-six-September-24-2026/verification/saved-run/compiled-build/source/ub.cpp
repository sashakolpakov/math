#define HEADER
#include "seed.cpp"
#include <numeric>
#include <chrono>
#include <cstring>
struct Z{
 double r,i;
 Z operator+(Z x)const{return {r+x.r,i+x.i};}
 Z operator-(Z x)const{return {r-x.r,i-x.i};}
 Z operator-()const{return {-r,-i};}
 Z operator*(Z x)const{return {r*x.r-i*x.i,r*x.i+i*x.r};}
 Z operator*(double y)const{return {r*y,i*y};}
 Z operator/(double y)const{return {r/y,i/y};}
 Z& operator+=(Z x){return *this=*this+x;}
 Z& operator-=(Z x){return *this=*this-x;}
};
Z conj(Z x){return {x.r,-x.i};}
double nr(Z x){return x.r*x.r+x.i*x.i;}
double ab(Z x){return sqrt(nr(x));}
double dot(Z x,Z y){return x.r*y.r+x.i*y.i;}
Z I(Z x){return {-x.i,x.r};}
Z ex(double x){V v=expair(x);return {v[0],v[1]};}
const Z one{1.,0.}, zero{};
const double sqrt6=sqrt(6.);
template<int N> inline void ldl(double (&M)[N][N],double* v){
 double D[N];
 F(i,N){D[i]=1./M[i][i];for(int j=i+1;j<N;j++){
   double l=M[j][i]*D[i]; for(int b=j;b<N;b++)M[b][j]-=l*M[b][i];v[j]-=l*v[i];
 }v[i]*=D[i];}
 for(int j=N-1;j>0;j--)F(i,j)v[i]-=M[j][i]*D[i]*v[j];
}

struct frame{
 Z Q[4][2], G[4][2];                                                   
 Z P[4][4], row[4];
 double m,top;
 bool init(const Z raw[4]){                                                                   
   Z S{};
   F(j,4)S+= (row[j]=raw[j]);
   m=sqrt(4-ab(S)); top=sqrt(4+ab(S));
   if(!(m>1.25))return false;
   double inv=1./(16-nr(S));
   Z basis[4][4]{};
   F(j,4){
     G[j][0]=(one*4-row[j]*conj(S))*inv;
     G[j][1]=(row[j]*4-S)*inv;
     basis[0][j]=one*.5;
     basis[1][j]=(row[j]-S*.25)/sqrt(4.-nr(S)/4);
   }
   for(int k=2;k<=3;k++){
     double best=-1;
     Z q[4]{};
     F(j,4){
       double s=1;
       F(l,k)s-=nr(basis[l][j]);
       if(s<best)continue;
       best=s;
       F(i,4){q[i]=(i==j?one:zero);F(l,k)q[i]-=basis[l][i]*conj(basis[l][j]);}
     }
     double r=0;F(i,4)r+=nr(q[i]);
     if(!(r>.45*.45))return false;
     F(i,4)basis[k][i]=(Q[i][k-2]=q[i]/sqrt(r));
   }
   F(i,4)F(j,4){
     P[i][j]=Q[i][0]*conj(Q[j][0])+Q[i][1]*conj(Q[j][1]);
   }
   return true;
 }
};

struct countL{
 uint64_t norm=0,jac=0,scalar=0,dual=0,passed=0;
};
const int kvar=13,mvar=20;
struct eq{
 alignas(64) double J[mvar][kvar]{};
 double c[mvar]{};
};
struct bound{
 double Rs,h,off,pol,z,zK,E1,E2,E3,E, Ephase, m,mB,mC,L,A;
};
struct block{
 double phases[9],r,sumerr,A,L,m,qpol,g; 
 Z a,B[4],C[4],E[2][2];
 frame FB,FC;                                 
 Z base[16],W[16][4], fixed[9][16], bm[4][4],cm[4][4];
 eq pre;
 bool init(const xy &X,const xy &Y,double rr){
    r=rr;g=1.-(X.b[4]+.5)/n-r;
    int k=1;
    F(j,5) phases[(j==X.s?0:k++)]=(X.b[j]+.5)/n;
    F(j,4) phases[5+j]=(Y.b[j+1]+.5)/n;
    return setup();
 }
 bool setup(){
    a=ex(phases[0]);E[0][0]=E[0][1]=E[1][0]=one;E[1][1]=a;
    Z v[4];
    F(i,4){B[i]=ex(phases[1+i]);C[i]=ex(phases[5+i]);v[i]=conj(B[i]);}
    if(!FB.init(v) || !FC.init(C))return false;
    m=min(FB.m,FC.m);
    if(!(m>=1.))return false;
    A=sqrt(2+ab(one+a));
    L=max(sqrt6,FC.top*sqrt(1.+(A/FB.m)*(A/FB.m)));
    F(i,4)F(j,4){
      int u=4*i+j;
      base[u]=-(one+C[i])*conj(FB.G[j][0]) - (one+C[i]*conj(a))*conj(FB.G[j][1]);
      F(l,4)W[u][l]=FC.Q[i][l/2]*conj(FB.Q[j][l%2])*sqrt6;
      fixed[0][u]=-C[i]*conj(I(a)*FB.G[j][1]);
      F(k,4){
        fixed[5+k][u]= i==k? -I(C[k])*(conj(FB.G[j][0])+conj(a*FB.G[j][1])):zero;
        fixed[1+k][u]=-(FC.G[i][0]+FC.G[i][1]*conj(a))*I(B[k])*FB.P[k][j];
      }
    }
    F(j,4)F(k,4){
      bm[k][j]=-conj(I(B[k])*FB.G[j][1]);
      cm[j][k]=-FC.G[j][1]*conj(I(C[k]));
    }
    Z SX=one+a,SY=one+a;
    pre=eq{};
    F(j,5){
      Z x=j?B[j-1]:a,y=j?C[j-1]:a;
      if(j){SX+=x;SY+=y;}
      pre.J[0][j]=x.r;pre.J[1][j]=x.i;
      pre.J[2][j?j+4:0]=y.r;pre.J[3][j?j+4:0]=y.i;
    }
    pre.c[0]=SX.i;pre.c[1]=-SX.r;
    pre.c[2]=SY.i;pre.c[3]=-SY.r;
    return true;
 }
 bound get(int N)const{
    bound b{};
    b.Rs=2*pi*r+1e-9;b.h=pi/N+1e-10;b.mB=FB.m-1e-8;b.mC=FC.m-1e-8;b.m=min(b.mB,b.mC);
    b.A=A+1e-7;b.L=max(sqrt6,(FC.top+1e-8)*sqrt(1.+(b.A/b.mB)*(b.A/b.mB)))+1e-7;
    double Amax=min(2.,b.A+b.Rs+1e-8), s2=b.Rs*b.Rs;
    double q=s2*(1+(Amax*Amax+6)/(b.mC*b.mC))+1e-7;
    if(!(q<5.9)){b.z=1e10;b.E=1e10;return b;}
    b.off=b.Rs*(sqrt6+Amax)/b.m+1e-7;
    double z2off=b.Rs*sqrt(6+Amax*Amax)/b.mC+1e-7;
    b.pol=q/(sqrt6+sqrt(6-q))+1e-7;
    double u=6*b.h+b.pol+1e-9;
    b.z=hp(b.off,u)+1e-7;
    b.zK=hp(z2off,u)+1e-7;
    b.E3=sqrt(6.*42)/2*b.h*b.h+b.pol+1e-7;
    b.Ephase=(b.L+b.A)/b.m * .5*s2 + .5*s2/b.m +1e-7;
    double eOff=b.Ephase + b.z*b.Rs/b.m +1e-8;
    b.E=hp(eOff,b.E3)+1e-7;
    return b;
 }
};
using Umat=array<Z,4>;
struct triglev{vector<Z> whole,half;void init(int N){if(!whole.empty())return;
 whole.resize(N);half.resize(N);F(i,N){whole[i]=ex(double(i)/N);half[i]=ex((i+.5)/N);}
 }};
triglev trig[8];
struct uc{
 Umat U,dU[4];
 array<int,4> b;
 double ang[4];
 void init(const array<int,4>&bins,int N,bool deriv=false){
   b=bins;
   F(j,4)ang[j]=(b[j]+.5)/N;
   auto &tabu=trig[__builtin_ctz((unsigned)N)-4];
   tabu.init(N);
   Z t=tabu.half[b[1]],diagP=tabu.whole[(b[0]+b[2]+1)%N],diagM=tabu.whole[(b[0]-b[2]+N)%N],
     offP=tabu.whole[(b[0]+b[3]+1)%N],offM=-tabu.whole[(b[0]-b[3]+N)%N];
   U={diagP*t.r,offP*t.i,offM*t.i,diagM*t.r};
   dU[1]={diagP*(-t.i),offP*t.r,offM*t.r,diagM*(-t.i)};
                                     
 }
 void initDeriv(){
   F(i,4)dU[0][i]=I(U[i]);
   dU[2]={I(U[0]),zero,zero,-I(U[3])};
   dU[3]={zero,I(U[1]),-I(U[2]),zero};
 }
};
struct dataU {
 Z D[16], K[16], jac[kvar][16];eq e; double mag[16];
};
void makeD(const block& B,const uc& U,dataU& d){
 F(j,16){
   Z z{}; F(l,4)z+=B.W[j][l]*U.U[l];
   d.K[j]=z;d.D[j]=z+B.base[j];
 }
}
void makeJ(const block&b,const uc&u,dataU&d){
 d.e=b.pre;
 F(i,4)F(j,4){
   int h=4*i+j;
   d.jac[0][h]=b.fixed[0][h];
   F(k,4){
     d.jac[1+k][h]=b.fixed[1+k][h]+d.D[4*i+k]*b.bm[k][j];
     d.jac[5+k][h]=b.fixed[5+k][h]+d.K[4*k+j]*b.cm[i][k];
     Z z{};F(l,4)z+=b.W[h][l]*u.dU[k][l];
     d.jac[9+k][h]=z;
   }
   d.e.c[4+h]=(d.mag[h]-1.)/2;
   F(k,kvar)d.e.J[4+h][k]=dot(d.D[h],d.jac[k][h]);
 }
}
inline bool scalar(const dataU&d,const bound &b){
 F(j,16){
   const double*J=d.e.J[j+4];
   double a=0,z=0;
   F(i,9)a+=J[i]*J[i];
   F(i,4)z+=abs(J[9+i]);
   double t=sqrt(a)*b.Rs+z*b.h+b.E*sqrt(d.mag[j]);
   if(d.e.c[j+4]>t || -d.e.c[j+4]>t+.5*b.z*b.z)return false;
 }
 return true;
}
                                        
double derr(const double *y,const dataU&d,const block&b0,const bound&b,double *er1=nullptr){
 Z Kcols[4][2]{},W[4][4];
 double nW=0,k=0,kk=0;
 F(i,4)F(j,4){
   W[i][j]=d.D[4*i+j]*y[4+4*i+j];
   nW+=nr(W[i][j]);
   F(l,2)Kcols[i][l]+=W[i][j]*b0.FB.Q[j][l];
 }
 F(i,4)F(l,2)k+=nr(Kcols[i][l]);
 F(l,2)F(j,2){
   Z z{};
   F(i,4)z+=Kcols[i][j]*conj(b0.FC.Q[i][l]);
   kk+=nr(z);
 }
 double mu1=sqrt(max(0.,nW-k))/b.mB, mu2=sqrt(max(0.,k-kk))/b.mC, mu3=sqrt(kk);
 double u=.5*b.Rs*b.Rs*(hp(mu1*b.L+mu2*b.A,mu1*b.A+mu2*sqrt6)+hp(mu1,mu2))
       +b.Rs*hp(mu1*b.z,mu2*b.zK)+mu3*b.E3;
 if(er1)*er1=u;
 return min(u,b.E*sqrt(nW))+1e-12*sqrt(nW);
}
struct trial{
 double v[kvar]{};
 double lambda[mvar]{};
 double ratio=0;
 static bool certificate(const double* yy,const dataU&d,const bound&b){
   double mx=0;
   F(a,mvar){if(!isfinite(yy[a]))return false;mx=max(mx,abs(yy[a]));}
   if(!(mx>1e-100 && mx<1e100))return false;
   double y[mvar],yc=0,g[kvar]{},sd=0,neg=0;
   F(a,mvar){
     y[a]=yy[a]/mx;
     yc+=y[a]*d.e.c[a];
     F(i,kvar)g[i]+=y[a]*d.e.J[a][i];
     if(a>=4){sd+=y[a]*y[a]*d.mag[a-4];neg=max(neg,-y[a]);}
   }
   double ss=0,z=0;F(i,9)ss+=g[i]*g[i];F(i,4)z+=abs(g[9+i]);
   double sup=b.Rs*sqrt(ss)+b.h*z+.5*b.z*b.z*neg+b.E*sqrt(sd)
       +.5*b.Rs*b.Rs*(hp(y[0],y[1])+hp(y[2],y[3]));
   return yc > sup+.0001;
 }
 bool pass(const dataU&d,const block&b0,const bound&b,int iters,int improve){
   const eq&e=d.e;
   double wgt[kvar],reg[3]={.5*b.Rs*b.Rs,.5*b.Rs*b.Rs,b.E},wZ=.2*b.z*b.z;
   F(i,9)wgt[i]=b.Rs;
   F(i,4)wgt[i+9]=b.h;
   F(loop,iters){
     double iv[mvar],M[kvar][kvar]{};
     F(i,kvar)v[i]=0;
     F(a,mvar){
       iv[a]=1./((a<4? reg[a/2] : reg[2]*d.mag[a-4]+wZ)+1e-5);
       F(i,kvar){
         double x=e.J[a][i]*iv[a];
         v[i]+=e.c[a]*x;
         F(j,i+1)M[i][j]+=x*e.J[a][j];
       }
     }
     F(i,kvar)M[i][i]+=1./wgt[i];
     ldl(M,v);
     double yc=0,g[kvar]{},nD=0,neg=0,allD=0,edge[2],yn;
     F(a,mvar){
       double z=e.c[a]; F(i,kvar)z-=e.J[a][i]*v[i];
       double y=lambda[a]=z*iv[a];
       if(a>=4){allD+=y*y;nD+=y*y*d.mag[a-4];neg=max(neg,-y);}
       yc+=y*e.c[a];
       F(i,kvar)g[i]+=y*e.J[a][i];
     }
     F(t,2)edge[t]=hp(lambda[2*t],lambda[2*t+1]);
     yn=sqrt(allD+edge[0]*edge[0]+edge[1]*edge[1]);
     if(!(yn>1e-30 && yn<1e80))break;
     double eps=.02*yn;
     double ns=0; F(i,9)ns+=g[i]*g[i];
     ns=sqrt(ns);
     double threshold= ns*b.Rs + .5*neg*b.z*b.z;
     double ws=b.Rs*yn/max(eps,ns);
     F(i,9)wgt[i]=ws;
     F(i,4){wgt[9+i]=b.h*yn/max(eps,abs(g[9+i])); threshold+=b.h*abs(g[9+i]);}
     F(t,2){
       threshold+=.5*b.Rs*b.Rs*edge[t];
       reg[t]=.5*b.Rs*b.Rs*yn/max(eps,edge[t]);
     }
     nD=sqrt(nD);
     double eD=b.E*nD;
     threshold+=eD;
     reg[2]=b.E*yn/max(eps,nD);
     wZ=.5*b.z*b.z*max(.01*yn,neg)*yn/max(allD,.001*yn*yn);
     ratio=max(ratio,yc/max(1e-100,threshold));
     if(yc>threshold-.001*yn && certificate(lambda,d,b))return false;
   }
   return true;
 }
};

struct Usearch{
 block B;
 int levels,iters,detail,first;
 countL counts[8]{};
 vector<array<int,4>> bins,prev;
 double bestres;
 bool test(uc& u,bound b,countL &c,int it){
    dataU d;
    c.norm++;
    makeD(B,u,d);
    double sum=0;
    F(j,16){
      d.mag[j]=nr(d.D[j]);
      double x=sqrt(d.mag[j])-1;
      sum+=x*x;
    }
    if(sum<b.z*b.z && (!levels))bestres=min(bestres,sqrt(sum));
    if(sum>b.z*b.z)return false;
    c.jac++;
    u.initDeriv();
    makeJ(B,u,d);
    if(!scalar(d,b))return false;
    c.scalar++;
    trial t;
    if(!t.pass(d,B,b,it,detail))return false;
    c.dual++;
    c.passed++;
    return true;
 }
 void runblock(){
    int N=16;
    F(l,levels){
      auto b=B.get(N);
      bins.clear();
      uc u;
      int it=l<first?0:iters;
      if(l==0){
        F(a,N/2)F(t,N/4)F(c,N)F(s,N){
          u.init({a,t,c,s},N);
          if(test(u,b,counts[l],it))bins.push_back(u.b);
        }
      }else{
        for(auto p:prev) F(ii,16){
          array<int,4>x;
          F(j,4)x[j]=2*p[j]+((ii>>j)&1);
          u.init(x,N);
          if(test(u,b,counts[l],it))bins.push_back(u.b);
        }
      }
                                   
      swap(bins,prev);N*=2;
    }
                   
 }
 void report(int samples)const{
   int N=16;
   F(l,levels){
     auto &c=counts[l];
     printf("N%d %.1f %.1f %.1f %.1f\n",N,c.norm/double(samples),c.jac/double(samples),c.scalar/double(samples),c.passed/double(samples));
     N*=2;
   }
 }
};

#ifndef UB_HEADER
int main(int argc,char**argv){
 int nn=atoi(argv[1]),nsamp=atoi(argv[2]);double r=atof(argv[3]);
 seeds S;S.build(nn);
 auto cells=S.list(nsamp);
 Usearch Q;Q.levels=atoi(argv[4]);Q.iters=atoi(argv[5]);Q.detail=atoi(argv[6]);Q.first=atoi(argv[7]);
 auto st=chrono::steady_clock::now();
 vector<int> a;
 for(auto &p:cells){
   if(!Q.B.init(p.first,p.second,r)){printf("bad");return 1;}
   Q.runblock();
   a.push_back(Q.prev.size());
 }
 sort(a.begin(),a.end());
 if(!a.empty())F(k,11)printf("%d ",a[k*(a.size()-1)/10]);printf("\n");
 Q.report(nsamp);
 printf("percell %.6f\n",chrono::duration<double>(chrono::steady_clock::now()-st).count()/cells.size());
}
#endif
