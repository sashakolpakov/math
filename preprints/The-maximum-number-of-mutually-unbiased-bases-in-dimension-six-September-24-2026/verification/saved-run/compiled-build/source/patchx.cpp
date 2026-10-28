#define UB_HEADER
#include "ub.cpp"
const int dk=6,hvar=25,ne=30,DIM=36,maxK=10;
struct Basis {
 double q[6][5]{}, Q[36][25]{};
 Basis(){
   F(j,5){double u=1./sqrt((j+1.)*(j+2.)); F(i,j+1)q[i][j]=u;q[j+1][j]=-(j+1.)*u;}
   F(i,6)F(j,6)F(a,5)F(b,5)Q[6*i+j][5*a+b]=q[i][a]*q[j][b];
 }
} bas;

void proj(const double *p,double *out){
 double r[6]{},c[6]{},g=0;
 F(i,6)F(j,6){r[i]+=p[6*i+j];c[j]+=p[6*i+j];g+=p[6*i+j];}
 F(i,6)F(j,6)out[6*i+j]=p[6*i+j]+g/36-(r[i]+c[j])/6;
}
template<int N>void jacobi(double (&M)[N][N],double (&V)[N][N]){
 F(i,N)F(j,N)V[i][j]=(i==j);
 F(sweep,40){
   double m=0;
   for(int p=0;p<N;p++)for(int q=p+1;q<N;q++){
     double x=M[p][q];m=max(m,abs(x));
     if(abs(x)<1e-13)continue;
     double tau=(M[q][q]-M[p][p])/(2*x);
     double t=copysign(1./(abs(tau)+sqrt(1+tau*tau)),tau);
     double c=1./sqrt(1+t*t),s=t*c;
     M[p][p]-=t*x;M[q][q]+=t*x;M[p][q]=M[q][p]=0;
     F(i,N)if(i!=p && i!=q){
       double a=M[i][p],b=M[i][q];
       M[p][i]=M[i][p]=c*a-s*b; M[q][i]=M[i][q]=s*a+c*b;
     }
     F(i,N){double a=V[i][p],b=V[i][q];V[i][p]=c*a-s*b;V[i][q]=s*a+c*b;}
   }
   if(m<1e-12)break;
 }
}
inline void dephase(const double*p,double*out){
 F(i,6)F(j,6){double z=p[6*i+j]-p[6*i]-p[j]+p[0];out[6*i+j]=z-nearbyint(z);}
}
struct Root{
 double p[36]{}, dp[36]{}, T[maxK][36]{}, C=0,n0=0,id=0,ort=0,hor=0,mnorm=0,froot=0;
 int k=-1;
 uint64_t used=0; double rad=0;
 void finish(){dephase(p,dp);}
};
struct buildH{
 double f[ne], J[ne][hvar], Gram[hvar][hvar], fullL[ne][36];
 double p[36]{}; bool certmode=false;
 double gen(bool jac){
   double s=0;int at=0;Z unit[6][6];
   F(i,6)F(j,6){if(!(abs(p[6*i+j])<=4.))return NAN;unit[i][j]=ex(p[6*i+j]);}
   F(i,6)F(j,i){
     Z q[6],sum{};
     F(g,6)sum+=(q[g]=unit[i][g]*conj(unit[j][g]));
     f[at]=sum.i/(2*pi);f[at+1]=-sum.r/(2*pi);s+=nr(sum)/((2*pi)*(2*pi));
     if(jac){
       Z cols[5]{};
       F(g,6)F(b,5)cols[b]+=q[g]*bas.q[g][b];
       F(a,5){double u=bas.q[i][a]-bas.q[j][a];F(b,5){
          J[at][5*a+b]=u*cols[b].r;
          J[at+1][5*a+b]=u*cols[b].i;
       }}
       if(certmode) F(h,36){
         int row=h/6,g=h%6;
         fullL[at][h]=(row==i?q[g].r: row==j?-q[g].r:0);
         fullL[at+1][h]=(row==i?q[g].i: row==j?-q[g].i:0);
       }
     }
     at+=2;
   }
   return s;
 }
 void gram(bool lower){
   F(i,hvar)F(j,lower?i+1:hvar){
     double z=0;F(a,ne)z+=J[a][i]*J[a][j];
     Gram[i][j]=z;
   }
 }
 int snap(const double*p0){
   F(h,36)p[h]=p0[h];
   F(it,24){
     double old=gen(true);
     if(!isfinite(old))return -3;
     if(old<1e-20)return it;
     gram(true);
     double x[hvar]{};
     F(i,hvar){Gram[i][i]+=.12;F(a,ne)x[i]-=J[a][i]*f[a];}
     ldl(Gram,x);
     double step[36]{},ss=0,prev[36];
     F(h,36){
       prev[h]=p[h];
       F(i,hvar)step[h]+=bas.Q[h][i]*x[i];
       ss+=step[h]*step[h];
     }
     double scale=min(1.,.25/sqrt(ss));
     bool ok=false;
     F(bt,5){
       F(h,36)p[h]=prev[h]+scale*step[h];
       if(bt==0 && scale==1. && old<.02) {ok=true;break;}                
       double val=gen(false);
       if(val<old){ok=true;break;}
       scale*=.5;
     }
     if(!ok)return -1;
   }
   return gen(true)<1e-18?24:-2;
 }
 bool patch(Root& R,bool tensor=true){
   certmode=true;double val=gen(true);
   if(!(val<1e-18))return false;
   F(h,36)R.p[h]=p[h];
   gram(false);
   double V[hvar][hvar], eig[hvar];
   jacobi(Gram,V);
   double M[36][ne]{},HV[36][hvar]{},LV[ne][hvar]{};int good=0;
   R.k=0;
   F(i,hvar){
     eig[i]=Gram[i][i];
     if(!isfinite(eig[i]))return false;
     double hvec[36]{},lvec[ne]{};
     F(h,36)F(j,hvar)hvec[h]+=bas.Q[h][j]*V[j][i];
     if(eig[i]<.64){
       if(R.k>=maxK)return false;
       F(h,36)R.T[R.k][h]=hvec[h];
       R.k++;continue;
     }
     F(a,ne){
       double z=0;F(j,hvar)z+=J[a][j]*V[j][i];lvec[a]=z/eig[i];
     }
     F(h,36){if(!(abs(hvec[h])<=2.))return false;HV[h][good]=hvec[h];}
     F(a,ne){if(!(abs(lvec[a])<=2.))return false;LV[a][good]=lvec[a];}
     good++;
     F(h,36)F(a,ne)M[h][a]+=hvec[h]*lvec[a];
   }
   F(i,R.k)F(h,36)if(!(abs(R.T[i][h])<=2.))return false;
   double ah=0,al=0;
   F(i,good){double rh=0,rl=0;F(j,good){
      double h=0,l=0;F(z,36)h+=HV[z][i]*HV[z][j];F(z,ne)l+=LV[z][i]*LV[z][j];
      rh+=abs(h);rl+=abs(l);
   } ah=max(ah,rh);al=max(al,rl);}
   R.mnorm=sqrt((ah+1e-8)*(al+1e-8))+1e-8;
   if(!(R.mnorm<2.))return false;
   R.C=pi*sqrt(8.)*R.mnorm+1e-7;
   if(tensor && R.C>4.35){                          
     int ei[ne],ej[ne],at=0;
     F(i,6)F(j,i){ei[at]=ei[at+1]=i;ej[at]=ej[at+1]=j;at+=2;}
     double S[ne][ne],A[ne][ne],U[ne][ne];
     F(a,ne)F(b,ne){
       int sign=(ei[a]==ei[b])+(ej[a]==ej[b])-(ei[a]==ej[b])-(ej[a]==ei[b]);
       double z=0;if(sign)F(h,36)z+=M[h][a]*M[h][b];
       A[a][b]=S[a][b]=z*sign;
     }
     jacobi(S,U);
     bool usable=true;F(i,ne)F(j,ne)if(!(abs(U[i][j])<=2.))usable=false;
     if(usable){
       double beta=0,X[ne][ne]{};
       F(i,ne)F(j,ne){
         double z=-(i==j);F(h,ne){z+=U[h][i]*U[h][j];X[i][j]+=A[i][h]*U[h][j];}
         beta+=z*z;
       }
       beta=sqrt(beta)+1e-8;
       double row=0;
       F(i,ne){double r=0;F(j,ne){double z=0;F(h,ne)z+=U[h][i]*X[h][j];r+=abs(z);}row=max(row,r);}
       if(beta<.1)R.C=min(R.C,pi*sqrt(6*(row+.0002)/(1-beta))+.00001);
     }
   }
                                                                             
   double PI[36][36],LP[ne][36]{},err=0,orth=0,hor=0;
   F(i,36)F(j,36)PI[i][j]=((i/6==j/6?1.:0)-1./6)*((i%6==j%6?1.:0)-1./6);
   F(a,ne)F(j,36)F(h,36)LP[a][j]+=fullL[a][h]*PI[h][j];
   F(i,36)F(j,36){
     double z=PI[i][j];
     F(a,R.k)z-=R.T[a][i]*R.T[a][j];
     F(a,ne)z-=M[i][a]*LP[a][j];
     err+=z*z;
   }
   F(a,R.k){
     double z[36];proj(R.T[a],z);
     F(h,36)hor+=(z[h]-R.T[a][h])*(z[h]-R.T[a][h]);
     F(i,R.k){double q=-(a==i);F(h,36)q+=R.T[a][h]*R.T[i][h];orth+=q*q;}
   }
   R.id=sqrt(err)+2e-6;R.ort=sqrt(orth)+1e-8;R.hor=sqrt(hor)+1e-8;
   R.froot=sqrt(val)+1e-9;R.n0=R.mnorm*R.froot+1e-9;
   if(!(R.id<1e-4 && R.ort<1e-5 && R.hor<1e-5 && R.C<20))return false;
   R.finish();
   return true;
 }
};
inline double circle(Z z){return atan2(z.i,z.r)/(2*pi);}
const int pos[9]={7,8,9,10,11,13,19,25,31};
struct Candidate{
 double P[36]{}, X[kvar][36]{}, arc,weighted,d2,maxrow;
 double invmag[16];
 bool prep(const block&B,const dataU&d,const bound&b,double sum){
   F(j,9){P[pos[j]]=B.phases[j];P[pos[j]]-=nearbyint(P[pos[j]]);X[j][pos[j]]=1.;}
   double mi=1e10;
   F(i,4)F(j,4){
     int e=4*i+j,h=6*(i+2)+(j+2);
     double m=sqrt(d.mag[e]);
     if(!(m>.15))return false;
     P[h]=circle(d.D[e]);
     if(!(abs(P[h])<=.51 && ab(ex(P[h])-d.D[e]/m)<1e-7))return false;
     Z q=I(d.D[e]/m);
     F(k,kvar)X[k][h]=dot(q,d.jac[k][e]);
     mi=min(mi,m-1e-6);invmag[e]=1./(m-1e-6)+1e-9;
   }
   double slack=max(0.,b.z*b.z-sum+1e-5)+1e-10;
   double q=slack/mi+1e-8;
   if(!(q<3.8))return false;
   double ratio=1./sqrt(1.-q/4)+1e-7;
   arc=sqrt(q)*ratio+1e-8;
   weighted=sqrt(slack)*ratio+1e-8;
   d2=(arc*arc+b.Rs*b.Rs)/((2*pi)*(2*pi))+1e-8;
   return true;
 }
 double delta(const Root&R,double*D)const{
   double raw[36];
   F(h,36){double x=P[h]-R.dp[h];raw[h]=x-nearbyint(x);}
   proj(raw,D);
   double s=0;F(h,36)s+=D[h]*D[h];return s;
 }
};
                                                      
inline double spectralUpper(int k,const double G[maxK][maxK]){
 double row=0, fro4=0;
 F(i,k){
   double z=0;F(j,k)z+=abs(G[i][j]);row=max(row,z);
   F(j,k){double a=0;F(l,k)a+=G[i][l]*G[l][j];fro4+=a*a;}
 }
 return min(row+1e-10,sqrt(sqrt(fro4))+2e-7);
}
inline bool chol(int k,double A[maxK][maxK]){
 F(i,k){
   F(j,i){
     double z=A[i][j];F(l,j)z-=A[i][l]*A[j][l];A[i][j]=z/A[j][j];
   }
   double z=A[i][i];F(l,i)z-=A[i][l]*A[i][l];
   if(!(z>1e-14))return false;
   A[i][i]=sqrt(z);
 }
 return true;
}
inline double ell(int k,const double U[16][maxK],int rows,const double G[maxK][maxK]){
 F(i,k)F(j,k)if(!(abs(G[i][j])<=10. && G[i][j]==G[j][i]))return 100.;
 F(h,rows)F(i,k)if(!(abs(U[h][i])<=10.))return 100.;
 double gu=spectralUpper(k,G),mx=0;
 F(h,rows){double z=0;F(i,k)z+=U[h][i]*U[h][i];mx=max(mx,z);}
 double span=sqrt(max(0.,mx*gu)),best=sqrt(mx)+sqrt(max(gu,0.))+1e-8;
 for(double coef:{.28,.58,1.}){
   double gam=gu+max(.03*gu+2e-6,coef*span);
   double gap=gam-gu-1e-9;
   if(!(gap>=1e-6))continue;
   double A[maxK][maxK];
   F(i,k)F(j,i+1)A[i][j]=(i==j?gam:0)-G[i][j];
   if(!chol(k,A))continue;
   double high=0;bool ok=true;
   F(h,rows){
     double z[maxK],scale=1.;
     F(i,k){double x=U[h][i];F(j,i)x-=A[i][j]*z[j];z[i]=x/A[i][i];}
     for(int i=k-1;i>=0;i--){
       double x=z[i];for(int j=i+1;j<k;j++)x-=A[j][i]*z[j];
       z[i]=x/A[i][i];if(!(abs(z[i])<1e8))ok=false;
       scale=max(scale,abs(z[i]));
     }
     if(!ok)break;
     double res=0,dotv=0,un=0;
     F(i,k){double x=U[h][i]-gam*z[i];F(j,k)x+=G[i][j]*z[j];
       res+=x*x;dotv+=U[h][i]*z[i];un+=U[h][i]*U[h][i];}
     double upper=dotv+1e-10*scale
          +(sqrt(un)+1e-10)*(sqrt(res)+1e-10*scale)/gap;
     high=max(high,upper);
   }
   if(ok)best=min(best,sqrt(gam*(1+high))+.000001);
 }
 return best+.000001;
}

inline double bootstrap(const Root&R,double init,double t){
 if(!(t>=0 && t<10 && init>=0 && init<3 && R.C<20))return 10.;
 t+=.00002;
 double s=init+1e-6;
 F(loop,30){
   double z=hp(R.n0+R.id*s+R.C*s*s,sqrt(1+R.ort)*t)+1e-8;
   if(z>=s)break;
   s=z;
 }
 return s;
}
struct covercompute{
 double delta[36], off[maxK],AB[kvar][maxK],U[16][maxK];
 double value(const Candidate&x,const bound&b,const Root&R,double target){
   double nd=x.delta(R,delta);
   if(nd>.145*.145)return 10.;
   int k=R.k;
   double g[kvar]{}, ns=0,su=0,dseed=0,dD=0,weighted=0,dm=0;
   F(j,kvar){
     F(h,36)g[j]+=delta[h]*x.X[j][h];
     if(j<9){ns+=g[j]*g[j];dseed+=delta[pos[j]]*delta[pos[j]];}
     else su+=abs(g[j]);
   }
   F(i,4)F(j,4){int e=4*i+j,h=6*i+j+14;
     dD+=delta[h]*delta[h];dm=max(dm,abs(delta[h]));
     weighted+=delta[h]*delta[h]*x.invmag[e];
   }
   double supp=min(sqrt(ns)*b.Rs+su*b.h+b.E*sqrt(dD)+dm*(x.arc*x.arc*x.arc/6),
                   sqrt(dseed)*b.Rs+x.weighted*sqrt(weighted));
   double s0=sqrt(nd+x.d2+(supp+.0001)/pi)+.00001;
   if(s0+1e-7<target)return s0+1e-7;
   if(k==0)return bootstrap(R,s0,1e-9);
   double toff=0;
   F(i,k){
     double z=0; F(h,36)z+=R.T[i][h]*delta[h];
     toff+=z*z;off[i]=2*pi*z;
   }
   if(toff>.092*.092)return 10.;
   F(a,kvar)F(i,k){
     double z=0; F(h,36)z+=R.T[i][h]*x.X[a][h];
     AB[a][i]=z;                              
   }
   F(row,16)F(i,k){
     double z=0; F(a,4)z+= (row>>a&1?1.:-1.)*AB[9+a][i];
     U[row][i]=off[i]+b.h*z;
   }
   double G[maxK][maxK], D2[maxK][maxK]{},Dweighted[maxK][maxK]{},inf=0;
   F(irow,4)F(col,4){
     int e=irow*4+col,h=irow*6+col+14;
     double z=0;
     F(i,k){
       double v=R.T[i][h];z+=v*v;
       F(j,k){double a=v*R.T[j][h];D2[i][j]+=a;Dweighted[i][j]+=a*x.invmag[e];}
     }
     inf=max(inf,z);
   }
   F(i,k)F(j,i+1){
     double z=0;F(a,9)z+=AB[a][i]*AB[a][j];
     G[j][i]=G[i][j]=1.45*b.Rs*b.Rs*z+(1+1/.45)*b.E*b.E*D2[i][j]+(i==j?1e-7:0);
   }
   double t=(ell(k,U,16,G)+sqrt(inf)*x.arc*x.arc*x.arc/6+.00015)/(2*pi)+.00002;
   double s=bootstrap(R,s0,t);
   if(s<=target)return s;
   F(i,k)F(j,i+1){
     double z=0;F(a,9)z+=R.T[i][pos[a]]*R.T[j][pos[a]];
     G[j][i]=G[i][j]=1.8*b.Rs*b.Rs*z+(1+1/.8)*x.weighted*x.weighted*Dweighted[i][j]+(i==j?1e-7:0);
   }
   F(i,k)U[0][i]=off[i];
   t=(ell(k,U,1,G)+.00015)/(2*pi)+.00002;
   return min(s,bootstrap(R,s0,t));
 }
};
struct Astats{
 uint64_t cands=0,attempts=0,patches=0,snapfail=0,ownfail=0,comparisons=0,snapIters=0;
 double tCoverage=0,tSnap=0;
 void operator+=(const Astats&a){
  cands+=a.cands;attempts+=a.attempts;patches+=a.patches;snapfail+=a.snapfail;ownfail+=a.ownfail;
  tCoverage+=a.tCoverage;tSnap+=a.tSnap;comparisons+=a.comparisons;snapIters+=a.snapIters;
 }
};
struct local {
 vector<Root>L;
 double target;
 int topK=4;
 Astats st;
 Candidate x;
 covercompute ccalc;
 void reset(double t){L.clear();target=t;st=Astats{};}
 bool test(const block&B,const dataU&d,const bound&b,double sum){
   st.cands++;
   if(!x.prep(B,d,b,sum)){st.snapfail++;return false;}
   auto start=chrono::steady_clock::now();
   pair<double,int> picks[8];
   int found=0;
   double D[36];
   st.comparisons+=L.size();
   for(int z=int(L.size())-1;z>=0;--z){
     auto &R=L[z];
     double nd=x.delta(R,D);
     if(nd>.145*.145)continue;
     double t=0;F(i,R.k){double v=0;F(h,36)v+=D[h]*R.T[i][h];t+=v*v;}
     double score=t+nd*.15;
     if(found==topK && picks[found-1].first<=score)continue;
     int p=min(found,topK-1);if(found<topK)found++;
     while(p>0 && picks[p-1].first>score){picks[p]=picks[p-1];p--;}
     picks[p]={score,z};
   }
   F(i,found){
     auto &R=L[picks[i].second];
     st.attempts++;
     double s=ccalc.value(x,b,R,target);
     if(s>=0 && s+1e-8<=target){
        R.used++;R.rad=max(R.rad,s+1e-8);
        st.tCoverage+=chrono::duration<double>(chrono::steady_clock::now()-start).count();
        return true;
     }
   }
   st.tCoverage+=chrono::duration<double>(chrono::steady_clock::now()-start).count();
   start=chrono::steady_clock::now();
   buildH H;
   int it=H.snap(x.P);
   Root R{};
   bool ok=it>=0 && H.patch(R,true);
   if(!ok)st.snapfail++;
   else{
     st.snapIters+=it;
     double s=ccalc.value(x,b,R,target);
     if(!(s>=0 && s+1e-8<=target)){st.ownfail++;ok=false;}
     else {R.used=1;R.rad=s+1e-8;L.push_back(R);st.patches++;}
   }
   st.tSnap+=chrono::duration<double>(chrono::steady_clock::now()-start).count();
   return ok;
 }
};

struct Asearch : Usearch {
 local patches;
 uint64_t unresolved=0,extraNodes=0; bool giveup=false;
 bool testA(uc& u,bound b,countL &c,int it,bool final,int N){
    if(final && giveup)return false;
    if(final && N>64 && ++extraNodes>1000000){giveup=true;unresolved++;return false;}
    dataU d;
    c.norm++;
    makeD(B,u,d);
    double sum=0;
    F(j,16){d.mag[j]=nr(d.D[j]);double x=sqrt(d.mag[j])-1;sum+=x*x;}
    if(sum>b.z*b.z+1e-5)return false;
    c.jac++;
    if(!it && !final)return true;
    u.initDeriv();makeJ(B,u,d);
    c.scalar++;
    trial t;if(!t.pass(d,B,b,it,detail))return false;
    c.dual++;c.passed++;
    if(final){
      if(patches.test(B,d,b,sum))return false;
      if(N>=512){unresolved++;return false;}
      int nn=2*N;auto nb=B.get(nn);
      F(mask,16){array<int,4>x;F(j,4)x[j]=2*u.b[j]+((mask>>j)&1);
        uc v;v.init(x,nn);testA(v,nb,c,iters,true,nn);}
      return false;
    }
    return true;
 }
 void runA(double target){
   unresolved=extraNodes=0;giveup=false;
   patches.reset(target);
   int N=16;
   F(l,levels){
     auto b=B.get(N); bins.clear();uc u;int it=l<first?0:iters; bool final=l+1==levels;
     if(l==0)F(a,N/2)F(t,N/4)F(c,N)F(s,N){u.init({a,t,c,s},N);if(testA(u,b,counts[l],it,final,N))bins.push_back(u.b);}
     else for(auto p:prev)F(ii,16){array<int,4>x;F(j,4)x[j]=2*p[j]+((ii>>j)&1);u.init(x,N);if(testA(u,b,counts[l],it,final,N))bins.push_back(u.b);}
     swap(bins,prev);N*=2;
   }
 }
};

#ifndef PATCH_HEADER
int main(int argc,char**argv){
 int nn=atoi(argv[1]),nsamp=atoi(argv[2]);double r=atof(argv[3]),target=atof(argv[4]);
 seeds S;S.build(nn); auto cells=S.list(nsamp);
 Asearch Q;Q.levels=3;Q.iters=atoi(argv[5]);Q.detail=1;Q.first=1;
 auto start=chrono::steady_clock::now();
 Astats s;vector<int>a,fail;
 for(auto &p:cells){
   if(!Q.B.init(p.first,p.second,r))return 1;
   Q.runA(target);
   auto &z=Q.patches.st;s+=z;
   a.push_back(z.patches);fail.push_back(z.snapfail+z.ownfail);
   if(nsamp<=30)printf("%lu -> %lu fail %lu+%lu times %.3f %.3f\n",z.cands,z.patches,z.snapfail,z.ownfail,z.tCoverage,z.tSnap);
 }
 Q.report(nsamp);
 sort(a.begin(),a.end()); sort(fail.begin(),fail.end());
 F(k,11)printf("%d ",a[k*(a.size()-1)/10]);printf("\n");
 printf("total %lu -> %lu fail %lu+%lu, att %.2f iter %.2f comp %.2f times %f %f %f per ball\n",s.cands,s.patches,s.snapfail,s.ownfail,s.attempts/double(s.cands),s.snapIters/double(max(uint64_t(1),s.patches+s.ownfail)),s.comparisons/double(s.cands),s.tCoverage/nsamp,s.tSnap/nsamp,chrono::duration<double>(chrono::steady_clock::now()-start).count()/nsamp);
}
#endif
