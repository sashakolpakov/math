#define PATCH_HEADER
#include "patchx.cpp"
#include <string>
#include <xmmintrin.h>
#include <climits>
inline void checkcpu(){
 environment();
 static_assert(sizeof(int)==4 && sizeof(uint64_t)==sizeof(unsigned long) && CHAR_BIT==8);
                                                                      
 unsigned csr=_mm_getcsr();
 if((csr & ((1u<<15)|(1u<<6)|(3u<<13))) || (csr & (63u<<7))!=(63u<<7))abort();
}
inline double wrap(double x){return x-nearbyint(x);}
inline double turn(double x){return x-floor(x);}
struct mapH{
 array<int,6> row,col;
 bool trans=false,neg=false;
 int idx(int i,int j)const{return trans?6*col[j]+row[i] : 6*row[i]+col[j];}
 void transform(const Root& in,Root& out)const{
   out.k=in.k;out.C=in.C;out.n0=in.n0;out.id=in.id;out.ort=in.ort;out.hor=in.hor;out.mnorm=in.mnorm;out.froot=in.froot;out.used=in.used;out.rad=in.rad;
   double sg=neg?-1.:1.;
   F(i,6)F(j,6){
     int h=6*i+j,g=idx(i,j);
     out.p[h]=sg*in.p[g];
     F(a,out.k)out.T[a][h]=sg*in.T[a][g];
   }
   out.finish();
 }
};
inline array<int,6> complement(int i,int j){
 array<int,6>a{i,j};
 int at=2;F(k,6)if(k!=i && k!=j)a[at++]=k;
 return a;
}
struct pivot{
 double gap;
 mapH f;
 double x[6];
};
inline array<double,4> yseq(const pivot&p,const double*ph,int col){
 array<double,4> y;
 double sg=p.f.neg?-1:1;
 double d0=ph[p.f.idx(0,col)]-ph[p.f.idx(0,0)];
 F(i,4)y[i]=turn(sg*(ph[p.f.idx(i+2,col)]-ph[p.f.idx(i+2,0)]-d0));
 return y;
}
template<class Fun> void variants(const Root&R, double tol,int mode,Fun fun){
 vector<pivot> pivs;
 double ming=2;
 F(t,2)F(neg,2)F(i,6)F(j,6)if(i!=j){
   mapH f{complement(i,j),{0,1,2,3,4,5},bool(t),bool(neg)};
   double sg=neg?-1:1;
   array<pair<double,int>,6>a;
   F(k,6)a[k]={turn(sg*(R.p[f.idx(1,k)]-R.p[f.idx(0,k)])),k};
   sort(a.begin(),a.end());
   double g[6],best=0;
   F(k,6){g[k]=a[(k+1)%6].first-a[k].first+(k==5);best=max(best,g[k]);}
   ming=min(ming,best);
   F(k,6)if(g[k]+tol>=best){
     pivot P{best,f,{}};
     int s=(k+1)%6;
     F(l,6){auto el=a[(s+l)%6];P.f.col[l]=el.second;P.x[l]=el.first-a[s].first+((s+l)>=6);}
     pivs.push_back(P);
   }
 }
 for(auto &P:pivs)if(P.gap<=ming+tol){
                                                        
   double score=-1;
   array<array<double,4>,5> ys;
   double ss[5];
   F(k,5){
     auto y=(ys[k]=yseq(P,R.p,k+1));
     double q=1; F(i,4)F(j,i)q=min(q,abs(wrap(y[i]-y[j])));
     ss[k]=q;score=max(score,q);
   }
   F(k,5)if(ss[k]+tol>=score || mode>=2){
     mapH f=P.f;
     array<pair<double,int>,4>b;
     F(i,4)b[i]={ys[k][i],f.row[i+2]};sort(b.begin(),b.end());
     int rotations=mode>=1?4:1;
     F(rot,rotations){
       F(i,4)f.row[i+2]=b[(i+rot)%4].second;
       if(fun(f,P.x))return;
     }
     if(mode==0)break;                       
   }
 }
}
mapH canonicalMap(const Root&R){
 mapH best{};
 double sig[25]{}; bool init=false;
 variants(R,1e-8,0,[&](const mapH&f,const double*x){
   double val[25];
   F(j,5) val[j]=x[j+1];
   double sg=f.neg?-1.:1.;
   F(i,4)F(j,5) val[5+5*i+j]=turn(sg*(R.p[f.idx(i+2,j+1)]-R.p[f.idx(i+2,0)]-R.p[f.idx(0,j+1)]+R.p[f.idx(0,0)]));
   bool less=!init;
   if(init)F(k,25){
     if(val[k]<sig[k]-1e-8){less=true;break;}
     if(val[k]>sig[k]+1e-8)break;
   }
   if(less){best=f;copy(val,val+25,sig);init=true;}
   return false;
 });
 return best;
}
struct Record {Root R; double radius;};
struct Atlas{
 int bins=8; double maxR;
 vector<Record> G;
 vector<vector<int>> bucket;
 static constexpr array<int,3> keyidx{14,22,27};                    
 uint64_t loops=0,trials=0,adds=0,vars=0;
 Atlas(double cap=.126,int bn=8):bins(bn),maxR(cap){bucket.resize(bins*bins*bins);}
 array<int,3> key(const double *dp)const{
   array<int,3> a; F(i,3)a[i]=min(bins-1,max(0,int(turn(dp[keyidx[i]])*bins))); return a;
 }
 int hash(array<int,3>a)const{return (a[0]*bins+a[1])*bins+a[2];}
                                                                                                                 
 pair<int,double> find(const Root&C,double margin) {
   auto a=key(C.dp);
   int reach=min(bins/2, max(1,int(ceil(2*margin*bins+.00001))));
   for(int i=-reach;i<=reach;i++)for(int j=-reach;j<=reach;j++)for(int k=-reach;k<=reach;k++){
     array<int,3>b{(a[0]+i+bins)%bins,(a[1]+j+bins)%bins,(a[2]+k+bins)%bins};
     auto &pool=bucket[hash(b)];loops+=pool.size();
     for(auto z:pool){
       auto &Q=G[z].R;
       double diff[36];bool far=false;
                                       
       for(auto h:keyidx)if(abs(wrap(C.dp[h]-Q.dp[h]))>margin*2+1e-7){far=true;break;}
       if(far)continue;
       F(h,36){
         double x=wrap(C.dp[h]-Q.dp[h]);
         if(abs(x)>margin*2+1e-7){far=true;break;}
         diff[h]=x;
       }
       if(far)continue;
       trials++;
       double D[36],s=0;proj(diff,D);F(h,36)s+=D[h]*D[h];
       if(margin>3e-7 && s<(margin-2e-7)*(margin-2e-7))return {z,sqrt(s)+1e-7};
     }
   }
   return {-1,0};
 }
 bool add(const Root&R,double radius,int mode=0){
    adds++;
    mapH f=canonicalMap(R);
    Root C;f.transform(R,C);
    double margin=maxR-radius;
    auto q=margin>1e-7?find(C,margin):pair<int,double>{-1,0};
    if(q.first<0 && mode>0 && margin>1e-7){
      Root alt;
      variants(R,min(.08,2*margin),mode,[&](const mapH&v,const double*){
        vars++;
        v.transform(R,alt);
        q=find(alt,margin);
        return q.first>=0;
      });
    }
    if(q.first>=0 && radius+q.second+2e-8<maxR){
      auto &g=G[q.first];g.radius=max(g.radius,radius+q.second+1e-8);
      return false;
    }
    if(G.size()>=2000000)abort();
    int z=G.size();bucket[hash(key(C.dp))].push_back(z);
    G.push_back({C,radius});
    return true;
 }
};
                   
struct CenterList {
 vector<pair<xy,xy>> cells;
 void load(const char*path,int samples=0){
   FILE*f=fopen(path,"r");size_t z;
   if(!f || fscanf(f,"%d %zu",&n,&z)!=2 || n!=112 || !z || z>2000000)abort();w=1./n;
   mt19937_64 rng(123);
   F(i,z){
    xy a{},b{};
    for(int &k:a.b)if(fscanf(f,"%d",&k)!=1)abort();
    if(fscanf(f,"%d",&a.s)!=1 || a.s<0 || a.s>=5)abort();
    for(int v:a.b)if(v<0 || v>=n)abort();
    b.b[0]=a.b[a.s];F(j,4)if(fscanf(f,"%d",&b.b[j+1])!=1 || b.b[j+1]<0 || b.b[j+1]>=n)abort();
    if(!samples || int(cells.size())<samples)cells.emplace_back(a,b);
    else {size_t at=rng()%(i+1);if(at<cells.size())cells[at]={a,b};}
   }
   fclose(f);
 }
};
inline void writeExact(FILE*f,const void*x,size_t s,size_t n){if(fwrite(x,s,n,f)!=n)abort();}
inline void readExact(FILE*f,void*x,size_t s,size_t n){if(fread(x,s,n,f)!=n)abort();}
void saveRecords(const char*path,const vector<Record>&v){
 FILE*f=fopen(path,"wb");if(!f)abort();uint64_t count=v.size();writeExact(f,&count,sizeof(count),1);
 for(auto &rec:v){
   const Root&r=rec.R;
   double values[8]={r.C,r.n0,r.id,r.ort,r.hor,r.mnorm,r.froot,rec.radius};
   writeExact(f,&r.k,sizeof(int),1);
   writeExact(f,r.p,sizeof(double),36);
   writeExact(f,r.T,sizeof(r.T[0]),r.k);
   writeExact(f,values,sizeof(double),8);
 }
 if(fclose(f)!=0)abort();
}
vector<Record> readRecords(const char*path){
 FILE*f=fopen(path,"rb");if(!f)abort();uint64_t count=0;readExact(f,&count,sizeof(count),1);
 if(count>2000000)abort();vector<Record> v(count);
 for(auto &rec:v){
   Root&r=rec.R;double values[8]{};
   readExact(f,&r.k,sizeof(int),1);if(r.k<0 || r.k>maxK)abort();
   readExact(f,r.p,sizeof(double),36);readExact(f,r.T,sizeof(r.T[0]),r.k);
   readExact(f,values,sizeof(double),8);
   r.C=values[0];r.n0=values[1];r.id=values[2];r.ort=values[3];r.hor=values[4];r.mnorm=values[5];r.froot=values[6];rec.radius=values[7];
   r.finish();
 }
 if(fclose(f)!=0)abort();return v;
}
#ifndef ATLAS_HEADER
int main(int argc,char**argv){
 checkcpu();if(argc!=6)abort();
 CenterList lists;lists.load(argv[1]);
 int part=atoi(argv[2]),parts=atoi(argv[3]);if(parts<1 || part<0 || part>=parts)abort();
 const double r=.0320001,target=.103,global=.125;
 Asearch Q;Q.levels=3;Q.iters=2;Q.detail=0;Q.first=1;
 Atlas A(global);
 Astats s; auto start=chrono::steady_clock::now();
 FILE*bad=fopen(argv[5],"w");if(!bad)abort();
 uint64_t fails=0;int done=0;
 for(int i=part;i<lists.cells.size();i+=parts){
   auto &p=lists.cells[i];
   if(!Q.B.init(p.first,p.second,r)){fprintf(bad,"%d\n",i);fails++;continue;}
   Q.runA(target);s+=Q.patches.st;
   if(Q.unresolved){fprintf(bad,"%d\n",i);fflush(bad);fails++;}
   for(auto &R:Q.patches.L)A.add(R,R.rad,1);
   if(++done%1000==0){printf("done %d G%zu failedBalls%lu coverFailures%lu+%lu\n",done,A.G.size(),fails,s.snapfail,s.ownfail);fflush(stdout);}
 }
 if(ferror(bad) || fclose(bad)!=0)abort();
 Q.report(max(1,done));
 printf("total done%d candidates%lu patches%lu global%zu failedBalls%lu time %.2f\n",done,s.cands,s.patches,A.G.size(),fails,chrono::duration<double>(chrono::steady_clock::now()-start).count());
 saveRecords(argv[4],A.G);
 return fails?1:0;
}
#endif
