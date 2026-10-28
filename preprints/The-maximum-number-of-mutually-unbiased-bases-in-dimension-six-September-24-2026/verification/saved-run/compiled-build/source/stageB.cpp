#define ATLAS_HEADER
#include "atlas.cpp"
#include <unordered_set>
void inverseTransform(const mapH&f,const Root&in,Root&out){
 out.k=in.k;out.C=in.C;out.n0=in.n0;out.id=in.id;out.ort=in.ort;out.hor=in.hor;out.mnorm=in.mnorm;out.froot=in.froot;out.used=in.used;out.rad=in.rad;
 double sg=f.neg?-1.:1.;
 F(i,6)F(j,6){
   int h=6*i+j,g=f.idx(i,j);
   out.p[g]=sg*in.p[h];F(a,in.k)out.T[a][g]=sg*in.T[a][h];
 }
 out.finish();
}
struct Choice{int index; mapH map; double dist;};
Choice assign(Atlas&A,const Root&R,double radius,int mode=1){
  mapH f=canonicalMap(R),used=f;
  Root C;f.transform(R,C);
  double margin=A.maxR-radius;
  auto q=margin>2e-7?A.find(C,margin):pair<int,double>{-1,0};
  if(q.first<0 && mode>0 && margin>2e-7){
    Root alt;
    variants(R,min(.08,2*margin),mode,[&](const mapH&v,const double*){
      A.vars++;v.transform(R,alt);q=A.find(alt,margin);
      if(q.first>=0){used=v;return true;}
      return false;
    });
  }
  if(q.first>=0 && radius+q.second+2e-8<A.maxR){
    auto &g=A.G[q.first];g.radius=max(g.radius,radius+q.second+1e-8);
    return {q.first,used,q.second};
  }
  if(A.G.size()>=2000000)abort();
  int z=A.G.size(); A.bucket[A.hash(A.key(C.dp))].push_back(z);
  A.G.push_back({C,radius});
  return {z,f,0};
}
struct statsB {
 uint64_t parents=0,base=0,inside=0,live=0,splits=0,snaps=0,badSnap=0,fails=0,pairTry=0,pairs=0,pairMarks=0;
 void operator+=(const statsB&s){parents+=s.parents;base+=s.base;inside+=s.inside;live+=s.live;splits+=s.splits;snaps+=s.snaps;badSnap+=s.badSnap;fails+=s.fails;pairTry+=s.pairTry;pairs+=s.pairs;pairMarks+=s.pairMarks;}
 void print()const{printf("parent%lu base%lu inside%lu live%lu split%lu snaps%lu bad%lu fail%lu pair%lu/%lu marks%lu\n",parents,base,inside,live,splits,snaps,badSnap,fails,pairs,pairTry,pairMarks);}
};
struct relationB {
 int index=-1,k=0;
 double eta[maxK]{};
 double rho=0, total=0, nu0=0, lam=0,sig=0,C=0,e=0,ort=0,childC=0,cn0=0,cid=0,cort=0;
 double eval(double t)const{
   if(!(t>=0 && t<=2))return 10.;
   t+=2e-8;
   double z=sqrt(1+ort)*t+1e-9;
   double d=min(total+1e-8,hp(z,nu0)+1e-8);
   F(iter,30){
     double v=min(nu0, min((1+ort)*d,lam*d+e))+1e-8;
     double ep=(1+ort)*sqrt((1+ort)*(1+cort))*t+sig*v+1e-8;
     double d1=hp(z,v)+1e-8;
     double d2=hp(sqrt(1+cort)*ep,cn0+cid*d+childC*d*d)+1e-8;
     double nd=min(d1,d2);
     if(nd>=d)break;
     d=nd;
   }
   return d+1e-8;
 }
 bool init(const Root&P,const Root&Q,double R,double target,int ix,bool allowFar=false,bool evalOnly=false){
   index=ix;k=P.k;C=P.C;ort=P.ort;childC=Q.C;cn0=Q.n0;cid=Q.id;cort=Q.ort;
   double raw[36],dq[36];
   double cut=(allowFar?.249:min(.23,R+target+1e-6));
   F(h,36){
     double z=wrap(Q.dp[h]-P.dp[h]);
     if(!(abs(z)<=2*cut+1e-7))return false;
     raw[h]=z;
   }
   proj(raw,dq);
   double sq=0;F(h,36)sq+=dq[h]*dq[h];
   sq=sqrt(sq);
   if(!(sq<=cut+1e-6))return false;
   F(a,k){double z=0;F(h,36)z+=P.T[a][h]*dq[h];eta[a]=z;}
   double nq=0;
   F(h,36){double z=dq[h];F(a,k)z-=eta[a]*P.T[a][h];nq+=z*z;}
   nq=sqrt(nq)+1e-8;
   total=R+sq+1e-8;
   nu0=P.n0+P.id*R+P.C*R*R+nq+1e-8;
   lam=P.id+P.C*total+1e-8;
   e=P.mnorm*Q.froot+1e-7;
   if(Q.k==0)sig=0;
   else{
     double S[maxK][36]{},W[maxK][36]{},G[maxK][maxK]{};
     F(a,Q.k){
       proj(Q.T[a],S[a]);
       F(h,36)W[a][h]=S[a][h];
       F(j,k){
         double cross=0;F(h,36)cross+=S[a][h]*P.T[j][h];
         F(h,36)W[a][h]-=cross*P.T[j][h];
       }
     }
     F(i,Q.k)F(j,i+1){
       double z=0;F(h,36)z+=W[i][h]*W[j][h];
       if(!(abs(z)<=2.))return false;
       G[i][j]=G[j][i]=z;
     }
     sig=sqrt(spectralUpper(Q.k,G)+1e-7)+1e-8;
   }
   if(evalOnly){rho=0;return true;}             
   double lo=0,hi=target*1.01;
   if(eval(0)>target-1e-7){rho=0;return false;}
   F(step,25){double m=(lo+hi)/2;if(eval(m)<target-2e-7)lo=m;else hi=m;}
   rho=max(0.,lo-1e-8);
   return rho>1e-7;
 }
 double corner(const double*u,double h)const{
   double t=0;F(a,k){double z=abs(u[a]-eta[a])+h;t+=z*z;}
   return sqrt(t)+1e-8;                     
 }
};
struct refiner{
 const Root& P;
 const double R,w,target;
 Atlas& A;
 statsB& st;
 int k,L,naxis,maxDepth=6;
 double E;
 vector<unsigned char> status;
 vector<size_t> stride;
 size_t remaining=0;
 vector<relationB> near;
 const vector<Record>* blockers=nullptr; int varlimit=0;
 refiner(const Record&r,double width,Atlas&children,statsB&s):P(r.R),R(r.radius),w(width),target(children.maxR),A(children),st(s){k=P.k;E=sqrt(1+P.ort)*R+1e-7;}
 bool outside(const double*u,double h)const{
   double s=0;F(a,k){double z=max(0.,abs(u[a])-h-1e-8);s+=z*z;}
   return s>E*E;
 }
 void setRadius(const relationB&rel,double t){
   if(rel.index<0)return;
   auto &z=A.G[rel.index];
   if(!(t<=rel.rho))abort();
   double d=rel.eval(t)+1e-8;
   if(!(d<=target))abort();
   z.radius=max(z.radius,d);
 }
 void markRec(const relationB&rel,int axis,size_t at,double s,int*low,int*up, double&mt){
   if(axis==k){
     if(status[at]==0){
       status[at]=1;remaining--; mt=max(mt,sqrt(s)+2e-8);st.pairMarks++;
     }
     return;
   }
   for(int b=low[axis];b<=up[axis];b++){
     double z=abs((b-L)*w-rel.eta[axis])+w/2+1e-8;
     double q=s+z*z;
     if(q>(rel.rho-5e-8)*(rel.rho-5e-8) || rel.rho<5e-8)continue;
     markRec(rel,axis+1,at+b*stride[axis],q,low,up,mt);
   }
 }
 void mark(relationB&rel){
   if(rel.rho<1e-7)return;
   int low[maxK],up[maxK];
   F(a,k){
     low[a]=max(0,L+int(floor((rel.eta[a]-rel.rho)/w))-1);
     up[a]=min(naxis-1,L+int(ceil((rel.eta[a]+rel.rho)/w))+1);
   }
   double mt=-1;markRec(rel,0,0,0.,low,up,mt);
   if(mt>=0)setRadius(rel,mt);
 }
 bool addNear(const Root&Q,int idx){
   st.pairTry++;
   relationB b;
   if(!b.init(P,Q,R,target,idx))return false;
   st.pairs++;near.push_back(b);mark(near.back());
   return true;
 }
 bool solveCell(const double*u,double halfwidth,int depth){
   if(outside(u,halfwidth))return true;
   st.live++;
   if(depth>0)for(auto &b:near){
     double t=b.corner(u,halfwidth);
     if(t < b.rho-1e-8){setRadius(b,t);return true;}
   }
   st.snaps++;
   double guess[36]; F(h,36){guess[h]=P.p[h];F(a,k)guess[h]+=P.T[a][h]*u[a];}
   Root Q{};buildH build;
   bool ok=build.snap(guess)>=0 && build.patch(Q,true);
   if(!ok)st.badSnap++;
   if(ok){
     relationB test;
     if(test.init(P,Q,R,target,-1,true,true)){
       double t=test.corner(u,halfwidth);
       double d=test.eval(t)+2e-8;
       if(d<target-1e-7){
         Choice q=assign(A,Q,d,1);
         Root aligned{};inverseTransform(q.map,A.G[q.index].R,aligned);
         addNear(aligned,q.index);                                      
         return true;
       }
     }
   }
   if(depth>=maxDepth || k==0){st.fails++;return false;}
   st.splits++;
   double v[maxK];
   bool success=true;
   F(mask,1<<k){
     F(a,k)v[a]=u[a]+((mask>>a&1)?1.:-1.)*halfwidth/2;
     if(!solveCell(v,halfwidth/2,depth+1)){success=false;break;}
   }
   return success;
 }
 bool preloadOne(const Root&V,const Root&Q,double rad,int idx,bool skip){
   st.pairTry++;
   if(rad<1e-7)return false;
   relationB b;
   if(!b.init(V,Q,R,rad,idx))return false;
   st.pairs++;
   auto rem=remaining;mark(b);
   if(!skip || remaining<rem)near.push_back(b);
   return true;
 }
 void preload(){
   int ct=A.G.size();
   auto load=[&](const Root& V,bool blocks,bool children){
     if(blocks && blockers)for(auto &rec:*blockers){
       if(!remaining)return;
       preloadOne(V,rec.R,rec.radius,-1,true);
     }
     if(children){
       int reach=min(A.bins, max(1,int(ceil(2*(R+target+2e-6)*A.bins+.00001))));
       if(2*reach+1>=A.bins){
         F(i,ct){if(!remaining)return;preloadOne(V,A.G[i].R,target,i,true);}
       }else{
         auto a=A.key(V.dp);
         for(int ii=-reach;ii<=reach;ii++)for(int jj=-reach;jj<=reach;jj++)for(int kk=-reach;kk<=reach;kk++){
           array<int,3>b{(a[0]+ii+A.bins)%A.bins,(a[1]+jj+A.bins)%A.bins,(a[2]+kk+A.bins)%A.bins};
           for(int i:A.bucket[A.hash(b)])if(i<ct){
             if(!remaining)return;
             preloadOne(V,A.G[i].R,target,i,true);
           }
         }
       }
     }
   };
   load(P,true,true);
   if(!remaining || !varlimit)return;
   unordered_set<uint64_t> seen;
   vector<mapH> maps;
   variants(P,.061,1,[&](const mapH&f,const double*){
      uint64_t hash=f.trans*2+f.neg+1;
      for(auto a:f.row)hash=hash*6+a;
      for(auto a:f.col)hash=hash*6+a;
      if(seen.insert(hash).second)maps.push_back(f);
      return maps.size()>=varlimit;
   });
   for(auto&f:maps){Root V{};f.transform(P,V);load(V,true,false);if(!remaining)return;}
   for(auto&f:maps){Root V{};f.transform(P,V);load(V,false,true);if(!remaining)return;}
 }
 bool run(){
   L=int(ceil(E/w+.500001));naxis=2*L+1;
   size_t total=1;stride.resize(k);
   for(int a=k-1;a>=0;a--){stride[a]=total;
     if(total>50000000UL/naxis){st.fails++;return false;}
     total*=naxis;
   }
   status.resize(total);
   double u[maxK]{};
   F(idx,total){
     F(a,k)u[a]= (int((idx/stride[a])%naxis)-L)*w;
     if(outside(u,w/2))status[idx]=2;
     else remaining++;
   }
   st.parents++; st.base+=total;st.inside+=remaining;
   preload();
   for(size_t idx=0; idx<total && remaining; idx++)if(status[idx]==0){
     F(a,k)u[a]= (int((idx/stride[a])%naxis)-L)*w;
     if(!solveCell(u,w/2,0))return false;
     if(status[idx]==0){status[idx]=1;remaining--;}
   }
   return true;
 }
};
inline void validate(const Record&z,double maxradius=.126){
 const Root&r=z.R;
 if(r.k<0 || r.k>maxK || !(z.radius>=0 && z.radius<=maxradius) ||
    !(r.C>=0 && r.C<20 && r.n0>=0 && r.n0<1e-6 && r.froot>=0 && r.froot<1e-6 &&
      r.id>=0 && r.id<1e-4 && r.ort>=0 && r.ort<1e-5 && r.hor>=0 && r.hor<1e-5 &&
      r.mnorm>=0 && r.mnorm<2))abort();
 F(h,36){if(!(abs(r.p[h])<=4))abort();
   F(a,r.k)if(!(abs(r.T[a][h])<=1.01))abort();}
}
#ifndef REFINE_HEADER
                                                                
int main(int argc,char**argv){
 checkcpu();if(argc<7)abort();
 string prefix=argv[5];bool batching=prefix!="-";
 double target=atof(argv[1]),w=atof(argv[2]);
 if(!(target>=.0001 && target<=.126 && w>=.0001 && w<=.05))abort();
 vector<Record> v, done, bad;
 for(int arg=6;arg<argc;arg++){
   auto dat=readRecords(argv[arg]);
   if(v.size()+dat.size()>8000000)abort();
   for(auto &z:dat)validate(z);
   v.insert(v.end(),dat.begin(),dat.end());
 }
 if(v.empty())abort();
 Atlas A(target,target<.03?16:8);
 size_t emitted=0,batchno=0;
 auto emit=[&](bool force){
   if(!batching)return;
   while(A.G.size()-emitted >= (force?1u:256u)){
     size_t num=min(size_t(256),A.G.size()-emitted);
     vector<Record> dat(A.G.begin()+emitted,A.G.begin()+emitted+num);
     for(auto &z:dat){z.radius=target;validate(z,target);}
     string path=prefix+to_string(batchno)+".bin",tmp=path+".tmp";
     saveRecords(tmp.c_str(),dat);
     if(rename(tmp.c_str(),path.c_str())!=0)abort();
     emitted+=num;batchno++;
   }
 };
 statsB all{};
 stable_sort(v.begin(),v.end(),[](const Record&a,const Record&b){return a.radius>b.radius;});
 auto start=chrono::steady_clock::now();
 for(size_t i=0;i<v.size();i++){
   statsB z{};
   refiner ref(v[i],w,A,z); ref.blockers=&done; ref.varlimit=120;
   bool ok=ref.run();all+=z;if(ok)done.push_back(v[i]);
   if(!ok){
     bad.push_back(v[i]);
     printf("bad parent %zu k%d r%.9f\n",i,v[i].R.k,v[i].radius);z.print();fflush(stdout);
   }
   emit(false);
   if(i%50==49){printf("done%zu/%zu ->%zu bad%zu time %.1f ",i+1,v.size(),A.G.size(),bad.size(),chrono::duration<double>(chrono::steady_clock::now()-start).count());all.print();fflush(stdout);}
 }
 printf("result %zu bad %zu time %.2f ",A.G.size(),bad.size(),chrono::duration<double>(chrono::steady_clock::now()-start).count());all.print();
 for(auto &z:A.G)validate(z,target);
 saveRecords(argv[3],A.G);saveRecords(argv[4],bad);
 emit(true);
 if(batching){
   string path=prefix+"done.txt",tmp=path+".tmp";
   FILE*f=fopen(tmp.c_str(),"w");if(!f || fprintf(f,"%zu %zu\n",batchno,emitted)<0 || fclose(f)!=0 || rename(tmp.c_str(),path.c_str())!=0)abort();
 }
 return bad.empty()?0:1;
}
#endif
