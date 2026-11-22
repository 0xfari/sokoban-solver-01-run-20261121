import{readdirSync as A,readFileSync as B,mkdirSync as C,writeFileSync as D}from"node:fs";
const I=process.env.MAKEFUN_INPUT_DIR??"/input",O=process.env.MAKEFUN_OUTPUT_DIR??"/output",U="udlr",V=[[0,-1],[0,1],[-1,0],[1,0]];
function S(s){
let R=s.split("\n").filter(r=>r),H=R.length,W=0;
for(let r of R)if(r.length>W)W=r.length;
let F=new Set(),G=new Set(),X=[],P=0,Y=0;
for(let y=0;y<H;y++)for(let x=0;x<W;x++){let c=R[y][x]||"#",i=y*W+x;
if(c!="#")F.add(i);
if(c=="."||c=="+"||c=="*")G.add(i);
if(c=="$"||c=="*")X.push(i);
if(c=="@"||c=="+"){P=i;Y=y}}
let N=W*H;
function BF(a,K,J){let p=new Int32Array(N).fill(-1),m=new Int8Array(N),q=[a];p[a]=a;
for(let h=0;h<q.length;h++){let c=q[h];
for(let k=0;k<4;k++){let n=c+V[k][0]+V[k][1]*W;
if(p[n]>=0||K.has(n)||!J(n))continue;p[n]=c;m[n]=k;q.push(n)}}
return[p,m]}
function PT(p,m,a,z){let t="",c=z;while(c!=a){t=U[m[c]]+t;c=p[c]}return t}
let seen=new Set(),RM=[];
for(let i of F){if(((i/W)|0)==Y||seen.has(i))continue;
let q=[i],cs=[];seen.add(i);
while(q.length){let c=q.pop();cs.push(c);
for(let k=0;k<4;k++){let n=c+V[k][0]+V[k][1]*W;
if(F.has(n)&&!seen.has(n)&&((n/W)|0)!=Y){seen.add(n);q.push(n)}}}
RM.push(cs)}
RM.sort((a,b)=>Math.min(...a)-Math.min(...b));
let M="",CP=P,CB=[...X];
for(let cs of RM){
let S2=new Set(cs),bx=CB.filter(i=>S2.has(i)),gl=[...G].filter(i=>S2.has(i));
if(!bx.length)continue;
let dr=cs.find(i=>{let y=(i/W)|0,x=i%W;return(y==Y-1||y==Y+1)&&F.has(Y*W+x)});
if(dr==null)continue;
let en=Y*W+dr%W,blk=new Set(CB),w1=BF(CP,blk,i=>F.has(i));
if(w1[0][en]<0)break;
M+=PT(w1[0],w1[1],CP,en);CP=en;
let dom=i=>S2.has(i)||((i/W)|0)==Y&&F.has(i);
let dead=new Set(),wall=(c,k)=>!dom(c+V[k][0]+V[k][1]*W);
for(let c of cs){if(G.has(c))continue;
let w0=wall(c,0),w1b=wall(c,1),w2=wall(c,2),w3=wall(c,3);
if((w0||w1b)&&(w2||w3)){dead.add(c);continue}
for(let k=0;k<4;k++){if(!wall(c,k))continue;
let ax=V[k<2?2:0],run=[c],ok=1;
for(let sg of[1,-1]){let n=c,cl=0;
for(;;){let n2=n+sg*ax[0]+sg*ax[1]*W;
if(!S2.has(n2)){cl=1;break}
if(!wall(n2,k)){cl=0;break}
n=n2;run.push(n)}
if(!cl){ok=0;break}}
if(ok&&!run.some(i=>G.has(i)))dead.add(c)}}
let m=bx.length,DT=[];
for(let g of gl){let d=new Int32Array(N).fill(-1),q=[g];d[g]=0;
for(let h=0;h<q.length;h++){let c=q[h];
for(let k=0;k<4;k++){let n=c+V[k][0]+V[k][1]*W;
if(!S2.has(n)||d[n]>=0)continue;d[n]=d[c]+1;q.push(n)}}
DT.push(d)}
function HH(b){let dp=new Array(1<<m).fill(1/0);dp[0]=0;
for(let mk=0;mk<(1<<m);mk++){let k=0,t=mk;while(t){k+=t&1;t>>=1}
if(k>=m||dp[mk]==1/0)continue;
for(let j=0;j<m;j++){if(mk>>j&1)continue;
let d=DT[j][b[k]];if(d>=0&&dp[mk]+d<dp[mk|1<<j])dp[mk|1<<j]=dp[mk]+d}}
return dp[(1<<m)-1]}
let b0=[...bx].sort((a,b)=>a-b),K0=CP+","+b0.join(","),vis=new Map([[K0,0]]),par=new Map(),Hp=[],Ct=0;
function HP(n){Hp.push(n);let i=Hp.length-1;while(i>0){let q=(i-1)>>1;if(Hp[q][0]<n[0]||Hp[q][0]==n[0]&&Hp[q][1]<=n[1])break;let t=Hp[q];Hp[q]=Hp[i];Hp[i]=t;i=q}}
function HQ(){let t=Hp[0],l=Hp.pop();if(Hp.length){Hp[0]=l;let i=0;for(;;){let a=2*i+1,c2=a+1,mi=i;
if(a<Hp.length&&(Hp[a][0]<Hp[mi][0]||Hp[a][0]==Hp[mi][0]&&Hp[mi][1]<Hp[mi][1]))mi=a;
if(c2<Hp.length&&(Hp[c2][0]<Hp[mi][0]||Hp[c2][0]==Hp[mi][0]&&Hp[c2][1]<Hp[mi][1]))mi=c2;
if(mi==i)break;let x=Hp[mi];Hp[mi]=Hp[i];Hp[i]=x;i=mi}}return t}
HP([HH(b0),0,K0,CP,b0,0]);
let goal=null;
while(Hp.length){let z=HQ(),K=z[2],p=z[3],b=z[4],g=z[5];
if(b.every(i=>G.has(i))){goal=K;break}
if(vis.get(K)<g)continue;
let bs=new Set(b),rc=BF(p,bs,dom)[0];
for(let i=0;i<m;i++)for(let k=0;k<4;k++){
let oc=b[i],t=oc+V[k][0]+V[k][1]*W;
if(!S2.has(t)||bs.has(t))continue;
let s2=oc-V[k][0]-V[k][1]*W;
if(rc[s2]<0)continue;
let nb=[...b];nb[i]=t;nb.sort((a,b2)=>a-b2);
if(nb.some(i2=>dead.has(i2)))continue;
let h2=HH(nb);if(h2==1/0)continue;
let K2=oc+","+nb.join(","),g2=g+1;
if(vis.has(K2)&&vis.get(K2)<=g2)continue;
vis.set(K2,g2);par.set(K2,[K,oc,k]);HP([g2+h2,++Ct,K2,oc,nb,g2])}}
if(!goal)break;
let pu=[],k=goal;
while(par.has(k)){let e=par.get(k);pu.unshift([e[1],e[2]]);k=e[0]}
let cb=[...b0];
for(let e of pu){let pb=e[0],pd=e[1],s2=pb-V[pd][0]-V[pd][1]*W,w2=BF(CP,new Set(cb),dom);
M+=PT(w2[0],w2[1],CP,s2)+U[pd];
cb[cb.indexOf(pb)]=pb+V[pd][0]+V[pd][1]*W;CP=pb}
CB=CB.filter(i=>!S2.has(i)).concat(cb)}
return M}
for(let id of A(I).sort()){let mv=S(B(I+"/"+id+"/level.txt","utf8"));C(O+"/"+id,{recursive:true});D(O+"/"+id+"/solution.txt",mv+"\n")}
