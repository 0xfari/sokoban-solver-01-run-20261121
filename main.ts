import fs from"node:fs";
const E=process.env,I=E.MAKEFUN_INPUT_DIR??"/input",O=E.MAKEFUN_OUTPUT_DIR??"/output",U="udlr";
function S(s){
let R=s.split("\n").filter(Boolean),H=R.length,W=Math.max(...R.map(r=>r.length)),DL=[-W,W,-1,1];
let F=new Set(),G=new Set(),X=[],P=0,Y=0;
for(let y=0;y<H;y++)for(let x=0;x<W;x++){let c=R[y][x]||"#",i=y*W+x;
if(c!="#")F.add(i);
if(".+*".includes(c))G.add(i);
if("$*".includes(c))X.push(i);
if("@+".includes(c)){P=i;Y=y}}
let N=W*H;
function BF(a,K,J){let p=new Int32Array(N).fill(-1),m=new Int8Array(N),q=[a];p[a]=a;
for(let h=0,c;c=q[h];h++){for(let k=0;k<4;k++){let n=c+DL[k];
if(p[n]>=0||K.has(n)||!J(n))continue;p[n]=c;m[n]=k;q.push(n)}}
return[p,m]}
function PT(p,m,a,z){let t="";for(let c=z;c!=a;c=p[c])t=U[m[c]]+t;return t}
let seen=new Set(),RM=[];
for(let i of F){if((i/W|0)==Y||seen.has(i))continue;
let q=[i],cs=[];seen.add(i);
while(q.length){let c=q.pop();cs.push(c);
for(let k=0;k<4;k++){let n=c+DL[k];
if(F.has(n)&&!seen.has(n)&&(n/W|0)!=Y){seen.add(n);q.push(n)}}}
RM.push(cs)}
let M="",CP=P,CB=[...X];
for(let cs of RM){
let S2=new Set(cs),bx=CB.filter(i=>S2.has(i)),gl=[...G].filter(i=>S2.has(i));
if(!bx.length)continue;
let dr=cs.find(i=>(i/W|0)==Y-1||(i/W|0)==Y+1&&F.has(Y*W+i%W));
if(dr==null)continue;
let en=Y*W+dr%W,blk=new Set(CB),w1=BF(CP,blk,i=>F.has(i));
if(w1[0][en]<0)break;
M+=PT(w1[0],w1[1],CP,en);CP=en;
let dom=i=>S2.has(i)||(i/W|0)==Y&&F.has(i);
let D=new Set(),wl=(c,k)=>!dom(c+DL[k]);
for(let c of cs){if(G.has(c))continue;
if((wl(c,0)||wl(c,1))&&(wl(c,2)||wl(c,3))){D.add(c);continue}
for(let k=0;k<4;k++){if(!wl(c,k))continue;
let r=[c],o=1;
for(let s of[1,-1]){let n=c;for(;;){let x=n+s*(k<2?-1:-W);if(!S2.has(x))break;if(!wl(x,k)){o=0;break}n=x;r.push(n)}if(!o)break}
if(o&&!r.some(i=>G.has(i)))D.add(c)}}
let m=bx.length,DT=[];
for(let g of gl){let d=new Int32Array(N).fill(-1),q=[g];d[g]=0;
for(let h=0,c;c=q[h];h++){for(let k=0;k<4;k++){let n=c+DL[k];
if(!S2.has(n)||d[n]>=0)continue;d[n]=d[c]+1;q.push(n)}}
DT.push(d)}
function HH(b){let dp=new Array(1<<m).fill(1/0);dp[0]=0;
for(let mk=0;mk<(1<<m);mk++){let k=0;for(let t=mk;t;t&=t-1)k++;
for(let j=0;j<m;j++){if(mk>>j&1)continue;
let d=DT[j][b[k]];if(d>=0&&dp[mk]+d<dp[mk|1<<j])dp[mk|1<<j]=dp[mk]+d}}
return dp[(1<<m)-1]}
let b0=[...bx].sort((x,y)=>x-y),K0=CP+","+b0,vis=new Map([[K0,0]]),par=new Map(),Hp=[];
function HP(n){Hp.push(n);let i=Hp.length-1;while(i>0){let q=(i-1)>>1;if(Hp[q][0]<=n[0])break;[Hp[q],Hp[i]]=[Hp[i],Hp[q]];i=q}}
function HQ(){let t=Hp[0],l=Hp.pop();if(Hp.length){Hp[0]=l;let i=0;for(;;){let a=2*i+1,c2=a+1,mi=i;
if(a<Hp.length&&Hp[a][0]<Hp[mi][0])mi=a;
if(c2<Hp.length&&Hp[c2][0]<Hp[mi][0])mi=c2;
if(mi==i)break;[Hp[mi],Hp[i]]=[Hp[i],Hp[mi]];i=mi}}return t}
HP([HH(b0),K0,CP,b0,0]);
let goal=null;
while(Hp.length){let z=HQ(),K=z[1],p=z[2],b=z[3],g=z[4];
if(b.every(i=>G.has(i))){goal=K;break}
if(vis.get(K)<g)continue;
let bs=new Set(b),rc=BF(p,bs,dom)[0];
for(let i=0;i<m;i++)for(let k=0;k<4;k++){
let oc=b[i],t=oc+DL[k];
if(!S2.has(t)||bs.has(t))continue;
let s2=oc-DL[k];
if(rc[s2]<0)continue;
let nb=[...b];nb[i]=t;nb.sort((x,y)=>x-y);
if(nb.some(i2=>D.has(i2)))continue;
let h2=HH(nb);if(h2==1/0)continue;
let K2=oc+","+nb,g2=g+1;
if(vis.has(K2)&&vis.get(K2)<=g2)continue;
vis.set(K2,g2);par.set(K2,[K,oc,k]);HP([g2+h2,K2,oc,nb,g2])}}
if(!goal)break;
let pu=[],k=goal;
while(par.has(k)){let e=par.get(k);pu.unshift([e[1],e[2]]);k=e[0]}
let cb=[...b0];
for(let e of pu){let pb=e[0],pd=e[1],s2=pb-DL[pd],w2=BF(CP,new Set(cb),dom);
M+=PT(w2[0],w2[1],CP,s2)+U[pd];
cb[cb.indexOf(pb)]=pb+DL[pd];CP=pb}
CB=CB.filter(i=>!S2.has(i)).concat(cb)}
return M}
for(let id of fs.readdirSync(I).sort()){let mv=S(fs.readFileSync(I+"/"+id+"/level.txt","utf8"));fs.mkdirSync(O+"/"+id,{recursive:true});fs.writeFileSync(O+"/"+id+"/solution.txt",mv+"\n")}
