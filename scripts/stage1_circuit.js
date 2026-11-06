"use strict";
// Build the Stage 1 variant of Glazer's precision-natural-polynomial.json.
//
// Usage: node scripts/stage1_circuit.js PRECISION_JSON MODE [OUTPUT_JSON]
//   MODE = identity  rebuild the pinned circuit unchanged (must equal the input)
//          regen     regenerate every mask/bitAnd gadget with the emulated macros
//                    of integer-diophantine-compiler.js (must give identical counts)
//          stage1    replace each bitAnd(V_i, S_i, N_j) by mask(V_i, S_i), and each
//                    bitAnd(K N_j, R_j + D, K F) by M_j + K Z_j = D + Z_j and
//                    mask(R_j, M_j), with Z_j the sum of W_i over sub states testing j
// Prints the node and variable counts used by the rational translator.
const fs=require("fs"),crypto=require("crypto");
const [,,src,mode,out]=process.argv;
const a=JSON.parse(fs.readFileSync(src));
const UROOT=a.metadata.sourceUniversalRoot;
const nodes=a.nodes.map(n=>({op:n.op,args:n.args.slice()}));
const cache=new Map(nodes.map((n,i)=>[JSON.stringify([n.op,...n.args]),i]));
const node=(op,args)=>{const k=JSON.stringify([op,...args]);if(cache.has(k))return cache.get(k);
  const id=nodes.length;nodes.push({op,args});cache.set(k,id);return id;};
let nextIndex=a.variableCount;const newVars=[],newBlocks=[];
const constant=n=>node("const",[BigInt(n).toString()]);
const fresh=name=>{const index=nextIndex++,id=node("var",[index]);newVars.push({index,name,kind:"witness",node:id});return id;};
const add=(...xs)=>xs.length===0?constant(0):xs.reduce((x,y)=>node("add",[x,y]));
const mul=(...xs)=>xs.length===0?constant(1):xs.reduce((x,y)=>node("mul",[x,y]));
const sq=x=>mul(x,x), scale=(n,x)=>mul(constant(n),x);
// formulas are represented directly by their polynomial roots
const eq=(x,y)=>add(x,scale(-1,y));
const and=(...fs)=>add(...fs.map(sq));
const lt=(x,y)=>{const d=fresh("strict_difference");return eq(y,add(x,constant(1),d));};
const power=(P,Q,R)=>{const start=nextIndex;nextIndex+=79;newBlocks.push({start,length:79,template:0});
  return node("call",[0,P,Q,R,start]);};
const binomial=(C,N,K)=>{const [base,total,place,u,r]=["base","total","place","quotient","remainder"].map(n=>fresh("binomial_"+n));
  return and(power(base,constant(2),add(N,constant(1))),power(total,add(base,constant(1)),N),power(place,base,K),
    lt(C,base),lt(r,place),eq(total,add(mul(place,add(mul(base,u),C)),r)));};
const odd=x=>eq(x,add(scale(2,fresh("odd_half")),constant(1)));
const orthogonal=(x,y)=>{const c=fresh("orthogonal_binomial");return and(binomial(c,add(x,y),x),odd(c));};
const mask=(x,y)=>{const c=fresh("mask_binomial");return and(binomial(c,y,x),odd(c));};
const bitAnd=(z,x,y)=>{const p=fresh("and_left_only"),q=fresh("and_right_only");
  return and(eq(x,add(z,p)),eq(y,add(z,q)),orthogonal(z,p),orthogonal(z,q),orthogonal(p,q));};

// ---- decode the baseline ----
const byIndex=new Map(a.variables.map(v=>[v.index,v]));
const varNode=name=>{const v=a.variables.find(v=>v.name===name);if(!v)throw Error("no var "+name);return v.node;};
const nameOf=id=>{const n=nodes[id];return n.op==="var"?(byIndex.get(n.args[0])||{}).name:undefined;};
let r=UROOT;const top=[];while(nodes[r].op==="add"){top.push(nodes[r].args[1]);r=nodes[r].args[0];}top.push(r);top.reverse();
const roots=top.map(s=>{const n=nodes[s];if(n.op!=="mul"||n.args[0]!==n.args[1])throw Error("not a square");return n.args[0];});
const chain=f=>{let r=f,xs=[];while(nodes[r].op==="add"&&nodes[nodes[r].args[1]].op==="mul"&&nodes[nodes[r].args[1]].args[0]===nodes[nodes[r].args[1]].args[1]){xs.push(nodes[nodes[r].args[1]].args[0]);r=nodes[r].args[0];}
  const n=nodes[r];if(n.op==="mul"&&n.args[0]===n.args[1])xs.push(n.args[0]);else return null;return xs.reverse();};
const K=varNode("digit_capacity"),F=varNode("time_mask"),D=varNode("register_mask");
const decEq=p=>{const n=nodes[p];if(n.op!=="add")return null;const m=nodes[n.args[1]];if(m.op!=="mul")return null;return [n.args[0],m.args[1]];};
const info=roots.map((f,k)=>{
  const c=chain(f);if(!c)return {k,kind:"other"};
  if(c.length===5){const e1=decEq(c[0]),e2=decEq(c[1]);
    if(e1&&nodes[e1[1]].op==="add"&&/^and_left_only/.test(nameOf(nodes[e1[1]].args[1])||"")){
      const z=nodes[e1[1]].args[0],x=e1[0],y=e2[0];
      const zn=nameOf(z);
      if(zn&&zn.startsWith("sub_nonzero_"))return {k,kind:"subBitAnd",sub:+zn.slice(12),s:x,nz:y,reg:+nameOf(y).slice(9)};
      const zm=nodes[z];if(zm.op==="mul"&&zm.args[0]===K)return {k,kind:"regBitAnd",reg:+nameOf(zm.args[1]).slice(9),x,y};
      throw Error("unclassified bitAnd");}}
  if(c.length===2){const e=decEq(c[1]);// mask: and(binomial, odd(c))
    const ch=chain(c[0]);if(ch&&ch.length===6&&nodes[ch[0]].op==="call"){const call=nodes[ch[0]];
      const name=nameOf(e?e[0]:-1)||"";if(name.startsWith("mask_binomial")){
        const Nplus1=call.args[3];const N=nodes[Nplus1].args[0];const place=nodes[ch[2]];return {k,kind:"mask",num:N,den:place.args[3]};}}}
  return {k,kind:"other"};});
const count=t=>info.filter(x=>x.kind===t).length;
console.error("decoded:",{top:roots.length,subBitAnd:count("subBitAnd"),regBitAnd:count("regBitAnd"),mask:count("mask")});

// ---- build the new top-level formula list ----
const newRoots=[];const stats={masksAdded:0,freshM:0};
const subsByReg=new Map();
for(const x of info)if(x.kind==="subBitAnd"){if(!subsByReg.has(x.reg))subsByReg.set(x.reg,[]);subsByReg.get(x.reg).push(x.sub);}
for(const x of info){const f=roots[x.k];
  if(mode==="identity"){newRoots.push(f);continue;}
  if(mode==="regen"){
    if(x.kind==="mask")newRoots.push(mask(x.den,x.num));
    else if(x.kind==="regBitAnd")newRoots.push(bitAnd(mul(K,varNode("nonzero_r"+x.reg)),add(varNode("history_r"+x.reg),D),mul(K,F)));
    else if(x.kind==="subBitAnd")newRoots.push(bitAnd(varNode("sub_nonzero_"+x.sub),x.s,x.nz));
    else newRoots.push(f);continue;}
  // stage1
  if(x.kind==="subBitAnd"){newRoots.push(mask(varNode("sub_nonzero_"+x.sub),x.s));stats.masksAdded++;}
  else if(x.kind==="regBitAnd"){const subs=(subsByReg.get(x.reg)||[]).sort((p,q)=>p-q);
    if(subs.length===0)continue;
    const Z=add(...subs.map(i=>varNode("sub_zero_"+i))),M=fresh("zero_test_mask_r"+x.reg);stats.freshM++;
    newRoots.push(eq(add(M,mul(K,Z)),add(D,Z)));   // M = D - (K-1) Z
    newRoots.push(mask(varNode("history_r"+x.reg),M));stats.masksAdded++;}
  else newRoots.push(f);}
console.error("stage changes:",stats,"registers tested:",subsByReg.size);
const newU=add(...newRoots.map(sq));
// ---- re-create the wrapper on top of the new universal root ----
const memo=new Map([[UROOT,newU]]);
// The wrapper (nodes after the universal root) is copied verbatim, without
// hash-consing, because the pinned file contains duplicate wrapper nodes.
for(let id=UROOT+1;id<a.nodes.length;id++){const n=a.nodes[id];
  if(n.op==="add"||n.op==="mul"){memo.set(id,nodes.length);nodes.push({op:n.op,args:n.args.map(j=>memo.has(j)?memo.get(j):j)});}
  else memo.set(id,id);}
const newRoot=memo.get(a.root);
// ---- compact ----
const reach=new Uint8Array(nodes.length);const stack=[newRoot];
while(stack.length){const i=stack.pop();if(reach[i])continue;reach[i]=1;const n=nodes[i];
  if(n.op==="add"||n.op==="mul")stack.push(...n.args);else if(n.op==="call")stack.push(...n.args.slice(1,4));}
const allVars=a.variables.concat(newVars),allBlocks=a.witnessBlocks.concat(newBlocks);
const usedVar=new Set(),usedBlock=new Set();
nodes.forEach((n,i)=>{if(!reach[i])return;if(n.op==="var")usedVar.add(n.args[0]);if(n.op==="call")usedBlock.add(n.args[4]);});
const items=[...allVars.filter(v=>usedVar.has(v.index)).map(v=>({t:"v",i:v.index,v})),
             ...allBlocks.filter(b=>usedBlock.has(b.start)).map(b=>({t:"b",i:b.start,b}))].sort((p,q)=>p.i-q.i);
const idxMap=new Map();let next=0;for(const it of items){idxMap.set(it.i,next);next+=it.t==="v"?1:79;}
const nodeMap=new Map();const outNodes=[];
nodes.forEach((n,i)=>{if(!reach[i])return;nodeMap.set(i,outNodes.length);let args;
  if(n.op==="var")args=[idxMap.get(n.args[0])];else if(n.op==="const")args=n.args;
  else if(n.op==="call")args=[0,...n.args.slice(1,4).map(j=>nodeMap.get(j)),idxMap.get(n.args[4])];
  else args=n.args.map(j=>nodeMap.get(j));outNodes.push({op:n.op,args});});
const outVars=items.filter(x=>x.t==="v").map(x=>({index:idxMap.get(x.i),name:x.v.name,kind:x.v.kind,node:nodeMap.get(x.v.node)}));
const outBlocks=items.filter(x=>x.t==="b").map(x=>({start:idxMap.get(x.i),length:79,template:0}));
const res={...a,variables:outVars,nodes:outNodes,root:nodeMap.get(newRoot),variableCount:next,witnessBlocks:outBlocks,
  metadata:{...a.metadata,sourceUniversalRoot:nodeMap.get(newU),stage1Mode:mode}};
const ops={};for(const n of outNodes)ops[n.op]=(ops[n.op]||0)+1;
const summary={mode,explicitVariables:outVars.length,explicitWitnesses:outVars.length-5,powerCalls:outBlocks.length,
  ops,variableCount:next,distinctNontrivialConstantValues:new Set(outNodes.filter(n=>n.op==="const"&&!["0","1","-1"].includes(n.args[0])).map(n=>n.args[0])).size};
console.log(JSON.stringify(summary));
if(out){const data=JSON.stringify(res);fs.writeFileSync(out,data);console.error("sha256",crypto.createHash("sha256").update(data).digest("hex"));}
