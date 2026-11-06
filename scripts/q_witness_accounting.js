"use strict";
// Total rational-witness count of the ordinary-integer definition built from a
// natural circuit. Reads Glazer's pinned ordinary-integer-definition.json as data
// and applies the allocation rule of rational-circuit-translator.js
// (Translator.translate). Checks the rule against the pinned counts.
//
// Usage: node scripts/q_witness_accounting.js DEFINITION_JSON CIRCUIT_JSON...
const fs=require("fs");
const [defFile,...circuits]=process.argv.slice(2);
const D=JSON.parse(fs.readFileSync(defFile));
const T=D.library.templates, R=D.recipes, P=R.precision;
const wc=name=>T.find(t=>t.name===name).witnessCount;
const consts=P.constantDefinitions.map(c=>T[c.template].witnessCount);
const ops=[0,0,0];for(const o of P.operations)ops[o[0]]++;
const lib={natural:wc("natural"),raw_add:wc("raw_add"),multiply:wc("multiply"),power_value:R.power_value.witnessCount,
  constantTemplateWitnesses:consts};
const pinned={total:D.witnessCount,precision:P.witnessCount,nonPrecision:D.witnessCount-P.witnessCount,
  sourceVariables:P.sourceVariables.length,adds:ops[0],muls:ops[1],powers:ops[2],constants:P.constantDefinitions.length};
// Translator.translate allocation: 3 generator coords; per source variable 5 point coords (non-inputs)
// plus a natural guard block (all variables, naturalInputs=true); per nontrivial constant 5 + template;
// per add 5 + raw_add; per mul 5 + multiply; per power call 5 + power_value.
function precision(c){return 3+5*(c.vars-c.inputs)+c.vars*lib.natural
  +c.constTemplates.reduce((s,w)=>s+5+w,0)+c.adds*(5+lib.raw_add)+c.muls*(5+lib.multiply)+c.powers*(5+lib.power_value);}
function fromCircuit(file){const a=JSON.parse(fs.readFileSync(file));const k={};for(const n of a.nodes)k[n.op]=(k[n.op]||0)+1;
  const cv=[...new Set(a.nodes.filter(n=>n.op==="const"&&!["0","1","-1"].includes(n.args[0])).map(n=>n.args[0]))];
  return {vars:a.variables.length,inputs:a.variables.filter(v=>v.kind==="input").length,adds:k.add,muls:k.mul,powers:k.call||0,constValues:cv.length};}
console.log("library",JSON.stringify(lib));console.log("pinned",JSON.stringify(pinned));
if(precision({vars:pinned.sourceVariables,inputs:5,adds:pinned.adds,muls:pinned.muls,powers:pinned.powers,constTemplates:consts})!==pinned.precision)
  throw Error("allocation rule does not reproduce the pinned precision recipe");
for(const f of circuits){const c=fromCircuit(f);
  if(c.constValues!==consts.length)throw Error("constant set changed");
  const prec=precision({...c,constTemplates:consts});
  console.log(f,JSON.stringify({...c,precisionQ:prec,totalQ:pinned.nonPrecision+prec}));}
