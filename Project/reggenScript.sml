open HolKernel Parse boolLib bossLib;

open basis_emitTheory;
open EmitML;
open RegTheory;

app load ["EmitML"];

val _ = new_theory "reggen";

emitML ("") 
("reggen",
 [OPEN ["list", "pair"] ,

 DATATYPE 
(`Reg = Eps 
| Sym 'a 
| Alt Reg Reg 
| Seq Reg Reg 
| Rep Reg`) ,


 DATATYPE 
(`MReg =  MEps
| MSym bool 'a
| MAlt MReg MReg
| MSeq MReg MReg
| MRep MReg`) ,

DATATYPE
(`CMReg = CMEps    
|CMSym bool 'a
|CMAlt bool bool CMReg CMReg
|CMSeq bool bool CMReg CMReg
|CMRep bool CMReg`),


DEFN split_def,
DEFN parts_def,
DEFN accept_def ,

DEFN empty_def,
DEFN final_def,
DEFN shift_def,
DEFN MARK_REG_def,
DEFN UNMARK_REG_def,
DEFN acceptM_def,

DEFN CMempty_def,
DEFN CMfinal_def,
DEFN CMapply_def,
DEFN CACHE_REG_def,
DEFN UNCACHE_REG_def,
DEFN CMshift_def,
DEFN acceptCM_def


]);


val _ = export_theory();
