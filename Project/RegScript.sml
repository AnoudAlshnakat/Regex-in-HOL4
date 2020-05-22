open HolKernel Parse boolLib bossLib pred_setLib ;
open pairSimps boolSimps rich_listSimps pred_setSimps;
open pairTheory listTheory rich_listTheory pred_setTheory quantHeuristicsTheory arithmeticTheory;
open pred_setSyntax ;
open EmitML; 

val _ = new_theory "Reg"; 

     (***********************************************************)
     (**               Basic regular expression                **)
     (***********************************************************)

(* Definition of Reg data type *)
val Regexx = Datatype `
  Reg =  Eps   (*         Empty            *)
| Sym 'a       (*         Symbol           *)
| Alt Reg Reg  (*      a|b Alternative     *)
| Seq Reg Reg  (*       ab Sequence        *)
| Rep Reg`;    (* a* Zero or more Repition *)




(* Definition of language_of that returns a language accepted by the Regs.*)
val language_of_def = Define `
(language_of Eps  = {[]}) /\
(language_of (Sym c : 'a Reg) = {[c]}) /\
(language_of (Alt p q) = (language_of p) UNION (language_of q)) /\
(language_of (Seq p q) = {(x ++ y) | x ∈ language_of p /\  y ∈ language_of q} ) /\
(language_of (Rep r) =  {x| ?w. (!e. MEM e w ==> e ∈ language_of r) /\ ((FLAT w)=x)}) `;

(*
val test1  = EVAL``language_of Eps``;
val test2  = EVAL``language_of (Sym a)``;
val test3  = EVAL``language_of (Alt (Sym a) (Sym b))``;
val test4  = EVAL``language_of (Rep (Sym a))``;
val test5  = EVAL``language_of (Rep (Alt (Sym a) (Sym b)))``;
val test6  = EVAL``language_of (Seq (Sym a) (Sym b) )``;
*)




(* A Definition of an auxilary function that produces all decompositions of a string
into two factors. *)
val split_def = Define `
(split []      = [([],[])] ) /\
(split (c::cs) = ([],c::cs)::MAP(\(s1,s2). (c::(s1), s2)) (split cs))`;

(*
val test1  = EVAL``split []``;
val test2  = EVAL``split [1;2]``; 
val test3  = EVAL``split [b;b;b]``; 
val test4  = EVAL``split [ b ;c ; b ;c]``;
val test5  = EVAL``split ([b;a]++[c;d])``;
*)




(* A Definition of an auxilary function that produces all decompositions of a string.*)
val parts_def = Define `
(parts []  = [[]] ) /\
(parts [c] = [[[c]]] ) /\
(parts (c::cs1::cs2) = FLAT (MAP (\x. [[c]::x; (c::(HD x))::(TL x)]) (parts (cs1::cs2))))`;

(*
val test1  = EVAL``parts []``;
val test2  = EVAL``parts [1]``; 
val test3  = EVAL``parts [b;b;b]``; 
(* [[[b]; [b]; [b]]; [[b; b]; [b]]; [[b]; [b; b]]; [[b; b; b]]]*)
val test4  = EVAL``parts [a;b;c;d]``;
val test5  = EVAL``parts ([a;b]) ++ parts ([c;d])``;
val test6  = EVAL``parts [Sym p; Sym s]``;
val test7  = EVAL``parts [] ++ parts []``;
val test7  = EVAL``FLAT [[a]; [b]; [c]; [d]]``;
val test7  = EVAL``FLAT [a;b;c;d]``;
val test8  = EVAL``[[b]; [b]; [b]] ++ FLAT [ [[b; b]; [b]]; [[b]; [b; b]]; [[b; b; b]]]``;
val test8  = EVAL``FLAT [ [[b]; [b]; [b]];[[b; b]; [b]]; [[b]; [b; b]]; [[b; b; b]]]``;
*)



(* Definition of accept that defines the language accepted by an arbitrary regular expression. *)
val accept_def = Define `
(accept Eps       u = NULL u )  /\
(accept (Sym c)   u = (u =[c]) )   /\
(accept (Alt p q) u = (accept p u \/ accept q u)) /\
(accept (Seq p q) u = (EXISTS (\x. accept p (FST x) /\ accept q (SND x))(split u)))   /\
(accept (Rep r)   u = EXISTS ( \ps. EVERY(\u1. accept r u1) ps) ( parts u ))`;




(* Sanity checks for split definition. *)
val split_thm1 = prove (``!l. l = (c::cs) ==> (SND (HD (split (l)))) = (l) ``,
 STRIP_TAC >>
 ASM_REWRITE_TAC[] >>
 REWRITE_TAC[split_def] >>
 ASM_SIMP_TAC list_ss [split_def]
);




val split_thm2 = prove (``!l. MEM ([], l) (split l) ``,
 Induct >|[
   REWRITE_TAC[split_def] >>
   EVAL_TAC,
   ASM_SIMP_TAC list_ss [split_def]
]);




val split_thm3 = prove (``!l1 l2. MEM (l1,l2) (split (l1++l2))``,
 Induct_on`l1` >|[
   REWRITE_TAC [split_thm2, APPEND, MEM] ,
   ASM_REWRITE_TAC [APPEND, MEM, MAP, split_def] >>
   REWRITE_TAC [MEM_MAP]>>
   ASM_SIMP_TAC (list_ss++QI_ss) [split_def] 
]);




val split_thm4 = prove (``! l1 l2 l. MEM (l1, l2) (split l) ==> (l1 ++ l2 = l) ``,
 Induct_on `l` >|[
   SIMP_TAC list_ss [split_def],
   ASM_SIMP_TAC (list_ss++QI_ss) [split_def, MEM_MAP] >>
   REPEAT GEN_TAC  >> 
   STRIP_TAC >|[
     `([]) ++ (h::l) = (h::l)` by REWRITE_TAC[APPEND] >> 
     METIS_TAC[],
     ASM_SIMP_TAC list_ss [] 
  ]
]);




val split_thm5 = prove (``! l1 l2 l. (l1 ++ l2 = l) ==> MEM (l1, l2) (split l) ``,
 REPEAT STRIP_TAC >>
 `l = l1 ⧺ l2` by ASM_REWRITE_TAC[] >>
 FULL_SIMP_TAC list_ss [split_thm3]
);




val split_thm6 = prove (``! l1 l2 l. (MEM (l1, l2) (split l)) = (l1 ++ l2 = l) ``,
 REPEAT GEN_TAC >>
 EQ_TAC >|[
   REWRITE_TAC[split_thm4] ,
   REWRITE_TAC[split_thm5]
]);




(* Sanity checks for parts definition. *)
val parts_thm_1 = prove (``!l. LENGTH l = 0 ==> (parts l = [[]]) ``,
 REPEAT STRIP_TAC >>
 ASSUME_TAC LENGTH_NIL>>
 RES_TAC>>
 ASM_REWRITE_TAC[]>>
 EVAL_TAC
);




val parts_thm_2 = prove (``!l. LENGTH l = 1 ==> (parts l = [[l]]) ``,
 Induct >|[
  EVAL_TAC,
  SIMP_TAC list_ss [parts_def]
]);




val parts_thm_3 = prove (``!a. MEM [[a]] (parts [a]) ``,
 REWRITE_TAC[parts_def]>>
 EVAL_TAC >>
 DECIDE_TAC 
);




val parts_thm_4 = prove (``!l l1 l2. l = l1++l2 ==> (parts (l1++l2) = parts(l)) ``,
 REPEAT STRIP_TAC >>
 ASM_REWRITE_TAC []
);




val parts_thm_5 = prove (``!l. l <> [] ==> ~ MEM ([[]]) (parts [l])  ``,
 Cases >|[
   DECIDE_TAC  ,
   STRIP_TAC >>
   ASM_REWRITE_TAC [parts_def] >>
   REWRITE_TAC [MEM] >> 
   EVAL_TAC
]);




val parts_thm_6 = prove (``!l1 l2. (l1 = [] /\ l2 = []) ==> MEM ([]) (parts(l1) ++ parts (l2))``,
 REPEAT STRIP_TAC >>
 ASM_REWRITE_TAC [] >>
 EVAL_TAC
);




(* Any member of the parts result list, can be flatten to give the original list as an input.
lemma to prove the Rep reg that appears when proving the following
"∀w. accept (Rep r) w ⇒ w ∈ language_of (Rep r)",
In the end, we end up proving (FLAT p = w), and this is true.
val test1  = EVAL``parts [a;b;c]``;
val test2  = EVAL``FLAT [[a]; [b; c]]``;  *)
val THM_x = store_thm ("THM_x", ``!l p. MEM p (parts l) <=> (~(MEM [] p) /\ (FLAT p = l))``,
 Induct >| [            (*parts with empty*)
   SIMP_TAC list_ss [parts_def] >>
   Cases_on `p` >>
   REPEAT (SIMP_TAC list_ss [] >> METIS_TAC[])   ,
    
   Cases_on `l`>| [     (* parts with [h] *)
     SIMP_TAC (list_ss) [parts_def] >> 
     REPEAT GEN_TAC >>
     EQ_TAC >>  
     REPEAT STRIP_TAC >> (
     Cases_on `p` >> 
     TRY (FULL_SIMP_TAC (list_ss) []) >>
     Cases_on `t` >> 
     TRY (FULL_SIMP_TAC (list_ss) []))  >>
     Cases_on `h'` >> 
     TRY (FULL_SIMP_TAC (list_ss) [])>>
     FULL_SIMP_TAC (list_ss) [] ,
                 
     REPEAT GEN_TAC >>   (*part with h'::h::t*)
     ASM_SIMP_TAC (list_ss++LIFT_COND_ss) [parts_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     Cases_on `p` >> 
     SIMP_TAC list_ss [] >> 
     REPEAT STRIP_TAC >> 
     EQ_TAC >> 
     STRIP_TAC  >|[
       ASM_SIMP_TAC list_ss [],

       Cases_on `x` >> 
       FULL_SIMP_TAC list_ss [],

       FULL_SIMP_TAC list_ss [APPEND_EQ_SING, APPEND_EQ_CONS, APPEND] >|[
         FULL_SIMP_TAC list_ss [],
         Q.EXISTS_TAC `t'` >>
         FULL_SIMP_TAC list_ss [],
         Q.EXISTS_TAC `(h::lt')::t'` >>
         FULL_SIMP_TAC list_ss [] 
      ]
    ] 
  ]
]);




(* This theorm is needed when proving the Rep part(appears in accept is equavlent to language_of) , where it needs to be simplified.  t.ex.
val test1  = EVAL``FLAT [[a;b;c]]``;
val test2  = EVAL``((FILTER (\x. x <> []) [[a;b;c]]))``;
val test3  = EVAL``(FLAT (FILTER (\x. x <> []) [[a;b;c]]))``;  *)
val FLAT_of_FILTER = prove ( ``(!l. (FLAT (FILTER (\x. x <> []) l)) = (FLAT l)) ``,
 Induct_on `l` >|[ 
   SIMP_TAC list_ss [FLAT_compute, FILTER],
   Cases_on `h` >> 
   FULL_SIMP_TAC list_ss [FLAT_compute, FILTER]
]);




(* a FLAT lemma (USLESS.) *)
val FLAT_splitup_thm = prove(``!c cs l. (c::cs = FLAT l) ==> ?h' tl'.(FLAT l = FLAT ((c::h')::tl'))``,
  Induct_on `l` >- 
  SIMP_TAC list_ss [] >>
  REPEAT STRIP_TAC >>
  Cases_on `h` >> 
   (FULL_SIMP_TAC list_ss [] >> METIS_TAC [])
);




(* Eq proof starts here first I tried to follow a modular type of verification for each Reg case, 
and it worked only for the Eps and Sym. *)
val EQ_ACC_LAN_EPS = prove (``!w. (accept Eps w) =  (w IN language_of Eps)``,
 REWRITE_TAC [accept_def, language_of_def] >>
 SIMP_TAC list_ss [IN_INSERT] >> 
 RW_TAC list_ss [EXISTS_SIMP,NULL_EQ]
);




val EQ_ACC_LAN_SYM = prove (``!w a. (accept (Sym a) w) =  (w IN language_of (Sym a))``,
 REWRITE_TAC [accept_def, language_of_def] >>
 SIMP_TAC list_ss [IN_INSERT] >> 
 RW_TAC list_ss [EXISTS_SIMP,NULL_EQ]
);




(* This theorm was needed because I did not know how to introdudce the exsistance quantifier in order to proof the Seq case. *)
val thm_lang_SEQ_extention = prove( ``(!w r r'. w IN (language_of (Seq r r')) <=>  
?x y. (w=x++y) /\ (x IN language_of r) /\  (y IN language_of r')) ``,
 REWRITE_TAC [language_of_def ] >>
 SIMP_TAC (std_ss++PRED_SET_ss) []
);




(* This theorm was needed in order to prove the second part of the project(Cached Marked). *)
val thm_lang_REP_extention = prove( `` !w r x. x IN language_of (Rep r) <=> ?w. ~(MEM [] w) /\ (EVERY (\e. e IN language_of r) w) /\ ((FLAT  w) = x)``,
 FULL_SIMP_TAC (list_ss++PRED_SET_ss) [language_of_def, EVERY_MEM]>>
 REPEAT STRIP_TAC>>
 EQ_TAC >|[
   REPEAT STRIP_TAC>>
   Q.EXISTS_TAC `(FILTER (\x. x <> []) w)` >>
   FULL_SIMP_TAC (list_ss) [FLAT_of_FILTER] >>
   FULL_SIMP_TAC (list_ss) [MEM_FILTER, EVERY_MEM] ,

   REPEAT STRIP_TAC >>
   Q.EXISTS_TAC `w`>>
   ASM_REWRITE_TAC []
]);




(* First Implications of the accept language_of equavelnce *)
val EQ_ACCEPT_LANG_IMP1 =  store_thm ("EQ_ACCEPT_LANG_EQ1", ``!r w. accept r w ==> w IN (language_of r) ``, 
 Induct_on `r` >|[
   (*FIRST:  Eps*)
   REWRITE_TAC [EQ_ACC_LAN_EPS] ,

   (*SECOND: Sym*)
   REWRITE_TAC [EQ_ACC_LAN_SYM] ,

   (*THIRD:  Alt*)
   REPEAT STRIP_TAC >>
   FULL_SIMP_TAC (list_ss) [language_of_def, accept_def] ,

   (*FOURTH: Seq*)
   REPEAT STRIP_TAC >>
   FULL_SIMP_TAC (list_ss) [split_thm6, accept_def, thm_lang_SEQ_extention, EXISTS_PROD, EXISTS_MEM] >>
   Q.EXISTS_TAC `p_1` >>
   Q.EXISTS_TAC `p_2` >>
   FULL_SIMP_TAC (list_ss) [split_thm6] ,

   (*FIFTH: Rep*)
   REPEAT STRIP_TAC >>
   ASM_REWRITE_TAC [language_of_def] >>
   FULL_SIMP_TAC (list_ss++PRED_SET_ss) [language_of_def, accept_def] >>
   FULL_SIMP_TAC std_ss [EXISTS_MEM, EVERY_MEM]>>
   Q.EXISTS_TAC `ps` >>
   FULL_SIMP_TAC std_ss [THM_x] 
]);




(* Second Implications of the accept language_of equavelnce *)
val EQ_ACCEPT_LANG_IMP2 =  store_thm ("EQ_ACCEPT_LANG_EQ2", ``!r w. w IN (language_of r) ==> accept r w ``, 
 Induct_on  `r` >|[
   (*FIRST:  Eps*)
   REWRITE_TAC [EQ_ACC_LAN_EPS] ,

   (*SECOND: Sym*)
   REWRITE_TAC [EQ_ACC_LAN_SYM] ,

   (*THIRD:  ALt*)
   REPEAT STRIP_TAC >>
   FULL_SIMP_TAC (list_ss++PRED_SET_ss) [language_of_def, accept_def] ,

   (*FOURTH: Seq*)
   REPEAT STRIP_TAC >>
   FULL_SIMP_TAC (list_ss) [language_of_def, accept_def, thm_lang_SEQ_extention,EXISTS_PROD,EXISTS_MEM] >>
   Q.EXISTS_TAC `x` >>
   Q.EXISTS_TAC `y` >>
   FULL_SIMP_TAC (list_ss) [split_thm6],

   (*FIFTH: Rep*)
   ASM_SIMP_TAC (list_ss++PRED_SET_ss++QI_ss) [accept_def, language_of_def, THM_x, EXISTS_MEM, EVERY_MEM] >>
   REPEAT STRIP_TAC >>
   Q.EXISTS_TAC `(FILTER (\x. x <> []) w)` >>
   FULL_SIMP_TAC list_ss [FLAT_of_FILTER] >>
   ASM_SIMP_TAC std_ss [MEM_FILTER]
]);




(* Pheeeeeewwwwwwwwww EQ finally the equavilence. *)
val ACCEPT_LANG_EQ =  store_thm ("ACCEPT_LANG_EQ",  ``!r w. w IN (language_of r) <=> accept r w ``,
 NTAC 2 GEN_TAC >> 
 EQ_TAC >> 
 REWRITE_TAC [EQ_ACCEPT_LANG_IMP1,EQ_ACCEPT_LANG_IMP2]
);






     (***********************************************************)
     (**               Marked regular expression               **)
     (***********************************************************)

(* Definition of Marked Reg data type, the bool is the mark of the symbols. *)
val _ = Datatype `
MReg =  MEps
| MSym bool 'a
| MAlt MReg MReg
| MSeq MReg MReg
| MRep MReg`;




(* A Definition of an auxilary function that checks potential emptiness state of the regex.
In the sence that the regs MEps or MRep can be considered as empty, because in MRep we need an occurance zero or more of the charachter, and the MEps is an empty string.
Formally: helps to checks whether the word has an empty charachter or not. 
*)
val empty_def = Define ` 
(empty MEps       = T)  /\
(empty (MSym _ _) = F)  /\
(empty (MAlt p q) = (empty p \/ empty q)) /\
(empty (MSeq p q) = (empty p /\ empty q)) /\
(empty (MRep _  ) = T ) `;

(*
val test1  = EVAL``empty MEps``;
val test2  = EVAL``empty (MSym F a)``; 
val test3  = EVAL``empty (MSym T a)``;
val test4  = EVAL``empty (MRep (MSym T b))``;
val test5  = EVAL``empty (MRep (MSym F b))``;
val test6  = EVAL``empty (MAlt (MSym T a) (MSym T a))``;
val test7  = EVAL``empty (MAlt (MSym T a) (MEps))``;
val test8  = EVAL``empty (MRep (MAlt (MSym T t) (MEps)))``;
val test9  = EVAL``empty (MSeq (MEps) (MSym T b)) ``;
*)




(* A Definition of an auxilary function that checks whether the word has a final charachter.
Final determins whther the word is marked or not.
It depends on three main cases:
1. Always false whenever the final marked reg is MEps, i.e. not final
2. For the symbols it depends on the state of it being marked or not. If marked, then it is final.
3. In the (MSeq p q) case, its can depend on the q being empty, i.e (empty MEps) or (empty MRep) 
*)
val final_def = Define `
(final MEps       = F) /\
(final (MSym b _) = b) /\
(final (MAlt p q) = (final p \/ final q)) /\
(final (MSeq p q) = (final p /\ empty q  \/ final q )) /\
(final (MRep  r ) = final r )`;

(*
val test1  = EVAL``final MEps``;
val test2  = EVAL``final (MSym F a)``; 
val test3  = EVAL``final (MSym T a)``;
val test4  = EVAL``final (MRep (MSym T b))``;
val test5  = EVAL``final (MRep (MSym F b))``;
val test6  = EVAL``final (MAlt (MSym T a) (MSym T a))``;
val test7  = EVAL``final (MAlt (MSym T a) (MEps))``;
val test8  = EVAL``final (MRep (MAlt (MSym T t) (MEps)))``;
val test9  = EVAL``final (MSeq (MEps) (MSym T b)) ``;
val test10 = EVAL``final (MRep (MEps))``;
*)




(* A Definition of the shift. It takes a marked (m:bool for the previous occurance of this 
charachter c) , regex(MReg), and a charachter('a) to be read and generates a marked expression. *)
val shift_def = Define `
(shift _   MEps      _ = MEps                            ) /\  (*doesn't get marked*)
(shift m  (MSym _ x) c = MSym (m /\ (x = c)) x           ) /\
(shift m  (MAlt p q) c = MAlt (shift m p c) (shift m q c)) /\
(shift m  (MSeq p q) c = MSeq (shift m p c) (shift (m /\ empty p \/ final p) q c)) /\
(shift m  (MRep r)   c = MRep (shift (m \/ final r) r c))`;

(*
val test1  = EVAL``shift F MEps F``;
val test2  = EVAL``shift F (MSym F a) a``; 
val test3  = EVAL``shift F (MSym T a) a``; 
val test4  = EVAL``shift T (MSym F a) a``; 
val test5  = EVAL``shift T (MSym T a) b``; 
val test6  = EVAL``shift F (MAlt (MSym F a) (MEps)) a``;
val test7  = EVAL``shift T (MRep (MSym T a)) a``;
val test8  = EVAL``shift T (MRep (MSym F a)) b``;
val test9  = EVAL``shift T (MAlt (MSym T a) (MSym b T)) a``;
*)




(* Definition of the MARK_REG. *)
val MARK_REG_def = Define `
(MARK_REG Eps       = MEps                          ) /\
(MARK_REG (Sym c)   = MSym F c                      ) /\
(MARK_REG (Alt p q) = MAlt (MARK_REG p) (MARK_REG q)) /\
(MARK_REG (Seq p q) = MSeq (MARK_REG p) (MARK_REG q)) /\
(MARK_REG (Rep r)   = MRep (MARK_REG r)             )`;

(*
val test1  = EVAL``MARK_REG Eps``;
val test2  = EVAL``MARK_REG (Sym a)``; 
val test3  = EVAL``MARK_REG (Rep (Eps))``;
val test4  = EVAL``MARK_REG (Rep (Sym b))``;
val test6  = EVAL``MARK_REG (Alt (Sym a) (Sym b))``;
val test7  = EVAL``MARK_REG (Alt (Sym a) (Eps))``;
val test8  = EVAL``MARK_REG (Rep (Alt (Sym a) (Eps)))``;
val test9  = EVAL``MARK_REG (Seq (Eps) (Sym b)) ``;
*)




(* Definition of the UNMARK_REG. *)
val UNMARK_REG_def = Define `
(UNMARK_REG MEps        = Eps                              ) /\
(UNMARK_REG (MSym _  c) = Sym c                            ) /\
(UNMARK_REG (MAlt p q)  = Alt (UNMARK_REG p) (UNMARK_REG q)) /\
(UNMARK_REG (MSeq p q)  = Seq (UNMARK_REG p) (UNMARK_REG q)) /\
(UNMARK_REG (MRep r)    = Rep (UNMARK_REG r))`;

(*
val test1  = EVAL``UNMARK_REG MEps``;
val test2  = EVAL``UNMARK_REG (MSym T a)``; 
val test3  = EVAL``UNMARK_REG (MRep (MEps))``;
val test4  = EVAL``UNMARK_REG (MRep (MSym T b))``;
val test6  = EVAL``UNMARK_REG (MAlt (MSym T a) (MSym T b))``;
val test7  = EVAL``UNMARK_REG (MAlt (MSym T a) (MEps))``;
val test8  = EVAL``UNMARK_REG (MRep (MAlt (MSym F a) (MEps)))``;
val test9  = EVAL``UNMARK_REG (MSeq (MEps) (MSym T b)) ``;
*)




(* Definition of the accept. *)
val acceptM_def = Define `
(acceptM r []      = empty r                                  ) /\
(acceptM r (c::cs) = final (FOLDL (shift F) (shift T r c)  cs))`;

(*
val test1  = EVAL``acceptM MEps []``;
val test2  = EVAL``acceptM (MSym T a) [a]``; 
val test3  = EVAL``acceptM (MSym T a) [b;b;b]``;
val test4  = EVAL``acceptM (MSym F a) [b;b;b]``;
val test5  = EVAL``acceptM (MRep (MSym T b)) [b;b;b;v]``;
val test6  = EVAL``acceptM (MRep (MSym T b)) []``;
val test6  = EVAL``acceptM (MRep (MSym F b)) []``;
val test7  = EVAL``acceptM (MAlt (MSym T a) (MSym T b)) [a]``;
val test8  = EVAL``acceptM (MRep (MAlt (MSym F a) (MSym F b))) [a;a;b;a;b;a]``;
val test9  = EVAL``acceptM (MSeq (MSym F a) (MSym F b)) [a;b]``;
val test9  = EVAL``acceptM (MSeq (MEps) (MEps)) []``;
val test6  = EVAL``acceptM (MARK_REG (Sym a)) [a]``;
*)




(* Lemma about unmarking a marked reg. *)
val UNMARK_REG_MARK = prove (  ``!r. UNMARK_REG (MARK_REG r) = r ``,
 Induct >> 
 ASM_SIMP_TAC list_ss [MARK_REG_def, UNMARK_REG_def]
);



(* Sanity checks for empty. *)
val empty_Sanity1 = prove (  ``empty MEps ``,
 REWRITE_TAC[empty_def]
);



val empty_Sanity2 = prove (  ``!r. empty r ==> empty (MRep r) ``,
 REWRITE_TAC[empty_def]
);



val empty_Sanity3 = prove (  ``!r. empty r ==> empty (MRep r) ``,
 REWRITE_TAC[empty_def]
);



val empty_Sanity4 = prove (  ``!r q. empty r ==> empty (MAlt q r) ``,
 FULL_SIMP_TAC bool_ss [empty_def]
);



val empty_Sanity5 = prove (  ``!r q. empty (MAlt q r) ==> empty q \/ empty r ``,
 FULL_SIMP_TAC bool_ss [empty_def]
);



val empty_Sanity6 = prove (  ``!r q. empty (MSeq q r) ==> empty q /\ empty r ``,
 FULL_SIMP_TAC bool_ss [empty_def]
);



(* Sanity checks for final. *)
val final_Sanity1 = prove (  ``!b a. b ==> final (MAlt (MSym b a)(MEps)) ``,
 FULL_SIMP_TAC bool_ss [empty_def, final_def]
);



val final_Sanity2 = prove (  ``!b t. b ==> final (MRep (MAlt (MSym b t) (MEps))) ``,
 FULL_SIMP_TAC bool_ss [empty_def, final_def]
);



val final_Sanity3 = prove (  ``~ final (MRep (MEps))``,
 FULL_SIMP_TAC bool_ss [ final_def]
);



(* Sanity checks for final empty. *)
val final_empty_Sanity1 = prove (  ``!b a. empty (MSym b a) ==> final (MSym b a)``,
 FULL_SIMP_TAC bool_ss [empty_def, final_def]
);



val final_empty_Sanity2 = prove (  ``!b a. final (MRep (MSym b a)) ==> empty (MRep(MSym b a))``,
 FULL_SIMP_TAC bool_ss [empty_def, final_def]
);



val final_empty_Sanity3 = prove (  ``!b a.  empty (MSeq MEps (MSym b a)) ==> final (MSeq MEps (MSym b a)) ``,
 FULL_SIMP_TAC bool_ss [empty_def, final_def]
);



(* Sanity checks for accept. *)
val final_acceptM_Sanity3 = prove (``!r s. (r=MEps) \/ (r = MRep s) ==> acceptM r []``  ,
 REPEAT STRIP_TAC >>
 FULL_SIMP_TAC bool_ss [acceptM_def, empty_def]
);



(* Sanity checks for shift. *)
val shift_unmark = prove ( ``!r B x. (UNMARK_REG (shift B r x)) = (UNMARK_REG r)``, 
 Induct >>
   ASM_SIMP_TAC (list_ss++PRED_SET_ss) [shift_def, UNMARK_REG_def] 
);




(* The proof of the the marked regs equavelance started with proving the empty case of the induction.
val test1  = EVAL``acceptM (MSym T a) []``; This one is false, thus [] is not in the language
val test2  = EVAL ``[] IN language_of (UNMARK_REG (MSym T a))``;
*)
val acceptM_Empty_EQ = prove (``!(r :α Reg) . acceptM (MARK_REG r) [] <=> [] IN (language_of r)``,
 Tactical.REVERSE Induct >> 
   (FULL_SIMP_TAC (list_ss) [language_of_def, MARK_REG_def, acceptM_def, empty_def] >>
   ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND, PULL_EXISTS]>>
   FULL_SIMP_TAC std_ss [EXISTS_MEM]>>
   Q.EXISTS_TAC `[]` >>
   FULL_SIMP_TAC (list_ss++QI_ss++PRED_SET_ss) [language_of_def, MARK_REG_def, acceptM_def, empty_def]) >>
  (FULL_SIMP_TAC (list_ss++QI_ss++PRED_SET_ss) [language_of_def, MARK_REG_def, acceptM_def, empty_def]) 
);




(* Proof of the first case (i.e. MEps) of the equality. *)
val acceptM_Eps = prove (``!r w. acceptM (MARK_REG Eps) w <=> w IN (language_of Eps)``,
 Induct_on `w`  >|[
   REWRITE_TAC [acceptM_Empty_EQ],
   Cases_on `w` >> 
   FULL_SIMP_TAC list_ss [FOLDL, final_def, shift_def, language_of_def, acceptM_def, MARK_REG_def] 
]);




(* Proof of the second case (i.e. MSym) of the equality. *)
val acceptM_Sym = prove (``!a w. acceptM (MARK_REG (Sym a)) w <=> w IN language_of (Sym a)``,
 Induct_on `w`>|[    
   (*[] ∈ language_of (Sym a)*)
   REWRITE_TAC [acceptM_Empty_EQ],

   GEN_TAC >> 
   REWRITE_TAC[acceptM_def, MARK_REG_def]>> 
   Cases_on `w` >|[  
     (*[h] ∈ language_of (Sym a)*)
     FULL_SIMP_TAC list_ss  [language_of_def, acceptM_def, MARK_REG_def]>>
     FULL_SIMP_TAC list_ss  [FOLDL, final_def, shift_def] >>
     REPEAT GEN_TAC >> 
     EQ_TAC >> 
     STRIP_TAC >> 
     ASM_REWRITE_TAC[] ,

     (*h::h'::t ∈ language_of (Sym a)*)
     Cases_on `t` >>
       NTAC 2 (
       FULL_SIMP_TAC bool_ss []>>
       REPEAT (FULL_SIMP_TAC list_ss [FOLDL, final_def, shift_def, language_of_def, acceptM_def, MARK_REG_def]
      ))
    ]
]);




(* Definition represents accepted words of a given marked regex. *)
val language_of_marked_def = Define` 
(language_of_marked MEps       =  {}                    )/\
(language_of_marked (MSym B x) = if B then {[]} else {} )/\
(language_of_marked (MAlt p q) = ((language_of_marked p) UNION (language_of_marked q))) /\
(language_of_marked (MSeq p q) = {a++b | a ∈ (language_of_marked p) /\ b ∈ (language_of (UNMARK_REG q))} UNION (language_of_marked q) )/\
(language_of_marked (MRep r)   = {a++b | a ∈ (language_of_marked r) /\ b ∈ (language_of (UNMARK_REG (MRep r)))})`;

(*
val test1  = EVAL``language_of_marked MEps``;
val test2  = EVAL``language_of_marked (MSym T a)``;
val test3  = EVAL``language_of_marked (MSym F a)``;
val test4  = EVAL``language_of_marked (MAlt (MEps)(MEps) )``;
val test5  = EVAL``language_of_marked (MAlt (MSym F a) (MSym T b))``;
val test6  = EVAL``language_of_marked (MRep (MSym T a))``;
val test7  = EVAL``language_of_marked (MRep (MAlt (MSym T a) (MSym T b)))``;
val test8  = EVAL``language_of_marked (MSeq (MSym T a) (MSym  T b) )``;
val test9  = EVAL``language_of_marked (MSeq (MSym T a) (MEps) )``;
*)




(* Lemma to introduce the exsistance quantifier in the MSeq case of the language of marked regex. *)
val in_language_of_MSeq = prove ( ``!p q w. (w IN language_of_marked (MSeq p q)) <=>
       (w ∈ language_of_marked q) \/ (?a b. (w = a ++ b) /\ (a ∈ (language_of_marked p)) /\
                (b ∈ (language_of (UNMARK_REG q))))``,
 REPEAT GEN_TAC >> 
 REWRITE_TAC[language_of_def, language_of_marked_def, UNMARK_REG_def]>>
 FULL_SIMP_TAC (list_ss++PRED_SET_ss++QI_ss) [] >> 
 DECIDE_TAC
);




(* Lemma to introduce the exsistance quantifier in the MRep case of the language of marked regex. *)
val in_language_of_MRep = prove ( ``(!w r. w IN language_of_marked (MRep r) <=>
 ?a b. (w = a ++ b) /\ (a IN (language_of_marked r) /\  b IN (language_of (Rep (UNMARK_REG r)))))``,
 REPEAT GEN_TAC >> 
 REWRITE_TAC[language_of_def, language_of_marked_def, UNMARK_REG_def]>>
 FULL_SIMP_TAC (std_ss++PRED_SET_ss) [] >> 
 DECIDE_TAC 
);




(* If the word has a charachter considered to be final (i.e. marked), so no other character has 
to be read, thus accept []. Otherwise If the charachter is not final, then don't accept the empty string. *)
val final_in_lang = store_thm( "final_in_lang", ``!(r :α MReg). (final r) = ([] IN language_of_marked r)``,
 Induct >| [
   (* MEps *)
   REWRITE_TAC[language_of_marked_def, final_def] >> 
   EVAL_TAC,

   (* MSym *)
   REWRITE_TAC[language_of_marked_def, final_def] >>  
   Cases_on `b` >> 
   REWRITE_TAC [] >> 
   EVAL_TAC ,

   (* MAlt *)
   REWRITE_TAC[language_of_marked_def, final_def] >>  
   ASM_REWRITE_TAC [] >> 
   SIMP_TAC list_ss[] , 

   (* MSeq *)
   Q.SUBGOAL_THEN `!r'. (empty r') = ([] IN language_of (UNMARK_REG r'))` ASSUME_TAC >|[
     NTAC 2 (POP_ASSUM (K ALL_TAC)) >>
     Induct_on `r'` >> 
     NTAC 4 (FULL_SIMP_TAC (list_ss) [language_of_def, empty_def, UNMARK_REG_def]) >|[
       ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND, PULL_EXISTS]>>
       FULL_SIMP_TAC std_ss [EXISTS_MEM] , 
       ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND, PULL_EXISTS]>>
       FULL_SIMP_TAC std_ss [EXISTS_MEM] >>  
       Q.EXISTS_TAC `[]` >> 
       SIMP_TAC list_ss []
       ] ,

      FULL_SIMP_TAC (list_ss) [language_of_marked_def, final_def, in_language_of_MSeq, UNMARK_REG_def, language_of_def]>> 
     EQ_TAC >> 
     STRIP_TAC >> 
     REPEAT (ASM_SIMP_TAC list_ss [])
   ] ,

   (* MRep *)
   REWRITE_TAC[final_def, language_of_marked_def] >>
   SIMP_TAC (list_ss++QI_ss++PRED_SET_ss)[language_of_marked_def, UNMARK_REG_def, final_def, ACCEPT_LANG_EQ]>>
   EVAL_TAC >>
   Induct_on `r` >> 
   DECIDE_TAC
]);




(* A lemma to incidate that the empty language is in the language_of the unmarked regex
which helps proving the marked reg being empty in one case; which happend when the empty string is
in its initial language. *)
val empty_in_lang = prove ( ``!r'. (empty r') = ([] IN language_of (UNMARK_REG r'))``, 
 Induct_on `r'` >>
   (ASM_SIMP_TAC (list_ss)[empty_def, language_of_def, UNMARK_REG_def] >> 
   FULL_SIMP_TAC (std_ss++PRED_SET_ss) [EXISTS_MEM, EVERY_MEM, PULL_EXISTS]) >|[
     EQ_TAC >> REPEAT STRIP_TAC >|[
       Q.EXISTS_TAC `[]`>>
       Q.EXISTS_TAC `[]`>>
       FULL_SIMP_TAC list_ss [language_of_def, UNMARK_REG_def] ,

       FULL_SIMP_TAC list_ss [] >>
       `[] = x` by ASM_REWRITE_TAC [] >>
       REV_FULL_SIMP_TAC std_ss [] ,

       FULL_SIMP_TAC list_ss [] >>
       `[] = y` by ASM_REWRITE_TAC []>>
       REV_FULL_SIMP_TAC std_ss []
     ]  ,

   Q.EXISTS_TAC `[]`>>
   FULL_SIMP_TAC list_ss [FLAT, language_of_def, UNMARK_REG_def, MEM]
]);


(* accept the empty language, proved by the previous lemma. *)
val accept_empty = prove ( ``!r. accept (UNMARK_REG r) [] <=> empty r ``,
  SIMP_TAC list_ss  [empty_in_lang, ACCEPT_LANG_EQ] 
);




(* Sanity check that gathers both final and empty in the languages. *)
val final_empty_relation = prove ( ``!r r'. (final r' <=> [] IN language_of_marked r') 
      <=> (!r'. empty r' <=> [] ∈ language_of (UNMARK_REG r'))``,
 REWRITE_TAC [final_in_lang, empty_in_lang]
);




(* Lemma to show that because the language of marked Eps is always phi, then if a list is a
member of it then the subset of that list is also a member  i.e. (h::t ∈ ∅ ⇔ t ∈ ∅) *)
val lang_marked_MEps_phi = prove (`` !B h t. h::t IN language_of_marked MEps <=>
       t IN language_of_marked MEps ``,
 REWRITE_TAC [language_of_marked_def] >>
 SIMP_TAC list_ss []
);




(* Using shift in the language_of marked wouldn't change the result of the previous claimed Lemma*)
val lang_marked_shift_Eps = prove (`` !B h t.  t IN language_of_marked (shift B MEps h) <=>
       h::t IN language_of_marked MEps \/  ((h::t IN language_of (Eps)) /\ B ) ``,
   FULL_SIMP_TAC list_ss [shift_def, language_of_def, acceptM_def, MARK_REG_def]>>
   FULL_SIMP_TAC list_ss [lang_marked_MEps_phi]
);




(* This is a connection between the language_of marked definition and the 
language_of whenever the languge is shifted. when shifting the regex by h is equavelnt to 
making h part of the the accepted langugae of either language_of or language_of_marked. *)
val lang_in_shift =  prove ( `` !r m h t. (t IN language_of_marked (shift m r h)) <=> 
      h::t IN language_of_marked (r) \/ ((h::t IN language_of (UNMARK_REG (r))) /\ m) ``,
 Induct >| [ 
   (*EPS*)
   REWRITE_TAC [lang_marked_shift_Eps, UNMARK_REG_def], 

  (*SYM*)
   FULL_SIMP_TAC list_ss [shift_def]>>
   Cases_on `m` >>
   FULL_SIMP_TAC list_ss [language_of_def, language_of_marked_def, UNMARK_REG_def]>>
   Induct_on `a = h` >> 
   REPEAT STRIP_TAC >> 
   Cases_on `b` >>  
   FULL_SIMP_TAC (list_ss++PRED_SET_ss)[], 

   (*ALT*)
   FULL_SIMP_TAC list_ss [shift_def, language_of_def, acceptM_def, MARK_REG_def]>>
   Cases_on `m` >>
   FULL_SIMP_TAC list_ss [language_of_def, language_of_marked_def, UNMARK_REG_def, MARK_REG_def]>> 
   REPEAT STRIP_TAC >>
   EQ_TAC >> 
   REPEAT STRIP_TAC >>
   FULL_SIMP_TAC list_ss [], 

   (*SEQ*)
   FULL_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [shift_def, language_of_def, UNMARK_REG_def,  
   MARK_REG_def, in_language_of_MSeq, final_in_lang , empty_in_lang , APPEND, shift_unmark]>>
   ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND, PULL_EXISTS]>>
   REPEAT STRIP_TAC>> 
     EQ_TAC >| [
       REPEAT STRIP_TAC >|[  (*first direction of implication*)
       ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND]>>
       DISJ2_TAC >>
       Q.EXISTS_TAC `[]` >>
       Q.EXISTS_TAC `h::t` >>
       ASM_REWRITE_TAC [APPEND] ,

       ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND]>>
       DISJ1_TAC >>
       Q.EXISTS_TAC `[]` >>
       Q.EXISTS_TAC `h::t` >>
       ASM_REWRITE_TAC [APPEND] ,

       ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND]>>
       DISJ1_TAC >>
       Q.EXISTS_TAC `h::a` >>
       Q.EXISTS_TAC `b`>>
       ASM_REWRITE_TAC [APPEND] ,

       ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND]>>
       DISJ2_TAC>>
       Q.EXISTS_TAC `h::a` >>
       Q.EXISTS_TAC `b`>>
       ASM_REWRITE_TAC [APPEND]
       ], 


       STRIP_TAC >|[       (*Second direction of implication*)
         Cases_on `a` >|[
         DISJ1_TAC >>
         FULL_SIMP_TAC list_ss [APPEND] ,
         DISJ2_TAC >>
         FULL_SIMP_TAC list_ss [] >>  
         METIS_TAC [APPEND]] ,

         Cases_on `x` >|[
           DISJ1_TAC >>
           FULL_SIMP_TAC list_ss [APPEND] ,
           DISJ2_TAC >>
           FULL_SIMP_TAC list_ss [] >>  
           METIS_TAC [APPEND]]
      ]
    ] ,

   (*REP*)
   REPEAT STRIP_TAC>>
   EQ_TAC >| [          (*first direction of the equality MRep case !!!!!! *)
     FULL_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss)  [ shift_def, language_of_def, UNMARK_REG_def,  
     MARK_REG_def, in_language_of_MRep, final_in_lang, empty_in_lang , APPEND, shift_unmark]>>
     ASM_SIMP_TAC (list_ss++PRED_SET_ss)  [LIST_TO_SET_APPEND, PULL_EXISTS]>>
     FULL_SIMP_TAC std_ss [EXISTS_MEM, EVERY_MEM] >>
     REPEAT STRIP_TAC >| [
       DISJ1_TAC >>
       Q.EXISTS_TAC `h::a`>>
       Q.EXISTS_TAC `w`>>
       FULL_SIMP_TAC list_ss [APPEND, FLAT, FLAT_compute] ,

       DISJ2_TAC >>
       Q.EXISTS_TAC `(h::a)::w`>>
       FULL_SIMP_TAC list_ss [APPEND, FLAT, FLAT_compute] >>
       REPEAT STRIP_TAC >> 
       ASM_REWRITE_TAC [] >>  
       FULL_SIMP_TAC list_ss [] ,

       DISJ1_TAC>>
       Q.EXISTS_TAC `[]`>>
       Q.EXISTS_TAC `(h::a)::w`>>
       FULL_SIMP_TAC list_ss [APPEND, FLAT, FLAT_compute] >>
       REPEAT STRIP_TAC >> 
       ASM_REWRITE_TAC [] >>  
       FULL_SIMP_TAC list_ss []
       ] ,   

                       (*second direction of the equality*)
   FULL_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [shift_def, UNMARK_REG_def, MARK_REG_def, 
   in_language_of_MRep, final_in_lang, empty_in_lang , shift_unmark, thm_lang_REP_extention]>>
   ASM_SIMP_TAC (list_ss++PRED_SET_ss) [LIST_TO_SET_APPEND, PULL_EXISTS]>>
   FULL_SIMP_TAC std_ss [EXISTS_MEM, EVERY_MEM, PULL_EXISTS]>>
   REPEAT STRIP_TAC >|[    
     Cases_on `a` >| [ 
       FULL_SIMP_TAC list_ss []>>
       Cases_on `w`>>
       FULL_SIMP_TAC list_ss []>>
       Cases_on `h'`>>
       FULL_SIMP_TAC list_ss [] >>
       Q.EXISTS_TAC `t''`>>
       Q.EXISTS_TAC `t'`>>
       FULL_SIMP_TAC list_ss []  ,

       Q.EXISTS_TAC `t'`>>
       Q.EXISTS_TAC `w`>>
       FULL_SIMP_TAC list_ss []
       ]  ,
      
    Cases_on `w`>>
    FULL_SIMP_TAC list_ss []>>
    Cases_on `h'`>>
    FULL_SIMP_TAC list_ss [] >>
    Q.EXISTS_TAC `t''`>>
    Q.EXISTS_TAC `t'`>>
    FULL_SIMP_TAC list_ss []
    ]
 ] 
]);




(* FOLDL Simplification. *)
val FOLDL_shift_empty = prove  (`` FOLDL (shift F) (r) [] = r `` ,
 REWRITE_TAC[FOLDL]
);




(* FOLDL function will only repeat the shifting operation that was proved in lang_in_shift with a simple base case FOLDL_shift_empty. *)
val lang_in_fold_empty = prove( ``!h R. ([] IN language_of_marked (FOLDL (shift F) R h)) <=> (h IN language_of_marked R)``,
  Induct_on `h`>| [
    REWRITE_TAC[FOLDL_shift_empty],
    FULL_SIMP_TAC list_ss [lang_in_shift]
]);




val lang_in_fold = prove ( ``!t h r.  t IN language_of_marked (FOLDL (shift F) r h) <=> (h++t) IN language_of_marked (r)``,
  Induct_on `h`>| [
    REWRITE_TAC[FOLDL_shift_empty, APPEND],
    FULL_SIMP_TAC list_ss [lang_in_shift]
]);




(* Proof of acceptM MAlt Case. *)
val acceptM_Alt = prove( ``! w R R0. acceptM (MARK_REG (Alt R R0)) (w) <=> w IN language_of (Alt R R0)``,
 Induct_on `w`>|[
   REWRITE_TAC [acceptM_Empty_EQ],

   FULL_SIMP_TAC (list_ss) [lang_in_shift, lang_in_fold , final_in_lang, acceptM_def] >>
   REPEAT STRIP_TAC >> 
   FULL_SIMP_TAC (list_ss) [ UNMARK_REG_MARK, language_of_def] >>
     `!r. language_of_marked (MARK_REG (r)) = {}` by ( 
     Induct >> 
     REPEAT STRIP_TAC >>
     ASM_REWRITE_TAC [language_of_marked_def, MARK_REG_def, UNION_IDEMPOT, UNMARK_REG_MARK]>>
     ASM_SIMP_TAC (list_ss)  [ PULL_EXISTS, EXISTS_MEM, EVERY_MEM, PULL_EXISTS, EXTENSION]>> 
     SIMP_TAC (list_ss++PRED_SET_ss) [language_of_marked_def, MARK_REG_def]) >>
     FULL_SIMP_TAC (list_ss) [] 
]);




(* Proof of acceptM MSeq Case. *)
val acceptM_Seq = prove( ``! w R R0. acceptM (MARK_REG (Seq R R0)) (w) <=> w IN language_of (Seq R R0) ``,
 Induct_on `w` >|[
   REWRITE_TAC [acceptM_Empty_EQ],

   FULL_SIMP_TAC (list_ss) [lang_in_shift, lang_in_fold , lang_in_fold_empty, final_in_lang, 
   acceptM_def, UNMARK_REG_MARK] >>
   REPEAT STRIP_TAC >>
   `!r. language_of_marked (MARK_REG r) = {}` by (
   Induct >> 
   ASM_REWRITE_TAC [language_of_marked_def, MARK_REG_def, UNION_IDEMPOT, UNMARK_REG_MARK]>>
   ASM_SIMP_TAC (list_ss)  [LIST_TO_SET_APPEND, PULL_EXISTS, EXISTS_MEM, EVERY_MEM, 
   PULL_EXISTS, EXTENSION]>> 
   SIMP_TAC (list_ss++PRED_SET_ss) [] ) >>
   FULL_SIMP_TAC (list_ss) [] 
]);




(* Proof of acceptM MRep Case. *)
val acceptM_Rep = prove( ``! w R R0. acceptM (MARK_REG (Rep R)) (w) <=> w IN language_of (Rep R)``,
 Induct_on `w`  >|[
   REWRITE_TAC [acceptM_Empty_EQ],

   FULL_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [lang_in_shift, lang_in_fold , 
   lang_in_fold_empty, final_in_lang, acceptM_def, UNMARK_REG_MARK] >>
   ASM_REWRITE_TAC [language_of_def, language_of_marked_def]>>
   ASM_SIMP_TAC (list_ss++PRED_SET_ss)  [LIST_TO_SET_APPEND, PULL_EXISTS]>>
   STRIP_TAC >>
   `!r. language_of_marked (MARK_REG r) = {}` by (
   Induct >> 
   ASM_REWRITE_TAC [language_of_marked_def, MARK_REG_def, UNION_IDEMPOT, UNMARK_REG_MARK]>>
   ASM_SIMP_TAC (list_ss)  [LIST_TO_SET_APPEND, PULL_EXISTS, EXISTS_MEM, EVERY_MEM, PULL_EXISTS, EXTENSION]>> 
  SIMP_TAC (list_ss++PRED_SET_ss) [] ) >>
  FULL_SIMP_TAC (list_ss) [] 
]
);




(* Correctness proof of Marked Regular Expressions,a second Pheeeeewww *)
val ACCEPTM_LANG_EQ = prove (  `` !r w. acceptM (MARK_REG r) w  <=> w IN (language_of r) ``,
  Induct_on `r` >|[
    REWRITE_TAC [acceptM_Eps],
    REWRITE_TAC [acceptM_Sym],
    REWRITE_TAC [acceptM_Alt],
    REWRITE_TAC [acceptM_Seq],
    REWRITE_TAC [acceptM_Rep]
    ]
);





     (***********************************************************)
     (**               Cached regular expression               **)
     (***********************************************************)

(* Definition of Cached Marked Reg data type. First bool for empty, the sec. for final. *)
val CMReg =  Datatype `
CMReg = CMEps    
|CMSym bool 'a
|CMAlt bool bool CMReg CMReg
|CMSeq bool bool CMReg CMReg
|CMRep bool CMReg`;




(* Definition of the cached marked empty, it uses the new cached bool that represents
the empty regex. *)
val CMempty_def = Define `
(CMempty CMEps               = T) /\
(CMempty (CMSym _ _)         = F) /\
(CMempty (CMAlt emp _ _ _) = emp) /\
(CMempty (CMSeq emp _ _ _) = emp) /\
(CMempty (CMRep _ _) =         T) `;

(*
val test1  = EVAL``CMempty CMEps``;
val test2  = EVAL``CMempty (CMSym F a)``; 
val test3  = EVAL``CMempty (CMSym T a)``;
val test4  = EVAL``CMempty (CMAlt T T (CMSym T a) (CMEps))``;
val test5  = EVAL``CMempty (CMAlt F T (CMSym T a) (CMEps))``;
val test6  = EVAL``CMempty (CMSeq T F (CMSym T a) (CMEps))``;
val test7  = EVAL``CMempty (CMSeq F F (CMSym T a) (CMEps))``;
val test8  = EVAL``CMempty (CMRep T   (CMSym F b))``;
*)




(* Definition of the cached marked final. *)
val CMfinal_def = Define `
(CMfinal CMEps               = F) /\
(CMfinal (CMSym a   _)       = a) /\
(CMfinal (CMAlt _ fin _ _) = fin) /\
(CMfinal (CMSeq _ fin _ _) = fin) /\
(CMfinal (CMRep fin _)     = fin) `;

(*
val test1  = EVAL``CMfinal CMEps``;
val test2  = EVAL``CMfinal (CMSym F a)``; 
val test3  = EVAL``CMfinal (CMSym T a)``;
val test4  = EVAL``CMfinal (CMAlt T T (CMSym T a) (CMEps))``;
val test5  = EVAL``CMfinal (CMAlt F F (CMSym T a) (CMEps))``;
val test6  = EVAL``CMfinal (CMSeq T T (CMSym T a) (CMEps))``;
val test7  = EVAL``CMfinal (CMSeq F F (CMSym T a) (CMEps))``;
val test8  = EVAL``CMfinal (CMRep T (CMSym F b))``;
*)




(* Definition of the cached marked apply that represent the smart constructor in the paper
and will be used when converting the Marked to MCached reg and in the shifting. *)
val CMapply_def = Define `
(CMapply CMEps           =       CMEps) /\
(CMapply (CMSym a b)     = (CMSym a b)) /\
(CMapply (CMAlt _ _ p q) = 
        CMAlt (CMempty p \/ CMempty q)  (CMfinal p \/ CMfinal q)               (p)  (q) ) /\
(CMapply (CMSeq _ _ p q) = 
        CMSeq (CMempty p /\ CMempty q) ((CMfinal p /\ CMempty q) \/ CMfinal q) (p)  (q) ) /\
(CMapply (CMRep _ r) = CMRep (CMfinal r)  r )`;

(*
val test1  = EVAL``CMapply CMEps``;
val test2  = EVAL``CMapply (CMSym F a)``; 
val test3  = EVAL``CMapply (CMSym T a)``;
val test4  = EVAL``CMapply (CMAlt T T (CMSym T a) (CMEps))``;
val test5  = EVAL``CMapply (CMAlt F F (CMSym T a) (CMSym T a))``;
val test6  = EVAL``CMapply (CMSeq T T (CMSym T a) (CMSym F a))``;
val test7  = EVAL``CMapply (CMSeq F F (CMSym T a) (CMEps))``;
val test8  = EVAL``CMapply (CMRep T (CMSym F b))``;
*)




(* Definition of the caching a reg. *)
val CACHE_REG_def = Define `
(CACHE_REG    MEps     =  CMapply (CMEps)    ) /\
(CACHE_REG  (MSym a b) =  CMapply (CMSym a b)) /\
(CACHE_REG  (MAlt p q) =  CMapply (CMAlt F F (CACHE_REG p) (CACHE_REG q))) /\
(CACHE_REG  (MSeq p q) =  CMapply (CMSeq F F (CACHE_REG p) (CACHE_REG q))) /\
(CACHE_REG  (MRep r)   =  CMapply (CMRep F (CACHE_REG r)))`;

(*
val test1  = EVAL``CACHE_REG MEps``;
val test2  = EVAL``CACHE_REG (MSym F a)``; 
val test3  = EVAL``CACHE_REG (MAlt (MSym T a) (MEps))``;
val test3  = EVAL``CACHE_REG (MAlt (MSym F a) (MEps))``;
val test4  = EVAL``CACHE_REG (MAlt (MSym T a) (MSym T a))``;
val test5  = EVAL``CACHE_REG (MRep (MSym F b))``;
*)




(* Definition of the uncaching a reg. *)
val UNCACHE_REG_def = Define `
(UNCACHE_REG  CMEps           =  MEps     ) /\
(UNCACHE_REG  (CMSym a b)     =  MSym a b ) /\
(UNCACHE_REG  (CMAlt _ _ p q) =  MAlt (UNCACHE_REG p) (UNCACHE_REG q)) /\
(UNCACHE_REG  (CMSeq _ _ p q) =  MSeq (UNCACHE_REG p) (UNCACHE_REG q)) /\
(UNCACHE_REG  (CMRep _ r)     =  MRep (UNCACHE_REG r))`;

(*
val test1  = EVAL``UNCACHE_REG CMEps``;
val test2  = EVAL``UNCACHE_REG (CMSym F a)``; 
val test3  = EVAL``UNCACHE_REG (CMAlt T T (CMSym T a) (CMEps))``;
val test4  = EVAL``UNCACHE_REG (CMAlt F F (CMSym T a) (CMSym T a))``;
val test5  = EVAL``UNCACHE_REG (CMRep T (CMSym F b))``;
*)




(* Definition of the shifting a reg. *)
val CMshift_def = Define `
(CMshift _ CMEps _ = CMEps) /\
(CMshift m (CMSym _ x) c = CMSym (m /\ (x = c)) x) /\
(CMshift m (CMAlt _ _ p q) c = CMapply (CMAlt F F (CMshift m p c) (CMshift m q c))) /\
(CMshift m (CMSeq _ _ p q) c = CMapply (CMSeq F F (CMshift m p c) (CMshift ((m /\ CMempty p) \/ CMfinal p) q c))) /\
(CMshift m (CMRep _ r) c =   CMapply (CMRep F (CMshift (m \/ CMfinal r) r c)))`;

(*
val test1  = EVAL``CMshift T  CMEps []``;
val test2  = EVAL``CMshift T (CMSym T a) a``; 
val test3  = EVAL``CMshift T (CMRep T (CMSym T b)) b``;
val test4  = EVAL``CMshift F (CMRep T (CMSym T b)) a``;
val test5  = EVAL``CMshift T ((CMAlt F T (CMSym T a) (CMSym T b))) a``;
val test6  = EVAL``CMshift F (CACHE_REG(MRep (MAlt (MSym F a) (MSym F b)))) b``;
val test7  = EVAL``CMshift T ((CMSeq F T (CMSym T a) (CMSym T b))) b``;
val test8  = EVAL``CMshift F (CMSeq F T (CMEps) (CMEps)) []``;
*)




(* Definition of the accepting a cached marked reg. *)
val acceptCM_def = Define `
(acceptCM r []      = CMempty r  ) /\
(acceptCM r (c::cs) = CMfinal (FOLDL (CMshift F) ((CMshift T r c))  cs))`;

(*
val test1  = EVAL``acceptCM CMEps []``;
val test2  = EVAL``acceptCM (CMSym T a) [a]``; 
val test3  = EVAL``acceptCM (CMSym T a) [b;b;b]``;
val test4  = EVAL``acceptCM (CMSym F a) [b;b;b]``;
val test5  = EVAL``acceptCM (CMRep T (CMSym T b)) [b;b;b;v]``;
val test5  = EVAL``acceptCM (CMRep F (CMSym T b)) [b;b;b]``;
val test6  = EVAL``acceptCM (CMRep T (CMSym T b)) []``;
val test6  = EVAL``acceptCM (CMRep T (CACHE_REG (MSym T b))) []``;
val test7  = EVAL``acceptCM ((CMAlt F T (CMSym T a) (CMSym T b))) [a]``;
val test8  = EVAL``acceptCM (CACHE_REG(MRep (MAlt (MSym F a) (MSym F b)))) [a;a;b;a;b;a]``;
val test9  = EVAL``acceptCM ((CMSeq F T (CMSym T a) (CMSym T b))) [a;b]``;
val test9  = EVAL``acceptCM (CMSeq F T (CMEps) (CMEps)) []``;
*)




(* The empty of the marked reg is equavelent to the cached one. *)
val empty_CMempty = prove (``! r.  empty r = CMempty (CACHE_REG r)``,
 Induct >>
   EVAL_TAC >> 
   REWRITE_TAC[CACHE_REG_def, empty_def, CMempty_def, CMapply_def]>> 
   FULL_SIMP_TAC std_ss [] 
);




(* The final of the marked reg is equavelent to the cached one. *)
val final_CMfinal = prove (``! r.  final r = CMfinal (CACHE_REG r)``,
 Induct >>
   EVAL_TAC >> 
   REWRITE_TAC[CACHE_REG_def, final_def, CMfinal_def, CMapply_def, empty_def, 
   CMempty_def, empty_CMempty]>>
   FULL_SIMP_TAC std_ss [] 
);




(* The shift of the marked reg is equavelent to the cached one. *)
val shift_CMshift = prove ( ``! r m c.  CACHE_REG (shift m r c) = CMshift m (CACHE_REG r) c``,
 Induct >>
   EVAL_TAC >> 
   REWRITE_TAC[CACHE_REG_def, final_def, CMfinal_def, CMapply_def, empty_def, 
   CMempty_def, empty_CMempty, final_CMfinal, shift_def, CMshift_def]>> 
   FULL_SIMP_TAC std_ss [] 
);




(* Uncaching what is cached equals the marked reg. *)
val CACHE_UNCACHE = prove (``! r. UNCACHE_REG (CACHE_REG (r)) = r``,
 Induct >>    
   ASM_REWRITE_TAC[CACHE_REG_def, UNCACHE_REG_def, CMapply_def]
);




(* Sanity check for shift T. *)
val shift_cache = prove(``!r h. (CMshift T (CACHE_REG r) h) = CACHE_REG (shift T r h)``,
 SIMP_TAC bool_ss [CACHE_REG_def, shift_CMshift] 
);




(* Sanity check for shift F. *)
val shift_cache_F = prove( ``!r h. (CMshift F (CACHE_REG r) h) = CACHE_REG (shift F r h)``,
SIMP_TAC bool_ss [CACHE_REG_def, shift_CMshift] 
);




(* Sanity check for shift B. *)
val shift_cache_B = prove(``!r h B. (CMshift B (CACHE_REG r) h) = CACHE_REG (shift B r h)``,
SIMP_TAC bool_ss [CACHE_REG_def, shift_CMshift] 
);




(*because the eqavelance proof contains a forward proof, 
it was required to use the SUFF_TAC and prove some extra lemmas about it,
which are the following two lemmas*)
val inner_final_eq = prove( ``! h t r. (FOLDL (CMshift F) (CMshift T (CACHE_REG r) h) t) =
 CACHE_REG (FOLDL (shift F) (shift T r h) t) ==> 
            (CMfinal (FOLDL (CMshift F) (CMshift T (CACHE_REG r) h) t) <=>
            final (FOLDL (shift F) (shift T r h) t)) `` ,
 SIMP_TAC list_ss [final_CMfinal] 
);




val foldl_CMshift = prove(`` !t h r. FOLDL (CMshift F) (CMshift T (CACHE_REG r) h) t =
            CACHE_REG (FOLDL (shift F) (shift T r h) t)``,
 HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [FOLDL_SNOC, MAP_SNOC]  >>
 SIMP_TAC list_ss [shift_CMshift] 
);



(* The accept of the marked reg is equavelent to the cached one. *)
val acceptCM_acceptM = prove(``! r  w. acceptCM (CACHE_REG r) w = acceptM (r) w``,
 Cases_on `w` >|[
   EVAL_TAC >> 
   REWRITE_TAC [empty_CMempty] ,

   GEN_TAC >>
   FULL_SIMP_TAC list_ss [acceptCM_def, acceptM_def]  >>
   ASSUME_TAC inner_final_eq >>
   Q_TAC SUFF_TAC `!r. FOLDL (CMshift F) (CMshift T (CACHE_REG r) h) t =
            CACHE_REG (FOLDL (shift F) (shift T r h) t)` >|[
   FULL_SIMP_TAC list_ss [ final_CMfinal,REFL_CLAUSE,IMP_CLAUSES] ,
   REWRITE_TAC [foldl_CMshift]
   ]
]);



(* Correctness of cached regex. *)
val ACCEPTCM_LANG_EQ = prove(
  ``!r w. acceptCM (CACHE_REG (MARK_REG r)) w <=> w IN (language_of r)``,
 REWRITE_TAC [acceptCM_acceptM, ACCEPTM_LANG_EQ ]
);


val _ = export_theory();
