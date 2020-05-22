structure reggenML :> reggenML =
struct
  nonfix acceptCM CMshift UNCACHE_REG CACHE_REG CMapply CMfinal CMempty
         acceptM UNMARK_REG MARK_REG shift final empty accept parts split
         CMRep CMSeq CMAlt CMSym CMEps MRep MSeq MAlt MSym MEps Rep Seq Alt
         Sym Eps * / div mod + - ^ @ <> > < >= <= := o before;
  
  open listML
  open pairML
  
  datatype 'a Reg
       = Eps
       | Sym of 'a
       | Alt of 'a Reg * 'a Reg
       | Seq of 'a Reg * 'a Reg
       | Rep of 'a Reg
  datatype 'a MReg
       = MEps
       | MSym of bool * 'a
       | MAlt of 'a MReg * 'a MReg
       | MSeq of 'a MReg * 'a MReg
       | MRep of 'a MReg
  datatype 'a CMReg
       = CMEps
       | CMSym of bool * 'a
       | CMAlt of bool * bool * 'a CMReg * 'a CMReg
       | CMSeq of bool * bool * 'a CMReg * 'a CMReg
       | CMRep of bool * 'a CMReg
  fun split [] = [([],[])]
    | split (c::cs) = ([],c::cs)::MAP (fn (s1,s2) => (c::s1,s2)) (split cs)
    
  fun parts [] = [[]]
    | parts [c] = [[[c]]]
    | parts (c::cs1::cs2) =
      FLAT (MAP (fn x => [[c]::x,(c::HD x)::TL x]) (parts (cs1::cs2)))
    
  fun accept Eps u = NULL u
    | accept (Sym(c)) u = (u = [c])
    | accept (Alt(p,q)) u = accept p u orelse accept q u
    | accept (Seq(p,q)) u =
      EXISTS (fn x => accept p (FST x) andalso accept q (SND x)) (split u)
    | accept (Rep(r)) u =
      EXISTS (fn ps => EVERY (fn u1 => accept r u1) ps) (parts u)
    
  fun empty MEps = true
    | empty (MSym(v0,v1)) = false
    | empty (MAlt(p,q)) = empty p orelse empty q
    | empty (MSeq(p,q)) = empty p andalso empty q
    | empty (MRep(v2)) = true
    
  fun final MEps = false
    | final (MSym(b,v0)) = b
    | final (MAlt(p,q)) = final p orelse final q
    | final (MSeq(p,q)) = final p andalso empty q orelse final q
    | final (MRep(r)) = final r
    
  fun shift v0 MEps v1 = MEps
    | shift m (MSym(v2,x)) c = MSym(m andalso (x = c),x)
    | shift m (MAlt(p,q)) c = MAlt(shift m p c,shift m q c)
    | shift m (MSeq(p,q)) c =
      MSeq(shift m p c,shift (m andalso empty p orelse final p) q c)
    | shift m (MRep(r)) c = MRep(shift (m orelse final r) r c)
    
  fun MARK_REG Eps = MEps
    | MARK_REG (Sym(c)) = MSym(false,c)
    | MARK_REG (Alt(p,q)) = MAlt(MARK_REG p,MARK_REG q)
    | MARK_REG (Seq(p,q)) = MSeq(MARK_REG p,MARK_REG q)
    | MARK_REG (Rep(r)) = MRep(MARK_REG r)
    
  fun UNMARK_REG MEps = Eps
    | UNMARK_REG (MSym(v0,c)) = Sym(c)
    | UNMARK_REG (MAlt(p,q)) = Alt(UNMARK_REG p,UNMARK_REG q)
    | UNMARK_REG (MSeq(p,q)) = Seq(UNMARK_REG p,UNMARK_REG q)
    | UNMARK_REG (MRep(r)) = Rep(UNMARK_REG r)
    
  fun acceptM r [] = empty r
    | acceptM r (c::cs) = final (FOLDL (shift false) (shift true r c) cs)
    
  fun CMempty CMEps = true
    | CMempty (CMSym(v0,v1)) = false
    | CMempty (CMAlt(emp,v2,v3,v4)) = emp
    | CMempty (CMSeq(emp,v5,v6,v7)) = emp
    | CMempty (CMRep(v8,v9)) = true
    
  fun CMfinal CMEps = false
    | CMfinal (CMSym(a,v0)) = a
    | CMfinal (CMAlt(v1,fin,v2,v3)) = fin
    | CMfinal (CMSeq(v4,fin,v5,v6)) = fin
    | CMfinal (CMRep(fin,v7)) = fin
    
  fun CMapply CMEps = CMEps
    | CMapply (CMSym(a,b)) = CMSym(a,b)
    | CMapply (CMAlt(v0,v1,p,q)) =
      CMAlt(CMempty p orelse CMempty q,CMfinal p orelse CMfinal q,p,q)
    | CMapply (CMSeq(v2,v3,p,q)) =
      CMSeq(CMempty p andalso CMempty q,
       CMfinal p andalso CMempty q orelse CMfinal q,p,q)
    | CMapply (CMRep(v4,r)) = CMRep(CMfinal r,r)
    
  fun CACHE_REG MEps = CMapply CMEps
    | CACHE_REG (MSym(a,b)) = CMapply (CMSym(a,b))
    | CACHE_REG (MAlt(p,q)) =
      CMapply (CMAlt(false,false,CACHE_REG p,CACHE_REG q))
    | CACHE_REG (MSeq(p,q)) =
      CMapply (CMSeq(false,false,CACHE_REG p,CACHE_REG q))
    | CACHE_REG (MRep(r)) = CMapply (CMRep(false,CACHE_REG r))
    
  fun UNCACHE_REG CMEps = MEps
    | UNCACHE_REG (CMSym(a,b)) = MSym(a,b)
    | UNCACHE_REG (CMAlt(v0,v1,p,q)) = MAlt(UNCACHE_REG p,UNCACHE_REG q)
    | UNCACHE_REG (CMSeq(v2,v3,p,q)) = MSeq(UNCACHE_REG p,UNCACHE_REG q)
    | UNCACHE_REG (CMRep(v4,r)) = MRep(UNCACHE_REG r)
    
  fun CMshift v0 CMEps v1 = CMEps
    | CMshift m (CMSym(v2,x)) c = CMSym(m andalso (x = c),x)
    | CMshift m (CMAlt(v3,v4,p,q)) c =
      CMapply (CMAlt(false,false,CMshift m p c,CMshift m q c))
    | CMshift m (CMSeq(v5,v6,p,q)) c =
      CMapply
        (CMSeq(false,false,CMshift m p c,
         CMshift (m andalso CMempty p orelse CMfinal p) q c))
    | CMshift m (CMRep(v7,r)) c =
      CMapply (CMRep(false,CMshift (m orelse CMfinal r) r c))
    
  fun acceptCM r [] = CMempty r
    | acceptCM r (c::cs) =
      CMfinal (FOLDL (CMshift false) (CMshift true r c) cs)
    
end
