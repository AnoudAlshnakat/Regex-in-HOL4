signature reggenML =
sig
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
  val split : 'a list -> ('a list * 'a list) list
  val parts : 'a list -> 'a list list list
  val accept : ''a Reg -> ''a list -> bool
  val empty : 'a MReg -> bool
  val final : 'a MReg -> bool
  val shift : bool -> ''a MReg -> ''a -> ''a MReg
  val MARK_REG : 'a Reg -> 'a MReg
  val UNMARK_REG : 'a MReg -> 'a Reg
  val acceptM : ''a MReg -> ''a list -> bool
  val CMempty : 'a CMReg -> bool
  val CMfinal : 'a CMReg -> bool
  val CMapply : 'a CMReg -> 'a CMReg
  val CACHE_REG : 'a MReg -> 'a CMReg
  val UNCACHE_REG : 'a CMReg -> 'a MReg
  val CMshift : bool -> ''a CMReg -> ''a -> ''a CMReg
  val acceptCM : ''a CMReg -> ''a list -> bool
end
