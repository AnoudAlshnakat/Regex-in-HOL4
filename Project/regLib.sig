(*open HolKernel Parse boolLib bossLib pred_setLib ; *)
signature regLib =
sig
   (*The interface has only a function definition that will be used by 4 instances of structs*)
  val match: char reggenML.Reg -> string -> bool
 
end
