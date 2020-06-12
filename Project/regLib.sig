(*open HolKernel Parse boolLib bossLib pred_setLib ; *)
signature regLib =
sig
  datatype rexp =
      Epsilon            (* empty *)
    | Symb of char       (* single char *)
    | Sum of rexp * rexp (* choice *)
    | Dot of rexp * rexp (* sequence *)
    | Star of rexp       (* Kleene star *)

  structure BuiltInMatch : sig
    val match : (rexp * string) -> bool
  end


  structure simpleMatch : sig
    val match : (rexp * string)  -> bool
  end



  structure markedMatch : sig
    val match : (rexp * string) -> bool
  end

  structure cachedMarkedMatch : sig
    val match : (rexp * string) -> bool
  end


end


