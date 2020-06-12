(*open HolKernel Parse boolLib bossLib pred_setLib ;*)
open reggenML;
open regexpMatch;

structure regLib :> regLib = 
struct

  datatype rexp =
      Epsilon            (* empty *)
    | Symb of char       (* single char *)
    | Sum of rexp * rexp (* choice *)
    | Dot of rexp * rexp (* sequence *)
    | Star of rexp       (* Kleene star *)


fun interface_to_BI r1 =
    case r1 of
      Epsilon          => regexpMatch.Epsilon
    | Symb c          => regexpMatch.Symbs (pred_to_set (fn x => x = c))
    | Sum (p, q)    => regexpMatch.Sum (interface_to_BI p, interface_to_BI q)
    | Dot (p, q)     => regexpMatch.Dot (interface_to_BI p, interface_to_BI q) 
    | Star r1      => regexpMatch.Star (interface_to_BI r1)

fun interface_to_IMPL Epsilon          = reggenML.Eps
 | interface_to_IMPL (Symb c)          = reggenML.Sym c
    | interface_to_IMPL (Sum (p, q))    = reggenML.Alt (interface_to_IMPL  p, interface_to_IMPL  q)
    | interface_to_IMPL (Dot (p, q))     = reggenML.Seq (interface_to_IMPL  p, interface_to_IMPL  q) 
    | interface_to_IMPL (Star r)      = reggenML.Rep (interface_to_IMPL  r)


structure BuiltInMatch =
struct
  fun match ((r1 : rexp), (str:string)) = regexpMatch.match (interface_to_BI r1) str;
end


structure simpleMatch =
struct
  fun match ((r1 : rexp), (str:string)) = reggenML.accept (interface_to_IMPL r1) (explode str);
end

structure markedMatch =
struct
  fun match ((r1 : rexp), (str:string)) = reggenML.acceptM ( MARK_REG (interface_to_IMPL r1)) (explode str);
end

structure cachedMarkedMatch =
struct
  fun match ((r1 : rexp), (str:string)) = reggenML.acceptCM ( CACHE_REG(MARK_REG(interface_to_IMPL r1))) (explode str);
end

end


(*)

  fun r2r r =
    case r of
      Epsilon            => regexpMatch.Epsilon
    | Symb c           => regexpMatch.Symbs (pred_to_set (fn x => x = c))
    | Sum (p, q)      => regexpMatch.Sum (r2r p, r2r q)
    | Dot (p, q)    => regexpMatch.Dot (r2r p, r2r q) 
    | Star r       => regexpMatch.Star (r2r r)





structure regacceptM :> regLib = 
struct
  fun match r1 (str:string) = reggenML.acceptM (reggenML.MARK_REG r1) (explode str);
end

structure regacceptCM :> regLib = 
struct
  fun match r1 (str:string) = reggenML.acceptCM (reggenML.CACHE_REG (reggenML.MARK_REG r1)) (explode str);
end



*)

