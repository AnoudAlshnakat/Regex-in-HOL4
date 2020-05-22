(*open HolKernel Parse boolLib bossLib pred_setLib ;*)
open reggenML;
open regexpMatch;

structure regBuiltIn :> regLib = 
struct
  fun sysRegtoOurs st_r =
    case st_r of
      reggenML.Eps          => regexpMatch.Epsilon
    | reggenML.Sym c          => regexpMatch.Symbs (pred_to_set (fn x => x = c))
    | reggenML.Alt (p, q)    => regexpMatch.Sum (sysRegtoOurs p, sysRegtoOurs q)
    | reggenML.Seq (p, q)     => regexpMatch.Dot (sysRegtoOurs p, sysRegtoOurs q) 
    | reggenML.Rep st_r      => regexpMatch.Star (sysRegtoOurs st_r)

  fun match st_r (str:string) = regexpMatch.match (sysRegtoOurs st_r) str;
end

structure regaccept :> regLib =
struct
  fun match st_r (str:string) = reggenML.accept st_r (explode str);
end

structure regacceptM :> regLib = 
struct
  fun match st_r (str:string) = reggenML.acceptM (reggenML.MARK_REG st_r) (explode str);
end

structure regacceptCM :> regLib = 
struct
  fun match st_r (str:string) = reggenML.acceptCM (reggenML.CACHE_REG (reggenML.MARK_REG st_r)) (explode str);
end

