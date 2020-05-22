(*This is a performance test of each accept function with different combinations*)
use "build.sml";
open List;

exception UnMatch;



(******************************************************************
TEST1 : All combinations of a string
*******************************************************************)


fun append (x,[]) = x::[]
| append (x,l) = x::l

(*Let the val x be in all positions of a list l, keeping the list with the same order*)
fun different_pos (x,[]) = [[x]]
| different_pos (x,l) = (x::l)::(map (fn l' => append(hd l,l')) (different_pos (x,tl l)))

(* possible combination of a list, the combinations has the same length of the input*)
fun shuffle [] = [[]]
        | shuffle l = concat(map(fn l' => different_pos (hd l,l')) (shuffle (tl l)))

(* all possible combination of a list*)
fun all_combinations [] = [[]]
  | all_combinations l = shuffle(l)

(*membership*)
fun mem  (x, []) = false
|mem (x, (y::l)) = (x=y) orelse (mem (x, l));

(*Regex in the paper and a potential string*)
val reg_paper = Seq(Rep(Seq(Seq (Rep (Alt (Sym #"a",Sym #"b")), Sym #"c"),Seq (Rep (Alt (Sym #"a",Sym #"b")), Sym #"c"))), Rep (Alt (Sym #"a", Sym #"b"))) 
val char_list = all_combinations ( [ #"a", #"a", #"b",#"b",#"b", #"b",  #"c", #"c"]);
val str_list  = map String.implode (char_list);   (*macke charachters a string*)
val eval_list = map (regaccept.match reg_paper) str_list; 
(*      use "Performance_test.sml";         *)

val _ = print "Test Starts \n \n \n \n  "
(*Test with accept*)
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
val eval_mem =  if (mem (false,  eval_list)) then print ("FAILED for accept \n ") else print ("Test succeded for accept \n");
val eval_list = map (regaccept.match reg_paper) str_list; (*evaluate all string lists*)
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;
print (" \n \n \n \n \n ");


(*Test with acceptM*)
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
val eval_list = map (regacceptM.match reg_paper) str_list; (*evaluate all string lists*)
val eval_mem =  if (mem (false,  eval_list)) then print ("Test failed for acceptM \n ") else print ("Test succeded for acceptM \n ");
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;
print (" \n \n \n \n \n ");


(*Test with acceptCM*)
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
val eval_list = map (regacceptCM.match reg_paper) str_list; (*evaluate all string lists*)
val eval_mem =  if (mem (false,  eval_list)) then print ("Test failed for acceptCM \n ") else print ("Test succeded for acceptCM \n ");
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;
print (" \n \n \n \n \n ");


(*Test with regexpMatch*)
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
val eval_list = map (regBuiltIn.match reg_paper) str_list; (*evaluate all string lists*)
val eval_mem =  if (mem (false,  eval_list)) then print ("Test failed for regexpMatch \n ") else print ("Test succeded for regexpMatch \n");
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;
print (" \n \n \n \n \n ");













(******************************************************************
TEST2 : A non combination of a string test, just the string as it is
*******************************************************************)


val reg_paper = Seq(Rep(Seq(Seq (Rep (Alt (Sym #"a",Sym #"b")), Sym #"c"),Seq (Rep (Alt (Sym #"a",Sym #"b")), Sym #"c"))), Rep (Alt (Sym #"a", Sym #"b"))) ;

val char_list1 = "aaaccccccccccccbbbbb";

print (" \n \n \n \n \n ");
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
fun eval_single_string reg_paper char_list1 =
print (" ");
if ((regaccept.match reg_paper  char_list1) = true) then 
print "Test SUCCEDED for regaccept \n" else 
raise UnMatch;
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;



(*      use "Performance_test.sml";         *)


print (" \n \n \n \n \n ");
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
fun eval_single_string reg_paper char_list1 =
print (" ");
if ((regacceptM.match reg_paper  char_list1) = true) then 
print "Test SUCCEDED for regacceptM \n" else 
raise UnMatch;
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;





print (" \n \n \n \n \n ");
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
fun eval_single_string reg_paper char_list1 =
print (" ");
if ((regacceptCM.match reg_paper  char_list1) = true) then 
print "Test SUCCEDED for regacceptCM \n" else 
raise UnMatch;
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;



print (" \n \n \n \n \n ");
val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
fun eval_single_string reg_paper char_list1 =
print (" ");
if ((regBuiltIn.match reg_paper  char_list1) = true) then 
print "Test SUCCEDED for regexpMatch \n" else 
raise UnMatch;
val check_cpu =  Timer.checkCPUTimer start_cpu;
val check_real =  Timer.checkRealTimer start_real;
