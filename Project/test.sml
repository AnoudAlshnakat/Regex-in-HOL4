use "build.sml";
open List;


val timer = Timer.totalCPUTimer ();
val timer2 = Timer.totalRealTimer ();

val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();

val _ = print "Test Starts \n \n \n \n  "

fun check_all a b = 
if ((regaccept.match a b) andalso
   (regacceptM.match a b) andalso
   (regacceptCM.match a b) andalso
   (regBuiltIn.match a b) ) 
then true
 else 
 false 

(*True Cases*)
val str0 = " "
val str1 = ""
val str2 = "F" 
val str3 = "Fu" 
val str4 = "zzzzzz" 
val str5 = "Fuzzy" 
val str6 = "FuzzyFuzzy" 
val str7 = "FuzzyWuzzy" 
val str8 = "uzzy" 

(*Eps*)
val reg1 = Eps

(*Basic Syms*)
val reg2 = Sym #"F"
val reg3 = Sym #"u"
val reg4 = Sym #"z"
val reg5 = Sym #"y"
val reg6 = Sym #"W"

(*Combinations*)
val reg7 = Seq (reg2, reg3) (* Fu*)
val reg8 = Rep (reg4)      (* zzzz *)
val reg9 = Seq (reg7, reg8) (* Fuzzzz *)
val reg10 = Seq (reg9, reg5) (*Fuzzy*) 
val reg11 = Seq(Seq (reg3, reg8), reg5) (*uzzy*)
val reg12 = Alt(reg2, reg6) (*F|W*)
val reg13 = Rep (Seq (reg12, reg11)) (*(F|W)uzzy*)


(*val start_cpu = Timer.startCPUTimer () ;*)
(*val start_real = Timer.startCPUTimer () ; *)

(*tests for accept acceptM acceptCM*)
val test1= check_all reg1 str1; (*Eps ""*)
val test2= check_all reg2 str2; (*F "F"*)
val test3= check_all reg7 str3; (*Fu "Fu"*)
val test4= check_all reg8 str4; (*zzzz *)
val test5= check_all reg10 str5;
val test6= check_all reg8 str1;
val test7= check_all reg8 str1;
val test8= check_all reg11 str8;
val test9= check_all (Rep reg10) str6;
val test10= check_all reg13 str6;
val test11= check_all reg13 str7;

(*type timer = Timer.real_timer * Timer.cpu_timer;*)

(*val check_cpu =  Timer.checkCPUTimer start_cpu; *)
(*val total_cpu =  Timer.totalCPUTimer ();*)

(*for CPU*)
val t1 = Timer.checkCPUTimer timer;
val check_cpu =  Timer.checkCPUTimer start_cpu;


(*for real time*)
val t2 = Timer.checkRealTimer timer2;
val check_real =  Timer.checkRealTimer start_real;



