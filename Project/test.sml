
open regLib;
open List;
open Time;

(* definitions of the reg, string*)
exception UnMatch;
val reg_paper = Dot(Star(Dot(Dot (Star (Sum (Symb #"a",Symb #"b")), Symb #"c"),Dot (Star (Sum (Symb #"a",Symb #"b")), Symb #"c"))), Star (Sum (Symb #"a", Symb #"b"))) ;
val charss = "aabbccaabbccaabbccaabbccaabbccaabbccaabbccaabbcc";


(*function to print out the time*)
fun time_print ({usr, sys}) rea =
let 
fun format t = Time.toString t;
in
   print("Test succeeded with the times ==>  User: " ^ format usr ^
		"  System: " ^ format sys ^ 
		"  Real: " ^ format rea ^ "\n")
end


val _ = print "Test Starts \n \n \n \n  ";

val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
if ((BuiltInMatch.match (reg_paper ,charss)) = true) then 
(time_print (Timer.checkCPUTimer start_cpu) (Timer.checkRealTimer start_real)) else 
raise UnMatch;
print (" \n \n ");

val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
if ((simpleMatch.match (reg_paper ,charss)) = true) then 
(time_print (Timer.checkCPUTimer start_cpu) (Timer.checkRealTimer start_real)) else 
raise UnMatch;
print (" \n \n ");

val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
if ((markedMatch.match (reg_paper ,charss)) = true) then 
(time_print (Timer.checkCPUTimer start_cpu) (Timer.checkRealTimer start_real)) else 
raise UnMatch;
print (" \n \n ");

val start_cpu = Timer.startCPUTimer () ;
val start_real =Timer.startRealTimer ();
if ((cachedMarkedMatch.match (reg_paper ,charss)) = true) then 
(time_print (Timer.checkCPUTimer start_cpu) (Timer.checkRealTimer start_real)) else 
raise UnMatch;
print (" \n \n ");



val _ = print "Test ends \n \n \n \n  "

