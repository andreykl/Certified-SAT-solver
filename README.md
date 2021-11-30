# Certified-SAT-solver

This is a verified (certified) boolean formula solver (the SAT solver).
The formula consists of literals, negations, conjunctions, and disjunctions.
This algorithm implements full exhaustive search using list of all possible
valuations for the formula.

This is NOT a backtracking algorithm described in wikipedia.
This is just another one. It looks to me like it is not easy thing
to implement unit propagation and pure literal elimination for this
algorithm. 

The idea of the algorithm:
    1. Basing on formula variable list build a list of all possible 
       valuations for the formula.
    2. Take this valuations one by one and check the formula using each
       valuation. If we face the valuation on which the formula evaluates to
       true, this means we have what we need. Otherwise, when after checking 
       all the possible valuations we haven't found the valuation on which
       the formula evaluates to true, this means that for all possible 
       valuations formula evaluates to false.
	   
For more information about the algorithm see comments in code.

This task is inspired by Adam Chlipala's tasks for the 
"Certified Programming with Dependent Types" (CPDT) book, 
http://adam.chlipala.net/cpdt/ .

The aim of this work is to show programming skills and have a bit fun.
