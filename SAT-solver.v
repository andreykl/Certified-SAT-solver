(*
This is a verified (certified) boolean formula solver (the SAT solver).
The formula consists of literals, negations, conjunctions, and disjunctions.
This algorithm implements full exhaustive search using list of all possible
valuations for the formula.

This is NOT a backtracking algorithm described on wikipedia.
This is just another one. It looks to me like it is not easy thing
to implement unit propagation and pure literal elimination for this
algorithm. 

The idea of the algorithm:
    1. Basing on formula variable list build a list of all possible 
       valuations for the formula.
    2. Take this valuations one by one and check the formula using each
       valuation. If we face the valuation on which the formula evaluates to
       true, this means we have what we need. Otherwise, when after the 
       checking all possible valuations we haven't found the valuation on which
       the formula evaluates to true, this means that for all possible 
       valuations formula evaluates to false.

This task is inspired by Adam Chlipala's tasks for the 
"Certified Programming with Dependent Types" (CPDT) book, 
http://adam.chlipala.net/cpdt/ .

The aim of this work is to show programming skills and have a bit fun.
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Set Asymmetric Patterns.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Our variables are encoded as natural numbers. *)
Definition var := nat.

(* Boolean formula. *)
Inductive formula : Set :=
  | Flit of var                  (* literal *)
  | Fneg of formula              (* negation of the formula *)
  | Fcon of formula & formula    (* conjunction of two formulas *)
  | Fdis of formula & formula.   (* disjunction of two formulas *)

(* Valuation is a map from variable to bool. *)
Definition valuation : Set := var -> bool.

(* Evaluates the formula. *)
Fixpoint formulaDenote (truth : valuation) (f : formula) : bool :=
  match f with
  | Flit var => truth var
  | Fneg f' => ~~ (formulaDenote truth f')
  | Fcon f1 f2 => formulaDenote truth f1 && formulaDenote truth f2
  | Fdis f1 f2 => formulaDenote truth f1 || formulaDenote truth f2
  end.

(* Add variable with value to the valuation. *)
Definition add_val (x : var) (value : bool) (vl : valuation) : valuation :=
  fun v => if v == x then value else vl v.

(* Notation from Software Foundations book (by Pierce at al.) *)
Notation "x '!->' v ';' vl" := (add_val x v vl)
                                 (at level 100, v at next level,
                                  right associativity).

Section Maybe.
  (* First we build simple version using the maybe type *)
  (* as it is shown in the CPDT book. *)

  (* The `maybe` type and notation from CPDT. *)
  Inductive maybe (A : Set) (P : A -> Prop) : Set := Unknown | Found a of P a.                    
  
  Notation "{{ x | P }}" := (@maybe _ (fun x => P)).
  Notation "??" := (Unknown _).
  Notation "[| x |]" := (@Found _ _ x _).

  (* Adding one variable to given valuation list. *)
  (* Adding both values (`true` and `false`) for variable `x` to *)
  (* both copies of head and repeat for tail. *)
  Fixpoint add_var' (x : var) (vals : list valuation) : list valuation :=
    match vals with
    | [:: ] => [:: ]
    | vl :: vls => [::  x !-> true; vl, x !-> false; vl & add_var' x vls]
     end.

  (* Building list of all possible valuations for given variable list. *)
  (* We start from `[ (fun _ => false) ]` and then add each variable *)
  (* to the list one by one using `add_var`. *)
  Fixpoint buildValuations' (vars : list var) : list valuation :=
    match vars with
    | [:: ] => [:: xpred0 ]
    | v :: vs => add_var' v (buildValuations' vs)
    end.

  (* Try to find a valuation on which given formula evaluates to `true`. *)
  (* Just go through valuation list and try each valuation *)
  (* using `formulaDenote`. *)
  Definition solveFormula' f :
    forall (vals : list valuation), {{vl | formulaDenote vl f}}.
    refine(fix F vals : {{vl | formulaDenote vl f}} :=
             if vals is vl' :: vals'
             then
               _
             else ??
          ).
    case H: (formulaDenote vl' f).
      by apply: [| vl' |].
      by apply: (F vals').
  Defined.
End Maybe.

(* ************************************************************************* *)
(*                                                                           *)
(* Below we define valuation equivalence under a given variable list and     *)
(* several lemmas for it.                                                    *)
(* We are interested in equivalence of two valuations for a given formula f, *)
(* so, we consider two valuations as equivalent (for the formula) when they  *)
(* both have the same assigments for all formula'sariables.                  *)
(*                                                                           *)
(* ************************************************************************* *)

(* Predicates for working with valuations, similar to mathcomp library's. *)
Notation xpredEq := (fun (p1 p2 : pred _) x => p1 x == p2 x).
Notation xpredNeq := (fun (p1 p2 : pred _) x => p1 x != p2 x).
Definition predEq :=
  fun (T : Type) (p1 p2 : pred T) => [pred x | xpredEq p1 p2 x].
Definition predNeq :=
  fun (T : Type) (p1 p2 : pred T) => [pred x | xpredNeq p1 p2 x].

Search "symmetry".

(* Symmetry for an equality predicate. *)
Lemma predEq_sym (T : eqType) (p1 p2 : pred T) : predEq p1 p2 =1 predEq p2 p1.
    by move => x /=; rewrite eq_sym.
Defined.
  
(* Valuation equivalence under given variable list itself. *)
Definition eqv (vrs : list var) (vl vl' : var -> bool) :=
  all (predEq vl vl') vrs.

(* Useful notation similar to what mathcomp library has. *)
Notation "vl '==(' vrs ')' vl'" := (eqv vrs vl vl') (at level 50).

(* Valuation equivalence reflexivity. *)
Lemma eqv_refl vrs : reflexive (eqv vrs).
  rewrite /reflexive => vl; apply/allP => x0 H; apply: eq_refl.
Defined.

(* If two valuations are equivalent under a variable list then *)
(* they return the same value for any variable in the list. *)
Lemma eqv_in vrs vl vl' v : vl ==(vrs) vl' -> v \in vrs -> vl v == vl' v.
    by move/allP => /(_ v) H /H.
Defined.

(* Valuation equivalence symmetry. *)
Lemma eqv_sym vrs vl vl' : (vl ==(vrs) vl') = (vl' ==(vrs) vl).
    by rewrite /eqv;
       under eq_all => x do rewrite predEq_sym.
Defined.

(* Valuation equivalence symmetry. *)
(* JFF, proof with induction. *)
Lemma eqv_sym' vrs vl vl' : (vl ==(vrs) vl') = (vl' ==(vrs) vl).
    by elim: vrs => //= v vrs ->; rewrite eq_sym.
Defined.

(* Valuation equivalence transitivity. *)
Lemma eqv_trans vrs : transitive (eqv vrs).
  rewrite /transitive => vl2 vl1 vl3 /allP H12 /allP H23; apply/allP => x H.
  by move: (H12 x H) (H23 x H) => /eq_op_trans H1 /H1.
Defined.

(* Include - are all variables of one sequence (`vrs'`) also *)
(* members of another (`vrs`)? (So, vrs is 'bigger' then vrs'). *)
Definition incl (T : eqType) (vrs' vrs : seq T) := all (mem vrs) vrs'.

(* If two valuations are equivalent under a variable list `vrs` then *)
(* they are also equivalent under any variable list included to `vrs`. *)
Lemma eqv_incl vrs vrs' vl vl' :
  incl vrs' vrs -> vl ==(vrs) vl' -> vl ==(vrs') vl'.
  move => /allP Hincl /allP Heqv.
  by apply/allP => x /Hincl /Heqv.
Defined.

(* When we have `undup (vrs ++ vrs')` *)
(* then we also have both includes below: *)
(* `incl vrs (undup (vrs ++ vrs'))`  *)
(* `incl vrs' (undup (vrs ++ vrs'))`. *)
Lemma incl_undup_cat (T : eqType) (vrs vrs' : seq T) :
  incl vrs (undup (vrs ++ vrs')) /\ incl vrs' (undup (vrs ++ vrs')).
  rewrite /incl; split;
    by apply/allP => t; rewrite /= mem_undup mem_cat => -> //; apply/orbT.
Defined.

(* Check if valuation is in list using valuation equivalence under *)
(* variable list. *)
Definition has_val (vrs : seq var) (val : valuation) (vls : list valuation) :=
  has (fun val' => val ==(vrs) val') vls.

(* Notation similar to mathcomp's *)
Notation "vl '\in(' vrs ')' vls" := (has_val vrs vl vls) (at level 30).
Notation "vl '\notin(' vrs ')' vls" := (~~has_val vrs vl vls) (at level 30).

(* Valuation list is complete under given variable list when *)
(* for any given valuation there is an equivalent  valuation *)
(* in the valuation list *)
Definition valuation_list_complete (vrs : seq var) (vals : seq valuation) :=
  forall (vl : valuation), vl \in(vrs) vals.

(* Notation for list completeness under variable list. *)
Notation "'\complete(' vrs ')' vls" :=
  (valuation_list_complete vrs vls) (at level 50).

(* When valuation list is complete and formula `f` evaluates to some *)
(* value `b` on all valuations from the list, this means that formula `f` *)
(* evaluates to value `b` on all valuations. *)
(* Just a direct consequence from the completeness definition given above. *)
Lemma list_complete__no_more_valuations f vrs vls :
  \complete(vrs) vls ->
  forall b, (forall vl, vl \in(vrs) vls -> formulaDenote vl f == b) ->
       forall vl, formulaDenote vl f == b.
  rewrite /valuation_list_complete => H1 b H2 vl.
  by move: (H1 vl) => /H2.
Defined.

(* Specialization of lemma above to boolean `false` due to some problems *)
(* arose when rewriting general lemma. *)
Lemma list_complete__no_more_valuations_false f vrs vls:
  \complete(vrs) vls ->
  (forall vl, vl \in(vrs) vls -> ~~ formulaDenote vl f) ->
  forall vl, ~~ formulaDenote vl f.
  move => lc H vl.
  rewrite -eqbF_neg;
    apply: (@list_complete__no_more_valuations f vrs vls lc _) => // vl0 H1.
  move: (H vl0 H1); by rewrite eqbF_neg.
Defined.

(* We also need three lemmas about `add_val`. *)
(* (Two of them just like in Software Foundations, keyword is `t_update`) *)

(* We have the same value for variable which we have just added to valuation *)
Lemma add_val_eq vl x v : (x !-> v; vl) x = v.
  by rewrite /add_val eq_refl.
Defined.

(* When we add a new variable to valuation, then value of the old variable *)
(* is the same as before adding the new one. *)
Lemma add_val_neq vl x x' v : x' != x -> (x !-> v; vl) x' = vl x'.
  by rewrite /add_val => /negbTE ->.
Defined.

(* When we add a new variable to valuation and this new variable is not in *)
(* given variable list, then resulting valuation equals under variable list *)
(* to initial valuation. *) 
Lemma add_val_notin_eqv vrs vl x v :
  x \notin vrs ->
  vl ==(vrs) (x !-> v; vl).
  elim: vrs => //= x' vrs' IH; rewrite in_cons.
  case E: (x == x') => //= /IH ->; rewrite add_val_neq;
    first by rewrite eq_refl.
  by move: E; rewrite eq_sym => ->.
Defined.

(* ****************************************************************** *)
(*                                                                    *)
(* Now after we have built a 'skeleton' version of `solveFormula`,    *)
(* and some theory about valuations, valuation equality, and          *)
(* and valuation lists, we are ready to build 'certified' version     *)
(* of solveFormula, so, the one with type                             *)
(*       `{vl | formulaDenote vl f = true} +                          *)
(*        {forall vl, formulaDenote vl f = false}`                    *)
(*                                                                    *)
(* ***   The main idea of certified algorithm.   ***                  *)
(*                                                                    *)
(* We search for valuation on which formula evaluates to true,        *)
(* otherwise, if we are not able to find such valuation, this means   *)
(* that on all possible valuations formula returns false.             *)
(*                                                                    *)
(* When we have the complete list of valuations, we can show that     *)
(* either we have such valuation in the list, or there is no such     *)
(* valuations at all (see lemma `list_complete__no_more_valuations`). *)
(*                                                                    *)
(* So, what we need to do is essentially to build complete list of    *)
(* valuations for the formula (means for the formula variables,       *)
(* see lemma `vals_eqv__f_eq` below) and check if there is valuation  *)
(* with required properties in the list.                              *)
(* ****************************************************************** *)

(* ****************************************************************** *)
(*                                                                    *)
(* The first step of certified algorithm: building the complete       *)
(* valuation list for given list of (formula) variables.              *)
(*                                                                    *)
(* ****************************************************************** *)

(* Useful notation from CPDT *)
Notation "[ x ]" := (@exist _ _ x _).
Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

(* Add one variable to complete list.                               *)
(* When we add one variable which is not in `vrs`, and `vls`        *)
(* is complete under `vrs` then we have `vls1` which is complete    *)
(* under `v::vrs`.                                                  *)
Definition add_var v vrs vls (prf : v \notin vrs) :
  {vls1 | forall vl, vl \in(vrs) vls -> vl \in(v::vrs) vls1}.
  refine(
      let fix F vls' : {vls1' | forall vl', vl' \in(vrs) vls' -> vl' \in(v::vrs) vls1'} :=
          match vls' with
          | [:: ] => [ [:: ] ]
          | vl'' :: vls'' =>
            let: [ vls1'' ] := F vls''
             in  [ [::  v !-> true; vl'', v !-> false; vl'' & vls1''] ]
          end
      in F vls
    ); first by [].
  move => vl'; move: (i vl') => {i} IH /=.
  case E: (vl' ==(vrs) vl'') => /=;
    last by move /IH ->; rewrite !orbT.
  rewrite !add_val_eq !(eqv_trans E) //;
    [ | by apply: add_val_notin_eqv .. ];
    by case : (vl' v).
Defined.

(* We just add variables one by one using `add_var` to list complete *)
(* list. The first list is complete under empty variable list *)
(* (any list is ok). Then `add_var` does its job. *)
Definition buildValuations vrs : uniq vrs -> {vls | forall vl, vl \in(vrs) vls}.
  refine (let fix F vrs : uniq vrs -> {vls | forall vl, vl \in(vrs) vls} :=
            match vrs with
            | [:: ] => fun _ => [ [:: xpred0] ]
            | v' :: vrs' =>
              fun Hu =>
                let: [ vls' ] := F vrs' _ in
                let: [ vls1'] := @add_var v' vrs' vls' _ in
                [ vls1' ]
            end
          in F vrs); first by []; move: Hu => /= /andP [] //.
  move => Hnin Hu vl.
  by move: (i vl) => /i0.
Defined.

(* ************************************************************** *)
(*                                                                *)
(* Now we need relate formula and its variable list               *)
(*                                                                *)
(* ************************************************************** *)

(* Build list of all formula variables for the given formula f. *)
Fixpoint fvars (f : formula) : seq var :=
  match f with
  | Flit x => [:: x]
   | Fneg f' => fvars f'
  | Fcon f1 f2 | Fdis f1 f2 => undup (fvars f1 ++ fvars f2)
  end.

(* Relation which exresses that given list of variables contains all *)
(* variables of the given formula. *)
Inductive vs : formula -> seq var -> Set :=
| VsLit x :
    vs (Flit x) [::x]
| VsNeg f xs :
    vs f xs -> vs (Fneg f) xs
| VsCon f1 xs1 f2 xs2 :
    vs f1 xs1 ->
    vs f2 xs2 ->
    vs (Fcon f1 f2) (undup (xs1 ++ xs2))
| VsDis f1 xs1 f2 xs2 :
    vs f1 xs1 ->
    vs f2 xs2 ->
    vs (Fdis f1 f2) (undup (xs1 ++ xs2)).

(* Proof that `fvars` gives all formula variables. *)
Definition vars_vs : forall f, vs f (fvars f).
  elim; by constructor.
Defined.

(* Proof that `fvars` is uniq *)
Lemma vars_uniq f : uniq (fvars f).
  elim: f => //= f1 H1 f2; by rewrite undup_uniq.
Defined.

(* Formula evaluates to the same value on valuations which *)
(* are equivalent under formula variable list. *)
Lemma vals_eqv__f_eq f vrs: vs f vrs ->
  forall vl' vl,
    vl ==(vrs) vl' ->
    formulaDenote vl f = formulaDenote vl' f. 
  elim => /=
           [ x vl' vl /andP [] /eqP //
           | f0 vrs0 H IH vl vl'
           | f0 vrs0 f1 vrs1 H0 IH0 H1 IH1 vl' vl
           | f0 vrs0 f1 vrs1 H0 IH0 H1 IH1 vl' vl
           ];
    [ by move/IH => ->
    | move: (incl_undup_cat vrs0 vrs1) =>
        [] /eqv_incl Hi0 /eqv_incl Hi1 H;
        by move: (Hi0 _ _ H) (Hi1 _ _ H) => /IH0 -> /IH1 -> .. ].
Defined.

(* Solving the formula. The idea is essentially the same as for *)
(* `solveFormula'` above: we just go through the list of valuations *)
(* and check the formula on valuation valuation. *)
(* The only thing now is that we show that we have checked every *)
(* valuation from the given valuation list. *)
Definition solveFormula1 f (vrs : seq var) (prf : vs f vrs):
  forall (vals : list valuation),
    {vl | formulaDenote vl f} +
    {forall vl, vl \in(vrs) vals -> ~~formulaDenote vl f}.
  refine(fix F vals : {vl | formulaDenote vl f} +
                      {forall vl, (vl \in(vrs) vals) -> ~~formulaDenote vl f} :=
           if vals is vl' :: vals'
           then
             _
           else !!
        ); first by [].
  case H: (formulaDenote vl' f); first by apply: [|| vl' ||].
  case: (F vals'); first by left.
  move => H1; right => vl /= /orP []; last by apply/H1.
  by move => /(vals_eqv__f_eq prf) ->; rewrite H.
Defined.

(* If our list of valuations is complete and we havent found valuation *)
(* in this list, this means that there is no such valuation at all *)
(* (The case when we have found such valuation is easy one) *)
Definition solveFormula0
        f (vrs : seq var)
        (prf : vs f vrs)
        (vals : list valuation)
        (vlc : \complete(vrs) vals)
  :
  {truth | formulaDenote truth f} + {forall truth, ~~formulaDenote truth f}.
  case: (@solveFormula1 f vrs prf vals).
  move => [] truth H; by apply: [|| truth ||].
  move /(list_complete__no_more_valuations_false vlc); by right.
Defined.

(* Certified `solveFormula` function. *)
(* Take the complete valuation list and try to find valuation with *)
(* needed properties in it. *)
Definition solveFormula f :
  {truth | formulaDenote truth f} + {forall truth, ~~formulaDenote truth f}.
  refine(
      let: [ vls ] := buildValuations (vars_uniq f)
      in solveFormula0 (vars_vs f) _).
  apply: i.
Defined.

Eval compute in solveFormula (Fcon (Flit 1) (Fneg (Flit 1))).
Eval compute in solveFormula (Fdis (Flit 1) (Fneg (Flit 1))).
