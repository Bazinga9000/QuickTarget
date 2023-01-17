From QuickChick Require Import Show Checker State Classes.
From QuickChick Require Import Producer Generators.
Require Import List.
Import ListNotations.

(* 
=====================
  Utility functions 
=====================  
*)

(* Make a frequency-weighted list of generators where the weight is equal to *)
(* some constant mutliple of the rank (worst = 1, 2nd worst = 2, etc.)*)
Fixpoint rankify {A : Type} {_ : Mutate A} (scale : nat) (l : list (A * nat)) : (list (nat * G A) * nat) :=
    match l with
    | nil => (nil, 0)
    | (a, _) :: l' => 
      let (rest, rank) := rankify scale l' in 
      let rank' := (scale * rank+1) in 
      ((rank', mutate a) :: rest, rank + 1)
    end. 

(* Large(?) constant for focusedStrat.*)
Axiom focusedStratScaleRatio    : nat.
Extract Constant focusedStratScaleRatio    => "100".

Definition gte n m := Nat.leb m n.

(* 
=====================
  Strategies
=====================  
*)
(* Just use arbitrary every time. Only here for completeness *)
Definition blindStrat {A : Type} {_ : Gen A} 
           (_ : State) (_ : list (A * nat)) (_ : list (A * nat)) : G A := arbitrary.

(* Mutate the highest scoring result every time. *)
Definition bestFirstStrat {A : Type} {_ : Gen A} {_ : Mutate A} 
           (_ : State) (passed : list (A * nat)) (discarded : list (A * nat)) : G A :=
    match passed with
    | nil => arbitrary
    | (a, score) :: t => mutate a
    end. 

(* Mutates a randomly chosen past result weighted directly by score *)
Definition geneticStrat {A : Type} {_ : Gen A} {_ : Mutate A} 
           (_ : State) (passed : list (A * nat)) (_ : list (A * nat)) : G A :=
    match passed with
    | nil => arbitrary
    | l => freq_ arbitrary (map (fun x => match x with (c,s) => (s, mutate c) end) l)
    end.


(* Mutates a randomly chosen past result weighted by _rank_ *)
(* Worst case so far has weight 1, 2nd worst has 2, etc. *)
(* Useful when your score curve is a bit jagged and weird. *)
Definition rankStrat {A : Type} {_ : Gen A} {_ : Mutate A} 
                     (_ : State) (passed : list (A * nat)) (_ : list (A * nat)) : G A :=
    match passed with
    | nil => arbitrary
    | l => freq_ arbitrary (fst (rankify 1 l))
    end.

(* An approximation to simulated annealing *)
(* Real simulated annealing is probably very annoying since I have no idea how *)
(* Coq deals with floats but I assume the answer is "not very well" *)
(* This is similar to rankStrat, but the scale factor increases over time *)
(* (here, by 1 per 100 tests run.) This has the effect of starting out with *)
(* 100 arbitrarily generated test cases, and then eventually becoming more like *)
(* best first as time goes on. *)
Definition focusingStrat {A : Type} {_ : Gen A} {_ : Mutate A} 
                         (st : State) (passed : list (A * nat)) (_ : list (A * nat)) : G A :=
    match passed with
    | nil => arbitrary
    | l => let totalTests := (numSuccessTests st) + (numDiscardedTests st) in
      if gte focusedStratScaleRatio totalTests then
        arbitrary (* If totalTests / focusedStratScaleRatio would be 0, just be random! *)
      else 
        let scale := Nat.div totalTests focusedStratScaleRatio in
        freq_ arbitrary (fst (rankify scale l))
    end.