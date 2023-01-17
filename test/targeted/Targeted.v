From QuickChick Require Export QuickChick Strategy Classes Test Checker.
Import MonadNotation.
From ExtLib.Structures Require Export
     Monads.

(* STLC implementation stolen with love from PLF *)

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.


Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

(** Now we need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Definition isValue (t : tm) : bool :=
  match t with
  | (tm_abs _ _ _) => true
  | tm_true => true
  | tm_false => true
  | _ => false
  end.
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

#[local] Instance optionMonad : Monad option :=
  { ret A a := Some a;
    bind T U oa f := match oa with
    | Some a => f a
    | None => None
    end
  }.

Fixpoint step (t : tm) : option tm := 
    match t with
    | <{(\x:T2, t1) t2}> => 
      if isValue t2 then 
         Some <{ [x:=t2]t1 }> else 
      if isValue t1 then 
        t2' <- step t2;;
        ret <{t1  t2'}>
      else
        t1' <- step t1;;
        ret <{t1' t2}>
    | <{if true then t1 else t2}> => Some t1
    | <{if false then t1 else t2}> => Some t2
    | <{if t1 then t2 else t3}> => 
      t1' <- step t1;;
      ret <{if t1' then t2 else t3}>
    | _ => None
    end.


Fixpoint stepCount (n : nat) (t : tm) : nat :=
  match n with
  | O => 20
  | S n' => (match step t with 
    | Some t' => stepCount n' t'
    | None => 20 - n
    end
  ) end.


Definition stepCountProp (t : tm) : option bool :=
  if Nat.leb (stepCount 20 t) 5 then Some true else Some false.


(* Derive all the classes *)
Derive GenSized for ascii.
Derive GenSized for string.
Derive GenSized for ty.
Derive GenSized for tm.

Derive Show for ty.
Derive Show for tm.

Derive Sized for bool.
Derive Sized for ascii.
Derive Sized for string.
Derive Sized for tm.
Derive Sized for ty.

Derive Mutate for bool.
Derive Mutate for ascii.
Derive Mutate for string.
Derive Mutate for ty.
Derive Mutate for tm.

Derive Sized for nat.
Derive Mutate for nat.

(* Will probably pass, since arbitrary makes small naturals *)
Definition blind20 : Checker.Result :=
  QuickTarget blindStrat (fun x => x) show (fun x => if Nat.leb x 20 then Some true else Some false).
QuickChick blind20.

(* Will fail almost immediately. *)
Definition targeted20 : Checker.Result :=
  QuickTarget bestFirstStrat (fun x => x) show (fun x => if Nat.leb x 20 then Some true else Some false).
QuickChick targeted20.

(* The rest of these will take a bit,
   trying out all the strategies.  *)
Definition targetedSTLC : Checker.Result :=
  QuickTarget bestFirstStrat (stepCount 20) show stepCountProp.
QuickChick targetedSTLC.

Definition targetedSTLCGenetic : Checker.Result :=
  QuickTarget geneticStrat (stepCount 20) show stepCountProp.
QuickChick targetedSTLCGenetic.

Definition targetedSTLCRank : Checker.Result :=
  QuickTarget rankStrat (stepCount 20) show stepCountProp.
QuickChick targetedSTLCRank.

Definition targetedSTLCFocusing : Checker.Result :=
  QuickTarget focusingStrat (stepCount 20) show stepCountProp.
QuickChick targetedSTLCFocusing.