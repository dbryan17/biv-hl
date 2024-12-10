(* ********************************************* *)
(*

Dakota Bryan 
Grad PL Final Project
Fall 2024

*)
(* ********************************************* *)

(* ******************* *)
(*

The file presents a biversional language, along with a logic to reason about this 
biversional language. 
The logic is extremely similar to relational hoare logic, but defined over the biversional language.

*)


(* 

Sources: 

The biversional language and logic was largely derived from the the implementation of IMP and Hoare logic 
in coq used in Software Foundations Volume 1 and 2 (https://softwarefoundations.cis.upenn.edu/).

The nessecary ascepts of IMP and Hoare logic here was also adapted from Software Foundations. 

Note: I can provide the files I used as a reference if needed

*)


(* ******************* *)

From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Unicode.Utf8.
Require Import Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Arith.EqNat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat. 
Import Nat.

(* ---------------------------- *)
(* ---------- SYNTAX ---------- *)
(* ---------------------------- *)

Inductive univExpr : Type := 
  | ENum (n : nat)
  | EVar (x: string)
  | EPlus (e1 e2 : univExpr)
  | EMinus (e1 e2 : univExpr)
  | EMult (e1 e2 : univExpr)
  | EMod (e1 e2 : univExpr).

Inductive univBexpr : Type := 
  | BFalse 
  | BTrue
  | BEq (e1 e2 : univExpr)
  | BNeq (e1 e2 : univExpr) 
  | BLe (e1 e2 : univExpr)
  | BGt (e1 e2 : univExpr)
  | BNot (b : univBexpr)
  | BAnd (b1 b2 : univBexpr)
  | BOr (b1 b2 : univBexpr).


Inductive univCom : Type := 
  | CAsgn (x: string) (a : univExpr)
  | CIf (b : univBexpr) (c1 c2 : univCom)
  | CSeq (c1 c2 : univCom)
  | CSkip 
  | CWhile (b : univBexpr) (c : univCom).

Inductive bivCom : Type := 
  | BCUcom (uc : univCom)
  | BCSplit (uc1 uc2 : univCom)
  | BCSeq (bc1 bc2 : bivCom)
  | BCIf (ub : univBexpr) (bc1 bc2 : bivCom)
  | BCWhile (ub : univBexpr) (bc1 : bivCom).

(* ---------------------------- *)
(* ---------- PARSER ---------- *)
(* ---------------------------- *)


Coercion ENum : nat >-> univExpr. 
Coercion EVar : string >-> univExpr.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.


Notation "<{ e }>"  := e (e custom com_aux) : com_scope.
Notation "e"        := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )"    := x (in custom com, x at level 99) : com_scope.
Notation "x"        := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                      (in custom com at level 0, only parsing,
                      f constr at level 0, x constr at level 9,
                      y constr at level 9) : com_scope.

Notation "x + y"     := (EPlus x y) (in custom com at level 50, left associativity).
Notation "x - y"     := (EMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"     := (EMult x y) (in custom com at level 40, left associativity).
Notation "x % y"     := (EMod x y) (in custom com at level 40, left associativity).

Notation "'true'"    := true (at level 1).
Notation "'true'"    := BTrue (in custom com at level 0).
Notation "'false'"   := false (at level 1).
Notation "'false'"   := BFalse (in custom com at level 0).
Notation "x <= y"    := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"     := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"     := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"    := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"    := (BAnd x y) (in custom com at level 80, left associativity).
Notation "x || y"    := (BOr x y) (in custom com at level 80, left associativity).
Notation "'~' b"     := (BNot b) (in custom com at level 75, right associativity).

Notation "'skip'" := CSkip (in custom com at level 0) : com_scope. 
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Notation "'[' c ']'" := (BCUcom c) (in custom com at level 99) : com_scope. 
Notation "a '∓' b" := (BCSplit a b) (in custom com at level 88, right associativity) : com_scope. 
Notation "a ';;' b" := (BCSeq a b) (in custom com at level 99, right associativity) : com_scope.
Notation "'bif' x 'then' a 'else' b 'end'" := 
         (BCIf x a b) 
           (in custom com at level 99) : com_scope.
Notation "'bwhile' x 'do' a 'end'" :=
         (BCWhile x a)
           (in custom com at level 99) : com_scope.

Open Scope com_scope.

(* ---------------------------- *)
(* --------- SEMANTICS -------- *)
(* ---------------------------- *)

Definition state := total_map nat.
Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).


Fixpoint eeval (st : state) (ue : univExpr) : nat := 
  match ue with 
  | ENum n => n 
  | EVar x => st x
  | <{e1 + e2}> => (eeval st e1) + (eeval st e2)
  | <{e1 - e2}> => (eeval st e1) - (eeval st e2)
  | <{e1 * e2}> => (eeval st e1) * (eeval st e2)
  | <{e1 % e2}> => (eeval st e1) mod (eeval st e2)
  end.

Fixpoint beval (st : state) (be : univBexpr) : bool := 
  match be with 
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (eeval st a1) =? (eeval st a2)
  | <{a1 <> a2}>  => negb ((eeval st a1) =? (eeval st a2))
  | <{a1 <= a2}>  => (eeval st a1) <=? (eeval st a2)
  | <{a1 > a2}>   => negb ((eeval st a1) <=? (eeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  | <{b1 || b2}>  => orb (beval st b1) (beval st b2)
  end. 

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 80,
          st constr, st' constr at next level).

Inductive univComEval : univCom -> state -> state -> Prop := 
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      eeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (univComEval c st st').

Inductive bivComEval : state -> state -> bivCom -> state -> state -> Prop := 
  | BE_BCUcom : forall stm stp uc stm' stp', 
      stm =[ uc ]=> stm' -> 
      stp =[ uc ]=> stp' ->
      bivComEval stm stp (BCUcom uc) stm' stp'
  | BE_BCSplit : forall stm stp uc1 uc2 stm' stp',
      stm =[ uc1 ]=> stm' -> 
      stp =[ uc2 ]=> stp' -> 
      bivComEval stm stp (BCSplit uc1 uc2) stm' stp'
  | BE_BCSeq : forall stm stp bc1 bc2 stm' stp' stm'' stp'',
      bivComEval stm stp bc1 stm' stp' ->
      bivComEval stm' stp' bc2 stm'' stp'' -> 
      bivComEval stm stp (BCSeq bc1 bc2) stm'' stp'' 
  | BE_BCIfTrueTrue : forall stm stp ub bc1 bc2 stm' stp', 
      beval stm ub = true -> 
      beval stp ub = true -> 
      bivComEval stm stp bc1 stm' stp' -> 
      bivComEval stm stp (BCIf ub bc1 bc2) stm' stp'
  | BE_BCIfFalseFalse : forall stm stp ub bc1 bc2 stm' stp', 
      beval stm ub = false -> 
      beval stp ub = false -> 
      bivComEval stm stp bc2 stm' stp' -> 
      bivComEval stm stp (BCIf ub bc1 bc2) stm' stp' 
  | BE_BCWhileTrueTrue : forall stm stp ub bc stm' stp' stm'' stp'', 
      beval stm ub = true ->
      beval stp ub = true ->
      bivComEval stm stp bc stm' stp' -> 
      bivComEval stm' stp' (BCWhile ub bc) stm'' stp'' -> 
      bivComEval stm stp (BCWhile ub bc) stm'' stp''
  | BE_BCWhileFalseFalse : forall stm stp ub bc,
      beval stm ub = false ->
      beval stp ub = false -> 
      bivComEval stm stp (BCWhile ub bc) stm stp.


(* ---------------------------- *)
(* ------ DETERMINISTIC ------- *)
(* ---------------------------- *)


Theorem unviComEval_deterministic : forall (uc : univCom) st st' st'', 
  st =[ uc ]=> st' -> 
  st =[ uc ]=> st'' -> 
  st' = st''.
Proof. 
  intros. generalize dependent st''. 
  induction H; intros. 
  - inversion H0; subst; auto.
  - inversion H0; subst; auto. 
  - inversion H1; subst. apply IHunivComEval1 in H4. rewrite <- H4 in H7. apply IHunivComEval2 in H7. assumption. 
  - inversion H1; subst. 
    + apply IHunivComEval. assumption. 
    + rewrite H in H7. easy.  
  - inversion H1; subst. 
    + rewrite H in H7. easy. 
    + apply IHunivComEval. assumption. 
  - inversion H0; subst; try reflexivity; try rewrite H in H3; easy.
  - inversion H2; subst. 
    + rewrite H in H7; easy. 
    + apply IHunivComEval2. apply IHunivComEval1 in H6. rewrite <- H6 in H9. assumption.
Qed.  

Theorem bivComEval_determinisitc : forall (bc: bivCom) stm stp stm' stm'' stp' stp'',
  bivComEval stm stp bc stm' stp' -> 
  bivComEval stm stp bc stm'' stp'' -> 
  stm' = stm'' /\ stp' = stp''. 
Proof. 
  intros. generalize dependent stm''. generalize dependent stp''. 
  induction H; intros.
  - inversion H1; subst. split. 
    + apply unviComEval_deterministic with (st := stm) (uc := uc); assumption.
    + apply unviComEval_deterministic with (st := stp) (uc := uc); assumption.
  - inversion H1; subst. split. 
    + apply unviComEval_deterministic with (st := stm) (uc := uc1); assumption.
    + apply unviComEval_deterministic with (st := stp) (uc := uc2); assumption.
  - inversion H1; subst. apply IHbivComEval1 in H6. 
    destruct H6. rewrite <- H2 in H9. rewrite <- H3 in H9. apply IHbivComEval2 in H9. assumption.
  - inversion H2; subst. 
    + apply IHbivComEval. assumption. 
    + rewrite H in H8. easy. 
  - inversion H2; subst. 
    + rewrite H in H8. easy. 
    + apply IHbivComEval. assumption. 
  - inversion H3; subst. 
    + apply IHbivComEval2. apply IHbivComEval1 in H10. destruct H10. rewrite <- H4 in H13. rewrite <- H5 in H13. assumption.
    + rewrite H in H8. easy. 
  - inversion H1; subst. 
    + rewrite H in H4. easy. 
    + split; reflexivity.
Qed. 

(* ---------------------------- *)
(* ------ BIVERSIONAL HL ------ *)
(* ---------------------------- *)

(* ---------------------------- *)
(* --------- PRELIMS ---------- *)
(* ---------------------------- *)

(* NOTES 
- we will let X- denote the value of X in the 'old' or 'left' memory
- same for X+ 
- this section is for defining the syntax and semantics of these biversional expressions 
*)


(* syntax of biverisonal (binary) expression *)
 Inductive bivExpr : Type := 
  | BENum (n : nat)
  | BEVarOld (x: string)
  | BEVarNew (x : string)
  | BEPlus (e1 e2 : bivExpr)
  | BEMinus (e1 e2 : bivExpr)
  | BEMult (e1 e2 : bivExpr)
  | BEMod (e1 e2 : bivExpr).

Inductive bivBExpr : Type := 
  | BBFalse 
  | BBTrue
  | BBEq (e1 e2 : bivExpr)
  | BBNeq (e1 e2 : bivExpr) 
  | BBLe (e1 e2 : bivExpr)
  | BBGt (e1 e2 : bivExpr)
  | BBNot (b : bivBExpr)
  | BBAnd (b1 b2 : bivBExpr)
  | BBOr (b1 b2 : bivBExpr).


(* for converting from univ (binary) expression to biversional *)

(* helpers *)
Definition get_last_char (s : string) : ascii := match get (length s - 1) s with 
  | None => "a"
  | Some c => c
end. 

Definition get_is_tag (c : ascii) : option bool := match c with 
  | "-"%char => Some true
  | "+"%char => Some false 
  | _ => None
end. 

Definition get_orig_var (s : string) : string := substring 0 ((length s) - 1) s.

(* important to note, if the variable is not tagged, we are letting it be tagged with old memory *)
Fixpoint to_biv_expr (e : univExpr) : bivExpr :=
  match e with
  | ENum n => BENum n
  | EVar x => match get_is_tag (get_last_char x) with 
                | Some true => BEVarOld (get_orig_var x) 
                | Some false => BEVarNew (get_orig_var x)
                | None => BEVarOld x
              end
  | EPlus e1 e2 => BEPlus (to_biv_expr e1) (to_biv_expr e2)
  | EMinus e1 e2 => BEMinus (to_biv_expr e1) (to_biv_expr e2)
  | EMult e1 e2 => BEMult (to_biv_expr e1) (to_biv_expr e2)
  | EMod e1 e2 => BEMod (to_biv_expr e1) (to_biv_expr e2)
  end.

Fixpoint to_biv_bexpr (be : univBexpr) : bivBExpr := 
  match be with 
  | BTrue => BBTrue
  | BFalse => BBFalse 
  | BEq a1 a2 => BBEq (to_biv_expr a1) (to_biv_expr a2)
  | BNeq a1 a2 => BBNeq (to_biv_expr a1) (to_biv_expr a2)
  | BLe a1 a2 => BBLe (to_biv_expr a1) (to_biv_expr a2)
  | BGt a1 a2 => BBGt (to_biv_expr a1) (to_biv_expr a2)
  | BNot b1 => BBNot (to_biv_bexpr b1)
  | BAnd b1 b2 => BBAnd (to_biv_bexpr b1) (to_biv_bexpr b2)
  | BOr b1 b2 => BBOr (to_biv_bexpr b1) (to_biv_bexpr b2)
  end. 


(* smeantics of biversional (binary) expressions *)

Fixpoint beeval (stm : state) (stp: state) (be : bivExpr) : nat := 
  match be with 
  | BENum n => n 
  | BEVarOld x => stm x
  | BEVarNew x => stp x
  | BEPlus e1 e2 => (beeval stm stp e1) + (beeval stm stp e2)
  | BEMinus e1 e2 => (beeval stm stp e1) - (beeval stm stp e2)
  | BEMult e1 e2 => (beeval stm stp e1) * (beeval stm stp e2)
  | BEMod e1 e2 => (beeval stm stp e1) mod (beeval stm stp e2)
  end.

Fixpoint bbeval (stm : state) (stp: state) (bbe : bivBExpr) : bool := 
  match bbe with 
  | BBTrue   => true
  | BBFalse    => false
  | BBEq a1 a2  => (beeval stm stp a1) =? (beeval stm stp a2)
  | BBNeq a1 a2  => negb ((beeval stm stp a1) =? (beeval stm stp a2))
  | BBLe a1 a2  => (beeval stm stp a1) <=? (beeval stm stp a2)
  | BBGt a1 a2  => negb ((beeval stm stp a1) <=? (beeval stm stp a2))
  | BBNot b1     => negb (bbeval stm stp b1)
  | BBAnd b1 b2 => andb (bbeval stm stp b1) (bbeval stm stp b2)
  | BBOr b1 b2 => orb (bbeval stm stp b1) (bbeval stm stp b2)
  end. 

(* ---------------------------- *)
(* ---------- SYNTAX ---------- *)
(* ---------------------------- *)

(* basics for bivsional assertions *)
Definition BivAssertion := state -> state -> Prop.

Definition bivAssert_implies (P Q : BivAssertion) : Prop :=
  forall stm stp, P stm stp -> Q stm stp.

Declare Scope bivAssert_spec_scope.

Notation "P ->> Q" := (bivAssert_implies P Q) (at level 80) : bivAssert_spec_scope.

Open Scope bivAssert_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : bivAssert_spec_scope.

(* biversional expressions as Props that will be lifted to bivAsserts *)
Definition BivExpr : Type := state -> state -> nat. 
(* and for boolean expression *)
Definition BivBExpr : Type := state -> state -> bool.
(* lift props to BivAssertions *)
Definition bivAssert_of_Prop (P : Prop) : BivAssertion := fun _ _ => P.
(* same for nats *)
Definition BivExpr_of_nat (n : nat) : BivExpr := fun _ _ => n.
Definition BivBExpr_of_bool (b : bool) : BivBExpr := fun _ _ => b. 


(* the lifting *)
Definition BivExpr_of_univExpr (e : univExpr) : BivExpr := fun stm stp => beeval stm stp (to_biv_expr e).
Definition BivBExpr_of_univBexpr (be : univBexpr) : BivBExpr := fun stm stp => bbeval stm stp ( to_biv_bexpr be). 

(* coercions so this lifting is done by default *)
Coercion bivAssert_of_Prop : Sortclass >-> BivAssertion. 
Coercion BivExpr_of_nat : nat >-> BivExpr. 
Coercion BivBExpr_of_bool : bool >-> BivBExpr.
Coercion BivExpr_of_univExpr : univExpr >-> BivExpr. 
Coercion BivBExpr_of_univBexpr : univBexpr >-> BivBExpr.
Add Printing Coercion BivExpr_of_nat BivExpr_of_univExpr bivAssert_of_Prop BivBExpr_of_bool BivBExpr_of_univBexpr.

Arguments bivAssert_of_Prop /.
Arguments BivExpr_of_nat /.
Arguments BivBExpr_of_bool /.
Arguments BivBExpr_of_univBexpr /.
Arguments BivExpr_of_univExpr /.
Add Printing Coercion BivExpr_of_nat BivExpr_of_univExpr bivAssert_of_Prop BivBExpr_of_bool BivBExpr_of_univBexpr.

Declare Scope bivAssertion_scope. 
Bind Scope bivAssertion_scope with BivAssertion.
Bind Scope bivAssertion_scope with BivExpr. 
Bind Scope bivAssertion_scope with BivBExpr. 
Delimit Scope bivAssertion_scope with BivAssertion. 

Notation bivAssert P := (P%BivAssertion : BivAssertion).
Notation mkBivExpr e := (e%BivAssertion : BivExpr).
Notation mkBivBExpr b := (b%BivAssertion : BivBExpr).

(* notations *)
Notation "~ P" := (fun stm stp => ~ bivAssert P stm stp) : bivAssertion_scope.
Notation "P /\ Q" := (fun stm stp => bivAssert P stm stp /\ bivAssert Q stm stp) : bivAssertion_scope.
Notation "P \/ Q" := (fun stm stp => bivAssert P stm stp \/ bivAssert Q stm stp) : bivAssertion_scope.
Notation "P -> Q" := (fun stm stp => bivAssert P stm stp ->  bivAssert Q stm stp) : bivAssertion_scope.
Notation "P <-> Q" := (fun stm stp => bivAssert P stm stp <->  bivAssert Q stm stp) : bivAssertion_scope.
Notation "a = b" := (fun stm stp => mkBivExpr a stm stp = mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a <> b" := (fun stm stp => mkBivExpr a stm stp <> mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a <= b" := (fun stm stp => mkBivExpr a stm stp <= mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a < b" := (fun stm stp => mkBivExpr a stm stp < mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a >= b" := (fun stm stp => mkBivExpr a stm stp >= mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a > b" := (fun stm stp => mkBivExpr a stm stp > mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a + b" := (fun stm stp => mkBivExpr a stm stp + mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a - b" := (fun stm stp => mkBivExpr a stm stp - mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a * b" := (fun stm stp => mkBivExpr a stm stp * mkBivExpr b stm stp) : bivAssertion_scope.
Notation "a % b" := (fun stm stp => mkBivExpr a stm stp mod mkBivExpr b stm stp) (at level 40): bivAssertion_scope.


Definition ap {X} (f : nat -> X) (x : BivExpr) :=
  fun stm stp => f (x stm stp).

Definition ap2 {X} (f : nat -> nat -> X) (x : BivExpr) (y : BivExpr) (stm : state) (stp : state) :=
  f (x stm stp) (y stm stp).


(* ---------------------------- *)
(* ------- RULES PRELIMS ------ *)
(* ---------------------------- *)

(* this is for the special semantics needed for some of the rules *)

(* substitution in state for assigns *)
Definition bivAssertion_sub_old (x : string) (e : univExpr) (P : BivAssertion) : BivAssertion := 
  fun (stm stp: state) => 
    P (x !-> eeval stm e; stm) (stp). 

Notation "P -[ X |-> a ]" := (bivAssertion_sub_old X a P)
  (at level 10, X at next level, a custom com) : bivAssert_spec_scope.

Definition bivAssertion_sub_new (x : string) (e : univExpr) (P : BivAssertion) : BivAssertion := 
  fun (stm stp: state) => 
    P (stm) (x !-> eeval stp e; stp).

Notation "P +[ X |-> a ]" := (bivAssertion_sub_new X a P)
  (at level 10, X at next level, a custom com) : bivAssert_spec_scope.

(* tagging for conditionals *)

Definition eval_in_old eb : BivAssertion := 
  (fun (stm stp : state) => 
    (beval stm eb) = true).

Definition eval_in_new eb : BivAssertion := 
  fun (stm stp : state) => 
    ((beval stp eb) = true).

Notation "eb '<[-]>'" := (eval_in_old eb) (at level 70).
Notation "eb '<[+]>'" := (eval_in_new eb) (at level 70).

Lemma bexp_eval_false_old : forall b stm stp,
  (beval stm b = false) -> ~ ((eval_in_old b) stm stp).
Proof. congruence. Qed.

Lemma bexp_eval_true_old : forall b stm stp,
  beval stm b = true -> ((eval_in_old b) stm stp).
Proof. congruence. Qed.

Lemma bexp_eval_false_new : forall b stm stp,
  beval stp b = false -> ~ ((eval_in_new b) stm stp).
Proof. congruence. Qed.

Lemma bexp_eval_true_new : forall b stm stp,
  beval stp b = true -> ((eval_in_new b) stm stp).
Proof. congruence. Qed.

(* valid biv hoare triple *)

Definition valid_bivHoare_triple 
           (P : BivAssertion) (bc : bivCom) (Q : BivAssertion) : Prop := 
  forall stm stp stm' stp', 
    bivComEval stm stp bc stm' stp' -> 
    P stm stp -> 
    Q stm' stp'. 

Notation "{{ P }} bc {{ Q }}" := 
  (valid_bivHoare_triple P bc Q)
    (at level 90, bc custom com at level 99)
    : bivAssert_spec_scope.

(* Define free vars *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition I : string := "I".
Definition N : string := "N".
Definition SUM : string := "SUM".

Definition WM : string := "W-".
Definition XM : string := "X-".
Definition YM : string := "Y-".
Definition ZM : string := "Z-".
Definition IM : string := "I-".
Definition NM : string := "N-".
Definition SUMM : string := "SUM-".

Definition WP : string := "W+".
Definition XP : string := "X+".
Definition YP : string := "Y+".
Definition ZP : string := "Z+".
Definition IP : string := "I+".
Definition NP : string := "N+".
Definition SUMP : string := "SUM+".

(* custom tatics *)

(* TODO got rid of unfolding SUM and such *)
Ltac bivAssertion_auto :=
  unfold "->>", get_orig_var, bivAssertion_sub_new, bivAssertion_sub_old, eval_in_old, eval_in_new, t_update;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;
  auto; try lia.

(* usefull when bivAssertion auto doesn't solve everything *)
Ltac orig_vars := unfold get_orig_var in *; simpl in *.

Ltac unfold_strs := unfold W, X, Y, Z, I, N, SUM, WM, XM, YM, ZM, IM, NM, SUMM, WP, XP, YP, ZP, IP, NP, SUMP in *.

(* ---------------------------- *)
(* ---------- RULES ----------- *)
(* ---------------------------- *)

(* ***** STRUCTURE RULES ****** *)

(* consequence *)
Theorem consq : forall (P P' Q Q' : BivAssertion) bc, 
  {{P'}} bc {{Q'}} ->
  P ->> P' -> 
  Q' ->> Q -> 
  {{P}} bc {{Q}}. 
Proof. 
  unfold valid_bivHoare_triple, "->>". 
  intros. apply H in H2. 
  - apply H1. assumption. 
  - apply H0. assumption. 
Qed. 

Theorem consq_pre : forall (P P' Q : BivAssertion) bc, 
  {{P'}} bc {{Q}} ->
  P ->> P' -> 
  {{P}} bc {{Q}}. 
Proof. 
  unfold valid_bivHoare_triple, "->>". 
  intros. apply H with (stm := stm) (stp := stp). 
  - assumption. 
  - apply H0. assumption. 
Qed. 

Theorem consq_post : forall (P Q Q': BivAssertion) bc, 
  {{P}} bc {{Q'}} ->
  Q' ->> Q -> 
  {{P}} bc {{Q}}. 
Proof. 
  unfold valid_bivHoare_triple, "->>". 
  intros. apply H0. apply H with (stm := stm) (stp := stp). 
  - assumption. 
  - assumption. 
Qed.  


(* * RELATIONAL (SPLIT) RULES * *)

(* TWO SIDED RULES *)

(* standard relational hoare logic rules *)
Theorem rhl_double_asgn : forall Q X Y am ap, 
  {{bivAssertion_sub_new Y ap (bivAssertion_sub_old X am Q)}} 
  X := am ∓ Y := ap 
  {{Q}}.
Proof. 
  unfold valid_bivHoare_triple. 
  intros. inversion H. subst.
  unfold bivAssertion_sub_new in H0. unfold bivAssertion_sub_old in H0. 
  inversion H5. subst. inversion H8. subst. assumption. 
Qed. 


Theorem rhl_double_asgn_forward : forall P m1 m2 e1 e2, 
  {{fun stm stp => P stm stp /\ stm X = m1 /\ stp Y = m2}}
    X := e1 ∓ Y := e2
  {{fun stm stp => P (X !-> m1 ; stm) (Y !-> m2 ; stp) /\ stm X = eeval (X !-> m1; stm) e1 /\ stp Y = eeval (Y !-> m2 ; stp) e2}}.
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H; subst. inversion H5; subst. inversion H8; subst. destruct H0. destruct H1. 
  split; rewrite t_update_shadow; rewrite t_update_shadow; 
  rewrite <- H1; rewrite <- H2; rewrite t_update_same; rewrite t_update_same; 
  try assumption; try split; eauto. 
Qed. 


Theorem rhl_double_skip : forall Q, 
  {{Q}} skip ∓ skip {{Q}}. 
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H; subst. inversion H5 ; subst. inversion H8; subst. assumption. 
Qed. 

(* double sequence is just a biversional sequence with split *)
(* this means for ex. [c1 ; c2] -> c1 ; c2 ∓ c1 ; c2 -> c1 ∓ c1 ;; c2 ∓ c2 *)
(* omitting this proof for now and providing the double rule *)

Theorem rhl_double_seq : forall P R Q uc1 uc2 uc1' uc2', 
  {{P}} uc1 ∓ uc1' {{R}} -> 
  {{R}} uc2 ∓ uc2' {{Q}} -> 
  {{P}} ((uc1 ; uc2) ∓ (uc1' ; uc2')) {{Q}}.   
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H1; subst. inversion H7; subst. inversion H10; subst. 
  eapply H0. 
  - eapply BE_BCSplit. 
    + eapply H9. 
    + eapply H12. 
  - eapply H. 
    + eapply BE_BCSplit. 
      * eapply H5. 
      * eapply H6. 
    + assumption. 
Qed. 

(* here, we are requiring that the loops iterate in lockstep *)

Theorem rhl_double_while : forall ube1 ube2 (I : BivAssertion) uc1 uc2, 
  (forall stm stp, I stm stp -> ((ube1<[-]> stm stp) <-> (ube2<[+]> stm stp))) -> 
  {{I /\ ube1<[-]>}} uc1 ∓ uc2 {{I}} -> 
  {{I}} while ube1 do uc1 end ∓ while ube2 do uc2 end {{I /\ ~ube1<[-]>}}.
Proof. 
  unfold eval_in_new, eval_in_old. 
  intros ube1 ube2 I uc1 uc2 H H1 stm stp stm' stp' H2 H3. 
  remember <{ while ube1 do uc1 end ∓ while ube2 do uc2 end }> as original_command eqn: Horig. 
  induction H2; try (inversion Horig); subst; clear Horig. 
  generalize dependent stp. generalize dependent stp'. 
  remember <{(while ube1 do uc1 end)}> as orig_com eqn: orig. 
  induction H0; try (inversion orig); subst; clear orig.  
  - intros. inversion H2; subst. 
    + split. 
      *  assumption. 
      *   rewrite <- not_true_iff_false in H0. assumption. 
    + split. 
      * specialize (H st stp). apply H in H3. rewrite H6, H0 in H3. 
        exfalso. apply eq_true_false_abs with (b := true). reflexivity. symmetry. apply H3. reflexivity. 
      * rewrite <- not_true_iff_false in H0. assumption. 
  - intros. inversion H2; subst. 
    + split. 
      * specialize (H st stp'). apply H in H3. rewrite H0, H8 in H3. 
        exfalso. apply eq_true_false_abs with (b := true). reflexivity. symmetry. apply H3. reflexivity. 
      * specialize (H st stp'). apply H in H3. rewrite H0, H8 in H3. 
        exfalso. apply eq_true_false_abs with (b := true). reflexivity. symmetry. apply H3. reflexivity. 
    + eapply IHunivComEval2.
      * reflexivity. 
      * apply H10. 
      * unfold valid_bivHoare_triple in H1. apply H1 with (stm := st) (stp := stp) (stp' := st'0) (stm' := st').
        { apply BE_BCSplit; assumption. }
        { split; assumption.  }
Qed. 

Theorem rhl_double_if: forall ube1 ube2 P Q uc1 uc2 uc1' uc2',
  (forall stm stp, P stm stp -> ((ube1<[-]> stm stp) <-> (ube2<[+]> stm stp))) -> 
  {{P /\ ube1<[-]>}} uc1 ∓ uc1' {{Q}} -> 
  {{P /\ ~ube1<[-]>}} uc2 ∓ uc2' {{Q}} -> 
  {{P}} if ube1 then uc1 else uc2 end ∓ if ube2 then uc1' else uc2' end {{Q}}.
Proof. 
  unfold valid_bivHoare_triple, eval_in_new, eval_in_old. intros. inversion H2; subst. inversion H8; subst. 
  - inversion H11; subst. 
    + apply H0 with (stm := stm) (stp := stp).
      * apply BE_BCSplit; assumption. 
      * eauto. 
    + specialize (H stm stp). apply H in H3. rewrite H10 in H3. rewrite H13 in H3. 
      exfalso. apply eq_true_false_abs with (b := true). reflexivity. symmetry. apply H3. reflexivity. 
  - inversion H11; subst. 
    + specialize (H stm stp). apply H in H3. rewrite H10 in H3. rewrite H13 in H3. 
      exfalso. apply eq_true_false_abs with (b := true). reflexivity. symmetry. apply H3. reflexivity. 
    + apply H1 with (stm := stm) (stp := stp). 
      * apply BE_BCSplit; assumption. 
      * split; try eauto; apply bexp_eval_false_old with (stp := stp); assumption.
Qed. 

Theorem rhl_double_if_opp: forall ube1 ube2 P Q uc1 uc2 uc1' uc2',
  (forall stm stp, P stm stp -> ((ube1<[-]> stm stp) <-> ~(ube2<[+]> stm stp))) -> 
  {{P /\ ube1<[-]>}} uc1 ∓ uc2' {{Q}} -> 
  {{P /\ ~ube1<[-]>}} uc2 ∓ uc1' {{Q}} -> 
  {{P}} if ube1 then uc1 else uc2 end ∓ if ube2 then uc1' else uc2' end {{Q}}.
Proof. 
  unfold valid_bivHoare_triple, eval_in_new, eval_in_old. intros. inversion H2; subst. inversion H8; subst. 
  - inversion H11; subst. 
    + specialize (H stm stp). apply H in H3. rewrite H10 in H3. rewrite H13 in H3. 
      exfalso. rewrite not_true_iff_false in H3. apply eq_true_false_abs with (b := true). 
      reflexivity. apply H3. reflexivity. 
    + apply H0 with (stm := stm) (stp := stp).
      * apply BE_BCSplit; assumption. 
      * eauto. 
  - inversion H11; subst. 
    + apply H1 with (stm := stm) (stp := stp). 
      * apply BE_BCSplit; assumption. 
      * split; try eauto; apply bexp_eval_false_old with (stp := stp); assumption.
    + specialize (H stm stp). apply H in H3. rewrite H10 in H3. rewrite H13 in H3. 
      exfalso. rewrite not_true_iff_false in H3. apply eq_true_false_abs with (b := true). 
      reflexivity. symmetry. apply H3. reflexivity. 
Qed. 

(* ONE SIDED RULES *)

Theorem rhl_skip_asgn : forall Q X e, 
  {{bivAssertion_sub_new X e Q}}
  skip ∓ X := e
  {{Q}}.
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H. subst. 
  unfold bivAssertion_sub_new in H0. inversion H5. inversion H8. subst. assumption. 
Qed. 

Theorem rhl_asgn_skip : forall Q X e, 
  {{bivAssertion_sub_old X e Q}}
  X := e ∓ skip 
  {{Q}}.
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H. subst. 
  unfold bivAssertion_sub_new in H0. inversion H5. inversion H8. subst. assumption. 
Qed. 

Theorem rhl_skip_seq : forall uc1 uc2 P Q R,
  {{P}} skip ∓ uc1 {{R}} -> 
  {{R}} skip ∓ uc2 {{Q}} -> 
  {{P}} skip ∓ (uc1 ; uc2) {{Q}}. 
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H1; subst. inversion H7; subst. 
  inversion H10; subst. apply H0 with (stm := stm') (stp := st'). 
  - apply BE_BCSplit; assumption. 
  - apply H with (stm := stm') (stp := stp). 
    + apply BE_BCSplit; assumption. 
    + assumption. 
Qed. 

Theorem rhl_seq_skip : forall uc1 uc2 P Q R,
  {{P}} uc1 ∓ skip {{R}} -> 
  {{R}} uc2 ∓ skip {{Q}} -> 
  {{P}} (uc1 ; uc2) ∓ skip {{Q}}. 
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H1; subst. inversion H7; subst. 
  inversion H10; subst. apply H0 with (stm := st') (stp := stp'). 
  - apply BE_BCSplit; assumption. 
  - apply H with (stm := stm) (stp := stp'). 
    + apply BE_BCSplit; assumption. 
    + assumption. 
Qed. 

Theorem rhl_one_side_if_l : forall P Q eb c1 c2 cp, 
  {{P /\ eb<[-]>}} c1 ∓ cp {{Q}} -> 
  {{P /\ ~eb<[-]>}} c2 ∓ cp {{Q}} -> 
  {{P}} if eb then c1 else c2 end ∓ cp {{Q}}.
Proof.  
  unfold valid_bivHoare_triple. intros. unfold eval_in_old in H. unfold eval_in_old in H0. inversion H1. subst. inversion H7. subst.  
  - apply H with (stm := stm) (stp := stp).
    + apply BE_BCSplit.
      * assumption. 
      * assumption. 
    + easy. 
  - apply H0 with (stm := stm) (stp := stp).
    + apply BE_BCSplit.
      * assumption. 
      * assumption. 
    + rewrite H9. easy. 
Qed. 

Theorem rhl_one_side_if_r : forall P Q eb c1 c2 cp, 
  {{P /\ eb<[+]>}} cp ∓ c1 {{Q}} -> 
  {{P /\ ~eb<[+]>}} cp ∓ c2 {{Q}} -> 
  {{P}} cp ∓ if eb then c1 else c2 end {{Q}}.
Proof.  
  unfold valid_bivHoare_triple. intros. unfold eval_in_new in H. unfold eval_in_new in H0. inversion H1. subst. inversion H10. subst.  
  - apply H with (stm := stm) (stp := stp).
    + apply BE_BCSplit.
      * assumption. 
      * assumption. 
    + easy. 
  - apply H0 with (stm := stm) (stp := stp).
    + apply BE_BCSplit.
      * assumption. 
      * assumption. 
    + rewrite H9. easy. 
Qed. 

Theorem rhl_one_side_while_l : forall ube uc I, 
  {{I /\ ube<[-]>}} uc ∓ skip {{I}} -> 
  {{I}} while ube do uc end ∓ skip {{I /\ ~ube<[-]>}}.
Proof.
  intros ube uc I HHoare stm stp stm' stp' Heval HI. 
  remember <{while ube do uc end ∓ skip}> as orig_com eqn:Horig. 
  induction Heval; try inversion Horig; subst; clear Horig.
  remember <{(while ube do uc end)}> as orig_com eqn: Horig. 
  induction H; try inversion Horig; subst; clear Horig. 
  - inversion H0; subst. unfold eval_in_old. rewrite not_true_iff_false. eauto. 
  - inversion H0; subst. unfold eval_in_old. apply IHunivComEval2.
    + reflexivity. 
    + unfold valid_bivHoare_triple in HHoare. apply HHoare with (stm := st) (stp := stp'). 
      { apply BE_BCSplit; assumption.  } 
      { split; assumption. }
Qed. 

Theorem rhl_one_side_while_r : forall ube uc I, 
  {{I /\ ube<[+]>}} skip ∓ uc {{I}} -> 
  {{I}} skip ∓  while ube do uc end {{I /\ ~ube<[+]>}}.
Proof.
  intros ube uc I HHoare stm stp stm' stp' Heval HI. 
  remember <{skip ∓ while ube do uc end}> as orig_com eqn:Horig. 
  induction Heval; try inversion Horig; subst; clear Horig.
  remember <{(while ube do uc end)}> as orig_com eqn: Horig. 
  induction H0; try inversion Horig; subst; clear Horig. 
  - inversion H; subst. unfold eval_in_new. rewrite not_true_iff_false. eauto. 
  - inversion H; subst. unfold eval_in_new. apply IHunivComEval2.
    + reflexivity. 
    + unfold valid_bivHoare_triple in HHoare. apply HHoare with (stm := stm') (stp := st). 
      { apply BE_BCSplit; assumption.  } 
      { split; assumption. }
Qed. 

(* ***** BIVERSIONAL RULES **** *)

(* Notes: 
- these are the rules for biversional aspects of the language 
- we don't need rules for single commands because we can rewrite then apply the double rules
- we prefix with bhl meaning these rules are unqiue to the biversional aspect of the language and logic (not just relational)
*)

Theorem bhl_seq : forall P Q R bc1 bc2, 
  {{P}} bc1 {{R}} -> 
  {{R}} bc2 {{Q}} -> 
  {{P}} bc1 ;; bc2 {{Q}}. 
Proof. 
  unfold valid_bivHoare_triple. intros. inversion H1. subst. eauto.  
Qed. 

Theorem bhl_while : forall I ube bc, 
  {{I /\ ube<[-]> /\ ube<[+]>}} bc {{I}} -> 
  {{I}} bwhile ube do bc end {{I /\ ~ube<[-]> /\ ~ube<[+]>}}.
Proof. 
  intros I ube bc HBivHoare stm stp stm' stp' Heval HI. remember <{bwhile ube do bc end}> as original_command eqn:Horig.
  induction Heval. 
  - inversion Horig. 
  - inversion Horig. 
  - inversion Horig. 
  - inversion Horig. 
  - inversion Horig. 
  - inversion Horig. apply IHHeval2. 
    + rewrite H2, H3. reflexivity. 
    + apply (HBivHoare stm stp stm' stp'). 
      * rewrite <- H3. assumption. 
      * split. 
        { assumption. }
        { unfold eval_in_old. unfold eval_in_new. rewrite <- H2. easy. }
  - inversion Horig. unfold eval_in_new. unfold eval_in_old. rewrite H2 in H, H0. split. 
    + assumption. 
    + split. 
      * rewrite H. easy. 
      * rewrite H0. easy. 
Qed. 

Theorem bhl_if : forall P Q ube bc1 bc2, 
  {{P /\ ube<[-]> /\ ube<[+]>}} bc1 {{Q}} -> 
  {{P /\ ~ube<[-]> /\ ~ube<[+]>}} bc2 {{Q}} -> 
  {{P}} bif ube then bc1 else bc2 end {{Q}}.
Proof. 
  unfold valid_bivHoare_triple. intros. unfold eval_in_old in H, H0. unfold eval_in_new in H, H0. inversion H1; subst; eauto. 
  - apply H0 with (stm := stm) (stp := stp).
    + assumption. 
    + rewrite H8, H11. eauto.
Qed. 

(* universional command rules rewritten to doubles *)
(* useful proofs for simplifying some rules *)
Theorem single_is_double_same : forall (uc: univCom) (stm stp stm' stp' : state), 
  bivComEval stm stp <{ [uc] }> stm' stp' <-> bivComEval stm stp <{uc ∓ uc}> stm' stp'. 
Proof. 
  intros. split.  
  - intros. inversion H. apply BE_BCSplit ; assumption. 
  - intros. inversion H. apply BE_BCUcom ; assumption. 
Qed. 

Theorem rewrite_single_bhl : forall (uc: univCom) (P Q : BivAssertion), 
  {{P}} [uc] {{Q}} <-> {{P}} uc ∓ uc {{Q}}.
Proof. 
  unfold valid_bivHoare_triple. split; intros. 
  - apply H with (stm := stm) (stp := stp).  
    + rewrite single_is_double_same. assumption. 
    + assumption. 
  - apply H with (stm := stm) (stp := stp).
    + rewrite <- single_is_double_same. assumption. 
    + assumption. 
Qed. 

Ltac rewrite_single_bhl := rewrite rewrite_single_bhl.

(* ---------------------------- *)
(* -------- SOUNDNESS --------- *)
(* ---------------------------- *)

(* for rules *)


(* --------- PRELIMS ---------- *)
Inductive derivable : BivAssertion -> bivCom -> BivAssertion -> Type := 
  | BHL_Consq: forall P P' Q Q' bc, 
    derivable P' bc Q' -> 
    (forall stm stp, P stm stp -> P' stm stp) -> 
    (forall stm stp, Q' stm stp -> Q stm stp) -> 
    derivable P bc Q
  | BHL_Double_Asgn : forall Q X Y am ap, 
    derivable (bivAssertion_sub_new Y ap (bivAssertion_sub_old X am Q)) <{X := am ∓ Y := ap}> Q
  | BHL_Double_Asgn_Forward : forall P m1 m2 e1 e2, 
    derivable (fun stm stp => P stm stp /\ stm X = m1 /\ stp Y = m2)
                <{X := e1 ∓ Y := e2}>
              (fun stm stp => P (X !-> m1 ; stm) (Y !-> m2 ; stp) /\ stm X = eeval (X !-> m1; stm) e1 /\ stp Y = eeval (Y !-> m2 ; stp) e2)
  | BHL_Double_Skip : forall Q,
    derivable Q <{skip ∓ skip}> Q
  | BHL_Double_Seq : forall P R Q uc1 uc2 uc1' uc2',
    derivable P <{uc1 ∓ uc1'}> R -> 
    derivable R <{uc2 ∓ uc2'}> Q -> 
    derivable P <{(uc1 ; uc2) ∓ (uc1' ; uc2')}> Q 
  | BHL_Double_While : forall ube1 ube2 I uc1 uc2, 
    (forall stm stp, (I stm stp -> ((ube1<[-]> stm stp) <-> (ube2<[+]> stm stp)))) -> 
    derivable (I /\ ube1<[-]>) <{uc1 ∓ uc2}> I -> 
    derivable I <{while ube1 do uc1 end ∓ while ube2 do uc2 end}> (I /\ ~ube1<[-]>)
  | BHL_Double_If : forall ube1 ube2 P Q uc1 uc2 uc1' uc2', 
    (forall stm stp, P stm stp -> (ube1<[-]> stm stp <-> (ube2<[+]> stm stp))) -> 
    derivable (fun stm stp => (P stm stp /\ ube1<[-]> stm stp)) <{uc1 ∓ uc1'}> Q -> 
    derivable (fun stm stp => (P stm stp /\ ~ube1<[-]> stm stp)) <{uc2 ∓ uc2'}> Q -> 
    derivable P <{if ube1 then uc1 else uc2 end ∓ if ube2 then uc1' else uc2' end}> Q
  | BHL_Double_If_Opp : forall ube1 ube2 P Q uc1 uc2 uc1' uc2', 
    (forall stm stp, P stm stp -> (ube1<[-]> stm stp <-> ~(ube2<[+]> stm stp))) -> 
    derivable (fun stm stp => (P stm stp /\ ube1<[-]> stm stp)) <{uc1 ∓ uc2'}> Q -> 
    derivable (fun stm stp => (P stm stp /\ ~ube1<[-]> stm stp)) <{uc2 ∓ uc1'}> Q -> 
    derivable P <{if ube1 then uc1 else uc2 end ∓ if ube2 then uc1' else uc2' end}> Q
  | BHL_Skip_Asgn : forall Q X e, 
    derivable (bivAssertion_sub_new X e Q) <{skip ∓ X := e}> Q 
  | BHL_Asgn_Skip : forall Q X e, 
    derivable (bivAssertion_sub_old X e Q) <{X := e ∓ skip}> Q 
  | BHL_Skip_Seq : forall uc1 uc2 P Q R, 
    derivable P <{skip ∓ uc1}> R -> 
    derivable R <{skip ∓ uc2}> Q -> 
    derivable P <{skip ∓ (uc1 ; uc2)}> Q
  | BHL_Seq_Skip : forall uc1 uc2 P Q R, 
    derivable P <{uc1 ∓ skip}> R -> 
    derivable R <{uc2 ∓ skip}> Q -> 
    derivable P <{(uc1 ; uc2) ∓ skip}> Q
  | BHL_One_Side_If_L : forall P Q eb c1 c2 cp,
    derivable (fun stm stp => P stm stp /\ eval_in_old eb stm stp) <{c1 ∓ cp}> Q ->
    derivable (fun stm stp => P stm stp /\ ~(eval_in_old eb stm stp)) <{c2 ∓ cp}> Q ->
    derivable P <{if eb then c1 else c2 end ∓ cp}> Q
  | BHL_One_Side_If_R : forall P Q eb c1 c2 cp,
    derivable (fun stm stp => P stm stp /\ eval_in_new eb stm stp) <{cp ∓ c1}> Q ->
    derivable (fun stm stp => P stm stp /\ ~(eval_in_new eb stm stp)) <{cp ∓ c2}> Q ->
    derivable P <{cp ∓ if eb then c1 else c2 end}> Q
  | BHL_One_Side_While_L : forall ube uc I, 
    derivable (I /\ ube<[-]>) <{uc ∓ skip}> (I) -> 
    derivable I <{while ube do uc end ∓ skip}> (I /\ ~ube<[-]>)
  | BHL_One_Side_While_R : forall ube uc I, 
    derivable (I /\ ube<[+]>) <{skip ∓ uc}> (I) -> 
    derivable I <{skip ∓ while ube do uc end}> (I /\ ~ube<[+]>)
  | BHL_Seq : forall P Q R bc1 bc2, 
    derivable P bc1 R -> derivable R bc2 Q -> derivable P <{bc1 ;; bc2}> Q
  | BHL_If : forall P Q ube bc1 bc2, 
    derivable (P /\ ube<[-]> /\ ube<[+]>) bc1 Q -> 
    derivable (P /\ ~ube<[-]> /\ ~ube<[+]>) bc2 Q -> 
    derivable P <{bif ube then bc1 else bc2 end}> Q
  | BHL_While : forall I eub bc,
    derivable (fun stm stp => I stm stp /\ eval_in_old eub stm stp /\ eval_in_new eub stm stp) bc I -> 
    derivable I <{ bwhile eub do bc end }> (fun stm stp => I stm stp /\ ~(eval_in_old eub stm stp) /\ ~(eval_in_new eub stm stp))
  | BHL_Single : forall P Q uc, 
    derivable P <{uc ∓ uc}> Q -> 
    derivable P <{[uc]}> Q.


Definition valid (P : BivAssertion) (bc : bivCom) (Q : BivAssertion) : Prop := 
  forall stm stp stm' stp', 
    bivComEval stm stp bc stm' stp' -> P stm stp -> Q stm' stp'. 

(* proof *)
Theorem bhl_sound : forall P bc Q, 
  derivable P bc Q -> valid P bc Q. 
Proof. 
  intros P bc Q X. induction X. 
  - eapply consq; eauto. 
  - eapply rhl_double_asgn.
  - eapply rhl_double_asgn_forward. 
  - eapply rhl_double_skip.
  - eapply rhl_double_seq; eauto. 
  - eapply rhl_double_while; eauto. 
  - eapply rhl_double_if; eauto. 
  - eapply rhl_double_if_opp; eauto. 
  - eapply rhl_skip_asgn. 
  - eapply rhl_asgn_skip. 
  - eapply rhl_skip_seq; eauto. 
  - eapply rhl_seq_skip; eauto. 
  - eapply rhl_one_side_if_l; eauto.
  - eapply rhl_one_side_if_r; eauto.
  - eapply rhl_one_side_while_l; eauto.
  - eapply rhl_one_side_while_r; eauto.
  - eapply bhl_seq; eauto. 
  - eapply bhl_if; eauto. 
  - eapply bhl_while; eauto. 
  - unfold valid. intros. rewrite single_is_double_same in H. eauto. 
Qed. 


(* ---------------------------- *)
(* --------- COMPLETE --------- *)
(* ---------------------------- *)

(* 

completeness only for bwhile, bif, and biversional seq 
all other commands require that they evaluate in lockstep,
so we cannot prove completeness

this is also partial given that they terminate, 
as defned in valid 

*)


Lemma BHL_Conseq_pre : forall (P Q P': BivAssertion) c,
    derivable P' c Q ->
    (forall stm stp, P stm stp -> P' stm stp) ->
    derivable P c Q.
Proof. eauto using BHL_Consq. Qed.

Lemma BHL_Conseq_post  : forall (P Q Q' : BivAssertion) c,
    derivable P c Q' ->
    (forall stm stp, Q' stm stp -> Q stm stp) ->
    derivable P c Q.
Proof. eauto using BHL_Consq. Qed. 

Definition wp (bc: bivCom) (Q: BivAssertion) : BivAssertion := 
  fun stm stp => forall stm' stp', bivComEval stm stp bc stm' stp' -> Q stm' stp'. 

Hint Unfold wp : core.
Hint Constructors bivComEval : core.

Theorem wp_is_precondition : forall bc Q, 
  {{wp bc Q}} bc {{Q}}. 
Proof. 
  intros. unfold wp. unfold valid_bivHoare_triple. intros. apply H0. assumption. 
Qed. 

Theorem wp_is_weakest : forall bc P' Q, 
  {{P'}} bc {{Q}} -> 
  P' ->> (wp bc Q).
Proof. 
  unfold "->>", valid_bivHoare_triple, wp. eauto. 
Qed. 

Lemma wp_biv_seq : forall P Q bc1 bc2, 
  derivable P bc1 (wp bc2 Q) -> 
  derivable (wp bc2 Q) bc2 Q -> 
  derivable P <{bc1 ;; bc2}> Q.
Proof. 
  intros. apply BHL_Seq with (wp bc2 Q); auto. 
Qed. 


Lemma wp_invariant : forall ubexpr bc Q, 
  valid (wp <{bwhile ubexpr do bc end}> Q /\ ubexpr<[-]> /\ ubexpr<[+]>) bc (wp <{bwhile ubexpr do bc end}> Q). 
Proof. 
  unfold valid, wp. intros. destruct H0. destruct H2. apply H0. apply BE_BCWhileTrueTrue with stm' stp'; assumption.  
Qed. 


Theorem bhl_partially_complete: forall P (bc : bivCom) Q,
  valid P bc Q -> derivable P bc Q.
Proof.
  unfold valid. intros P bc. generalize dependent P.  
  induction bc; intros. 
  - admit. (* single... need to ensure lockstep for this too *)
  - admit. (* split *)
  - apply wp_biv_seq. 
    + apply IHbc1. eauto.
    + apply IHbc2. eauto. 
  - apply BHL_If. 
    + apply IHbc1. intros. apply H with (stm := stm) (stp := stp).
      * unfold eval_in_new, eval_in_old in H1. destruct H1. destruct H2. apply BE_BCIfTrueTrue; eauto. 
      * destruct H1. assumption. 
    + apply IHbc2. intros. apply H with (stm := stm) (stp := stp). 
      * unfold eval_in_new, eval_in_old in H1. repeat rewrite not_true_iff_false in H1. destruct H1. destruct H2. 
        apply BE_BCIfFalseFalse; eauto. 
      * destruct H1; assumption. 
  - eapply BHL_Conseq_post. 
    + eapply BHL_Conseq_pre. 
      * apply BHL_While. apply IHbc. apply wp_invariant. 
      * intros. unfold wp. intros. eapply H. 
        { apply H1. }
        { assumption. }
    + intros. destruct H0. unfold wp in H0. eapply H0. 
      destruct H1. unfold eval_in_new, eval_in_old in *. rewrite not_true_iff_false in *.  
      apply BE_BCWhileFalseFalse; assumption. 
Admitted. 
(* admitted all cases except bwhile, bif, and bseq *)


(* ---------------------------- *)
(* --------- EXAMPLES --------- *)
(* ---------------------------- *)
(* 
not too many interesting things can be proven because we are requiring the loops 
to evaluate in lockstep to evaluate, and the proof system is only relatively complete
w.r.t commands evaluating and loops evaluating in lockstep. 
Split loops must evaluate in lockstep for us to prove anything about them, and bwhile 
loops must evaulate in lockstep to evaluate. I give some examples of these limitations below
*)


(* ************* 0 ************ *)

(* some small examples *)

(* double asgn *)
Example double_asgn_ex0_p : {{True}} X := 3 ∓ Y := 4 {{ XM = YP - 1}}.
Proof. 
  eapply consq_pre.
  - eapply rhl_double_asgn.
  - bivAssertion_auto. 
Qed. 

(* double skip *)
Example dobule_skip_ex0_p : {{XM = 42}} skip ∓ skip {{XM = 42}}.
Proof. 
  apply rhl_double_skip. 
Qed. 

(* double seq *)
Example double_seq_ex0_p : 
  {{YM = 4 /\ YP = 42}}
    (X := Y + 2 ; Y := 42) ∓ (X := 6 ; skip)
  {{XM = XP /\ YM = YP}}.
Proof. 
  eapply consq_pre. 
  - eapply rhl_double_seq. 
    + eapply rhl_double_asgn. 
    + eapply rhl_asgn_skip. 
  - bivAssertion_auto. unfold_strs. orig_vars. lia. 
Qed. 


(* double while *)
Example double_while_ex0_c : bivCom := 
<{
  [I := 1];;

    while (Y <> 0) do 
      I := I + Z;
      Y := Y - 1
    end
  ∓ 
    while (Y > 0) do 
      I := I + Z;
      Y := Y - 1
    end
}>. 

Example double_while_ex0_p : 
  {{YM = YP /\ ZM = ZP}} 
  double_while_ex0_c
  {{YM = YP /\ ZM = ZP /\ IM = IP}}.
Proof. 
  unfold double_while_ex0_c. eapply consq_post. 
  - apply bhl_seq with (R := (YM = YP /\ ZM = ZP /\ IM = IP)%BivAssertion). 
    + rewrite_single_bhl. eapply consq_pre. 
      * eapply rhl_double_asgn. 
      * bivAssertion_auto. 
    + eapply rhl_double_while. 
      * intros. unfold eval_in_new, eval_in_old. unfold_strs. orig_vars. orig_vars. destruct H. destruct H0. 
        rewrite H. destruct (stp "Y"%string).
        { easy. }
        { simpl. reflexivity. }
      * eapply rhl_double_seq with (R := (YM = YP /\ ZM = ZP /\ IM = IP)%BivAssertion). 
        { eapply consq_pre. 
          - eapply rhl_double_asgn. 
          - bivAssertion_auto. destruct H. destruct H. destruct H1. unfold_strs. orig_vars. 
            rewrite H. rewrite H1. rewrite H2. split; auto.  
        }
        { eapply consq_pre. 
          - eapply rhl_double_asgn. 
          - bivAssertion_auto. destruct H. destruct H0. unfold_strs. orig_vars. 
            rewrite H. rewrite H0. rewrite H1. split; auto. 
        }
  - bivAssertion_auto. 
Qed.  

Example double_if_ex0_c : bivCom :=
<{
    if(Y > 0) then 
      X := 4 
    else 
      X := 3 
    end
  ∓
    if(Y <> 0) then 
      X := 4 
    else 
      X := 3 
    end
}>. 

Example double_if_ex0_p :
  {{YM = YP}}
  double_if_ex0_c
  {{XM = XP}}.
Proof. 
  unfold double_if_ex0_c. eapply rhl_double_if. 
  - intros. unfold eval_in_new, eval_in_old. simpl in *. split; intros. 
    + rewrite <- H0. unfold_strs. orig_vars. rewrite H. 
      destruct (stp "Y"%string); simpl; reflexivity. 
    + unfold_strs. orig_vars. rewrite H.  
      destruct (stp "Y"%string). 
      * exfalso. contradict H0. rewrite not_true_iff_false. simpl. reflexivity.  
      * simpl. reflexivity. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn.
    + bivAssertion_auto. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn. 
    + bivAssertion_auto. 
Qed. 

(* opposite if *)

Example double_if_ex1_c : bivCom := 
<{
    if (X > 0) then 
      Y := 5
    else 
      Y := 4
    end
  ∓ 
    if (X <= 0) then 
      Y := 4
    else 
      Y := 5
    end
}>.

Example double_if_ex1_p : 
  {{XM = XP}}
  double_if_ex1_c
  {{YM = YP}}. 
Proof. 
  unfold double_if_ex1_c. apply rhl_double_if_opp. 
  - intros. unfold eval_in_new, eval_in_old. unfold_strs. orig_vars. orig_vars. 
    rewrite H. unfold negb. rewrite not_true_iff_false.  
    destruct (stp "X"%string <=? 0) eqn:H1.  
    + split; eauto; try (symmetry; eauto). 
    + split; eauto. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn. 
    + bivAssertion_auto. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn. 
    + bivAssertion_auto. 
Qed. 

(* one sided while *)
(* 
this is somewhat odd, because the program doesn't evaluate in lockstep 
but an obviously equivilant program does evaluate in lockstep, 
which allows us to do this 
*)
Example single_while_ex0_c : bivCom := 
<{
    while (Y <> 0) do 
      Y := Y - 1
    end
  ∓ 
    skip
}>.

Example single_while_ex0_p : 
  {{IM = IP}} 
  single_while_ex0_c
  {{IM = IP}}.
Proof. 
  unfold single_while_ex0_c. eapply consq_post. 
  - eapply rhl_one_side_while_l. 
    + eapply consq_pre. 
      * eapply rhl_asgn_skip. 
      * bivAssertion_auto. 
  - bivAssertion_auto. 
Qed. 


(* ************* 1 ************ *)
(* this is an example of a natural way to refactor programs *)

Example P : univCom := 
<{
  N := 2; 
  SUM := 0;
  I := 1;
  while (I <= N) do 
    if (I % 2 = 0) then
      SUM := SUM + I
    else
      skip
    end;
    I := I + 1
  end 
}>.

Lemma reduce_map_update_stm: (I !-> 3; SUM !-> 2; I !-> 2; I !-> 1; SUM !-> 0; N !-> 2) = (I !-> 3; SUM !-> 2; N !-> 2).
Proof. 
  rewrite t_update_permute.
  - rewrite t_update_shadow. rewrite t_update_shadow. rewrite t_update_permute. rewrite t_update_shadow. reflexivity. unfold I, SUM.  apply String.eqb_neq. reflexivity. 
  -  unfold I, SUM.  apply String.eqb_neq. reflexivity. 
Qed. 

(* evaluating of univCom *)
Example pProof: 
  empty_st =[P]=> (I !-> 3 ; SUM !-> 2 ; N !-> 2).
Proof. 
 unfold P.
  apply E_Seq with (N !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_Seq with (SUM !-> 0 ; N !-> 2).
    + apply E_Asgn. reflexivity. 
    + apply E_Seq with (I !-> 1; SUM !-> 0; N !-> 2).
      * apply E_Asgn. reflexivity. 
      * eapply E_WhileTrue.
        {reflexivity. }
        { apply E_Seq with (st' := (I !-> 1; SUM !-> 0; N !-> 2)) (st'' := (I !-> 2; I !-> 1; SUM !-> 0; N !-> 2) ). 
          - apply E_IfFalse.
            + reflexivity. 
            + apply E_Skip.
          - apply E_Asgn. reflexivity. 
        }
        { eapply E_WhileTrue. 
          - reflexivity. 
          - apply E_Seq with (st' := (SUM !-> 2; I !-> 2; I !-> 1; SUM !-> 0; N !-> 2)) (st'' := (I !-> 3; SUM !-> 2; I !-> 2; I !-> 1;  SUM !-> 0; N !-> 2) ). 
            + apply E_IfTrue. 
              * reflexivity. 
              * apply E_Asgn. reflexivity. 
            + apply E_Asgn. reflexivity.
          - rewrite reduce_map_update_stm. eapply E_WhileFalse. simpl. reflexivity. 
        }
Qed. 

Example POD : univCom := 
<{
  N := 2;
  SUM := 0;
  I := 0;
  while (I <= N) do 
    SUM := SUM + I;
    I := I + 2
  end
}>.

Lemma reduce_map_update_stp : (I !-> 4; SUM !-> 2; I !-> 2; SUM !-> 0; I !-> 0; SUM !-> 0; N !-> 2) = (I !-> 4; SUM !-> 2; N !-> 2).
Proof. 
  rewrite t_update_permute. 
  - rewrite t_update_shadow. rewrite t_update_permute. 
    + rewrite t_update_shadow. rewrite t_update_permute. 
      * rewrite t_update_shadow. rewrite t_update_permute. 
        { rewrite t_update_shadow. reflexivity. } 
        { unfold I, SUM.  apply String.eqb_neq. reflexivity. }
      * unfold I, SUM.  apply String.eqb_neq. reflexivity. 
    + unfold I, SUM.  apply String.eqb_neq. reflexivity. 
  - unfold I, SUM.  apply String.eqb_neq. reflexivity. 
Qed.

Example PodProof :  
  empty_st =[POD]=> (I !-> 4 ; SUM !-> 2 ; N !-> 2).
Proof. 
unfold POD.
  apply E_Seq with (N !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_Seq with (SUM !-> 0 ; N !-> 2).
    + apply E_Asgn. reflexivity. 
    + apply E_Seq with (I !-> 0; SUM !-> 0; N !-> 2).
      * apply E_Asgn. reflexivity. 
      * eapply E_WhileTrue.
        { reflexivity. }
        { apply E_Seq with (st' := (SUM !-> 0; I !-> 0; SUM !-> 0; N !-> 2)) (st'' := (I !-> 2; SUM !-> 0; I !-> 0; SUM !-> 0; N !-> 2) ). 
          - apply E_Asgn. eauto. 
          - apply E_Asgn. eauto.  
        }
        { eapply E_WhileTrue. 
          - reflexivity. 
          - apply E_Seq with (st' := (SUM !-> 2; I !-> 2; SUM !-> 0; I !-> 0; SUM !-> 0; N !-> 2)) (st'' := (I !-> 4;SUM !-> 2; I !-> 2; SUM !-> 0; I !-> 0; SUM !-> 0; N !-> 2) ). 
            + apply E_Asgn. eauto. 
            + apply E_Asgn. eauto. 
          - rewrite reduce_map_update_stp. eapply E_WhileFalse. eauto. 
        }
Qed. 


(* this is how we would represent those two programs as one biversional program *)
Example PODBiv : bivCom := 
<{
  [N := 2];;
  [SUM := 0];;
  I := 1 ∓ I := 0 ;;
  bwhile (I <= N) do 
      if (I % 2 = 0) then
        SUM := SUM + I
      else
        skip
      end
    ∓ 
      SUM := SUM + I
    ;;
    I := I + 1 ∓ I := I + 2
  end 
}>. 

Example podBivEvallProof: 
  bivComEval empty_st empty_st PODBiv (I !-> 3; SUM !-> 2; N !-> 2) (I !-> 4; SUM !-> 2; N !-> 2).
Proof. 
  unfold PODBiv. apply BE_BCSeq with (stm' := (N !-> 2)) (stp' := (N !-> 2)).
  - apply BE_BCUcom.
    + apply E_Asgn. reflexivity.  
    + apply E_Asgn. reflexivity. 
  - apply BE_BCSeq with (stm' := (SUM !-> 0 ; N !-> 2)) (stp' := (SUM !-> 0 ; N !-> 2)).
    + apply BE_BCUcom. 
      * apply E_Asgn. reflexivity. 
      * apply E_Asgn. reflexivity. 
    + apply BE_BCSeq with (stm' := (I !-> 1 ; SUM !-> 0 ; N !-> 2)) (stp' := (I !-> 0; SUM !-> 0 ; N !-> 2)).
      * apply BE_BCSplit. 
        { apply E_Asgn. reflexivity. }
        { apply E_Asgn. reflexivity. }
      * apply BE_BCWhileTrueTrue  with (stm' := (I !-> 2; I !-> 1 ; SUM !-> 0 ; N !-> 2)) (stp' := (I !-> 2 ; SUM !-> 0; I !-> 0; SUM !-> 0 ; N !-> 2)).
        { reflexivity. }
        { reflexivity. }
        { apply BE_BCSeq with (stm' := (I !-> 1 ; SUM !-> 0 ; N !-> 2)) (stp' := (SUM !-> 0 ; I !-> 0; SUM !-> 0 ; N !-> 2)).
          - apply BE_BCSplit. 
            + apply E_IfFalse. 
              * reflexivity. 
              * apply E_Skip. 
            + apply E_Asgn. reflexivity. 
          - apply BE_BCSplit.
            + apply E_Asgn. reflexivity. 
            + apply E_Asgn. reflexivity.
         }
        { apply BE_BCWhileTrueTrue with (stm' := (I !-> 3; SUM !-> 2; I !-> 2; I !-> 1 ; SUM !-> 0 ; N !-> 2)) (stp' := (I !-> 4; SUM !-> 2; I !-> 2 ; SUM !-> 0; I !-> 0; SUM !-> 0 ; N !-> 2)).
          - reflexivity. 
          - reflexivity. 
          - apply BE_BCSeq with (stm' := (SUM !-> 2; I !-> 2; I !-> 1 ; SUM !-> 0 ; N !-> 2)) (stp' := (SUM !-> 2; I !-> 2 ; SUM !-> 0; I !-> 0; SUM !-> 0 ; N !-> 2)).
            + apply BE_BCSplit. 
              * apply E_IfTrue. 
                { reflexivity. }
                { apply E_Asgn. reflexivity. }
              * apply E_Asgn. reflexivity. 
            + apply BE_BCSplit.
              * apply E_Asgn. reflexivity. 
              * apply E_Asgn. reflexivity. 
          - rewrite reduce_map_update_stm. rewrite reduce_map_update_stp. apply BE_BCWhileFalseFalse. 
            + reflexivity. 
            + reflexivity. 
        }
Qed. 

(* BivHl proof *)

(* 
this is not that interesting, but shows how we must make loops evaluate in lockstep and 
we can only match up states that in lockstep.
We also can't relate sums per iteration because there is no relation

Since we proved that this loop evaluates and soudness, we know that these biv assertions hold
*)

Example podBivLogicProof : {{True}} PODBiv {{((IM - 1) * 2 = IP)}}.
 Proof. 
  unfold PODBiv. eapply bhl_seq with (R := (NM = NP /\ NM = 2)%BivAssertion). 
   - eapply consq_pre.
    + rewrite rewrite_single_bhl. eapply rhl_double_asgn. 
    + bivAssertion_auto. 
  - eapply bhl_seq with (R := (SUMM = SUMP /\ NM = NP /\ NM = 2)%BivAssertion ). 
    + eapply consq_pre.
      * rewrite rewrite_single_bhl. eapply rhl_double_asgn. 
      * bivAssertion_auto.
    + eapply bhl_seq with (R := (IP % 2 = 0 /\ IM = IP + 1 /\ SUMM = SUMP /\ NM = NP /\ NM = 2 /\ IP = 0 /\ IM = 1)%BivAssertion ).
      * eapply consq_pre. 
        { eapply rhl_double_asgn.  }
        { bivAssertion_auto.   }
      * eapply consq_pre with (P' := (((IM - 1) * 2 = IP) /\ 1 <= IM )%BivAssertion).
        { eapply consq_post with (Q' := ((((IM - 1) * 2 = IP ) /\ (1 <= IM))   /\ ~(( <{I <=
          N}> )<[-]>) /\ ~( BLe (EVar I)(EVar N) )<[+]>)%BivAssertion). 
          - eapply bhl_while with (I := (((IM - 1) * 2 = IP ) /\ (1 <= IM) )%BivAssertion). 
            eapply bhl_seq with (R := (((IM - 1) * 2 = IP  ) /\ (1 <= IM))%BivAssertion). 
            + eapply rhl_one_side_if_l. 
              * eapply consq_pre. 
                { eapply rhl_double_asgn.  }
                { bivAssertion_auto.  }
              * eapply consq_pre. 
                { eapply rhl_skip_asgn. }
                { bivAssertion_auto. }
            + eapply consq_pre.  
              * eapply rhl_double_asgn.
              * bivAssertion_auto. unfold I. orig_vars. destruct H. rewrite <- H. split. 
                { bivAssertion_auto. }
                { lia.  }   
          - bivAssertion_auto. 
        }
        { bivAssertion_auto. }
Qed.  

(* something interesting... *)
(* if we put something impossible in the post condition... we can prove it if we are clever *)
(* the false part here is with the %s, because /\ has higher precedence that -> *)

Example podBivLogicProofFalse : {{True}} PODBiv {{IM % 2 = 0 -> (SUMM = SUMP) /\ IM % 2 = 1 -> (SUMM = SUMP + 25 /\ IM = IP + 1) /\ IP % 2 = 0}}.
 Proof. 
  unfold PODBiv. eapply bhl_seq with (R := (NM = NP /\ NM = 2)%BivAssertion ). 
   - eapply consq_pre.
    + rewrite rewrite_single_bhl. eapply rhl_double_asgn.  
    + bivAssertion_auto. 
  - eapply bhl_seq with (R := (SUMM = SUMP /\ NM = NP /\ NM = 2)%BivAssertion ). 
    + eapply consq_pre.
      * rewrite rewrite_single_bhl. eapply rhl_double_asgn.  
      * bivAssertion_auto.
    + eapply bhl_seq with (R := (IP % 2 = 0 /\ IM = IP + 1 /\ SUMM = SUMP /\ NM = NP /\ NM = 2 /\ IP = 0 /\ IM = 1)%BivAssertion ).
      * eapply consq_pre. 
        { eapply rhl_double_asgn.  }
        { bivAssertion_auto.   }
      * eapply consq_pre with (P' := (IM % 2 = 0 -> (SUMM = SUMP /\ IM = IP) /\ IM % 2 = 1 -> (SUMM = SUMP + 25 /\ IM = IP + 1) /\ IP % 2 = 0)%BivAssertion).
        { eapply consq_post with (Q' := ((IM % 2 = 0 -> (SUMM = SUMP /\ IM = IP) /\ IM % 2 = 1 -> (SUMM = SUMP + 25 /\ IM = IP + 1) /\ IP % 2 = 0) /\ ~(( <{I <=
N}> )<[-]>) /\ ~( BLe (EVar I)(EVar N) )<[+]>)%BivAssertion). 
          - eapply bhl_while with (I := (IM % 2 = 0 -> (SUMM = SUMP /\ IM = IP) /\ IM % 2 = 1 -> (SUMM = SUMP + 25 /\ IM = IP + 1) /\ IP % 2 = 0)%BivAssertion). 
            eapply bhl_seq with (R := ((IM % 2 = 0 -> (SUMM = SUMP /\ IM = IP) /\ IM % 2 = 1 -> (SUMM = SUMP + 25 /\ IM = IP + 1) /\ IP % 2 = 0))%BivAssertion). 
            + eapply rhl_one_side_if_l. 
              * eapply consq_pre. 
                { eapply rhl_double_asgn.  }
                { bivAssertion_auto. }
              * eapply consq_pre. 
                { eapply rhl_skip_asgn. }
                { bivAssertion_auto. }
            + eapply consq_pre. 
              * eapply rhl_double_asgn.
              * bivAssertion_auto. 
          - bivAssertion_auto. 
        } 
        { bivAssertion_auto. }
Qed. 


(* ************* 2 ************ *)

(* single if examples *)
(* this is a piece of the above example, but actually proves something somewhat more interesting *)

Example singleif_ex0 : bivCom := 
<{      
    if (I % 2 = 0) then
      SUM := SUM + I
    else
      skip
    end
  ∓ 
    SUM := SUM + I
}>.

Example singleif_ex0_proof0 : 
  {{SUMM = SUMP /\ IM = IP}} singleif_ex0 {{IM % 2 = 0 -> SUMM = SUMP /\ IM = IP}}.
Proof. 
  unfold singleif_ex0. eapply rhl_one_side_if_l. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn.   
    + bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H. rewrite H2. rewrite H. split. 
      * reflexivity. 
      * reflexivity. 
  - eapply consq_pre. 
    + eapply rhl_skip_asgn.   
    + bivAssertion_auto. orig_vars. destruct H. exfalso. contradict H1.  apply H0. 
Qed. 

(* or more specifically... *)

Example singleif_ex0_proof1 : 
  {{IM % 2 = 0 -> (SUMM = SUMP /\ IM = IP)}} singleif_ex0 {{IM % 2 = 0 -> SUMM = SUMP /\ IM = IP}}.
Proof. 
  unfold singleif_ex0. eapply rhl_one_side_if_l. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn.   
    + bivAssertion_auto. destruct H. rewrite H0 in H. destruct H. 
      * reflexivity. 
      * split.
        { unfold_strs. orig_vars. rewrite H2. rewrite H. reflexivity. } 
        {assumption.  }
  - eapply consq_pre. 
    + eapply rhl_skip_asgn.   
    + bivAssertion_auto. destruct H. orig_vars. exfalso. contradict H1. assumption. 
Qed. 

(* ************* 3 ************ *)

(* 
this is an example of a relation that can be proved, but the command will never evaluate
demonstraiting the partial completeness. In this example, we show how these semantics introduce another
form of not evaluating for while loops... the guard for a bwhile does not evaluate to the same boolean in both states
*)

Example bwhile_ex0 : bivCom :=
<{
  bwhile(I <= N) do 
      SUM := SUM + I * 2
    ∓ 
      SUM := SUM + I
  ;; 
      I := I + 1
    ∓
      I := I + 2
  end
}>.

(* we can prove... *)
(* because the sums are always the same for each iteration *)
Theorem bwhile_ex0_proof0 : 
  {{SUMM = SUMP /\ IM = 0 /\ IP = 0}} bwhile_ex0 {{SUMM = SUMP}}.
Proof. 
  eapply consq_post. eapply consq_pre. 
  - eapply bhl_while with (I := (SUMM = SUMP /\ IP = IM * 2)%BivAssertion). eapply bhl_seq with (R := (SUMM = SUMP /\ IP = IM * 2)%BivAssertion). 
    + eapply consq_pre. 
      * eapply rhl_double_asgn. 
      * bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H. split. 
        { rewrite H. rewrite H1. reflexivity. }  
        { rewrite H1.  reflexivity. }
    + eapply consq_pre. 
      * eapply rhl_double_asgn. 
      * bivAssertion_auto. unfold I. orig_vars. destruct H. rewrite H. rewrite H0. split. 
        { reflexivity. }
        { lia. }
  - bivAssertion_auto. 
  - bivAssertion_auto. 
Qed. 

(* but this loop clearly does not evaluate *)
Example bwhile_ex0_eval: 
  bivComEval (SUM !-> 0; I !-> 0; N !-> 3) (SUM !-> 0; I !-> 0; N !-> 3) bwhile_ex0 (SUM !-> 6; I !-> 4; N !-> 3) (SUM !-> 2; I !-> 4; N !-> 3). 
Proof. 
  unfold bwhile_ex0. eapply BE_BCWhileTrueTrue.
  - reflexivity. 
  - reflexivity. 
  - eapply BE_BCSeq. 
    + eapply BE_BCSplit. 
      * eapply E_Asgn. reflexivity. 
      * eapply E_Asgn. reflexivity. 
    + eapply BE_BCSplit. 
      * eapply E_Asgn. reflexivity. 
      * eapply E_Asgn. reflexivity. 
  - eapply BE_BCWhileTrueTrue.
    + reflexivity. 
    + reflexivity. 
    + eapply BE_BCSeq. 
      * eapply BE_BCSplit.
        { eapply E_Asgn. reflexivity. }
        { eapply E_Asgn. reflexivity. }
      * eapply BE_BCSplit. 
        { eapply E_Asgn. reflexivity. }
        { eapply E_Asgn. reflexivity. }
    + eapply BE_BCWhileTrueTrue. 
      * reflexivity.  
      * simpl. (* gets to false = true because this never evals *) admit.  
      * admit. 
      * admit. 
Admitted. 

(* another interesting example of where one could go wrong *)
(* here, we are assuming something impossible b/c nats cannot be negative, this allows us to prove anything *)
Example double_asgn_ex_wrong_proof : {{(XM = 1 /\ XP = 3) -[X |-> X + 2]+[X |-> X + 3]}}
<{X := X + 2 ∓ X := X + 3}>
{{XM + 45 = XP}}.
Proof. 
  eapply consq_pre. 
  - eapply rhl_double_asgn. 
  - unfold "->>", bivAssertion_sub_new, bivAssertion_sub_old, t_update; simpl. intros. destruct H. rewrite H. rewrite H0. 
    lia. 
Qed. 

(* ************* 4 ************ *)
(* more double asng examples *)

Example double_asgn_ex1_proof : {{XM = XP}} X:= X * 2 ∓ X := X + X {{ XM = XP}}.
Proof. 
  eapply consq_pre.
  - eapply rhl_double_asgn.
  - bivAssertion_auto. unfold_strs. orig_vars. lia. 
Qed. 

Example double_asgn_ex2_proof : {{True}} X:= 3 ∓ Y := 4 {{ XM = YP - 1}}.
Proof. 
  eapply consq_pre.
  - eapply rhl_double_asgn.
  - bivAssertion_auto. 
Qed. 

Example double_asgn_ex3_proof : {{XM + 1 = XP}} <{X := X + 2 ∓ X := X + 3}> {{XM + 2 = XP}}.
Proof. 
  eapply consq_pre. 
    - eapply rhl_double_asgn. 
    - bivAssertion_auto. unfold_strs. orig_vars. rewrite <- H. lia. 
Qed. 

(* ************* 5 ************ *)

(* comparing biversional if with double if *)

Example bif_ex0 : bivCom := 
<{
  bif (X <= 10) then 
    Y := Y + 1 ∓ Y := Y + 2
  else 
    skip ∓ Y := Y + 2
  end
}>. 

Example bif_ex0_proof :
  {{XM = XP /\ YP = YM}} bif_ex0 {{(XM <= 10 -> YM = YP - 1) /\ (~(XM <= 10) -> YM = YP - 2)}}.
Proof. 
  unfold bif_ex0. eapply bhl_if. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn.
    + bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H. lia. 
  - eapply consq_pre. 
    + eapply rhl_skip_asgn. 
    + bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H. destruct H0. split. 
      * intros. easy.  
      * rewrite H1. lia.   
Qed. 

Example double_if_ex0 : bivCom := 
<{
    if (X <= 10) then 
      Y := Y + 1
    else 
      skip
    end
  ∓
    if (X <= 10) then 
      Y := Y + 2
    else 
      Y := Y + 2
    end
}>. 

Example double_if_ex0_proof : 
  {{XM = XP /\ YP = YM}} double_if_ex0 {{(XM <= 10 -> YM = YP - 1) /\ (~(XM <= 10) -> YM = YP - 2)}}.
Proof. 
  unfold double_if_ex0. eapply rhl_double_if. 
  - intros. unfold eval_in_new, eval_in_old. simpl in *. 
    unfold_strs. orig_vars. destruct H. rewrite H. reflexivity. 
  - eapply consq_pre. 
    + eapply rhl_double_asgn.
    + bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H. lia. 
  - eapply consq_pre. 
    + eapply rhl_skip_asgn. 
    + bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H. split. 
      * intros. easy. 
      * lia.
Qed. 
(* we can see there is one more step making it a little longer *)
(* however, we can only use bif if the guards do not change *)

(* ************* 6 ************ *)

(* a pretty interesting example that uses both 
single while, and sequence skip 
*)

Example single_while_ex1_c : bivCom := 
<{
    while (Y <> 0) do 
      I := I + 1; 
      Y := Y - 1
    end
  ∓ 
    skip
}>.

(* 

given that YP = YM = IM = IP /\ these are greater than or equal to 1

then, 

we show that the final value of IM (which was getting incremented each loop iteration)
is equal to the unchanged YP and IP values added. 

*)

Example single_while_ex1_p : 
  {{YP = YM /\ IM = IP /\ YP = IP /\ IM >= 1}} 
  single_while_ex1_c
  {{IM = YP + IP}}.
Proof. 
  unfold single_while_ex1_c. eapply consq_post. 
  - eapply consq_pre with (P' := (IM + YM = YP + IP /\ IP = YP /\ IM >= 1)%BivAssertion). 
    + eapply rhl_one_side_while_l. eapply rhl_seq_skip with (R := ((IM - 1) + YM = YP + IP /\ IP = YP /\ YM >= 1 /\ IM >= 1)%BivAssertion).
      * eapply consq_pre. 
        { eapply rhl_asgn_skip. }
        { bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H. destruct H1. split.  
          - rewrite H1 in *. rewrite <- H. lia. 
          - split.  
            + assumption.
            + destruct (stm "Y"%string). 
              * easy. 
              * lia. 
        }
      * eapply consq_pre. 
        { eapply rhl_asgn_skip. }
        { bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H0. destruct H1.    
          rewrite H0 in *. clear H0. split.  
          - rewrite <- add_sub_swap in H.
            + rewrite <- add_sub_assoc in H.
              * assumption. 
              * assumption.  
            + assumption. 
          - split.  
            + reflexivity. 
            + assumption. 
        }
    + bivAssertion_auto. 
  - bivAssertion_auto. destruct H. destruct H. destruct H1. 
    unfold_strs. orig_vars. destruct (stm "Y"%string).
    + rewrite add_0_r in H. assumption. 
    + unfold negb in H0. simpl in H0. easy. 
Qed. 

(* ************* 7 ************ *)

(* 
an example to compute the exponential of a number 
refactored by changing the loop guard
*)

Fixpoint exp (z : nat) (e : nat) : nat :=
match e with 
| 0 => 1
| S n => z * exp(z) (n)
end.

Lemma exp_succ : forall z n : nat, 
  exp (z) (n) * z = exp (z) (S n).
Proof. 
  intros. simpl. rewrite mul_comm. reflexivity. 
Qed. 

Lemma exp_pred : forall z y : nat, 
  y > 0 -> 
  exp (z) (pred y) * z = exp (z) (y). 
Proof. 
  intros. simpl. destruct y. 
  - easy. 
  - rewrite <- exp_succ. simpl. reflexivity. 
Qed. 

Lemma exp_succ_m : forall z x n i : nat, 
  x - n > 0 -> 
  exp (z) (x - S n) * z = exp (z) (x - n).
Proof.
  intros. assert (x - S n = pred (x - n)). 
  - lia. 
  - rewrite H0. rewrite exp_pred. 
    + reflexivity.  
    + assumption.
Qed. 

(* double while *)
Example double_while_ex1_c : bivCom := 
<{
  [I := 1];;
  [Y := X] ;; 
    while (Y <> 0) do 
      I := I * Z;
      Y := Y - 1
    end
  ∓ 
    while (Y > 0) do 
      I := I * Z;
      Y := Y - 1
    end
}>. 

Example double_while_ex1_p : 
  {{XM = XP /\ ZM = ZP /\ XM > 0}} 
  double_while_ex1_c
  {{fun stm stp : state => 
    ((beeval stm stp (BEVarOld Y)) = (beeval stm stp (BEVarNew Y))) /\ 
    ((beeval stm stp (BEVarOld Z)) = (beeval stm stp (BEVarNew Z))) /\
    ((beeval stm stp (BEVarOld I)) = (beeval stm stp (BEVarNew I))) /\
    exp (beeval stm stp (BEVarOld Z)) (beeval stm stp (BEVarOld X)) = 
    beeval stm stp (BEVarOld I)    
  }}.
Proof. 
  unfold double_while_ex1_c. eapply consq_post. 
  - apply bhl_seq with (R := (XM = XP /\ ZM = ZP /\ XM > 0 /\ IM = IP /\ IM = 1)%BivAssertion). 
    + rewrite_single_bhl. eapply consq_pre. 
      * eapply rhl_double_asgn. 
      * bivAssertion_auto. 
    + apply bhl_seq with 
      (R := (XM = XP /\ ZM = ZP /\ XM >= YM /\ IM = IP /\ YM = YP /\ IM = 1 /\ YM = XM)%BivAssertion). 
      * eapply consq_pre. 
        { rewrite_single_bhl. eapply rhl_double_asgn. }
        { bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H0.
          destruct H1. lia. 
        }
      * eapply consq_pre with (P' := fun stm stp => (((beeval stm stp (BEVarOld X)) = (beeval stm stp (BEVarNew X))) /\ 
                                     ((beeval stm stp (BEVarOld Z)) = (beeval stm stp (BEVarNew Z))) /\
                                     ((beeval stm stp (BEVarOld X)) >= (beeval stm stp (BEVarOld Y))) /\
                                     ((beeval stm stp (BEVarOld I)) = (beeval stm stp (BEVarNew I))) /\
                                     ((beeval stm stp (BEVarOld Y)) = (beeval stm stp (BEVarNew Y))) /\
                                     (beeval stm stp (BEVarOld I)) = (exp (beeval stm stp (BEVarOld Z)) 
                                     (beeval stm stp (BEMinus (BEVarOld X) (BEVarOld Y)))
                                     ))).
        { eapply rhl_double_while. 
          - bivAssertion_auto. destruct H. destruct H0. destruct H1.
            destruct H2. destruct H3. rewrite H3. clear. destruct (stp Y); simpl; reflexivity. 
          - eapply rhl_double_seq 
            with (R := fun stm stp => (((beeval stm stp (BEVarOld X)) = (beeval stm stp (BEVarNew X))) /\ 
                       ((beeval stm stp (BEVarOld Z)) = (beeval stm stp (BEVarNew Z))) /\
                       ((beeval stm stp (BEVarOld X)) >= (beeval stm stp (BEVarOld Y))) /\
                       ((beeval stm stp (BEVarOld I)) = (beeval stm stp (BEVarNew I))) /\
                       ((beeval stm stp (BEVarOld Y)) = (beeval stm stp (BEVarNew Y))) /\
                       (beeval stm stp (BEVarOld I)) = (exp (beeval stm stp (BEVarOld Z)) 
                       (beeval stm stp (BEMinus (BEVarOld X) ( BEMinus (BEVarOld Y) (BENum 1))))
                       ))).
            + eapply consq_pre. 
              * eapply rhl_double_asgn. 
              * bivAssertion_auto. destruct H. destruct H. destruct H1. 
                destruct H2. destruct H3. destruct H4. split.
                { assumption. }   
                { split.  
                  - assumption. 
                  - split. 
                    + assumption. 
                    + split. 
                      * lia. 
                      * split. 
                        { assumption. }
                        { rewrite H5. destruct (stm Y).  
                          - easy. 
                          - rewrite exp_succ_m. 
                            + rewrite sub_succ. rewrite sub_0_r. reflexivity. 
                            + eauto. 
                            + lia.  
                        }
                }
            + eapply consq_pre. 
              * eapply rhl_double_asgn. 
              * bivAssertion_auto.  
        }
        { bivAssertion_auto. unfold_strs. orig_vars. destruct H. destruct H0. 
          destruct H1. destruct H2. destruct H3. destruct H4. split. 
          - assumption. 
          - split. 
            + assumption. 
            + split. 
              * assumption. 
              * split. 
                { assumption. }
                { split. 
                  - assumption. 
                  - rewrite H4. rewrite H5. rewrite sub_diag. simpl. reflexivity.  
                }
        }
  - bivAssertion_auto. unfold_strs. destruct H. destruct H. destruct H1. 
    destruct H2. destruct H3. destruct H4. split. 
    + assumption. 
    + split. 
      * assumption. 
      * split. 
        { assumption. }   
        { destruct (stm "Y"%string). 
          - rewrite sub_0_r in H5. auto.  
          - easy. 
        }
Qed.  