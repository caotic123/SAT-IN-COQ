Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.FinFun.
Require Import  Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Export ListNotations.
From Coq Require Import ssreflect ssrfun ssrbool.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
From Coq Require Import Lia.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Lists.List.
Require Import FunInd.
Require Import Coq.Init.Nat.
From Hammer Require Import Tactics.


Definition Finite A := {l : list A & Full l}.
Definition EqDec A := forall n m : A, {n = m} + {n <> m}.

Class Symbol (A : Set) := {
    finite : Finite A;
    eq_dec : EqDec A;
}.

Definition Mapping A := A -> bool.

Inductive Formula {A : Set} {S : Symbol A} := 
    |FTop : Formula
    |FBottom : Formula
    |Literal : A -> Formula
    |And : Formula -> Formula -> Formula
    |Or : Formula -> Formula -> Formula
    |Neg : Formula -> Formula.

Inductive EVALUATION {A} {S : Symbol A} (M : Mapping A) : Formula -> bool -> Prop :=
    |ETop : EVALUATION M FTop true
    |EBottom : EVALUATION M FBottom false 
    |ELiteral : forall (s : A), EVALUATION M (Literal s) (M s)
    |EAnd : forall F F' b b', 
        EVALUATION M F b -> EVALUATION M F' b' -> EVALUATION M (And F F') (b && b')
    |EOR : forall F F' b b', 
        EVALUATION M F b -> EVALUATION M F' b' -> EVALUATION M (Or F F') (b || b')
    |ENeg : forall F b, EVALUATION M F b -> EVALUATION M (Neg F) (negb b).


Definition Satisfability {A} {S : Symbol A} F := exists (M : Mapping A), EVALUATION M F true. 
Definition UNSatisfability {A} {S : Symbol A} F := forall (M : Mapping A), EVALUATION M F false. 
Definition UNSatisfability2 {A} {S : Symbol A} F := ~ (Satisfability F). 

Theorem conflict_theorem : forall {A} {S : Symbol A} F (M : Mapping A) b, 
    EVALUATION M F b -> ~ EVALUATION M F (negb b).
intros.
move => H'.
dependent induction H.
inversion H'.
inversion H'.
inversion H'.
destruct (M s).
inversion H.
inversion H.
dependent destruction H'.
assert (b0 = ~~ (b && b') \/ b'0 = ~~ (b && b')).
generalize dependent (b && b').
intros.
destruct b0.
destruct b1.
by right.
by right.
by left.
destruct H1.
rewrite H1 in H'1.
destruct b.
destruct b'.
auto.
destruct b'0.
auto.
by destruct b0.
auto.
destruct b'0.
destruct b.
by destruct b'.
by destruct b0.
destruct b.
by destruct b'.
by destruct b0.
dependent destruction H'.
assert (b0 = ~~ (b || b') \/ b'0 = ~~ (b || b')).
generalize dependent (~~ (b || b')).
intros.
destruct b0.
destruct b1.
by left.
by right.
by right.
destruct H1.
rewrite H1 in H'1.
destruct b.
destruct b'.
auto.
auto.
destruct b'.
rewrite H1 in x.
destruct b'0.
inversion x.
auto.
auto.
destruct b0.
rewrite <- x in H1.
subst.
destruct b.
auto.
auto.
destruct b.
auto.
by subst.
inversion H'.
destruct b0.
destruct b.
auto.
auto.
by destruct b.
Qed.

Theorem EVALUATION_dec : forall {A} {S : Symbol A} F (M : Mapping A), exists b, EVALUATION M F b.
intros.
induction F.
exists true; constructor.
exists false; constructor.
exists (M a); constructor.
destruct IHF1.
destruct IHF2.
exists (x && x0).
by constructor.
destruct IHF1.
destruct IHF2.
exists (x || x0).
by constructor.
destruct IHF.
exists (negb x).
by constructor.
Qed.

Theorem unsatisfibility_equiv : forall {A} {S : Symbol A} F, UNSatisfability F <-> UNSatisfability2 F.
intros.
unfold UNSatisfability. unfold UNSatisfability2. unfold Satisfability.
constructor.
move => U U'.
destruct U'.
set (U x).
destruct (conflict_theorem  _ _ _ e H).
intros.
pose (EVALUATION_dec F M).
destruct e.
destruct x.
destruct H.
by exists M.
assumption.
Qed.


Definition valid {A} {S : Symbol A} F := forall (M : Mapping A), EVALUATION M F true.
Definition entails {A} {S : Symbol A}F F' := forall (M : Mapping A), EVALUATION M F true -> EVALUATION M F' true.
Definition prop_equiv {A} {S : Symbol A} F F' := forall (M : Mapping A), EVALUATION M F true <-> EVALUATION M F' true.

Definition clause_size {A} {S : Symbol A} : Formula -> nat.
intros.
induction H.
exact 1.
exact 1.
exact 1.
exact (IHFormula1 + IHFormula2).
exact (max IHFormula1 IHFormula2).
exact IHFormula. 
Defined.

Definition is_conj {A} {S : Symbol A} : Formula -> Prop := fun F =>
   match F with
       |(And _ _ ) => True
       |_ => False
   end.

Definition conjuctive_form {A} {S : Symbol A} : Formula  -> Prop.
intros.
induction H.
exact True.
exact True.
exact True.
exact (IHFormula1 /\ IHFormula2 /\ ~ (is_conj H) /\ ~ (is_conj H0)).
exact (IHFormula1 /\ IHFormula2).
exact IHFormula. 
Defined.

Definition _2'SAT {A} {S : Symbol A} (F : Formula) := clause_size F = 2 /\ conjuctive_form F.

Example Example2Sat {A} {S : Symbol A} : _2'SAT (Or (And FTop FTop) FTop).
constructor.
constructor.
do 4! constructor.
auto.
auto.
Qed.

Example ExampleNot2Sat {A} {S : Symbol A} : ~ _2'SAT (And (And FTop FTop) FTop).
move => H.
inversion H.
inversion H0.
Qed.

Definition _3'SAT {A} {S : Symbol A} (F : Formula) := clause_size F = 3 /\ conjuctive_form F.

(* We define NP'HARD problems by the equiv of 3-sat *)

Definition section {A} {B} (f : A -> B) (g : B -> A) : Type :=
    forall b : B, f (g b) = b.

Definition retract {A} {B} (f : A -> B) (g : B -> A) : Type :=
    forall a : A, g (f a) = a.

Record Iso (A : Type) (B : Type) : Prop :=
   {
      f : A -> B;
      g : B -> A;
      rightInv : section f g;
      leftInv  : retract f g;
   }.

Definition NP'HARD {A} {S : Symbol A} (P : Prop) := exists F, _3'SAT F -> Iso (Satisfability F) P.

Inductive decision_procedure {A} {S : Symbol A} (f : Formula) :=
     | SAT : Satisfability f -> decision_procedure f
     | UNSAT : UNSatisfability f -> decision_procedure f.

Definition decision_procedure_fun {A} {S : Symbol A} := forall (f : Formula), decision_procedure f.

Definition evaluate {A} {S : Symbol A} (f : Formula) (M : Mapping A) : bool.
induction f.
(* FTop *)
exact true.
(* FBotoom *)
exact false.
(*ELiteral *)
exact (M a).
(*EAnd*)
exact (IHf1 && IHf2).
(*EOr*)
exact (IHf1 || IHf2).
(*ENeg*)
exact (negb IHf).
Defined.

Definition partial_eval_and {A} {S : Symbol A} (f : Formula) (f' : Formula) : Formula :=
    match f, f' with 
        |FTop, FTop => FTop
        |FBottom, _ => FBottom
        |_, FBottom => FBottom
        |_, _ => (And f f')
    end.

Definition partial_eval_or {A} {S : Symbol A} (f : Formula) (f' : Formula) : Formula :=
    match f, f' with 
        |FTop, _ => FTop
        |_, FTop => FTop
        |FBottom, FBottom => FBottom
        |_, _ => (Or f f')
    end.

Definition partial_eval_neg {A} {S : Symbol A} (f : Formula) : Formula :=
    match f with 
        |FTop => FBottom
        |FBottom => FTop
        |_ => (Neg f)
    end.

Definition is_norm {A} {S : Symbol A} (f : Formula) : bool :=
    match f with 
        |FTop => true
        |FBottom => true
        |_ => false
    end.


Definition partial_evaluate {A} {S : Symbol A} (f : Formula) (M : A -> option bool) : Formula.
induction f.
(* FTop *)
exact FTop.
(* FBotoom *)
exact FBottom.
(*ELiteral *)
destruct (M a).
destruct b.
exact FTop.
exact FBottom.
exact (Literal a). 
(*EAnd*)
exact (partial_eval_and IHf1 IHf2).
(*EOr*)
exact (partial_eval_or IHf1 IHf2).
(*ENeg*)
exact (partial_eval_neg IHf).
Defined.


Theorem norm_eval {A} {S : Symbol A} x M : is_norm x -> is_norm (partial_evaluate x M).
intros.
destruct x.
trivial.
trivial.
inversion H.
inversion H.
inversion H.
inversion H.
Qed.

Theorem norm_is_ftop_or_fbottom {A} {S : Symbol A} x : is_norm x = true -> x = FTop \/ x = FBottom.
intros.
destruct x.
by left.
by right.
inversion H.
inversion H.
inversion H.
inversion H.
Qed.

Theorem not_norm_is_ftop_or_fbottom {A} {S : Symbol A} x : is_norm x = false -> ~ x = FTop /\ ~ x = FBottom.
intros.
destruct x.
inversion H.
inversion H.
by constructor.
by constructor.
by constructor.
by constructor.
Qed.

Example test_eval {A} {S : Symbol A} :  evaluate (Or (And FTop FBottom) FTop) (fun x => false) = true.
by cbv.
Qed.

Example test_eval2 {A} {S : Symbol A} : partial_evaluate (And (And FTop FBottom) FTop) (fun x => Some(false)) = FBottom.
by cbv.
Qed.


Definition eval_is_normal  {A} {S : Symbol A} F (M : Mapping A) (M2 : A -> option bool) := 
   forall (M' : Mapping A), evaluate (partial_evaluate F M2) M' = evaluate F M.

Theorem fully_eval_is_normal {A} {S : Symbol A} F (M : Mapping A) : eval_is_normal F M (fun x => Some (M x)).
unfold eval_is_normal.
intros.
induction F.
trivial.
trivial.
simpl.
destruct (M a).
trivial.
trivial.
simpl in *.
generalize dependent (partial_evaluate F1 (fun x : A => Some (M x))).
generalize dependent (partial_evaluate F2 (fun x : A => Some (M x))).
intros.
rewrite <- IHF1.
rewrite <- IHF2.
remember (is_norm f0).
remember (is_norm f).
symmetry in Heqb.
symmetry in Heqb0.
destruct b.
destruct b0.
pose (norm_is_ftop_or_fbottom _ Heqb).
pose (norm_is_ftop_or_fbottom _ Heqb0).
destruct o.
destruct o0.
subst; trivial.
subst; trivial.
subst; trivial.
destruct (norm_is_ftop_or_fbottom _ Heqb).
destruct (not_norm_is_ftop_or_fbottom _ Heqb0).
subst.
destruct f.
trivial.
by contradiction H1.
trivial.
trivial.
trivial.
trivial.
subst; simpl; trivial.
destruct (not_norm_is_ftop_or_fbottom _ Heqb).
destruct b0.
destruct (norm_is_ftop_or_fbottom _ Heqb0).
destruct f.
destruct f0.
by [].
by [].
by [].
by [].
by [].
by [].
by [].
by [].
by [].
by [].
by [].
subst; simpl.
destruct f0.
by []. by []. 
simpl.
by rewrite Bool.andb_false_r.
by rewrite Bool.andb_false_r.
by rewrite Bool.andb_false_r.
by rewrite Bool.andb_false_r.
destruct f0.
by destruct f.
by destruct f.
by destruct f.
by destruct f.
by destruct f.
by destruct f.
simpl.
generalize dependent (partial_evaluate F1 (fun x : A => Some (M x))).
generalize dependent (partial_evaluate F2 (fun x : A => Some (M x))).
intros.
rewrite <- IHF1.
rewrite <- IHF2.
remember (is_norm f0).
remember (is_norm f).
symmetry in Heqb. symmetry in Heqb0.
destruct b.
destruct (norm_is_ftop_or_fbottom _ Heqb).
subst; by [].
destruct b0.
destruct (norm_is_ftop_or_fbottom _ Heqb0).
subst; by [].
subst; by [].
subst; simpl.
destruct (not_norm_is_ftop_or_fbottom _ Heqb0).
by destruct f.
destruct (not_norm_is_ftop_or_fbottom _ Heqb).
destruct b0.
destruct (norm_is_ftop_or_fbottom _ Heqb0).
subst; simpl.
destruct f0.
by []. by []. 
simpl.
by rewrite Bool.orb_true_r.
by rewrite Bool.orb_true_r.
by rewrite Bool.orb_true_r.
by rewrite Bool.orb_true_r.
subst; by destruct f0.
destruct (not_norm_is_ftop_or_fbottom _ Heqb0).
destruct f0; by destruct f.
simpl.
generalize dependent (partial_evaluate F (fun x : A => Some (M x))).
intros.
rewrite <- IHF.
by destruct f.
Qed.

Definition mapping_is_partially_defined {A} {B} {S : Symbol A} {M : A -> option B} :
   (forall x, {h & M x = Some h}) -> A -> B.
intros.
destruct (X H).
exact x.
Defined.

Require Import Coq.Logic.Eqdep_dec.

Theorem func_ext_evaluate {A} {S : Symbol A} F (M M': A -> option bool):
    (forall x, M x = M' x) -> partial_evaluate F M = partial_evaluate F M'.
intros.
induction F.
trivial.
trivial.
simpl; rewrite H; trivial.
simpl.
rewrite IHF1.
rewrite IHF2.
trivial.
simpl.
rewrite IHF1.
rewrite IHF2.
trivial.
simpl in *.
rewrite IHF.
trivial.
Qed.

Theorem fully_eval_is_normal2 {A} {S : Symbol A} F (M : A -> option bool) 
    (C : forall x, {h & M x = Some h}) : eval_is_normal F (mapping_is_partially_defined C) M.
unfold eval_is_normal.
intros.
pose (fully_eval_is_normal F (mapping_is_partially_defined C) M').
unfold eval_is_normal in e.
rewrite <- e.
have : forall x, Some (mapping_is_partially_defined C x) = (M x).
intros.
unfold mapping_is_partially_defined.
remember (C x).
destruct s.
auto.
move => Heq.
clear e.
generalize dependent (mapping_is_partially_defined C).
intros.
clear C.
have : forall F F' M, F = F' -> evaluate F M = evaluate F' M.
intros.
rewrite H.
trivial.
move => H2.
pose (H2 (partial_evaluate F M) (partial_evaluate F (fun x : A => Some (b x)))).
rewrite e.
apply func_ext_evaluate.
move => x.
pose (Heq x).
by symmetry.
trivial.
Qed.


Definition get_literals {A} {S : Symbol A} (f : Formula) : list A.
induction f.
(* FTop *)
exact [].
(* FBotoom *)
exact [].
(*ELiteral *)
exact [a].
(*EAnd*)
exact (IHf1 ++ IHf2).
(*EOr*)
exact (IHf1 ++ IHf2).
(*ENeg*)
exact IHf.
Defined.


Definition get_truth_table (n : nat) : list (list bool).
induction n.
exact [[]].
exact ((map (fun x => true :: x) IHn) ++ (map (fun x => false :: x) IHn)).
Defined.

Definition total_mapping {A} {S : Symbol A} (M : Mapping A) := map (fun x => M x) (projT1 (@finite _ S)).

Theorem completeness_truth_table (xs : list bool) : In xs (get_truth_table (length xs)). 
have : forall xs xss x', In xs xss -> In (x' :: xs) (map (fun x => x' :: x) xss).
intros.
induction xss.
inversion H.
simpl in *.
inversion H.
subst.
by left.
inversion H.
subst; by left.
inversion H.
subst; by left.
right; apply : IHxss.
assumption.
intros.
unfold total_mapping.
induction xs.
by left.
intros.
simpl.
apply in_or_app.
destruct a.
left; by apply H.
right; by apply H.
Qed.


Theorem completeness_mapping_truth_table {A : Set} {S : Symbol A} : 
   forall (M : Mapping A), In (total_mapping M) (get_truth_table (length (total_mapping M))).
intros. 
apply completeness_truth_table.
Qed.

Ltac tedious_formula_proof := simpl in *; subst; [congruence || tauto].

Theorem norm_and : forall {A} {S : Symbol A} F1 F2, 
   is_norm (partial_eval_and F1 F2) ->
      (F1 = FTop /\ F2 = FTop) \/ F1 = FBottom \/ F2 = FBottom.
intros.
destruct F1.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
Qed.

Theorem norm_and2 : forall {A} {S : Symbol A} F1 F2, is_norm F1 /\ is_norm F2 ->
   is_norm (partial_eval_and F1 F2).
intros.
destruct F1.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
Qed.

Theorem norm_or2 : forall {A} {S : Symbol A} F1 F2, is_norm F1 /\ is_norm F2 ->
   is_norm (partial_eval_or F1 F2).
intros.
destruct F1.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
destruct F2. all : try tedious_formula_proof.
Qed.

Theorem norm_neg : forall {A} {S : Symbol A} F, is_norm F ->
   is_norm (partial_eval_neg F).
destruct F.
all : try tedious_formula_proof.
Qed.

Fixpoint zip_function {A : Set} {B : Set} (eq_dec : EqDec A) (H : list A) (H' : list B) : A -> option B.
refine (match H, H' with
    |[], [] => _
    |x :: xs, y :: ys => _
    |[], _ :: ys => _
    |_ :: xs, [] => _
end).
exact (fun _ => None).
exact (fun _ => None).
exact (fun _ => None).
exact (fun a' => if (@eq_dec x a') then Some(y) else ((zip_function _ _ eq_dec xs ys) a')). 
Defined.


Functional Scheme zip_ind := Induction for zip_function Sort Prop.

Lemma double2_list_ind :
  forall (A : Type) (B : Type)  (P : list A -> list B -> Type),
    (* base cases *)
    (P [] []) ->
    (forall x l2, P [] (x :: l2)) ->
    (forall x l1, P (x :: l1) []) ->
    (* inductive step *)
    (forall x1 x2 l1 l2, P l1 l2 -> P (x1 :: l1) (x2 :: l2)) ->
    (* conclusion *)
    forall l1 l2, P l1 l2.
Proof.
  intros A P Hnil_nil Hnil_l2 Hl1_nil Hind.
  induction l1 as [| x1 l1' IHl1].
  - (* Case l1 = [] *)
    induction l2 as [| x2 l2' IHl2].
    + (* Case l2 = [] *)
      apply Hnil_l2.
    + (* Case l2 = x2 :: l2' *)
      apply Hl1_nil.
  - (* Case l1 = x1 :: l1' *)
    induction l2 as [| x2 l2' IHl2].
    + (* Case l2 = [] *)
      apply Hind.
    + (* Case l2 = x2 :: l2' *)
      apply X.
      apply IHl1.
Qed.


Theorem completness_zip_func {A : Set} {B : Set} (eq_dec' : EqDec A) (H : list A) (H' : list B):
    forall x, length H <= length H' -> In x H -> {h | (zip_function eq_dec' H H') x = Some h}.
intros.
move : x H0 H1.
eapply (double2_list_ind A B (fun H H' => forall x : A,
   length H <= length H' -> In x H -> {h | zip_function eq_dec' H H' x = Some h})).
intros.
inversion H1.
intros.
inversion H1.
intros.
have : False.
inversion H0.
move => F.
destruct F.
intros.
remember (eq_dec' x1 x).
destruct s.
subst.
exists x2.
simpl.
rewrite <- Heqs.
trivial.
have : In x l1.
inversion H2.
by contradiction n.
assumption.
move => H3.
simpl.
rewrite <- Heqs.
simpl.
apply H0.
auto with arith.
inversion H2.
subst.
by contradiction n.
assumption.
Qed.

Definition partial_evaluate_by_table_truth {A : Set} {S : Symbol A} (F : Formula) (a : list bool) : Formula.
pose (@zip_function A bool (@eq_dec _ S) (nodup eq_dec (projT1 (@finite _ S))) a).
exact (partial_evaluate F o).
Defined.

Definition brute_force {A : Set} {S : Symbol A} (F : Formula) : list Formula.
induction (get_truth_table (length (nodup (@eq_dec _ S) (projT1 (@finite _ S))))).
exact ([partial_evaluate_by_table_truth F []]).
exact (partial_evaluate_by_table_truth F a :: IHl).
Defined.


Functional Scheme brute_force_ind := Induction for brute_force Sort Prop.

Theorem get_truth_table_2_exp_size : forall n, length (get_truth_table n) = 2^n.
intros.
induction n.
trivial.
simpl.
rewrite app_length.
rewrite map_length.
rewrite map_length.
rewrite IHn.
auto with arith.
Qed.


Lemma truth_table_not_empty: forall n, ~ In [] (get_truth_table (S n)).
intros.
move => H.
induction n.
inversion H.
inversion H0.
inversion H0.
inversion H1.
inversion H1.
have : In [] (get_truth_table (S n)).
simpl in H.
have : forall x' xs, In [] (map [eta cons x'] xs) -> In [] xs.
intros.
induction xs.
inversion H0.
inversion H0.
inversion H1.
right; apply IHxs.
assumption.
move => H'.
destruct (in_app_or _ _ _ H).
apply (H' _ true).
exact H0.
apply (H' _ false).
exact H0.
apply IHn.
Qed.

Theorem get_truth_table_size_clauses : forall n x, In x (get_truth_table n) -> length x = n.
intros.
generalize dependent x.
induction n.
intros.
simpl in H.
inversion H.
subst.
trivial.
inversion H0.
intros.
destruct x.
destruct (truth_table_not_empty _ H).
pose (IHn x).
have : In x (get_truth_table n).
have : forall b x xs x', In (b :: x) (map [eta cons x'] xs) -> In x xs.
intros.
induction xs.
inversion H0.
inversion H0.
injection H1.
intros; subst.
by left.
right; apply IHxs.
exact H1.
move => H1.
destruct (in_app_or _ _ _ H).
apply (H1 _ b x (get_truth_table n) true).
exact H0.
apply (H1 _ b x (get_truth_table n) false).
exact H0.
move => H2.
rewrite <- e.
trivial.
exact H2.
Qed.

Theorem literals_are_always_less : forall {A} {S' : Symbol A} F, length (nodup eq_dec (get_literals F)) < length (get_truth_table (length (get_literals F))).
intros.
rewrite get_truth_table_2_exp_size.
induction (get_literals F).
auto.
simpl.
destruct (in_dec eq_dec a l).
lia.
simpl.
lia.
Qed.

Definition list_mapping {A : Set} {S : Symbol A} (M : A -> option bool) L := 
    fun x => match (find (fun y => is_left (eq_dec x y)) L) with
        |Some x => M x
        |None => None
    end.

Definition mimimal_symbol_mapping {A : Set} {S : Symbol A} F (M : A -> option bool) := 
    list_mapping M (get_literals F).


Theorem mimimal_symbol_set : forall {A : Set} {S : Symbol A} F (M : A -> option bool) (M' : A -> option bool), 
    (forall x, In x (get_literals F) -> M x = M' x) -> partial_evaluate F M = partial_evaluate F M'.
intros.
induction F.
auto.
auto.
simpl in *.
pose (H a).
rewrite e.
by left.
reflexivity.
have : forall x : A, In x (get_literals F1) -> M x = M' x.
clear IHF2 IHF1.
induction F1.
intros; inversion H0.
intros; inversion H0.
intros.
apply H.
inversion H0.
subst.
by left.
inversion H1.
intros.
apply H.
simpl.
apply in_or_app.
by left.
intros.
apply H.
simpl in *.
apply in_or_app.
by left.
intros.
apply H.
simpl in *.
apply in_or_app.
by left.
have : forall x : A, In x (get_literals F2) -> M x = M' x.
clear IHF2 IHF1.
induction F2.
intros; inversion H0.
intros; inversion H0.
intros.
apply H.
inversion H0.
subst.
simpl.
apply in_or_app.
by right.
inversion H1.
intros.
apply H.
simpl.
apply in_or_app.
by right.
intros.
apply H.
simpl in *.
apply in_or_app.
by right.
intros.
apply H.
simpl in *.
apply in_or_app.
by right.
intros.
pose (IHF1 H1).
pose (IHF2 H0).
simpl.
rewrite e.
rewrite e0.
trivial.
have : forall x : A, In x (get_literals F1) -> M x = M' x.
clear IHF2 IHF1.
induction F1.
intros; inversion H0.
intros; inversion H0.
intros.
apply H.
inversion H0.
subst.
by left.
inversion H1.
intros.
apply H.
simpl.
apply in_or_app.
by left.
intros.
apply H.
simpl in *.
apply in_or_app.
by left.
intros.
apply H.
simpl in *.
apply in_or_app.
by left.
have : forall x : A, In x (get_literals F2) -> M x = M' x.
clear IHF2 IHF1.
induction F2.
intros; inversion H0.
intros; inversion H0.
intros.
apply H.
inversion H0.
subst.
simpl.
apply in_or_app.
by right.
inversion H1.
intros.
apply H.
simpl.
apply in_or_app.
by right.
intros.
apply H.
simpl in *.
apply in_or_app.
by right.
intros.
apply H.
simpl in *.
apply in_or_app.
by right.
intros.
pose (IHF1 H1).
pose (IHF2 H0).
simpl.
rewrite e.
rewrite e0.
trivial.
have : (forall x : A, In x (get_literals F) -> M x = M' x).
auto.
sauto.
Qed.

Theorem mimimal_symbol_set_literal : forall {A : Set} {S : Symbol A} a (M : A -> option bool), 
   is_norm (partial_evaluate (Literal a) M) -> mimimal_symbol_mapping (Literal a) M a = M a.
intros.
unfold mimimal_symbol_mapping.
have : In a (get_literals (Literal a)).
by left.
move => In_a.
have : forall x xs, In x xs -> find (fun y : A => eq_dec x y) xs = Some x.
intros.
induction xs.
inversion H0.
simpl.
remember (eq_dec x a0).
inversion H0.
destruct s.
simpl.
by rewrite H1.
simpl.
by contradiction n.
rewrite Heqs.
destruct s.
rewrite <- Heqs.
simpl.
by rewrite e.
rewrite <- Heqs.
apply IHxs.
assumption.
move => H'.
unfold list_mapping.
rewrite H'.
assumption.
reflexivity.
Qed.

Definition smaller_prop : forall {A : Set} {S : Symbol A} (F1 F2 : Formula), Prop.
intros.
induction F2.
exact False.
exact False.
exact False.
exact (IHF2_1 \/ IHF2_2 \/ F2_1 = F1 \/ F2_2 = F1).
exact (IHF2_1 \/ IHF2_2 \/ F2_1 = F1 \/ F2_2 = F1).
exact (IHF2 \/ F2 = F1).
Defined.


Theorem set_extend_symbols : forall {A : Set} {S : Symbol A} F1 F2 , smaller_prop F1 F2 ->
    forall x, In x (get_literals F1) -> In x (get_literals F2).
intros.
induction F2.
inversion H.
inversion H.
inversion H.
simpl.
destruct H.
apply in_or_app.
firstorder.
destruct H.
apply in_or_app.
firstorder.
apply in_or_app.
destruct H.
subst; by left.
subst; by right.
destruct H.
simpl.
apply in_or_app.
firstorder.
destruct H.
simpl.
apply in_or_app.
firstorder.
simpl; apply in_or_app.
firstorder.
subst; by left.
subst; by right.
simpl in *.
destruct H.
apply IHF2.
assumption.
by rewrite H.
Qed.

Lemma list_mapping_in : forall {A : Set} {S : Symbol A} xs x M h, list_mapping M xs x = Some h -> In x xs.
intros.
induction xs.
inversion H.
unfold list_mapping in H.
simpl in H.
remember (eq_dec x a).
destruct s. 
simpl in *.
by left.
simpl in H.
right.
apply IHxs.
assumption.
Qed.


Theorem extend_minimal_symbol : forall {A : Set} {S : Symbol A} M F1 F2 , smaller_prop F1 F2 ->
    forall x h, mimimal_symbol_mapping F1 M x = Some h -> mimimal_symbol_mapping F2 M x = Some h.
intros.

unfold mimimal_symbol_mapping in *.
pose (@set_extend_symbols _ _ F1 F2 H).
move : i.
generalize dependent (get_literals F1).
generalize dependent (get_literals F2).
clear F1 F2 H.
intros.
pose(i x).
pose (i0 (list_mapping_in _ _ _ _ H0)).
generalize dependent i1.
clear i0.
move => H.
have : list_mapping M l0 x = Some h -> M x = Some h.
clear i H0 H l.
induction l0.
intros.
inversion H.
intros.
unfold list_mapping in H.
simpl in H.
remember (eq_dec x a).
destruct s.
simpl in H.
rewrite e.
assumption.
simpl in H.
apply IHl0.
assumption.
move => H'.
have : M x = Some h.
by apply H'.
move => H2.
clear H' i H0 l0.
induction l.
inversion H.
unfold list_mapping.
simpl.
remember (eq_dec x a).
destruct s.
simpl.
by rewrite <- e.
apply IHl.
destruct H.
by contradiction n.
assumption.
Qed.

Lemma find_left : forall {A : Set} B {S : Symbol A} (xs : list A) ys (x : A) (M : A -> option B),
   In x xs -> match find (fun y : A => eq_dec x y) (xs ++ ys) with
         | Some x => M x
         | None => None
         end = None -> match find (fun y : A => eq_dec x y) xs with
         | Some x => M x
         | None => None
         end = None.
intros.
induction xs.
inversion H.
simpl in *.
destruct H.
remember (eq_dec x a).
destruct s.
simpl in *.
assumption.
by contradiction n.
remember (eq_dec x a).
destruct s.
assumption.
apply IHxs.
assumption.
assumption.
Qed.


Lemma find_assoc : forall {A : Set} {S : Symbol A} (xs : list A) ys (x : A) b,
   find (fun y : A => eq_dec x y) (xs ++ ys) = b -> find (fun y : A => eq_dec x y) (ys ++ xs) = b.
intros.
induction xs.
by rewrite app_nil_r.
simpl in *.
remember (eq_dec x a).
destruct s.
simpl in *.
rewrite <- H.
rewrite e.
clear IHxs H Heqs e.
induction ys.
simpl.
remember (eq_dec a a).
destruct s.
trivial.
congruence.
simpl in *.
remember (eq_dec a a0).
destruct s.
simpl.
by rewrite e.
assumption.
simpl in H.
apply IHxs in H.
clear IHxs.
clear Heqs.
induction ys.
simpl in *.
remember (eq_dec x a).
destruct s.
congruence.
exact H.
simpl in *.
remember (eq_dec x a0).
destruct s.
simpl in *; congruence.
apply IHys.
exact H.
Qed.

Lemma find_right : forall {A : Set} B {S : Symbol A} (xs : list A) ys (x : A) (M : A -> option B),
   In x ys -> match find (fun y : A => eq_dec x y) (xs ++ ys) with
         | Some x => M x
         | None => None
         end = None -> match find (fun y : A => eq_dec x y) ys with
         | Some x => M x
         | None => None
         end = None.

intros.
remember (find (fun y : A => eq_dec x y) (xs ++ ys)).
symmetry in Heqo.
apply find_assoc in Heqo.
subst.
by rewrite (@find_left _ _ _ ys xs x M H H0).
Qed.


Theorem extend_minimal_symbol2 : forall {A : Set} {S : Symbol A} M F1 F2 , smaller_prop F1 F2 ->
     (partial_evaluate F1 (mimimal_symbol_mapping F1 M)) = (partial_evaluate F1 (mimimal_symbol_mapping F2 M)).
intros.
pose (@mimimal_symbol_set _ S F1 (mimimal_symbol_mapping F1 M) (mimimal_symbol_mapping F2 M)).
apply e.
intros.

clear e.
remember (mimimal_symbol_mapping F1 M x).
destruct o.
rewrite (extend_minimal_symbol _ _ _ _ _ _ (eq_sym Heqo)).
assumption.
auto.
unfold mimimal_symbol_mapping in *.
unfold list_mapping in *.
have : M x = None.
clear H.
induction F1.
inversion H0.
inversion H0.
simpl in *.
destruct H0.
rewrite H in Heqo.
remember (eq_dec x x) .
destruct s.
simpl in Heqo.
auto.
by contradiction n.
inversion H.
simpl in *.
destruct (in_app_or (get_literals F1_1) (get_literals F1_2) x H0).
pose (@find_left _ _ _ (get_literals F1_1) (get_literals F1_2) x M H (eq_sym Heqo)).
apply IHF1_1.
assumption.
auto.
pose (@find_right _ _ _ (get_literals F1_1) (get_literals F1_2) x M H (eq_sym Heqo)).
apply IHF1_2.
assumption.
auto.
simpl in H0.
destruct (in_app_or (get_literals F1_1) (get_literals F1_2) x H0).
pose (@find_left _ _ _ (get_literals F1_1) (get_literals F1_2) x M H (eq_sym Heqo)).
apply IHF1_1.
assumption.
auto.
pose (@find_right _ _ _ (get_literals F1_1) (get_literals F1_2) x M H (eq_sym Heqo)).
apply IHF1_2.
assumption.
auto.
simpl in H0.
apply IHF1.
auto.
auto.
intros.
clear Heqo H0 H F1.
generalize dependent (get_literals F2).
elim.
auto.
intros.
simpl in *.
remember (eq_dec x a).
destruct s.
simpl.
by rewrite <- e.
exact H.
Qed.


Theorem norm_mimimal_symbol_set : forall {A : Set} {S : Symbol A} F (M : A -> option bool), 
    is_norm (partial_evaluate F (mimimal_symbol_mapping F M)) -> is_norm (partial_evaluate F M).
intros.
have : (partial_evaluate F M) = partial_evaluate F (mimimal_symbol_mapping F M).
apply mimimal_symbol_set.
intros.
unfold mimimal_symbol_mapping.
clear H.
induction (get_literals F).
inversion H0.
inversion H0.
rewrite H.
unfold list_mapping.
simpl.
remember (eq_dec x x).
destruct s.
trivial.
by contradiction n.
unfold list_mapping.
simpl.
remember (eq_dec x a).
destruct s.
sauto.
simpl.
apply IHl.
exact H.
intros.
sauto.
Qed.

Theorem eval_is_normal3 : forall {A : Set} {S : Symbol A} F (M : A -> option bool),
    (forall x, {h | M x = Some h}) -> is_norm (partial_evaluate F (mimimal_symbol_mapping F M)).
intros.
induction F.
trivial.
trivial.
simpl.
unfold mimimal_symbol_mapping.
simpl.
unfold list_mapping.
simpl.
remember (eq_dec a a).
destruct s.
simpl.
remember (M a).
destruct o.
by destruct b.
destruct (H a).
congruence.
by contradiction n.
simpl in *.
apply norm_and2.
constructor.
rewrite <- extend_minimal_symbol2.
exact IHF1.
simpl.
do 2! right; left.
reflexivity.
rewrite <- extend_minimal_symbol2.
exact IHF2.
do 3! right.
reflexivity.
simpl in *.
apply norm_or2.
constructor.
rewrite <- extend_minimal_symbol2.
exact IHF1.
simpl.
do 2! right; left.
reflexivity.
rewrite <- extend_minimal_symbol2.
exact IHF2.
do 3! right.
reflexivity.
simpl in *.
rewrite <- extend_minimal_symbol2.
by apply norm_neg.
simpl.
by right.
Qed.

Require Coq.Vectors.Fin.

Definition nth {A} (xs : list A) (H : Fin.t (length xs)) : A.
induction xs.
inversion H.
dependent destruction H.
exact a.
exact (IHxs H).
Defined.

Theorem nth_In {A} (xs : list A) (H : Fin.t (length xs)) : In (nth _ H) xs.
induction xs.
inversion H.
dependent destruction H.
left; reflexivity.
right; exact (IHxs H).
Defined.

Theorem nth_In_rev {A} x (xs : list A): In x xs -> exists H, x = nth xs H.
intros.
dependent induction xs.
inversion H.
inversion H.
rewrite H0.
exists F1.
reflexivity.
destruct (IHxs H0).
rewrite H1.
clear H1 H0 H IHxs.
move : x0.
induction xs.
intros.
inversion x0.
intros.
dependent destruction x0.
exists (FS F1).
auto.
destruct (IHxs x0).
exists (FS (FS x0)).
have : nth (a0 :: xs) (FS x0) = nth xs x0.
reflexivity.
move => H2.
rewrite H2.
reflexivity.
Qed.


Definition from_truth_table {A} {S : Symbol A} (H : Fin.t (length (get_truth_table 
           (length (nodup (@eq_dec _ S) (projT1 (@finite _ S))))))) := 
   nth (get_truth_table (length (nodup (@eq_dec _ S) (projT1 (@finite _ S))))) H.


Theorem partial_evaluate_by_table_truth_is_norm {A : Set} {S : Symbol A} F H :
   is_norm (partial_evaluate_by_table_truth F (from_truth_table H)).

intros.
unfold partial_evaluate_by_table_truth.
have: forall x : A, {h : bool &
          (zip_function eq_dec (nodup eq_dec (projT1 (@finite _ S))) (from_truth_table H)) x = 
         Some h}.
intros.
destruct (completness_zip_func eq_dec (nodup eq_dec (projT1 (@finite _ S))) (from_truth_table H) x).
pose (get_truth_table_size_clauses (length (nodup eq_dec (projT1 (@finite _ S)))) (from_truth_table H)).
rewrite e.
pose (completeness_truth_table (from_truth_table H)).
unfold from_truth_table.
apply nth_In.
auto.
apply nodup_In.
sauto.
exists x0.
exact e.
intros.
apply norm_mimimal_symbol_set.
apply eval_is_normal3.
move => x.
destruct (H0 x).
exists x0.
exact e.
Qed.

Theorem brute_force_is_complete {A : Set} {S : Symbol A} F: 
    forall (M : A -> bool), exists H, partial_evaluate F (fun x => Some (M x)) = 
       partial_evaluate_by_table_truth F H.
intros.
pose (completeness_truth_table (total_mapping M)).
unfold total_mapping in i.
have: 
   In (map [eta M] (nodup eq_dec (projT1 finite))) (get_truth_table (length (map [eta M] (nodup eq_dec (projT1 finite))))).
generalize dependent (projT1 finite).
intros.
clear F.
induction l.
by left.
simpl in *.
remember (in_dec eq_dec a l).
destruct s.
exact IHl.
have : forall (b : bool) x xs, In x xs -> In (b :: x) (map [eta cons b] xs).
clear Heqs n IHl i l a M.
intros.
induction xs.
inversion H.
inversion H.
rewrite H0.
by left.
by right; firstorder.
intros.
simpl in *.
eapply in_app_or in i.
destruct i.
apply in_or_app.
destruct (M a).
left; by apply H.
right; by apply H.
apply in_or_app.
destruct (M a).
left; by apply H.
right; by apply H.
intros.
clear i.
destruct (nth_In_rev _ _ H).
exists (nth _ x).
rewrite <- H0.
clear H0 x H.
unfold partial_evaluate_by_table_truth.
rewrite (mimimal_symbol_set F (fun x : A => Some (M x)) (zip_function eq_dec (nodup eq_dec (projT1 finite))
     (map [eta M] (nodup eq_dec (projT1 finite))))).
intros.
clear H.
pose (projT2 finite x).
move : i.
induction (projT1 finite).
intros.
inversion i.
intros.
simpl.
remember (in_dec eq_dec a l ).
destruct s.
inversion i.
apply IHl.
rewrite <- H.
auto.
by apply IHl.
inversion i.
simpl.
remember (eq_dec a x).
destruct s.
simpl.
by subst.
congruence.
have : a <> x.
clear Heqs IHl i.
induction l.
inversion H.
move => eq.
inversion H.
rewrite H0 in n.
subst.
contradiction n.
apply IHl.
destruct n.
rewrite eq.
by right.
assumption.
assumption.
intros.
simpl.
remember (eq_dec a x).
destruct s.
congruence.
by apply IHl.
reflexivity.
Qed.

Inductive CLiteral {A : Set} {S : Symbol A} := 
    |CProp : A -> CLiteral
    |CNeg : CLiteral -> CLiteral.

Definition Clause {A : Set} {S : Symbol A} := list CLiteral.
Definition CNF {A : Set} {S : Symbol A} := list Clause.

Definition CLiteral_to_Formula {A : Set} {S : Symbol A} (literal : CLiteral) : Formula.
induction literal.
exact (Literal a).
exact (Neg IHliteral).
Defined.

Definition Clause_to_Formula {A : Set} {S : Symbol A} (clause : Clause) : Formula.
induction clause.
exact FTop.
exact (Or (CLiteral_to_Formula a) IHclause).
Defined.

Definition CNF_to_Formula {A : Set} {S : Symbol A} (cnf : CNF) : Formula.
induction cnf.
exact FTop.
exact (And (Clause_to_Formula a) IHcnf).
Defined.


Definition Unit {A : Set} {S : Symbol A} (clause : Clause) := length clause = 1.

Theorem clause_is_smaller_prop {A : Set} {S : Symbol A} (cnf : CNF) c : In c cnf ->
    smaller_prop (Clause_to_Formula c) (CNF_to_Formula cnf).
intros.
induction cnf.
inversion H.
simpl in *.
destruct H.
rewrite H.
by do 2! right; left.
right; left.
firstorder.
Qed.

Definition is_literal_or_neg {A : Set} {S : Symbol A} (f : Formula) : Prop.
destruct f.
exact False.
exact False.
exact True.
exact False.
exact False.
exact True.
Defined.

Theorem cliteral_is_literal_or_neg_formula {A : Set} {S : Symbol A} l :
    is_literal_or_neg (CLiteral_to_Formula l) /\ 
          forall F2, smaller_prop F2 (CLiteral_to_Formula l) -> is_literal_or_neg F2.
intros.
induction l.
constructor.
constructor.
intros.
simpl in *.
induction F2.
all : try tedious_formula_proof.
destruct IHl.
constructor.
constructor.
move => F2.
pose (H0 F2).
simpl.
move => H'.
destruct H'.
by apply i.
rewrite <- H1.
assumption.
Qed.


Theorem sat_unit_is_always_true {A : Set} {S : Symbol A} (cnf : CNF) M
    (sat : partial_evaluate (CNF_to_Formula cnf) M = FTop) unit : In unit cnf -> Unit unit -> 
         partial_evaluate (Clause_to_Formula unit) M = FTop.
intros.
induction cnf.
inversion H.
destruct cnf.
simpl in *.

pose (clause_is_smaller_prop _ _ H).



have : 




