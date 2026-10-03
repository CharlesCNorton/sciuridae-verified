(******************************************************************************)
(*  Lib/Base.v                                                                *)
(*                                                                            *)
(*  Boolean equality with reflection, finite sets as lists, and finite types  *)
(*  built from an enumeration table.  Everything downstream decides its       *)
(*  finite facts with these functions and transports them to Prop through the *)
(*  reflection lemmas proved here, so no proof enumerates cases by hand.      *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia NArith.
Import ListNotations.

(* ======================== Boolean equality ======================== *)

Class Beq (A : Type) := {
  beq : A -> A -> bool;
  beq_spec : forall x y : A, reflect (x = y) (beq x y)
}.

Lemma beq_true {A} `{Beq A} (x y : A) : beq x y = true <-> x = y.
Proof. destruct (beq_spec x y); split; congruence. Qed.

Lemma beq_refl {A} `{Beq A} (x : A) : beq x x = true.
Proof. apply beq_true; reflexivity. Qed.

#[export] Instance Beq_nat : Beq nat := { beq := Nat.eqb; beq_spec := Nat.eqb_spec }.

#[export] Instance Beq_N : Beq N := { beq := N.eqb; beq_spec := N.eqb_spec }.

#[export] Instance Beq_bool : Beq bool := { beq := Bool.eqb; beq_spec := Bool.eqb_spec }.

(* ======================== Finite sets as lists ======================== *)

Section Sets.
  Context {A : Type} `{Beq A}.

  Definition mem (x : A) (l : list A) : bool := existsb (beq x) l.

  Lemma mem_spec (x : A) (l : list A) : reflect (In x l) (mem x l).
  Proof.
    unfold mem; apply iff_reflect; rewrite existsb_exists; split.
    - intros Hin; exists x; split; [exact Hin | apply beq_refl].
    - intros [y [Hy Heq]]; apply (proj1 (beq_true _ _)) in Heq; subst; exact Hy.
  Qed.

  Lemma mem_true (x : A) (l : list A) : mem x l = true <-> In x l.
  Proof. symmetry; apply reflect_iff, mem_spec. Qed.

  Definition subset (l1 l2 : list A) : bool := forallb (fun x => mem x l2) l1.

  Lemma subset_spec (l1 l2 : list A) : reflect (incl l1 l2) (subset l1 l2).
  Proof.
    unfold subset; apply iff_reflect; rewrite forallb_forall; split.
    - intros Hincl x Hx; apply mem_true, Hincl, Hx.
    - intros Hall x Hx; apply mem_true, Hall, Hx.
  Qed.

  Definition Disjoint (l1 l2 : list A) : Prop := forall x, In x l1 -> In x l2 -> False.

  Definition disjoint (l1 l2 : list A) : bool := forallb (fun x => negb (mem x l2)) l1.

  Lemma disjoint_spec (l1 l2 : list A) : reflect (Disjoint l1 l2) (disjoint l1 l2).
  Proof.
    unfold disjoint, Disjoint; apply iff_reflect; rewrite forallb_forall; split.
    - intros Hd x Hx; apply negb_true_iff; destruct (mem_spec x l2); [exfalso; eauto | reflexivity].
    - intros Hall x H1 H2; specialize (Hall x H1); apply negb_true_iff in Hall.
      apply mem_true in H2; congruence.
  Qed.

  Definition SameSet (l1 l2 : list A) : Prop := incl l1 l2 /\ incl l2 l1.

  Definition seteq (l1 l2 : list A) : bool := subset l1 l2 && subset l2 l1.

  Lemma seteq_spec (l1 l2 : list A) : reflect (SameSet l1 l2) (seteq l1 l2).
  Proof.
    unfold seteq, SameSet; destruct (subset_spec l1 l2), (subset_spec l2 l1);
      constructor; tauto.
  Qed.

  Lemma SameSet_sym (l1 l2 : list A) : SameSet l1 l2 -> SameSet l2 l1.
  Proof. unfold SameSet; tauto. Qed.

  Lemma SameSet_trans (l1 l2 l3 : list A) :
    SameSet l1 l2 -> SameSet l2 l3 -> SameSet l1 l3.
  Proof. unfold SameSet, incl; intuition. Qed.

  (* Order-preserving duplicate removal: keeps the first occurrence. *)
  Fixpoint dedup_acc (seen : list A) (l : list A) : list A :=
    match l with
    | [] => []
    | x :: t => if mem x seen then dedup_acc seen t else x :: dedup_acc (x :: seen) t
    end.

  Definition dedup (l : list A) : list A := dedup_acc [] l.

  Lemma dedup_acc_In (seen l : list A) (x : A) :
    In x (dedup_acc seen l) <-> In x l /\ ~ In x seen.
  Proof.
    revert seen; induction l as [|y t IH]; intros seen; simpl.
    - tauto.
    - destruct (mem_spec y seen) as [Hy | Hy].
      + rewrite IH; split.
        * intros [Hin Hns]; tauto.
        * intros [[<- | Hin] Hns]; [contradiction | tauto].
      + simpl; rewrite IH; simpl; split.
        * intros [<- | [Hin Hns]]; [tauto | split; [right; exact Hin | tauto]].
        * intros [[<- | Hin] Hns]; [left; reflexivity |].
          destruct (beq_spec y x) as [-> | Hne]; [left; reflexivity | right].
          split; [exact Hin | intros [Heq | Hs]; [congruence | contradiction]].
  Qed.

  Lemma dedup_In (l : list A) (x : A) : In x (dedup l) <-> In x l.
  Proof. unfold dedup; rewrite dedup_acc_In; simpl; tauto. Qed.

  Lemma dedup_acc_NoDup (seen l : list A) : NoDup (dedup_acc seen l).
  Proof.
    revert seen; induction l as [|y t IH]; intros seen; simpl.
    - constructor.
    - destruct (mem y seen); [apply IH |].
      constructor; [| apply IH].
      rewrite dedup_acc_In; simpl; tauto.
  Qed.

  Lemma dedup_NoDup (l : list A) : NoDup (dedup l).
  Proof. apply dedup_acc_NoDup. Qed.

  (* Set union, duplicate-free. *)
  Definition union (l1 l2 : list A) : list A := dedup (l1 ++ l2).

  Lemma union_In (l1 l2 : list A) (x : A) : In x (union l1 l2) <-> In x l1 \/ In x l2.
  Proof. unfold union; rewrite dedup_In, in_app_iff; tauto. Qed.

  (* Union of a family. *)
  Definition unions {B} (f : B -> list A) (l : list B) : list A := dedup (flat_map f l).

  Lemma unions_In {B} (f : B -> list A) (l : list B) (x : A) :
    In x (unions f l) <-> exists b, In b l /\ In x (f b).
  Proof. unfold unions; rewrite dedup_In, in_flat_map; reflexivity. Qed.

  Fixpoint nodupb (l : list A) : bool :=
    match l with [] => true | x :: t => negb (mem x t) && nodupb t end.

  Lemma nodupb_spec (l : list A) : reflect (NoDup l) (nodupb l).
  Proof.
    apply iff_reflect; induction l as [|x t IH]; simpl.
    - split; intros _; [reflexivity | constructor].
    - rewrite andb_true_iff, negb_true_iff, <- IH; split.
      + intros Hnd; inversion Hnd; subst; split; [| assumption].
        destruct (mem_spec x t); [contradiction | reflexivity].
      + intros [Hm Hnd]; constructor; [| exact Hnd].
        intros Hin; apply mem_true in Hin; congruence.
  Qed.
End Sets.

(* ======================== Finite types ======================== *)

Class Finite (A : Type) `{Beq A} := {
  enum : list A;
  enum_complete : forall x : A, In x enum;
  enum_nodup : NoDup enum
}.

Section FiniteFacts.
  Context {A : Type} `{Finite A}.

  (* A boolean property holds everywhere iff it holds on the enumeration. *)
  Lemma forall_enum (P : A -> bool) :
    forallb P enum = true -> forall x, P x = true.
  Proof. rewrite forallb_forall; intros Hall x; apply Hall, enum_complete. Qed.

  Lemma exists_enum (P : A -> bool) :
    existsb P enum = true -> exists x, P x = true.
  Proof. rewrite existsb_exists; intros [x [_ Hx]]; exists x; exact Hx. Qed.

  Lemma count_enum_NoDup (P : A -> bool) : NoDup (filter P enum).
  Proof. apply NoDup_filter, enum_nodup. Qed.
End FiniteFacts.

(* Building a [Finite] instance from an enumeration table and an index
   function.  The two side conditions are each checked by computation:
   [table_index] is a linear case analysis (one [reflexivity] per value),
   [indices_ok] is a single boolean evaluated by [vm_compute]. *)
Section FromTable.
  Variable A : Type.
  Variable index : A -> nat.
  Variable table : list A.
  Hypothesis table_index : forall x, nth_error table (index x) = Some x.
  Hypothesis indices_ok : map index table = seq 0 (length table).

  Definition table_beq (x y : A) : bool := Nat.eqb (index x) (index y).

  Lemma table_beq_spec (x y : A) : reflect (x = y) (table_beq x y).
  Proof.
    unfold table_beq; apply iff_reflect; rewrite Nat.eqb_eq; split.
    - intros ->; reflexivity.
    - intros Heq; pose proof (table_index x) as Hx; pose proof (table_index y) as Hy.
      rewrite Heq in Hx; congruence.
  Qed.

  Lemma table_complete (x : A) : In x table.
  Proof. eapply nth_error_In, table_index. Qed.

  Lemma table_nodup : NoDup table.
  Proof.
    apply (NoDup_map_inv index); rewrite indices_ok; apply seq_NoDup.
  Qed.
End FromTable.

Ltac solve_table_index := intros x; destruct x; reflexivity.

(* ======================== Structural instances ======================== *)

Fixpoint list_beq {A} `{Beq A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: t1, y :: t2 => beq x y && list_beq t1 t2
  | _, _ => false
  end.

Lemma list_beq_spec {A} `{Beq A} (l1 l2 : list A) : reflect (l1 = l2) (list_beq l1 l2).
Proof.
  apply iff_reflect; revert l2; induction l1 as [|x t IH]; intros [|y t2]; simpl;
    try (split; congruence).
  rewrite andb_true_iff, <- IH, beq_true; split; [intros E; injection E; auto | intros [-> ->]; reflexivity].
Qed.

#[export] Instance Beq_list {A} `{Beq A} : Beq (list A) := { beq := list_beq; beq_spec := list_beq_spec }.

Definition option_beq {A} `{Beq A} (o1 o2 : option A) : bool :=
  match o1, o2 with
  | Some x, Some y => beq x y
  | None, None => true
  | _, _ => false
  end.

Lemma option_beq_spec {A} `{Beq A} (o1 o2 : option A) : reflect (o1 = o2) (option_beq o1 o2).
Proof.
  apply iff_reflect; destruct o1, o2; simpl; try (split; congruence).
  rewrite beq_true; split; congruence.
Qed.

#[export] Instance Beq_option {A} `{Beq A} : Beq (option A) := { beq := option_beq; beq_spec := option_beq_spec }.

Definition prod_beq {A B} `{Beq A} `{Beq B} (p1 p2 : A * B) : bool :=
  beq (fst p1) (fst p2) && beq (snd p1) (snd p2).

Lemma prod_beq_spec {A B} `{Beq A} `{Beq B} (p1 p2 : A * B) : reflect (p1 = p2) (prod_beq p1 p2).
Proof.
  apply iff_reflect; destruct p1, p2; unfold prod_beq; simpl.
  rewrite andb_true_iff, !beq_true; split; [intros E; injection E; auto | intros [-> ->]; reflexivity].
Qed.

#[export] Instance Beq_prod {A B} `{Beq A} `{Beq B} : Beq (A * B) := { beq := prod_beq; beq_spec := prod_beq_spec }.

(* ======================== Deciding universal statements ======================== *)

(* The workhorse for finite facts: check an implication on the enumeration by
   computation, then use it for every value of the type. *)
Lemma enum_implies {A} `{Finite A} (P Q : A -> bool) :
  forallb (fun x => implb (P x) (Q x)) enum = true -> forall x, P x = true -> Q x = true.
Proof.
  intros Hall x Hp; pose proof (forall_enum (fun x => implb (P x) (Q x)) Hall x) as Hx.
  cbv beta in Hx; rewrite Hp in Hx; exact Hx.
Qed.

(* ======================== Small arithmetic helpers ======================== *)

Definition count {A} (P : A -> bool) (l : list A) : nat := length (filter P l).

Lemma count_map {A B} (P : B -> bool) (f : A -> B) (l : list A) :
  count P (map f l) = count (fun x => P (f x)) l.
Proof.
  unfold count; induction l as [|x t IH]; simpl; [reflexivity |].
  destruct (P (f x)); simpl; rewrite IH; reflexivity.
Qed.

(* Evaluate a closed subterm once and replace it by its value, so that a
   later [vm_compute] does not recompute it under binders. *)
Ltac precompute t :=
  let T := fresh "T" in
  let HT := fresh "HT" in
  remember t as T eqn:HT; vm_compute in HT; subst T.
