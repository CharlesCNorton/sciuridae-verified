(******************************************************************************)
(*  Key/Matrix.v                                                              *)
(*                                                                            *)
(*  A concrete instance of Key/Key.v: taxa described by a character matrix    *)
(*  with one measured character (a length, as an interval) and finitely many  *)
(*  discrete characters whose states are coded as natural numbers.  A        *)
(*  profile lists, for each discrete character, every state documented in    *)
(*  the taxon (its polymorphism); characters with no sourced data list every *)
(*  state, so they can never be used to separate that taxon.                  *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia.
From Sciuridae Require Import Lib.Base Key.Key.
Import ListNotations.

Section Matrix.
  Context {C : Type} `{Finite C}.            (* discrete characters *)

  Record obs : Type := {
    o_len : option nat;                      (* measured length, mm *)
    o_state : C -> option nat                (* observed state code, if any *)
  }.

  Record profile : Type := {
    p_min : nat;                             (* length interval, mm *)
    p_max : nat;
    p_states : C -> list nat                 (* documented states *)
  }.

  Definition Consistent (o : obs) (p : profile) : Prop :=
    (forall n, o_len o = Some n -> p_min p <= n <= p_max p) /\
    (forall c v, o_state o c = Some v -> In v (p_states p c)).

  Definition len_ok (o : obs) (p : profile) : bool :=
    match o_len o with
    | None => true
    | Some n => (p_min p <=? n) && (n <=? p_max p)
    end.

  Definition state_ok (o : obs) (p : profile) (c : C) : bool :=
    match o_state o c with
    | None => true
    | Some v => mem v (p_states p c)
    end.

  Definition consistentb (o : obs) (p : profile) : bool :=
    len_ok o p && forallb (state_ok o p) enum.

  Lemma consistentb_spec (o : obs) (p : profile) : reflect (Consistent o p) (consistentb o p).
  Proof.
    apply iff_reflect; unfold Consistent, consistentb, len_ok, state_ok.
    rewrite andb_true_iff, forallb_forall; split.
    - intros [Hl Hs]; split.
      + destruct (o_len o) as [n |]; [| reflexivity].
        destruct (Hl n eq_refl); apply andb_true_iff; split; apply Nat.leb_le; assumption.
      + intros c _; destruct (o_state o c) as [v |] eqn:E; [| reflexivity].
        apply mem_true, (Hs c v E).
    - intros [Hl Hs]; split.
      + intros n En; rewrite En in Hl; apply andb_true_iff in Hl as [H1 H2].
        apply Nat.leb_le in H1, H2; lia.
      + intros c v Ev; specialize (Hs c (enum_complete c)); rewrite Ev in Hs.
        apply mem_true, Hs.
  Qed.

  Inductive question : Type :=
  | LenAtMost : nat -> question             (* "length <= t mm?" *)
  | StateIn : C -> list nat -> question.    (* "state of c is one of vs?" *)

  Definition ask (q : question) (o : obs) : option bool :=
    match q with
    | LenAtMost t => option_map (fun n => n <=? t) (o_len o)
    | StateIn c vs => option_map (fun v => mem v vs) (o_state o c)
    end.

  Definition decide (q : question) (p : profile) : option bool :=
    match q with
    | LenAtMost t =>
        if p_max p <=? t then Some true
        else if t <? p_min p then Some false
        else None
    | StateIn c vs =>
        if subset (p_states p c) vs then Some true
        else if disjoint (p_states p c) vs then Some false
        else None
    end.

  Lemma decide_sound (q : question) (p : profile) (o : obs) (b b' : bool) :
    decide q p = Some b -> Consistent o p -> ask q o = Some b' -> b' = b.
  Proof.
    intros Hd [Hl Hs] Ha; destruct q as [t | c vs]; simpl in Hd, Ha.
    - destruct (o_len o) as [n |] eqn:En; simpl in Ha; [| discriminate].
      injection Ha as <-; specialize (Hl n eq_refl).
      destruct (p_max p <=? t) eqn:E1.
      + injection Hd as <-; apply Nat.leb_le in E1; apply Nat.leb_le; lia.
      + destruct (t <? p_min p) eqn:E2; [| discriminate].
        injection Hd as <-; apply Nat.ltb_lt in E2; apply Nat.leb_gt; lia.
    - destruct (o_state o c) as [v |] eqn:Ev; simpl in Ha; [| discriminate].
      injection Ha as <-; specialize (Hs c v Ev).
      destruct (subset_spec (p_states p c) vs) as [Hsub | Hsub].
      + injection Hd as <-; apply mem_true, Hsub, Hs.
      + destruct (disjoint_spec (p_states p c) vs) as [Hdis | Hdis]; [| discriminate].
        injection Hd as <-; destruct (mem_spec v vs) as [Hv | Hv]; [| reflexivity].
        exfalso; exact (Hdis v Hs Hv).
  Qed.

  (* A complete observation records the length and every discrete state. *)
  Definition complete (o : obs) : bool :=
    match o_len o with Some _ => true | None => false end &&
    forallb (fun c => match o_state o c with Some _ => true | None => false end) enum.

  Lemma complete_answers {T : Type} (k : @key T question) (o : obs) :
    complete o = true -> @answers T obs question ask k o = true.
  Proof.
    unfold complete; rewrite andb_true_iff, forallb_forall; intros [Hl Hs].
    induction k as [ts | q yes IHy no IHn]; simpl; [reflexivity |].
    destruct q as [t | c vs]; simpl.
    - destruct (o_len o); [| discriminate]; simpl.
      destruct (_ <=? t); assumption.
    - specialize (Hs c (enum_complete c)).
      destruct (o_state o c); [| discriminate]; simpl.
      destruct (mem _ vs); assumption.
  Qed.

  (* ---------- Well-formed profiles ---------- *)

  (* Each discrete character has a declared number of states; a profile is
     well formed when its interval is non-empty and every state list is a
     non-empty list of declared states. *)
  Variable nstates : C -> nat.

  Definition wf_profile (p : profile) : bool :=
    (p_min p <=? p_max p) &&
    forallb (fun c => negb (Nat.eqb (length (p_states p c)) 0) &&
                      forallb (fun v => v <? nstates c) (p_states p c)) enum.

  (* A profile's "typical" complete observation: every well-formed profile is
     satisfiable, so no taxon is vacuously unidentifiable. *)
  Definition witness (p : profile) : obs :=
    {| o_len := Some (p_min p);
       o_state := fun c => match p_states p c with v :: _ => Some v | [] => None end |}.

  Lemma witness_consistent (p : profile) : wf_profile p = true -> Consistent (witness p) p.
  Proof.
    unfold wf_profile; rewrite andb_true_iff, forallb_forall; intros [Hmm Hc].
    apply Nat.leb_le in Hmm; split; simpl.
    - intros n En; injection En as <-; lia.
    - intros c v Ev; destruct (p_states p c) as [| w ws]; [discriminate |].
      injection Ev as <-; left; reflexivity.
  Qed.

  Lemma witness_complete (p : profile) : wf_profile p = true -> complete (witness p) = true.
  Proof.
    unfold wf_profile, complete; rewrite !andb_true_iff, !forallb_forall; intros [_ Hc]; simpl.
    split; [reflexivity |]; intros c Hin; specialize (Hc c Hin).
    apply andb_true_iff in Hc as [Hne _].
    destruct (p_states p c); [discriminate | reflexivity].
  Qed.
  (* ---------- Pairs the data cannot separate ---------- *)

  Definition first_common (l1 l2 : list nat) : option nat := find (fun v => mem v l2) l1.

  Lemma first_common_spec (l1 l2 : list nat) (v : nat) :
    first_common l1 l2 = Some v -> In v l1 /\ In v l2.
  Proof.
    unfold first_common; intros Hf; apply find_some in Hf as [H1 H2].
    split; [exact H1 | apply mem_true, H2].
  Qed.

  (* A complete observation lying in both profiles, when one exists. *)
  Definition meet (p1 p2 : profile) : obs :=
    {| o_len := Some (Nat.max (p_min p1) (p_min p2));
       o_state := fun c => first_common (p_states p1 c) (p_states p2 c) |}.

  Definition inseparableb (p1 p2 : profile) : bool :=
    (Nat.max (p_min p1) (p_min p2) <=? Nat.min (p_max p1) (p_max p2)) &&
    forallb (fun c => match first_common (p_states p1 c) (p_states p2 c) with
                      | Some _ => true | None => false end) enum.

  Lemma inseparable_meet (p1 p2 : profile) :
    inseparableb p1 p2 = true ->
    complete (meet p1 p2) = true /\ Consistent (meet p1 p2) p1 /\ Consistent (meet p1 p2) p2.
  Proof.
    unfold inseparableb; rewrite andb_true_iff, forallb_forall; intros [Hlen Hc].
    apply Nat.leb_le in Hlen.
    split; [| split; split].
    - unfold complete; simpl; apply forallb_forall; intros c Hin.
      specialize (Hc c Hin); destruct (first_common _ _); [reflexivity | discriminate].
    - intros n En; simpl in En; injection En as <-; lia.
    - intros c v Ev; simpl in Ev; exact (proj1 (first_common_spec _ _ _ Ev)).
    - intros n En; simpl in En; injection En as <-; lia.
    - intros c v Ev; simpl in Ev; exact (proj2 (first_common_spec _ _ _ Ev)).
  Qed.

End Matrix.

Arguments obs C : clear implicits.
Arguments profile C : clear implicits.
Arguments question C : clear implicits.
