(******************************************************************************)
(*  Key/Key.v                                                                 *)
(*                                                                            *)
(*  Dichotomous identification keys, in general.                              *)
(*                                                                            *)
(*  A taxon is described by a profile: the set of character states its        *)
(*  members can show.  An observation records the states seen on one          *)
(*  specimen, possibly leaving characters unobserved.  A key is a binary tree *)
(*  of couplets (yes/no questions about one character); its leaves list       *)
(*  taxa.  When a couplet asks about an unobserved character, the key follows *)
(*  both branches, so a key always returns a set of candidates.               *)
(*                                                                            *)
(*  Results (all for arbitrary observations, not just canonical specimens):   *)
(*    - key_sound:       a taxon whose profile is consistent with the         *)
(*                       observation is always among the candidates;          *)
(*    - identify_exact:  filtering the candidates by consistency yields       *)
(*                       exactly the consistent taxa;                         *)
(*    - key_resolves:    on a complete observation a resolved key returns a   *)
(*                       single taxon, and at most one taxon is consistent;   *)
(*    - no_resolving_key: if two taxa share a complete observation, no sound  *)
(*                       resolved key can exist (data cannot separate them).  *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia.
From Sciuridae Require Import Lib.Base.
Import ListNotations.

Section Keys.
  Context {T : Type} `{Finite T}.

  Variables Obs Profile Question : Type.

  Variable Consistent : Obs -> Profile -> Prop.
  Variable consistentb : Obs -> Profile -> bool.
  Hypothesis consistentb_spec : forall o p, reflect (Consistent o p) (consistentb o p).

  (* [ask q o = None] when the character asked about was not observed. *)
  Variable ask : Question -> Obs -> option bool.
  (* [decide q p = Some b] when every observation consistent with [p] that
     answers [q] at all answers [b]. *)
  Variable decide : Question -> Profile -> option bool.
  Hypothesis decide_sound :
    forall q p o b b', decide q p = Some b -> Consistent o p -> ask q o = Some b' -> b' = b.

  Variable profile : T -> Profile.

  Inductive key : Type :=
  | Leaf : list T -> key
  | Couplet : Question -> key -> key -> key.

  Fixpoint run (k : key) (o : Obs) : list T :=
    match k with
    | Leaf ts => ts
    | Couplet q yes no =>
        match ask q o with
        | Some true => run yes o
        | Some false => run no o
        | None => run yes o ++ run no o
        end
    end.

  (* [routes t k]: following the profile of [t], [t] is listed at every leaf
     it can reach.  Where a couplet does not decide [t] (the taxon varies in
     that character, or its state is undocumented), [t] must key out
     correctly on both sides, as in printed keys where a variable genus
     appears twice. *)
  Fixpoint routes (t : T) (k : key) : bool :=
    match k with
    | Leaf ts => mem t ts
    | Couplet q yes no =>
        match decide q (profile t) with
        | Some true => routes t yes
        | Some false => routes t no
        | None => routes t yes && routes t no
        end
    end.

  Theorem routes_sound (k : key) (t : T) (o : Obs) :
    routes t k = true -> Consistent o (profile t) -> In t (run k o).
  Proof.
    induction k as [ts | q yes IHy no IHn]; simpl; intros Hr Hc.
    - apply mem_true, Hr.
    - destruct (decide q (profile t)) as [[|] |] eqn:Hd;
        destruct (ask q o) as [[|] |] eqn:Ha.
      + apply IHy; assumption.
      + pose proof (decide_sound q _ o true false Hd Hc Ha); discriminate.
      + apply in_or_app; left; apply IHy; assumption.
      + pose proof (decide_sound q _ o false true Hd Hc Ha); discriminate.
      + apply IHn; assumption.
      + apply in_or_app; right; apply IHn; assumption.
      + apply andb_true_iff in Hr as [Hy _]; apply IHy; assumption.
      + apply andb_true_iff in Hr as [_ Hn]; apply IHn; assumption.
      + apply andb_true_iff in Hr as [Hy _]; apply in_or_app; left; apply IHy; assumption.
  Qed.

  (* ---------- Whole-key properties ---------- *)

  Definition sound_key (k : key) : bool := forallb (fun t => routes t k) enum.

  Theorem key_sound (k : key) :
    sound_key k = true -> forall t o, Consistent o (profile t) -> In t (run k o).
  Proof.
    intros Hk t o Hc; apply routes_sound; [| exact Hc].
    exact (forall_enum (fun t => routes t k) Hk t).
  Qed.

  (* Candidates filtered by consistency: exactly the matching taxa. *)
  Definition identify (k : key) (o : Obs) : list T :=
    filter (fun t => consistentb o (profile t)) (run k o).

  Theorem identify_exact (k : key) :
    sound_key k = true -> forall t o, In t (identify k o) <-> Consistent o (profile t).
  Proof.
    intros Hk t o; unfold identify; rewrite filter_In; split.
    - intros [_ Hc]; apply (reflect_iff _ _ (consistentb_spec o (profile t))), Hc.
    - intros Hc; split; [apply (key_sound k Hk t o Hc) |].
      apply (reflect_iff _ _ (consistentb_spec o (profile t))), Hc.
  Qed.

  (* The key agrees with brute-force matching against the whole table. *)
  Definition match_table (o : Obs) : list T := filter (fun t => consistentb o (profile t)) enum.

  Corollary identify_agrees_with_table (k : key) :
    sound_key k = true -> forall o t, In t (identify k o) <-> In t (match_table o).
  Proof.
    intros Hk o t; rewrite (identify_exact k Hk); unfold match_table; rewrite filter_In.
    rewrite <- (reflect_iff _ _ (consistentb_spec o (profile t))).
    split; [intros Hc; split; [apply enum_complete | exact Hc] | tauto].
  Qed.

  (* ---------- Resolution on complete observations ---------- *)

  Fixpoint leaf_sets (k : key) : list (list T) :=
    match k with
    | Leaf ts => [ts]
    | Couplet _ yes no => leaf_sets yes ++ leaf_sets no
    end.

  Definition resolved (k : key) : bool := forallb (fun ts => length ts =? 1) (leaf_sets k).

  (* An observation is complete for [k] when it answers every couplet in it. *)
  Fixpoint answers (k : key) (o : Obs) : bool :=
    match k with
    | Leaf _ => true
    | Couplet q yes no =>
        match ask q o with
        | Some true => answers yes o
        | Some false => answers no o
        | None => false
        end
    end.

  Lemma answers_leaf (k : key) (o : Obs) :
    answers k o = true -> In (run k o) (leaf_sets k).
  Proof.
    induction k as [ts | q yes IHy no IHn]; simpl; intros Ha; [left; reflexivity |].
    destruct (ask q o) as [[|] |]; try discriminate; apply in_or_app;
      [left; apply IHy | right; apply IHn]; exact Ha.
  Qed.

  Theorem key_resolves (k : key) :
    sound_key k = true -> resolved k = true ->
    forall t o, answers k o = true -> Consistent o (profile t) -> run k o = [t].
  Proof.
    intros Hk Hres t o Ha Hc.
    pose proof (answers_leaf k o Ha) as Hleaf.
    unfold resolved in Hres; rewrite forallb_forall in Hres.
    specialize (Hres _ Hleaf); apply Nat.eqb_eq in Hres.
    pose proof (key_sound k Hk t o Hc) as Hin.
    destruct (run k o) as [| x [| y rest]]; simpl in Hres; try discriminate.
    destruct Hin as [-> | []]; reflexivity.
  Qed.

  Corollary unique_identification (k : key) :
    sound_key k = true -> resolved k = true ->
    forall t1 t2 o, answers k o = true ->
    Consistent o (profile t1) -> Consistent o (profile t2) -> t1 = t2.
  Proof.
    intros Hk Hres t1 t2 o Ha H1 H2.
    pose proof (key_resolves k Hk Hres t1 o Ha H1) as E1.
    pose proof (key_resolves k Hk Hres t2 o Ha H2) as E2.
    rewrite E1 in E2; congruence.
  Qed.

  (* ---------- Limits: what no key can do ---------- *)

  Theorem no_resolving_key (t1 t2 : T) (o : Obs) :
    t1 <> t2 -> Consistent o (profile t1) -> Consistent o (profile t2) ->
    forall k, sound_key k = true -> resolved k = true -> answers k o = false.
  Proof.
    intros Hne H1 H2 k Hk Hres.
    destruct (answers k o) eqn:Ha; [| reflexivity].
    exfalso; apply Hne; exact (unique_identification k Hk Hres t1 t2 o Ha H1 H2).
  Qed.

  (* ---------- Inventory ---------- *)

  Definition leaf_taxa (k : key) : list T := concat (leaf_sets k).

  (* Every taxon keys out somewhere (implied by soundness, but cheap to state),
     and the number of places it keys out. *)
  Definition covers (k : key) : bool := forallb (fun t => mem t (leaf_taxa k)) enum.

  Definition placements (k : key) (t : T) : nat := count (fun x => beq x t) (leaf_taxa k).

  Fixpoint depth (k : key) : nat :=
    match k with
    | Leaf _ => 0
    | Couplet _ yes no => S (Nat.max (depth yes) (depth no))
    end.

  Fixpoint couplets (k : key) : nat :=
    match k with
    | Leaf _ => 0
    | Couplet _ yes no => S (couplets yes + couplets no)
    end.
End Keys.

Arguments Leaf {T Question} _.
Arguments Couplet {T Question} _ _ _.
