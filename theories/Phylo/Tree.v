(******************************************************************************)
(*  Phylo/Tree.v                                                              *)
(*                                                                            *)
(*  Rooted binary trees annotated with posterior support (per mille, rounded  *)
(*  down), node age and its 95% HPD interval (units of 0.01 Ma).  The main    *)
(*  theorem is that the                                                       *)
(*  clusters of any tree with distinct tips form a hierarchy; hence the       *)
(*  well-supported clusters of a published tree are mutually consistent, and *)
(*  every fully resolved tree with distinct tips is a "phylogeny" in the      *)
(*  sense of Phylo/Clusters.v.                                                *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia.
From Sciuridae Require Import Lib.Base Phylo.Clusters.
Import ListNotations.

Inductive tree (L : Type) : Type :=
| Tip : L -> tree L
| Fork : nat (* posterior, per mille *) -> nat (* age, 0.01 Ma *) ->
         nat (* 95% HPD lower bound *) -> nat (* 95% HPD upper bound *) ->
         tree L -> tree L -> tree L.

Arguments Tip {L} _.
Arguments Fork {L} _ _ _ _ _ _.

Section Trees.
  Context {L : Type} `{Beq L}.

  Fixpoint leaves (t : tree L) : list L :=
    match t with
    | Tip x => [x]
    | Fork _ _ _ _ l r => leaves l ++ leaves r
    end.

  (* The clusters of all internal nodes, root first. *)
  Fixpoint clusters (t : tree L) : list (list L) :=
    match t with
    | Tip _ => []
    | Fork _ _ _ _ l r => (leaves l ++ leaves r) :: clusters l ++ clusters r
    end.

  (* Clusters of internal nodes whose posterior is at least [theta]. *)
  Fixpoint supported (theta : nat) (t : tree L) : list (list L) :=
    match t with
    | Tip _ => []
    | Fork p _ _ _ l r =>
        (if theta <=? p then [leaves l ++ leaves r] else [])
          ++ supported theta l ++ supported theta r
    end.

  Lemma supported_incl (theta : nat) (t : tree L) : incl (supported theta t) (clusters t).
  Proof.
    induction t as [x | p a lo hi l IHl r IHr]; simpl; [apply incl_refl |].
    intros c Hc; apply in_app_iff in Hc as [Hc | Hc].
    - destruct (theta <=? p); simpl in Hc; [| contradiction].
      destruct Hc as [<- | []]; left; reflexivity.
    - right; apply in_app_iff in Hc as [Hc | Hc]; apply in_app_iff;
        [left; apply IHl | right; apply IHr]; exact Hc.
  Qed.

  Lemma clusters_within (t : tree L) (c : list L) :
    In c (clusters t) -> incl c (leaves t).
  Proof.
    induction t as [x | p a lo hi l IHl r IHr]; simpl; [contradiction |].
    intros [<- | Hc]; [apply incl_refl |].
    apply in_app_iff in Hc as [Hc | Hc]; intros y Hy; apply in_app_iff;
      [left; apply (IHl Hc) | right; apply (IHr Hc)]; exact Hy.
  Qed.

  Lemma NoDup_app_disjoint (l1 l2 : list L) : NoDup (l1 ++ l2) -> Disjoint l1 l2.
  Proof.
    induction l1 as [|x t IH]; simpl; intros Hnd y Hy1 Hy2; [contradiction |].
    inversion Hnd as [| ? ? Hnin Hnd']; subst.
    destruct Hy1 as [<- | Hy1].
    - apply Hnin, in_app_iff; right; exact Hy2.
    - exact (IH Hnd' y Hy1 Hy2).
  Qed.

  Lemma NoDup_app_l (l1 l2 : list L) : NoDup (l1 ++ l2) -> NoDup l1.
  Proof.
    induction l1 as [|x t IH]; simpl; intros Hnd; [constructor |].
    inversion Hnd as [| ? ? Hnin Hnd']; subst; constructor; [| exact (IH Hnd')].
    intros Hin; apply Hnin, in_app_iff; left; exact Hin.
  Qed.

  Lemma NoDup_app_r (l1 l2 : list L) : NoDup (l1 ++ l2) -> NoDup l2.
  Proof.
    induction l1 as [|x t IH]; simpl; intros Hnd; [exact Hnd |].
    inversion Hnd; subst; apply IH; assumption.
  Qed.

  (* The fundamental structural fact: clusters of a tree with distinct tips
     are pairwise nested or disjoint. *)
  Theorem clusters_hierarchy (t : tree L) : NoDup (leaves t) -> Hierarchy (clusters t).
  Proof.
    induction t as [x | p a lo hi l IHl r IHr]; simpl; intros Hnd; [intros ? ? [] |].
    pose proof (NoDup_app_l _ _ Hnd) as Hl; pose proof (NoDup_app_r _ _ Hnd) as Hr.
    pose proof (NoDup_app_disjoint _ _ Hnd) as Hdis.
    assert (Hsub : forall c, In c (clusters l ++ clusters r) -> incl c (leaves l ++ leaves r)).
    { intros c Hc y Hy; apply in_app_iff in Hc as [Hc | Hc]; apply in_app_iff;
        [left; apply (clusters_within l c Hc) | right; apply (clusters_within r c Hc)]; exact Hy. }
    intros c1 c2 [<- | H1] [<- | H2].
    - left; apply incl_refl.
    - right; left; apply Hsub, H2.
    - left; apply Hsub, H1.
    - apply in_app_iff in H1 as [H1 | H1]; apply in_app_iff in H2 as [H2 | H2].
      + apply IHl; assumption.
      + right; right; intros y Hy1 Hy2.
        exact (Hdis y (clusters_within l c1 H1 y Hy1) (clusters_within r c2 H2 y Hy2)).
      + right; right; intros y Hy1 Hy2.
        exact (Hdis y (clusters_within l c2 H2 y Hy2) (clusters_within r c1 H1 y Hy1)).
      + apply IHr; assumption.
  Qed.

  Corollary supported_hierarchy (theta : nat) (t : tree L) :
    NoDup (leaves t) -> Hierarchy (supported theta t).
  Proof.
    intros Hnd; apply (Hierarchy_incl _ (clusters t));
      [apply supported_incl | apply clusters_hierarchy, Hnd].
  Qed.

  (* A tree respects its own supported clusters, so the evidence is never
     vacuous: some fully resolved phylogeny satisfies it. *)
  Corollary tree_respects_supported (theta : nat) (t : tree L) :
    Respects (clusters t) (supported theta t).
  Proof.
    intros c Hc; exists c; split; [exact (supported_incl theta t c Hc) | split; apply incl_refl].
  Qed.

  (* "Every fully resolved phylogeny with distinct tips that contains all
     well-supported clades of [t]". *)
  Definition Resolution (theta : nat) (t : tree L) (t' : tree L) : Prop :=
    NoDup (leaves t') /\ Respects (clusters t') (supported theta t).

  Lemma Resolution_self (theta : nat) (t : tree L) :
    NoDup (leaves t) -> Resolution theta t t.
  Proof. split; [assumption | apply tree_respects_supported]. Qed.

  Theorem resolution_monophyly (theta : nat) (t t' : tree L) (s c : list L) :
    Resolution theta t t' -> find_same (supported theta t) s = Some c ->
    Monophyletic (clusters t') s.
  Proof.
    intros [_ Hresp] Hfind; destruct (find_same_sound _ _ _ Hfind) as [Hc Hsame].
    exact (evidence_monophyly _ _ c s Hresp Hc Hsame).
  Qed.

  Theorem resolution_non_monophyly (theta : nat) (t t' : tree L) (s c : list L) :
    Resolution theta t t' -> find_conflict (supported theta t) s = Some c ->
    ~ Monophyletic (clusters t') s.
  Proof.
    intros [Hnd Hresp] Hfind; destruct (find_conflict_sound _ _ _ Hfind) as [Hc Hconf].
    exact (conflict_excludes_monophyly _ _ c s (clusters_hierarchy t' Hnd) Hresp Hc Hconf).
  Qed.

  Theorem resolution_sisters (theta : nat) (t t' : tree L) (a b ca cb cab : list L) :
    Resolution theta t t' -> Disjoint a b ->
    find_same (supported theta t) a = Some ca ->
    find_same (supported theta t) b = Some cb ->
    find_same (supported theta t) (a ++ b) = Some cab ->
    Sisters (clusters t') a b.
  Proof.
    intros [_ Hresp] Hd Ha Hb Hab.
    destruct (find_same_sound _ _ _ Ha) as [Ha1 Ha2], (find_same_sound _ _ _ Hb) as [Hb1 Hb2],
      (find_same_sound _ _ _ Hab) as [Hab1 Hab2].
    exact (evidence_sisters _ _ a b ca cb cab Hresp Hd Ha1 Ha2 Hb1 Hb2 Hab1 Hab2).
  Qed.

  Theorem resolution_not_sisters (theta : nat) (t t' : tree L) (a b c : list L) :
    Resolution theta t t' -> find_conflict (supported theta t) (a ++ b) = Some c ->
    ~ Sisters (clusters t') a b.
  Proof.
    intros [Hnd Hresp] Hfind; destruct (find_conflict_sound _ _ _ Hfind) as [Hc Hconf].
    exact (conflict_excludes_sisters _ _ c a b (clusters_hierarchy t' Hnd) Hresp Hc Hconf).
  Qed.

  (* ---------- Node ages ---------- *)

  Definition age (t : tree L) : nat :=
    match t with Tip _ => 0 | Fork _ a _ _ _ _ => a end.

  Definition age_hpd (t : tree L) : nat * nat :=
    match t with Tip _ => (0, 0) | Fork _ _ lo hi _ _ => (lo, hi) end.

  (* Every node is at least as old as its children, and its age lies in its
     95% HPD interval. *)
  Fixpoint time_consistent (t : tree L) : bool :=
    match t with
    | Tip _ => true
    | Fork _ a lo hi l r =>
        (lo <=? a) && (a <=? hi) && (age l <=? a) && (age r <=? a) && time_consistent l && time_consistent r
    end.

  (* The node whose cluster is exactly [s], if any. *)
  Fixpoint find_node (s : list L) (t : tree L) : option (tree L) :=
    match t with
    | Tip _ => None
    | Fork _ _ _ _ l r =>
        if seteq (leaves l ++ leaves r) s then Some t
        else match find_node s l with Some n => Some n | None => find_node s r end
    end.

  (* The most recent common ancestor of a non-empty tip set: the smallest
     subtree containing all of them. *)
  Fixpoint mrca (s : list L) (t : tree L) : tree L :=
    match t with
    | Tip _ => t
    | Fork _ _ _ _ l r =>
        if subset s (leaves l) then mrca s l
        else if subset s (leaves r) then mrca s r
        else t
    end.

  Lemma mrca_contains (s : list L) (t : tree L) :
    incl s (leaves t) -> incl s (leaves (mrca s t)).
  Proof.
    induction t as [x | p a lo hi l IHl r IHr]; simpl; intros Hs; [exact Hs |].
    destruct (subset_spec s (leaves l)) as [Hl | Hl]; [apply IHl, Hl |].
    destruct (subset_spec s (leaves r)) as [Hr | Hr]; [apply IHr, Hr | exact Hs].
  Qed.
End Trees.
