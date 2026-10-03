(******************************************************************************)
(*  Phylo/Clusters.v                                                          *)
(*                                                                            *)
(*  Phylogenies as cluster systems.  A rooted phylogeny with distinct tips is *)
(*  determined by its clusters (the tip sets of its clades), and those        *)
(*  clusters form a hierarchy: any two are nested or disjoint.                *)
(*                                                                            *)
(*  Evidence is a list of clusters (here: the well-supported clades of a      *)
(*  published tree).  A phylogeny "respects" the evidence when every          *)
(*  evidential cluster is one of its clades.  The two robustness theorems     *)
(*  below are what licence the taxonomic conclusions in this development:     *)
(*                                                                            *)
(*    - a group that IS an evidential cluster is monophyletic in every        *)
(*      phylogeny respecting the evidence;                                    *)
(*    - a group that CONFLICTS with an evidential cluster (overlaps it        *)
(*      without nesting) is monophyletic in NO phylogeny respecting the       *)
(*      evidence.                                                             *)
(*                                                                            *)
(*  Groups that are neither are left undecided: the evidence does not settle  *)
(*  them, and this development never claims otherwise.                        *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia.
From Sciuridae Require Import Lib.Base.
Import ListNotations.

Section Clusters.
  Context {L : Type} `{Beq L}.

  (* ---------- Compatibility and conflict ---------- *)

  Definition Compatible (a b : list L) : Prop :=
    incl a b \/ incl b a \/ Disjoint a b.

  Definition compatible (a b : list L) : bool :=
    subset a b || subset b a || disjoint a b.

  Lemma compatible_spec (a b : list L) : reflect (Compatible a b) (compatible a b).
  Proof.
    unfold Compatible, compatible.
    destruct (subset_spec a b), (subset_spec b a), (disjoint_spec a b);
      simpl; constructor; tauto.
  Qed.

  Definition Conflict (a b : list L) : Prop := ~ Compatible a b.

  Lemma Compatible_sym (a b : list L) : Compatible a b -> Compatible b a.
  Proof. unfold Compatible, Disjoint; intros [H1 | [H1 | H1]]; eauto. Qed.

  (* Compatibility only depends on clusters as sets. *)
  Lemma Compatible_SameSet (a a' b b' : list L) :
    SameSet a a' -> SameSet b b' -> Compatible a b -> Compatible a' b'.
  Proof.
    unfold SameSet, Compatible, Disjoint, incl.
    intros [Ha Ha'] [Hb Hb'] [Hc | [Hc | Hc]]; eauto 7.
  Qed.

  (* ---------- Hierarchies ---------- *)

  Definition Hierarchy (h : list (list L)) : Prop :=
    forall a b, In a h -> In b h -> Compatible a b.

  Lemma Hierarchy_incl (h h' : list (list L)) :
    incl h h' -> Hierarchy h' -> Hierarchy h.
  Proof. unfold Hierarchy, incl; auto. Qed.

  (* ---------- Monophyly relative to a phylogeny ---------- *)

  Definition Monophyletic (h : list (list L)) (s : list L) : Prop :=
    exists c, In c h /\ SameSet c s.

  (* A phylogeny [h] respects evidence [ev] if every evidential cluster is a
     clade of [h]. *)
  Definition Respects (h ev : list (list L)) : Prop :=
    forall c, In c ev -> Monophyletic h c.

  Lemma Respects_refl (h : list (list L)) : Respects h h.
  Proof.
    intros c Hc; exists c; split; [exact Hc | split; apply incl_refl].
  Qed.

  Theorem evidence_monophyly (h ev : list (list L)) (c s : list L) :
    Respects h ev -> In c ev -> SameSet c s -> Monophyletic h s.
  Proof.
    intros Hresp Hc Hcs; destruct (Hresp c Hc) as [c' [Hc' Hsame]].
    exists c'; split; [exact Hc' | eapply SameSet_trans; eassumption].
  Qed.

  Theorem conflict_excludes_monophyly (h ev : list (list L)) (c s : list L) :
    Hierarchy h -> Respects h ev -> In c ev -> Conflict c s -> ~ Monophyletic h s.
  Proof.
    intros Hhier Hresp Hc Hconf [s' [Hs' Hsame]].
    destruct (Hresp c Hc) as [c' [Hc' Hcsame]].
    apply Hconf.
    apply (Compatible_SameSet c' c s' s); [exact Hcsame | exact Hsame | apply Hhier; assumption].
  Qed.

  (* ---------- Sister groups ---------- *)

  (* Two disjoint groups are sisters when each is a clade and so is their
     union.  In a fully resolved tree this is exactly "the two children of
     one node". *)
  Definition Sisters (h : list (list L)) (a b : list L) : Prop :=
    Disjoint a b /\ Monophyletic h a /\ Monophyletic h b /\ Monophyletic h (a ++ b).

  Theorem evidence_sisters (h ev : list (list L)) (a b ca cb cab : list L) :
    Respects h ev -> Disjoint a b ->
    In ca ev -> SameSet ca a ->
    In cb ev -> SameSet cb b ->
    In cab ev -> SameSet cab (a ++ b) ->
    Sisters h a b.
  Proof.
    intros Hresp Hd Ha Ha' Hb Hb' Hab Hab'.
    split; [exact Hd |]; split; [| split].
    - exact (evidence_monophyly h ev ca a Hresp Ha Ha').
    - exact (evidence_monophyly h ev cb b Hresp Hb Hb').
    - exact (evidence_monophyly h ev cab (a ++ b) Hresp Hab Hab').
  Qed.

  Theorem conflict_excludes_sisters (h ev : list (list L)) (c a b : list L) :
    Hierarchy h -> Respects h ev -> In c ev -> Conflict c (a ++ b) -> ~ Sisters h a b.
  Proof.
    intros Hhier Hresp Hc Hconf [_ [_ [_ Hab]]].
    exact (conflict_excludes_monophyly h ev c (a ++ b) Hhier Hresp Hc Hconf Hab).
  Qed.

  (* ---------- Decision procedures returning witnesses ---------- *)

  Fixpoint find_same (ev : list (list L)) (s : list L) : option (list L) :=
    match ev with
    | [] => None
    | c :: rest => if seteq c s then Some c else find_same rest s
    end.

  Lemma find_same_sound (ev : list (list L)) (s c : list L) :
    find_same ev s = Some c -> In c ev /\ SameSet c s.
  Proof.
    induction ev as [|c' rest IH]; simpl; [discriminate |].
    destruct (seteq_spec c' s) as [Hs | Hs]; intros Heq.
    - inversion Heq; subst; split; [left; reflexivity | exact Hs].
    - destruct (IH Heq); split; [right |]; assumption.
  Qed.

  Fixpoint find_conflict (ev : list (list L)) (s : list L) : option (list L) :=
    match ev with
    | [] => None
    | c :: rest => if compatible c s then find_conflict rest s else Some c
    end.

  Lemma find_conflict_sound (ev : list (list L)) (s c : list L) :
    find_conflict ev s = Some c -> In c ev /\ Conflict c s.
  Proof.
    induction ev as [|c' rest IH]; simpl; [discriminate |].
    destruct (compatible_spec c' s) as [Hs | Hs]; intros Heq.
    - destruct (IH Heq); split; [right |]; assumption.
    - inversion Heq; subst; split; [left; reflexivity | exact Hs].
  Qed.

  (* If no evidential cluster conflicts with [s], the evidence alone cannot
     refute the monophyly of [s]: adding [s] keeps the evidence a hierarchy. *)
  Lemma find_conflict_none (ev : list (list L)) (s : list L) :
    find_conflict ev s = None -> forall c, In c ev -> Compatible c s.
  Proof.
    induction ev as [|c' rest IH]; simpl; [contradiction |].
    destruct (compatible_spec c' s) as [Hs | Hs]; [| discriminate].
    intros Hnone c [<- | Hc]; [exact Hs | exact (IH Hnone c Hc)].
  Qed.

  Theorem undecided_is_consistent (ev : list (list L)) (s : list L) :
    Hierarchy ev -> find_conflict ev s = None -> Hierarchy (s :: ev).
  Proof.
    intros Hhier Hnone a b [<- | Ha] [<- | Hb].
    - right; left; apply incl_refl.
    - apply Compatible_sym, (find_conflict_none ev s Hnone b Hb).
    - apply (find_conflict_none ev s Hnone a Ha).
    - apply Hhier; assumption.
  Qed.

  (* Decision of hierarchy-ness for a concrete cluster list. *)
  Definition hierarchyb (h : list (list L)) : bool :=
    forallb (fun a => forallb (fun b => compatible a b) h) h.

  Lemma hierarchyb_spec (h : list (list L)) : hierarchyb h = true -> Hierarchy h.
  Proof.
    unfold hierarchyb; rewrite forallb_forall; intros Hall a b Ha Hb.
    specialize (Hall a Ha); rewrite forallb_forall in Hall.
    apply (reflect_iff _ _ (compatible_spec a b)), Hall, Hb.
  Qed.
End Clusters.
