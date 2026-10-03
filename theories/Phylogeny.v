(******************************************************************************)
(*  Phylogeny.v                                                               *)
(*                                                                            *)
(*  The MDD classification tested against an independent molecular            *)
(*  phylogeny: the sciurid subtree of Upham, Esselstyn & Jetz (2019), DNA-    *)
(*  only maximum clade credibility tree (207 sampled species).                *)
(*                                                                            *)
(*  Evidence = clades with posterior probability >= 0.95.  Using              *)
(*  Phylo/Clusters.v and Phylo/Tree.v every verdict below holds in EVERY      *)
(*  fully resolved phylogeny that contains all well-supported clades (a       *)
(*  "resolution"), so no verdict depends on poorly supported nodes:           *)
(*    Supported  - the group is a well-supported clade: monophyletic in       *)
(*                 every resolution;                                          *)
(*    Refuted    - the group conflicts with a well-supported clade:           *)
(*                 monophyletic in no resolution;                             *)
(*    Undecided  - neither; adding the group keeps the evidence consistent;   *)
(*    Untestable - fewer than two sampled tips.                               *)
(*  Verdicts concern the species sampled by the tree; 5 MDD genera were not   *)
(*  sampled (unsampled_genera).                                               *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia String NArith.
From Sciuridae Require Import Lib.Base Phylo.Clusters Phylo.Tree
  Data.Taxonomy Data.Species Data.Upham2019 Classification.
Import ListNotations.

Definition threshold : nat := 950.                (* posterior >= 0.95 *)
Definition evidence : list (list N) := supported threshold upham2019.

Definition tip_genus (i : N) : option Genus :=
  option_map (fun r => species_genus (tip_species r)) (nth_error tips (N.to_nat i)).

Definition tips_where (P : Genus -> bool) : list N :=
  filter (fun i => match tip_genus i with Some g => P g | None => false end) (leaves upham2019).

Definition genus_tips (g : Genus) : list N := tips_where (fun g' => beq g' g).
Definition genera_tips (gs : list Genus) : list N := tips_where (fun g => mem g gs).
Definition tribe_tips (t : Tribe) : list N := tips_where (fun g => beq (genus_tribe g) (Some t)).
Definition subfamily_tips (sf : Subfamily) : list N := tips_where (fun g => beq (genus_subfamily g) sf).

Inductive Status := Supported | Refuted | Undecided | Untestable.

Definition status (s : list N) : Status :=
  if List.length s <=? 1 then Untestable
  else match find_same evidence s with
       | Some _ => Supported
       | None => match find_conflict evidence s with Some _ => Refuted | None => Undecided end
       end.

(* ======================== What each verdict means ======================== *)

Theorem supported_sound (s : list N) :
  status s = Supported -> forall t', Resolution threshold upham2019 t' -> Monophyletic (clusters t') s.
Proof.
  unfold status; intros Hs t' Hres.
  destruct (List.length s <=? 1); [discriminate |].
  destruct (find_same evidence s) as [c |] eqn:E; [| destruct (find_conflict evidence s); discriminate].
  exact (resolution_monophyly threshold upham2019 t' s c Hres E).
Qed.

Theorem refuted_sound (s : list N) :
  status s = Refuted -> forall t', Resolution threshold upham2019 t' -> ~ Monophyletic (clusters t') s.
Proof.
  unfold status; intros Hs t' Hres.
  destruct (List.length s <=? 1); [discriminate |].
  destruct (find_same evidence s); [discriminate |].
  destruct (find_conflict evidence s) as [c |] eqn:E; [| discriminate].
  exact (resolution_non_monophyly threshold upham2019 t' s c Hres E).
Qed.

(* The tips of the tree are distinct; this is what makes the evidence a
   consistent hierarchy and the MCC tree itself a resolution. *)
Theorem upham_tips_distinct : NoDup (leaves upham2019).
Proof. apply (reflect_iff _ _ (nodupb_spec _)); vm_compute; reflexivity. Qed.

Theorem evidence_consistent : Hierarchy evidence.
Proof. apply supported_hierarchy, upham_tips_distinct. Qed.

Theorem mcc_is_a_resolution : Resolution threshold upham2019 upham2019.
Proof. apply Resolution_self, upham_tips_distinct. Qed.

(* Undecided groups really are open: the evidence stays consistent if they are
   added as clades, and the evidence does not already contain them. *)
Theorem undecided_sound (s : list N) :
  status s = Undecided -> Hierarchy (s :: evidence) /\ find_same evidence s = None.
Proof.
  unfold status; intros Hs.
  destruct (List.length s <=? 1); [discriminate |].
  destruct (find_same evidence s); [discriminate |].
  destruct (find_conflict evidence s) eqn:E; [discriminate |].
  split; [exact (undecided_is_consistent evidence s evidence_consistent E) | reflexivity].
Qed.

(* ======================== The data ======================== *)

Theorem upham_size :
  List.length (leaves upham2019) = 207 /\ List.length evidence = 120.
Proof. vm_compute. split; reflexivity. Qed.

(* Node heights never increase towards the tips. *)
Theorem upham_time_consistent : time_consistent upham2019 = true.
Proof. vm_compute. reflexivity. Qed.

(* Crown Sciuridae: 30.20 Ma (95% HPD 25.52-35.34 Ma), posterior 1.0. *)
Theorem crown_sciuridae :
  age upham2019 = 3020 /\ age_hpd upham2019 = (2552, 3534) /\
  (match upham2019 with Fork p _ _ _ _ _ => p | Tip _ => 0 end) = 1000.
Proof. vm_compute. repeat split. Qed.

Theorem every_tip_has_a_genus (i : N) : In i (leaves upham2019) -> tip_genus i <> None.
Proof.
  intros Hi.
  assert (H : forallb (fun i => negb (beq (tip_genus i) None)) (leaves upham2019) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H; specialize (H i Hi); apply negb_true_iff in H.
  intros E; rewrite E in H; discriminate.
Qed.

Theorem unsampled_genera :
  filter (fun g => Nat.eqb (List.length (genus_tips g)) 0) enum =
  [Glyphotes; Olisthomys; Priapomys; Biswamoyopterus; Syntheosciurus].
Proof. vm_compute. reflexivity. Qed.

(* ======================== Verdicts for every taxon ======================== *)

Theorem subfamily_verdicts :
  map (fun sf => (sf, status (subfamily_tips sf))) enum =
  [(Ratufinae, Supported); (Sciurillinae, Untestable); (Sciurinae, Supported);
   (Nannosciurinae, Supported); (Xerinae, Supported)].
Proof. vm_compute. reflexivity. Qed.

Theorem tribe_verdicts :
  map (fun t => (t, status (tribe_tips t))) enum =
  [(Exilisciurini, Supported); (Funambulini, Supported); (Nannosciurini, Supported);
   (Pteromyini, Supported); (Sciurini, Supported); (Marmotini, Supported);
   (Protoxerini, Supported); (Sciurotamiini, Untestable); (Tamiini, Supported);
   (Xerini, Supported)].
Proof. vm_compute. reflexivity. Qed.

Definition genus_verdict_table : list (Genus * Status) :=
  map (fun g => (g, status (genus_tips g))) enum.

Theorem genus_verdicts :
  filter (fun gs => match snd gs with Supported | Untestable => false | _ => true end) genus_verdict_table =
  [(Sundasciurus, Undecided); (Hylopetes, Refuted); (Microsciurus, Refuted); (Sciurus, Refuted);
   (Funisciurus, Undecided); (Paraxerus, Undecided); (Geosciurus, Undecided)] /\
  count (fun gs => match snd gs with Supported => true | _ => false end) genus_verdict_table = 22 /\
  count (fun gs => match snd gs with Untestable => true | _ => false end) genus_verdict_table = 35.
Proof. precompute genus_verdict_table. vm_compute. repeat split. Qed.

(* Every subfamily and tribe with two or more sampled tips is monophyletic in
   every resolution. *)
Theorem testable_tribes_monophyletic (t : Tribe) :
  t <> Sciurotamiini -> forall t', Resolution threshold upham2019 t' -> Monophyletic (clusters t') (tribe_tips t).
Proof.
  intros Ht; apply supported_sound.
  assert (H : forall t, negb (beq t Sciurotamiini) = true ->
            (match status (tribe_tips t) with Supported => true | _ => false end) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  specialize (H t); destruct (beq_spec t Sciurotamiini) as [E | _]; [contradiction |].
  specialize (H eq_refl); destruct (status (tribe_tips t)); try discriminate; reflexivity.
Qed.

Theorem testable_subfamilies_monophyletic (sf : Subfamily) :
  sf <> Sciurillinae -> forall t', Resolution threshold upham2019 t' -> Monophyletic (clusters t') (subfamily_tips sf).
Proof.
  intros Hs; apply supported_sound.
  assert (H : forall sf, negb (beq sf Sciurillinae) = true ->
            (match status (subfamily_tips sf) with Supported => true | _ => false end) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  specialize (H sf); destruct (beq_spec sf Sciurillinae) as [E | _]; [contradiction |].
  specialize (H eq_refl); destruct (status (subfamily_tips sf)); try discriminate; reflexivity.
Qed.

(* ======================== Genera the tree refutes ======================== *)

Theorem sciurus_not_monophyletic :
  forall t', Resolution threshold upham2019 t' -> ~ Monophyletic (clusters t') (genus_tips Sciurus).
Proof. apply refuted_sound; vm_compute; reflexivity. Qed.

Theorem microsciurus_not_monophyletic :
  forall t', Resolution threshold upham2019 t' -> ~ Monophyletic (clusters t') (genus_tips Microsciurus).
Proof. apply refuted_sound; vm_compute; reflexivity. Qed.

Theorem hylopetes_not_monophyletic :
  forall t', Resolution threshold upham2019 t' -> ~ Monophyletic (clusters t') (genus_tips Hylopetes).
Proof. apply refuted_sound; vm_compute; reflexivity. Qed.

(* ======================== Former genera ======================== *)

(* Spermophilus in the broad pre-2009 sense (Helgen et al. 2009 split it into
   eight genera) is not a clade: the well-supported clade that refutes it
   contains the prairie dogs, Cynomys. *)
Definition spermophilus_sensu_lato : list Genus :=
  [Spermophilus; Urocitellus; Ictidomys; Poliocitellus; Xerospermophilus;
   Callospermophilus; Otospermophilus; Notocitellus].

Theorem spermophilus_sensu_lato_not_monophyletic :
  forall t', Resolution threshold upham2019 t' -> ~ Monophyletic (clusters t') (genera_tips spermophilus_sensu_lato).
Proof. apply refuted_sound; vm_compute; reflexivity. Qed.

Theorem spermophilus_refutation_involves_prairie_dogs :
  match find_conflict evidence (genera_tips spermophilus_sensu_lato) with
  | Some c => existsb (fun i => beq (tip_genus i) (Some Cynomys)) c
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* Tamias in the broad sense (now Eutamias, Neotamias, Tamias) is a clade. *)
Theorem tamias_sensu_lato_monophyletic :
  forall t', Resolution threshold upham2019 t' -> Monophyletic (clusters t') (genera_tips [Eutamias; Neotamias; Tamias]).
Proof. apply supported_sound; vm_compute; reflexivity. Qed.

(* Xerus in the broad sense (now Euxerus, Geosciurus, Xerus) is not settled
   by this tree at posterior 0.95. *)
Theorem xerus_sensu_lato_undecided : status (genera_tips [Euxerus; Geosciurus; Xerus]) = Undecided.
Proof. vm_compute. reflexivity. Qed.

(* ======================== Sister groups ======================== *)

Lemma disjoint_tips (a b : list N) : disjoint a b = true -> Disjoint a b.
Proof. intros H; apply (reflect_iff _ _ (disjoint_spec a b)), H. Qed.

Ltac sisters_by_evidence :=
  intros t' Hres; eapply resolution_sisters;
  [exact Hres | apply disjoint_tips; vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].

Ltac not_sisters_by_evidence :=
  intros t' Hres; eapply resolution_not_sisters; [exact Hres | vm_compute; reflexivity].

Theorem nannosciurinae_xerinae_sisters :
  forall t', Resolution threshold upham2019 t' ->
  Sisters (clusters t') (subfamily_tips Nannosciurinae) (subfamily_tips Xerinae).
Proof. sisters_by_evidence. Qed.

Theorem sciurinae_sister_to_nannosciurinae_xerinae :
  forall t', Resolution threshold upham2019 t' ->
  Sisters (clusters t') (subfamily_tips Sciurinae)
          (subfamily_tips Nannosciurinae ++ subfamily_tips Xerinae).
Proof. sisters_by_evidence. Qed.

Theorem sciurini_pteromyini_sisters :
  forall t', Resolution threshold upham2019 t' ->
  Sisters (clusters t') (tribe_tips Sciurini) (tribe_tips Pteromyini).
Proof. sisters_by_evidence. Qed.

Theorem marmotini_tamiini_sisters :
  forall t', Resolution threshold upham2019 t' ->
  Sisters (clusters t') (tribe_tips Marmotini) (tribe_tips Tamiini).
Proof. sisters_by_evidence. Qed.

(* Within Xerinae, Xerini is sister to all other tribes. *)
Theorem xerini_sister_to_other_xerinae :
  forall t', Resolution threshold upham2019 t' ->
  Sisters (clusters t') (tribe_tips Xerini)
          (tribe_tips Protoxerini ++ tribe_tips Sciurotamiini ++ tribe_tips Marmotini ++ tribe_tips Tamiini).
Proof. sisters_by_evidence. Qed.

(* Pairings that well-supported clades rule out. *)
Theorem xerini_protoxerini_not_sisters :
  forall t', Resolution threshold upham2019 t' ->
  ~ Sisters (clusters t') (tribe_tips Xerini) (tribe_tips Protoxerini).
Proof. not_sisters_by_evidence. Qed.

Theorem xerini_marmotini_not_sisters :
  forall t', Resolution threshold upham2019 t' ->
  ~ Sisters (clusters t') (tribe_tips Xerini) (tribe_tips Marmotini).
Proof. not_sisters_by_evidence. Qed.

Theorem sciurillinae_sciurinae_not_sisters :
  forall t', Resolution threshold upham2019 t' ->
  ~ Sisters (clusters t') (subfamily_tips Sciurillinae) (subfamily_tips Sciurinae).
Proof. not_sisters_by_evidence. Qed.

(* The relationships among Ratufinae, Sciurillinae and the remaining
   subfamilies are not resolved at posterior 0.95. *)
Theorem basal_split_undecided :
  status (subfamily_tips Ratufinae ++ subfamily_tips Sciurillinae) = Undecided /\
  status (subfamily_tips Sciurillinae ++ subfamily_tips Sciurinae ++ subfamily_tips Nannosciurinae ++ subfamily_tips Xerinae) = Undecided.
Proof. vm_compute. split; reflexivity. Qed.
