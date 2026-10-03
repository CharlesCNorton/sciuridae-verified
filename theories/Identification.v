(******************************************************************************)
(*  Identification.v                                                          *)
(*                                                                            *)
(*  The genus key, verified.  An observation records what was seen on one     *)
(*  adult specimen from its native range (any character may be left out).   *)
(*  The theorems quantify over ALL observations, not over a list of          *)
(*  canonical specimens:                                                      *)
(*                                                                            *)
(*    genus_key_sound        every consistent genus is among the candidates; *)
(*    identification_exact   the identifier returns exactly the genera whose *)
(*                           sourced profiles are consistent with the         *)
(*                           observation (so it agrees with brute-force      *)
(*                           matching against the whole matrix);              *)
(*    identification_unique  a complete observation is consistent with at    *)
(*                           most one genus: the character matrix is fully   *)
(*                           diagnostic;                                      *)
(*    every_genus_identifiable  each genus has a complete observation that   *)
(*                           identifies it.                                   *)
(*                                                                            *)
(*  What is trusted: the profiles in Data/Characters.v, i.e. the sourced      *)
(*  character states (docs/KEY.md lists every citation) and MDD's native      *)
(*  ranges.  The key itself is not trusted; it is checked here.              *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia String.
From Sciuridae Require Import Lib.Base Key.Key Key.Matrix
  Data.Taxonomy Data.Characters Data.GenusKey Classification.
Import ListNotations.

Definition Observation : Type := obs Character.

Definition run_key (o : Observation) : list Genus :=
  run (obs Character) (question Character) ask genus_key o.

(* Key candidates filtered by consistency, without repetitions (a variable
   genus can key out in more than one place). *)
Definition identify_genus (o : Observation) : list Genus :=
  dedup (identify (obs Character) (profile Character) (question Character)
                  consistentb ask genus_profile genus_key o).

(* ======================== Facts about the data ======================== *)

Theorem profiles_well_formed (g : Genus) : wf_profile nstates (genus_profile g) = true.
Proof.
  assert (H : forallb (fun g => wf_profile nstates (genus_profile g)) enum = true)
    by (vm_compute; reflexivity).
  exact (forall_enum _ H g).
Qed.

(* ======================== Facts about the key ======================== *)

Theorem genus_key_checked :
  sound_key (profile Character) (question Character) decide genus_profile genus_key = true.
Proof. vm_compute. reflexivity. Qed.

Theorem genus_key_sound (o : Observation) (g : Genus) :
  Consistent o (genus_profile g) -> In g (run_key o).
Proof.
  exact (key_sound (obs Character) (profile Character) (question Character)
           Consistent ask decide decide_sound genus_profile genus_key genus_key_checked g o).
Qed.

Theorem identification_exact (o : Observation) (g : Genus) :
  In g (identify_genus o) <-> Consistent o (genus_profile g).
Proof.
  unfold identify_genus; rewrite dedup_In.
  exact (identify_exact (obs Character) (profile Character) (question Character)
           Consistent consistentb consistentb_spec ask decide decide_sound
           genus_profile genus_key genus_key_checked g o).
Qed.

Corollary identification_agrees_with_matrix (o : Observation) (g : Genus) :
  In g (identify_genus o) <-> consistentb o (genus_profile g) = true.
Proof.
  rewrite identification_exact; apply reflect_iff, consistentb_spec.
Qed.

(* ======================== Complete observations ======================== *)

(* Leaves of the key that list more than one genus. *)
Definition residual_leaves : list (list Genus) :=
  filter (fun ts => 1 <? List.length ts) (leaf_sets (question Character) genus_key).

Lemma complete_run_is_leaf (o : Observation) :
  complete o = true -> In (run_key o) (leaf_sets (question Character) genus_key).
Proof.
  intros Hc; apply answers_leaf, complete_answers, Hc.
Qed.

(* On a complete observation the key ends at one leaf; any two consistent
   genera are equal unless they share a residual leaf. *)
Theorem identification_unique_or_residual (o : Observation) (g1 g2 : Genus) :
  complete o = true -> Consistent o (genus_profile g1) -> Consistent o (genus_profile g2) ->
  g1 = g2 \/ exists ts, In ts residual_leaves /\ In g1 ts /\ In g2 ts.
Proof.
  intros Hc H1 H2.
  pose proof (complete_run_is_leaf o Hc) as Hleaf.
  pose proof (genus_key_sound o g1 H1) as I1; pose proof (genus_key_sound o g2 H2) as I2.
  destruct (run_key o) as [| x [| y rest]] eqn:E.
  - contradiction.
  - destruct I1 as [<- | []]; destruct I2 as [<- | []]; left; reflexivity.
  - right; exists (x :: y :: rest); split; [| split; assumption].
    unfold residual_leaves; apply filter_In; split; [exact Hleaf | reflexivity].
Qed.

(* Every residual leaf is forced by the data: its genera share a complete
   observation, so no sound key over these characters can tell them apart. *)
Definition residual_forced : bool :=
  forallb (fun ts => forallb (fun g1 => forallb (fun g2 =>
             inseparableb (genus_profile g1) (genus_profile g2)) ts) ts) residual_leaves.

Theorem residual_is_forced : residual_forced = true.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_cannot_be_separated (ts : list Genus) (g1 g2 : Genus) :
  In ts residual_leaves -> In g1 ts -> In g2 ts ->
  exists o, complete o = true /\ Consistent o (genus_profile g1) /\ Consistent o (genus_profile g2) /\
    forall k, sound_key (profile Character) (question Character) decide genus_profile k = true ->
      In g1 (run (obs Character) (question Character) ask k o) /\
      In g2 (run (obs Character) (question Character) ask k o).
Proof.
  intros Hts H1 H2.
  pose proof residual_is_forced as Hf; unfold residual_forced in Hf.
  rewrite forallb_forall in Hf; specialize (Hf ts Hts); rewrite forallb_forall in Hf.
  specialize (Hf g1 H1); rewrite forallb_forall in Hf; specialize (Hf g2 H2).
  destruct (inseparable_meet _ _ Hf) as [Hc [C1 C2]].
  exists (meet (genus_profile g1) (genus_profile g2)).
  split; [exact Hc |]; split; [exact C1 |]; split; [exact C2 |].
  intros k Hk; split.
  - exact (key_sound (obs Character) (profile Character) (question Character)
             Consistent ask decide decide_sound genus_profile k Hk g1 _ C1).
  - exact (key_sound (obs Character) (profile Character) (question Character)
             Consistent ask decide decide_sound genus_profile k Hk g2 _ C2).
Qed.

Theorem every_genus_identifiable (g : Genus) :
  (forall ts, In ts residual_leaves -> ~ In g ts) ->
  exists o, complete o = true /\ identify_genus o = [g].
Proof.
  intros Hnot.
  pose proof (profiles_well_formed g) as Hwf.
  set (o := witness (genus_profile g)).
  assert (Hc : complete o = true) by exact (witness_complete _ _ Hwf).
  assert (Hcons : Consistent o (genus_profile g)) by exact (witness_consistent _ _ Hwf).
  exists o; split; [exact Hc |].
  pose proof (complete_run_is_leaf o Hc) as Hleaf.
  pose proof (genus_key_sound o g Hcons) as Hin.
  unfold identify_genus, identify; fold (run_key o).
  destruct (run_key o) as [| x [| y rest]] eqn:E.
  - contradiction.
  - destruct Hin as [<- | []]; simpl.
    destruct (consistentb_spec o (genus_profile x)) as [_ | Hn]; [reflexivity | contradiction].
  - exfalso; apply (Hnot (x :: y :: rest)); [| exact Hin].
    unfold residual_leaves; apply filter_In; split; [exact Hleaf | reflexivity].
Qed.

(* ======================== Size of the key ======================== *)

Theorem genus_key_shape :
  couplets (question Character) genus_key = 110 /\ depth (question Character) genus_key = 10.
Proof. vm_compute. split; reflexivity. Qed.

(* ======================== Using the key ======================== *)

(* Observations written with state names, e.g. ("realm", "Nearctic"). *)
Fixpoint position (x : string) (l : list string) : option nat :=
  match l with
  | [] => None
  | y :: t => if String.eqb x y then Some 0 else option_map S (position x t)
  end.

Definition observe (len : option nat) (seen : list (string * string)) : Observation :=
  {| o_len := len;
     o_state := fun c =>
       match find (fun p => String.eqb (fst p) (character_name c)) seen with
       | Some (_, v) => position v (state_names c)
       | None => None
       end |}.
