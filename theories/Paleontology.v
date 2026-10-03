(******************************************************************************)
(*  Paleontology.v                                                            *)
(*                                                                            *)
(*  Four fossil genera that the previous version of this project mixed into  *)
(*  the extant genus list (one of them as a gliding flying squirrel).  Their *)
(*  data are sourced (data/fossils.json).  Two kinds of result:              *)
(*                                                                            *)
(*  1. What the fossils show: none preserves evidence of gliding.            *)
(*                                                                            *)
(*  2. Fossils against molecular dates.  A fossil inside the crown group of  *)
(*     a clade cannot be older than that clade's crown node.  So if the      *)
(*     youngest possible age of a genus's oldest dated occurrence exceeds    *)
(*     the upper 95% HPD bound of the crown node in Upham et al. (2019),     *)
(*     placing the genus inside that crown group conflicts with the dated    *)
(*     tree.  [dating_allows] applies this test to every published placement.*)
(*     It is a consistency check between two data sets, not a phylogenetic  *)
(*     analysis: a "conflict" means the placement and the dating cannot both *)
(*     be right, and it is silent about which one is wrong.                   *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia String NArith.
From Sciuridae Require Import Lib.Base Phylo.Tree Data.Geography Data.Taxonomy
  Data.Upham2019 Data.Fossils Classification Phylogeny.
Import ListNotations.

(* ======================== Crown nodes ======================== *)

(* The crown node of a group of sampled tips, and the upper bound of its 95%
   HPD age interval (0.01 Ma). *)
Definition crown (s : list N) : tree N := mrca s upham2019.
Definition crown_hpd_max (s : list N) : nat := snd (age_hpd (crown s)).

Definition all_tips : list N := leaves upham2019.

(* For the groups used below the crown node is exactly the group: each is a
   clade of the tree, so its MRCA has no other descendants. *)
Theorem crown_nodes_are_exact :
  seteq (leaves (crown all_tips)) all_tips = true /\
  forallb (fun sf => seteq (leaves (crown (subfamily_tips sf))) (subfamily_tips sf))
          [Ratufinae; Sciurinae; Nannosciurinae; Xerinae] = true /\
  forallb (fun t => seteq (leaves (crown (tribe_tips t))) (tribe_tips t))
          [Pteromyini; Sciurini; Marmotini; Protoxerini; Xerini; Tamiini] = true.
Proof. vm_compute. repeat split. Qed.

Theorem crown_upper_bounds :
  crown_hpd_max all_tips = 3534 /\
  crown_hpd_max (subfamily_tips Sciurinae) = 2412 /\
  crown_hpd_max (subfamily_tips Xerinae) = 2816 /\
  crown_hpd_max (tribe_tips Pteromyini) = 1975 /\
  crown_hpd_max (tribe_tips Sciurini) = 1610.
Proof. vm_compute. repeat split. Qed.

(* ======================== The test ======================== *)

Definition youngest_age_of_oldest (f : FossilGenus) : nat := fst (oldest_dated (fossil_info f)).

(* Stem placements and "Sciuridae, unassigned" make no claim about crown
   membership, so the dating cannot test them. *)
Definition dating_allows (f : FossilGenus) (op : Opinion) : bool :=
  match op with
  | Stem | StemOfTribe _ | IncertaeSedis => true
  | InSubfamilyOp sf => youngest_age_of_oldest f <=? crown_hpd_max (subfamily_tips sf)
  | InTribeOp t => youngest_age_of_oldest f <=? crown_hpd_max (tribe_tips t)
  end.

(* Every published placement, tested. *)
Theorem placements_tested :
  map (fun f => (f, map (fun p => dating_allows f (fst p)) (placements (fossil_info f)))) enum =
  [(Douglassciurus, [true; false]);
   (Hesperopetes, [true; true]);
   (Palaeosciurus, [true; false; true]);
   (Protosciurus, [false; true])].
Proof. vm_compute. reflexivity. Qed.

(* Douglassciurus jeffersoni (36.6-35.8 Ma) is older than the oldest age the
   dated tree allows for crown Sciuridae (35.34 Ma): it is a stem squirrel,
   as Casanovas-Vilar et al. (2018) concluded, and the alternative placement
   in Sciurinae conflicts with the dating. *)
Theorem douglassciurus_predates_crown_squirrels :
  youngest_age_of_oldest Douglassciurus > crown_hpd_max all_tips /\
  dating_allows Douglassciurus (InSubfamilyOp Sciurinae) = false.
Proof. vm_compute. split; [lia | reflexivity]. Qed.

(* Hesperopetes is as old: it cannot be a crown flying squirrel (crown
   Pteromyini at most 19.75 Ma) and not even a crown sciurid; a position on
   the lineage leading to flying squirrels remains open. *)
Theorem hesperopetes_not_a_crown_flying_squirrel :
  youngest_age_of_oldest Hesperopetes > crown_hpd_max (tribe_tips Pteromyini) /\
  youngest_age_of_oldest Hesperopetes > crown_hpd_max all_tips /\
  dating_allows Hesperopetes (StemOfTribe Pteromyini) = true.
Proof. vm_compute. repeat split; lia. Qed.

(* Protosciurus (Oligocene, at least 23.03 Ma) cannot belong to crown Sciurini
   (at most 16.10 Ma), as Black (1963) proposed. *)
Theorem protosciurus_not_crown_sciurini :
  youngest_age_of_oldest Protosciurus > crown_hpd_max (tribe_tips Sciurini) /\
  dating_allows Protosciurus (InTribeOp Sciurini) = false.
Proof. vm_compute. split; [lia | reflexivity]. Qed.

(* Palaeosciurus (first appearance at least 27.3 Ma) is too old for crown
   Sciurinae (at most 24.12 Ma) but not for crown Xerinae (at most 28.16 Ma). *)
Theorem palaeosciurus_against_dating :
  dating_allows Palaeosciurus (InSubfamilyOp Sciurinae) = false /\
  dating_allows Palaeosciurus (InSubfamilyOp Xerinae) = true.
Proof. vm_compute. split; reflexivity. Qed.

(* ======================== What the fossils show ======================== *)

Theorem no_fossil_shows_gliding (f : FossilGenus) : gliding_evidence (fossil_info f) = false.
Proof. destruct f; reflexivity. Qed.

(* Only Douglassciurus is known from a skeleton; Hesperopetes from teeth alone. *)
Theorem fossil_material :
  map (fun f => material (fossil_info f)) enum = [Skeleton; TeethOnly; TeethAndLimbBones; SkullAndTeeth].
Proof. vm_compute. reflexivity. Qed.

(* Fossil genera are not extant genera: the two types are disjoint by
   construction, and every extant genus is an MDD v2.5 genus. *)
Theorem fossil_count : List.length (enum : list FossilGenus) = 4.
Proof. vm_compute. reflexivity. Qed.
