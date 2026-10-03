(******************************************************************************)
(*  Classification.v                                                          *)
(*                                                                            *)
(*  The Linnaean classification of Sciuridae according to the Mammal          *)
(*  Diversity Database v2.5 (2026): 5 subfamilies, 10 tribes, 64 genera,      *)
(*  321 species.  Ranks nest by construction (a species is typed by its       *)
(*  genus; a genus is placed in a tribe or directly in a tribeless            *)
(*  subfamily; a tribe lies in one subfamily), so the statements here are     *)
(*  about the content of the classification, not its consistency.            *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia String.
From Sciuridae Require Import Lib.Base Data.Geography Data.Taxonomy Data.Species.
Import ListNotations.

(* ======================== Rank functions ======================== *)

Definition genus_subfamily (g : Genus) : Subfamily :=
  match genus_placement g with
  | InTribe t => tribe_subfamily t
  | InSubfamily sf => sf
  end.

Definition genus_tribe (g : Genus) : option Tribe :=
  match genus_placement g with
  | InTribe t => Some t
  | InSubfamily _ => None
  end.

Definition species_subfamily (s : AnySpecies) : Subfamily := genus_subfamily (species_genus s).
Definition species_tribe (s : AnySpecies) : option Tribe := genus_tribe (species_genus s).

Definition species_of_genus (g : Genus) : list AnySpecies :=
  filter (fun s => beq (species_genus s) g) enum.

Definition genera_of_subfamily (sf : Subfamily) : list Genus :=
  filter (fun g => beq (genus_subfamily g) sf) enum.

Definition genera_of_tribe (t : Tribe) : list Genus :=
  filter (fun g => beq (genus_tribe g) (Some t)) enum.

Lemma species_of_genus_spec (g : Genus) (s : AnySpecies) :
  In s (species_of_genus g) <-> species_genus s = g.
Proof.
  unfold species_of_genus; rewrite filter_In, beq_true.
  split; [tauto | intros H; split; [apply enum_complete | exact H]].
Qed.

(* ======================== Nesting of ranks ======================== *)

Theorem ranks_nest (g : Genus) (t : Tribe) :
  genus_tribe g = Some t -> genus_subfamily g = tribe_subfamily t.
Proof.
  unfold genus_tribe, genus_subfamily; destruct (genus_placement g); congruence.
Qed.

Theorem species_ranks_nest (s : AnySpecies) (t : Tribe) :
  species_tribe s = Some t -> species_subfamily s = tribe_subfamily t.
Proof. apply ranks_nest. Qed.

(* Exactly two subfamilies are not divided into tribes. *)
Theorem tribeless_genera :
  filter (fun g => beq (genus_tribe g) None) enum = [Ratufa; Sciurillus].
Proof. vm_compute. reflexivity. Qed.

Theorem tribes_of_subfamilies :
  map (fun sf => (sf, filter (fun t => beq (tribe_subfamily t) sf) enum)) enum =
  [(Ratufinae, []); (Sciurillinae, []);
   (Sciurinae, [Pteromyini; Sciurini]);
   (Nannosciurinae, [Exilisciurini; Funambulini; Nannosciurini]);
   (Xerinae, [Marmotini; Protoxerini; Sciurotamiini; Tamiini; Xerini])].
Proof. vm_compute. reflexivity. Qed.

(* ======================== Inventory ======================== *)

Theorem subfamily_count : List.length (enum : list Subfamily) = 5.
Proof. vm_compute. reflexivity. Qed.

Theorem tribe_count : List.length (enum : list Tribe) = 10.
Proof. vm_compute. reflexivity. Qed.

Theorem genus_count : List.length (enum : list Genus) = 64.
Proof. vm_compute. reflexivity. Qed.

Theorem species_count : List.length (enum : list AnySpecies) = 321.
Proof. vm_compute. reflexivity. Qed.

Theorem genera_per_subfamily :
  map (fun sf => (sf, List.length (genera_of_subfamily sf))) enum =
  [(Ratufinae, 1); (Sciurillinae, 1); (Sciurinae, 22); (Nannosciurinae, 14); (Xerinae, 26)].
Proof. vm_compute. reflexivity. Qed.

Theorem species_per_subfamily :
  map (fun sf => (sf, count (fun s => beq (species_subfamily s) sf) enum)) enum =
  [(Ratufinae, 5); (Sciurillinae, 1); (Sciurinae, 102); (Nannosciurinae, 75); (Xerinae, 138)].
Proof. vm_compute. reflexivity. Qed.

Theorem genera_per_tribe :
  map (fun t => (t, List.length (genera_of_tribe t))) enum =
  [(Exilisciurini, 1); (Funambulini, 1); (Nannosciurini, 12); (Pteromyini, 17);
   (Sciurini, 5); (Marmotini, 11); (Protoxerini, 6); (Sciurotamiini, 1);
   (Tamiini, 3); (Xerini, 5)].
Proof. vm_compute. reflexivity. Qed.

Theorem species_per_tribe :
  map (fun t => (t, count (fun s => beq (species_tribe s) (Some t)) enum)) enum =
  [(Exilisciurini, 3); (Funambulini, 6); (Nannosciurini, 66); (Pteromyini, 58);
   (Sciurini, 44); (Marmotini, 71); (Protoxerini, 31); (Sciurotamiini, 2);
   (Tamiini, 28); (Xerini, 6)].
Proof. vm_compute. reflexivity. Qed.

(* Every genus has at least one species, and the genera partition the species. *)
Theorem genera_nonempty (g : Genus) : species_of_genus g <> [].
Proof.
  assert (H : forallb (fun g => negb (Nat.eqb (List.length (species_of_genus g)) 0)) enum = true)
    by (vm_compute; reflexivity).
  pose proof (forall_enum _ H g) as Hg; cbv beta in Hg.
  intros E; rewrite E in Hg; discriminate.
Qed.

Theorem genera_partition_species :
  fold_right plus 0 (map (fun g => List.length (species_of_genus g)) enum) = 321.
Proof. vm_compute. reflexivity. Qed.

Theorem monotypic_genera :
  filter (fun g => Nat.eqb (List.length (species_of_genus g)) 1) enum =
  [Rubrisciurus; Glyphotes; Menetes; Nannosciurus; Rhinosciurus; Sciurillus;
   Eoglaucomys; Olisthomys; Priapomys; Aeretes; Belomys; Pteromyscus; Trogopterus;
   Rheithrosciurus; Syntheosciurus; Poliocitellus; Epixerus; Myosciurus; Eutamias;
   Tamias; Spermophilopsis; Atlantoxerus; Euxerus; Xerus].
Proof. vm_compute. reflexivity. Qed.

(* Sciurus is the largest genus. *)
Theorem sciurus_largest (g : Genus) :
  g <> Sciurus -> List.length (species_of_genus g) < List.length (species_of_genus Sciurus).
Proof.
  intros Hne.
  assert (H : forall g, negb (beq g Sciurus) = true ->
            (List.length (species_of_genus g) <? List.length (species_of_genus Sciurus)) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  apply Nat.ltb_lt, H; destruct (beq_spec g Sciurus); [contradiction | reflexivity].
Qed.

Theorem sciurus_size : List.length (species_of_genus Sciurus) = 29.
Proof. vm_compute. reflexivity. Qed.

(* Typing guarantees: a species value carries its genus. *)
Theorem species_genus_sp (g : Genus) (s : Species g) : species_genus (sp s) = g.
Proof. reflexivity. Qed.

(* ======================== Changes relative to older checklists ======================== *)

(* The two genus splits adopted by MDD that the classical chipmunk and
   African ground squirrel genera no longer reflect. *)
Theorem chipmunks_three_genera : genera_of_tribe Tamiini = [Eutamias; Neotamias; Tamias].
Proof. vm_compute. reflexivity. Qed.

Theorem african_ground_squirrels_split :
  filter (fun g => beq (genus_tribe g) (Some Xerini)) enum =
  [Spermophilopsis; Atlantoxerus; Euxerus; Geosciurus; Xerus].
Proof. vm_compute. reflexivity. Qed.

(* ======================== The gray squirrel ======================== *)

Definition gray_squirrel : AnySpecies := sp Sciurus_carolinensis.

Theorem gray_squirrel_classification :
  species_genus gray_squirrel = Sciurus /\
  species_tribe gray_squirrel = Some Sciurini /\
  species_subfamily gray_squirrel = Sciurinae /\
  common_name (info gray_squirrel) = "Eastern Gray Squirrel"%string /\
  author (info gray_squirrel) = "J. F. Gmelin"%string /\ year (info gray_squirrel) = 1788.
Proof. vm_compute. repeat split. Qed.
