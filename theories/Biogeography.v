(******************************************************************************)
(*  Biogeography.v                                                            *)
(*                                                                            *)
(*  Native distributions from MDD v2.5.  Ranges are recorded per species;     *)
(*  the range of a genus or higher taxon is defined as the union of its       *)
(*  species' ranges, so it cannot disagree with them (the old hand-written    *)
(*  genus table placed Urocitellus in North America only, contradicting its   *)
(*  own species; that error is impossible here, see urocitellus_holarctic).   *)
(*                                                                            *)
(*  MDD flags some country and realm records as uncertain.  "Documented"      *)
(*  ranges below include them, "confirmed" ranges exclude them; each theorem *)
(*  says which it uses.  Introduced populations are not native ranges and    *)
(*  are not part of MDD's distribution fields.                               *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia String.
From Sciuridae Require Import Lib.Base Data.Geography Data.Taxonomy Data.Species Classification.
Import ListNotations.

(* ======================== Ranges ======================== *)

Definition documented_countries (s : AnySpecies) : list Country :=
  countries (info s) ++ countries_uncertain (info s).

Definition documented_realms (s : AnySpecies) : list Realm :=
  realms (info s) ++ realms_uncertain (info s).

Definition species_continents (s : AnySpecies) : list Continent := continents (info s).

Definition genus_countries (g : Genus) : list Country :=
  unions documented_countries (species_of_genus g).

Definition genus_realms (g : Genus) : list Realm :=
  unions documented_realms (species_of_genus g).

Definition genus_confirmed_realms (g : Genus) : list Realm :=
  unions (fun s => realms (info s)) (species_of_genus g).

Definition genus_continents (g : Genus) : list Continent :=
  unions species_continents (species_of_genus g).

(* A genus occurs where at least one of its species occurs, and only there. *)
Theorem genus_realms_spec (g : Genus) (r : Realm) :
  In r (genus_realms g) <-> exists s, species_genus s = g /\ In r (documented_realms s).
Proof.
  unfold genus_realms; rewrite unions_In; split.
  - intros [s [Hs Hr]]; exists s; split; [exact (proj1 (species_of_genus_spec g s) Hs) | exact Hr].
  - intros [s [Hs Hr]]; exists s; split; [exact (proj2 (species_of_genus_spec g s) Hs) | exact Hr].
Qed.

Theorem genus_continents_spec (g : Genus) (c : Continent) :
  In c (genus_continents g) <-> exists s, species_genus s = g /\ In c (species_continents s).
Proof.
  unfold genus_continents; rewrite unions_In; split.
  - intros [s [Hs Hc]]; exists s; split; [exact (proj1 (species_of_genus_spec g s) Hs) | exact Hc].
  - intros [s [Hs Hc]]; exists s; split; [exact (proj2 (species_of_genus_spec g s) Hs) | exact Hc].
Qed.

Theorem genus_countries_spec (g : Genus) (c : Country) :
  In c (genus_countries g) <-> exists s, species_genus s = g /\ In c (documented_countries s).
Proof.
  unfold genus_countries; rewrite unions_In; split.
  - intros [s [Hs Hc]]; exists s; split; [exact (proj1 (species_of_genus_spec g s) Hs) | exact Hc].
  - intros [s [Hs Hc]]; exists s; split; [exact (proj2 (species_of_genus_spec g s) Hs) | exact Hc].
Qed.

(* Every species has a non-empty confirmed range on every axis. *)
Theorem ranges_nonempty (s : AnySpecies) :
  countries (info s) <> [] /\ continents (info s) <> [] /\ realms (info s) <> [].
Proof.
  assert (H : forall s, true = true ->
            negb (beq (countries (info s)) []) && negb (beq (continents (info s)) [])
            && negb (beq (realms (info s)) []) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  specialize (H s eq_refl); rewrite !andb_true_iff, !negb_true_iff in H.
  destruct H as [[H1 H2] H3]; repeat split; intros E;
    [rewrite E in H1 | rewrite E in H2 | rewrite E in H3]; discriminate.
Qed.

(* ======================== Where squirrels are not ======================== *)

Theorem absent_from_oceania_and_antarctica (s : AnySpecies) :
  ~ In Oceania (species_continents s) /\ ~ In Antarctica (species_continents s) /\
  ~ In Oceanian (documented_realms s) /\ ~ In Antarctic (documented_realms s).
Proof.
  assert (H : forall s, true = true ->
            negb (mem Oceania (species_continents s)) && negb (mem Antarctica (species_continents s))
            && negb (mem Oceanian (documented_realms s)) && negb (mem Antarctic (documented_realms s)) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  specialize (H s eq_refl); rewrite !andb_true_iff, !negb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4]; repeat split; intros Hin; apply mem_true in Hin; congruence.
Qed.

(* No genus is native both to Africa and to the Americas. *)
Theorem africa_americas_disjoint (g : Genus) :
  In Africa (genus_continents g) ->
  ~ In North_America (genus_continents g) /\ ~ In South_America (genus_continents g).
Proof.
  intros Haf.
  assert (H : forall g, mem Africa (genus_continents g) = true ->
            negb (mem North_America (genus_continents g)) && negb (mem South_America (genus_continents g)) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  specialize (H g (proj2 (mem_true _ _) Haf)); rewrite andb_true_iff, !negb_true_iff in H.
  destruct H as [H1 H2]; split; intros Hin; apply mem_true in Hin; congruence.
Qed.

(* ======================== Clade-level patterns ======================== *)

(* Every African squirrel belongs to Xerinae. *)
Theorem african_squirrels_are_xerine (s : AnySpecies) :
  In Africa (species_continents s) -> species_subfamily s = Xerinae.
Proof.
  intros Haf; apply beq_true.
  revert s Haf; intros s Haf; apply (enum_implies (fun s => mem Africa (species_continents s))
                                       (fun s => beq (species_subfamily s) Xerinae));
    [vm_compute; reflexivity | apply mem_true, Haf].
Qed.

(* Nannosciurinae (formerly Callosciurinae) is entirely Asian. *)
Theorem nannosciurinae_asian (s : AnySpecies) :
  species_subfamily s = Nannosciurinae -> species_continents s = [Asia].
Proof.
  intros Hs; apply beq_true.
  apply (enum_implies (fun s => beq (species_subfamily s) Nannosciurinae)
                      (fun s => beq (species_continents s) [Asia]));
    [vm_compute; reflexivity | apply beq_true, Hs].
Qed.

(* Protoxerini is entirely Afrotropical. *)
Theorem protoxerini_afrotropical (s : AnySpecies) :
  species_tribe s = Some Protoxerini -> documented_realms s = [Afrotropic].
Proof.
  intros Hs; apply beq_true.
  apply (enum_implies (fun s => beq (species_tribe s) (Some Protoxerini))
                      (fun s => beq (documented_realms s) [Afrotropic]));
    [vm_compute; reflexivity | apply beq_true, Hs].
Qed.

(* The only squirrels in the Australasian realm are the three Sulawesi genera
   of Nannosciurini. *)
Theorem australasian_genera :
  filter (fun g => mem Australasia (genus_realms g)) enum = [Hyosciurus; Prosciurillus; Rubrisciurus] /\
  map genus_tribe [Hyosciurus; Prosciurillus; Rubrisciurus] = [Some Nannosciurini; Some Nannosciurini; Some Nannosciurini].
Proof. vm_compute. split; reflexivity. Qed.

(* Exactly three genera are Holarctic (native to both the Nearctic and the
   Palearctic), and Urocitellus is one of them. *)
Theorem holarctic_genera :
  filter (fun g => mem Nearctic (genus_realms g) && mem Palearctic (genus_realms g)) enum =
  [Sciurus; Marmota; Urocitellus].
Proof. vm_compute. reflexivity. Qed.

Theorem urocitellus_holarctic :
  In Nearctic (genus_confirmed_realms Urocitellus) /\ In Palearctic (genus_confirmed_realms Urocitellus) /\
  In Palearctic (realms (info (sp Urocitellus_undulatus))) /\ In Asia (genus_continents Urocitellus).
Proof. vm_compute. repeat split; repeat (first [left; reflexivity | right]). Qed.

(* The only flying squirrel native to the Neotropical realm. *)
Theorem neotropical_flying_squirrels :
  filter (fun s => beq (species_tribe s) (Some Pteromyini) && mem Neotropic (documented_realms s)) enum =
  [sp Glaucomys_volans].
Proof. vm_compute. reflexivity. Qed.

Theorem south_american_genera :
  filter (fun g => mem South_America (genus_continents g)) enum = [Sciurillus; Microsciurus; Sciurus].
Proof. vm_compute. reflexivity. Qed.

Theorem european_genera :
  filter (fun g => mem Europe (genus_continents g)) enum = [Pteromys; Sciurus; Marmota; Spermophilus; Eutamias].
Proof. vm_compute. reflexivity. Qed.

(* ======================== Diversity ======================== *)

Definition genera_on (c : Continent) : nat := count (fun g => mem c (genus_continents g)) enum.
Definition species_on (c : Continent) : nat := count (fun s => mem c (species_continents s)) enum.
Definition genera_in_realm (r : Realm) : nat := count (fun g => mem r (genus_realms g)) enum.
Definition genera_in_country (c : Country) : nat := count (fun g => mem c (genus_countries g)) enum.

Theorem continental_diversity :
  map (fun c => (c, genera_on c, species_on c)) enum =
  [(Africa, 10, 36); (Antarctica, 0, 0); (Asia, 39, 167); (Europe, 5, 16);
   (North_America, 17, 96); (Oceania, 0, 0); (South_America, 3, 21)].
Proof. vm_compute. reflexivity. Qed.

Theorem asia_richest (c : Continent) : c <> Asia -> genera_on c < genera_on Asia.
Proof.
  intros Hne.
  assert (H : forall c, negb (beq c Asia) = true -> (genera_on c <? genera_on Asia) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  apply Nat.ltb_lt, H; destruct (beq_spec c Asia); [contradiction | reflexivity].
Qed.

Theorem realm_diversity :
  map (fun r => (r, genera_in_realm r)) enum =
  [(Afrotropic, 9); (Antarctic, 0); (Australasia, 3); (Indomalaya, 25); (Nearctic, 15);
   (Neotropic, 5); (Oceanian, 0); (Palearctic, 24)].
Proof. vm_compute. reflexivity. Qed.

(* China has more native sciurid genera than any other country. *)
Lemma genera_in_country_table (c : Country) :
  genera_in_country c = count (mem c) (map genus_countries enum).
Proof. unfold genera_in_country; rewrite count_map; reflexivity. Qed.

Theorem china_richest_in_genera (c : Country) : c <> China -> genera_in_country c < genera_in_country China.
Proof.
  intros Hne; rewrite !genera_in_country_table.
  assert (H : forall c, negb (beq c China) = true ->
            (count (mem c) (map genus_countries enum) <? count (mem China) (map genus_countries enum)) = true).
  { apply enum_implies; precompute (map genus_countries enum); vm_compute; reflexivity. }
  apply Nat.ltb_lt, H; destruct (beq_spec c China); [contradiction | reflexivity].
Qed.

Theorem china_genus_count : genera_in_country China = 20.
Proof. vm_compute. reflexivity. Qed.

(* ======================== Endemism ======================== *)

Definition endemic_to_realm (g : Genus) (r : Realm) : Prop := genus_realms g = [r].

Definition realm_endemics (r : Realm) : list Genus :=
  filter (fun g => beq (genus_realms g) [r]) enum.

Theorem realm_endemic_counts :
  map (fun r => (r, List.length (realm_endemics r))) enum =
  [(Afrotropic, 8); (Antarctic, 0); (Australasia, 3); (Indomalaya, 14); (Nearctic, 11);
   (Neotropic, 3); (Oceanian, 0); (Palearctic, 9)].
Proof. vm_compute. reflexivity. Qed.

Theorem realm_endemics_spec (g : Genus) (r : Realm) :
  In g (realm_endemics r) <-> endemic_to_realm g r.
Proof.
  unfold realm_endemics, endemic_to_realm; rewrite filter_In, beq_true.
  split; [tauto | intros H; split; [apply enum_complete | exact H]].
Qed.

(* ======================== Uncertain records ======================== *)

Theorem species_with_uncertain_records :
  count (fun s => negb (beq (countries_uncertain (info s)) []) || negb (beq (realms_uncertain (info s)) [])) enum = 15.
Proof. vm_compute. reflexivity. Qed.
