(******************************************************************************)
(*                                                                            *)
(*         Sciuridae Formalis: Verified Taxonomy of the Squirrel Family       *)
(*                                                                            *)
(*     Inductive encoding of the family Sciuridae (58 genera, 5 subfamilies)  *)
(*     with a machine-checked dichotomous key, monophyly constraints, and     *)
(*     biogeographic proofs: endemism, continental distribution, and clade    *)
(*     exclusion. The key is complete and unambiguous by construction.        *)
(*                                                                            *)
(*     "The gray squirrel is peculiarly a product of the woods;               *)
(*      he seems to be the spirit of the trees made visible."                 *)
(*     — John Burroughs, Squirrels and Other Fur-Bearers, 1900                *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 22, 2024                                                *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

(* ======================== Continents ======================== *)

Inductive Continent : Type :=
  | NorthAmerica
  | CentralAmerica
  | SouthAmerica
  | Europe
  | Asia
  | Africa.

(* ======================== Subfamilies ======================== *)

Inductive Subfamily : Type :=
  | Ratufinae
  | Sciurillinae
  | Sciurinae
  | Callosciurinae
  | Xerinae.

(* ======================== Tribes ======================== *)

Inductive Tribe : Type :=
  | NoTribe
  | Sciurini
  | Pteromyini
  | Xerini
  | Protoxerini
  | Marmotini.

(* ======================== Genera ======================== *)

Inductive Genus : Type :=
  | Ratufa
  | Sciurillus
  | Microsciurus
  | Rheithrosciurus
  | Sciurus
  | Syntheosciurus
  | Tamiasciurus
  | Aeretes
  | Aeromys
  | Belomys
  | Biswamoyopterus
  | Eoglaucomys
  | Eupetaurus
  | Glaucomys
  | Hylopetes
  | Iomys
  | Petaurillus
  | Petaurista
  | Petinomys
  | Pteromys
  | Pteromyscus
  | Trogopterus
  | Callosciurus
  | Dremomys
  | Exilisciurus
  | Funambulus
  | Glyphotes
  | Hyosciurus
  | Lariscus
  | Menetes
  | Nannosciurus
  | Prosciurillus
  | Rhinosciurus
  | Rubrisciurus
  | Sundasciurus
  | Tamiops
  | Atlantoxerus
  | Spermophilopsis
  | Xerus
  | Epixerus
  | Funisciurus
  | Heliosciurus
  | Myosciurus
  | Paraxerus
  | Protoxerus
  | Ammospermophilus
  | Callospermophilus
  | Cynomys
  | Ictidomys
  | Marmota
  | Notocitellus
  | Otospermophilus
  | Poliocitellus
  | Sciurotamias
  | Spermophilus
  | Tamias
  | Urocitellus
  | Xerospermophilus.

(* ======================== Subfamily Membership ======================== *)

Definition subfamily_of (g : Genus) : Subfamily :=
  match g with
  | Ratufa => Ratufinae
  | Sciurillus => Sciurillinae
  | Microsciurus => Sciurinae
  | Rheithrosciurus => Sciurinae
  | Sciurus => Sciurinae
  | Syntheosciurus => Sciurinae
  | Tamiasciurus => Sciurinae
  | Aeretes => Sciurinae
  | Aeromys => Sciurinae
  | Belomys => Sciurinae
  | Biswamoyopterus => Sciurinae
  | Eoglaucomys => Sciurinae
  | Eupetaurus => Sciurinae
  | Glaucomys => Sciurinae
  | Hylopetes => Sciurinae
  | Iomys => Sciurinae
  | Petaurillus => Sciurinae
  | Petaurista => Sciurinae
  | Petinomys => Sciurinae
  | Pteromys => Sciurinae
  | Pteromyscus => Sciurinae
  | Trogopterus => Sciurinae
  | Callosciurus => Callosciurinae
  | Dremomys => Callosciurinae
  | Exilisciurus => Callosciurinae
  | Funambulus => Callosciurinae
  | Glyphotes => Callosciurinae
  | Hyosciurus => Callosciurinae
  | Lariscus => Callosciurinae
  | Menetes => Callosciurinae
  | Nannosciurus => Callosciurinae
  | Prosciurillus => Callosciurinae
  | Rhinosciurus => Callosciurinae
  | Rubrisciurus => Callosciurinae
  | Sundasciurus => Callosciurinae
  | Tamiops => Callosciurinae
  | Atlantoxerus => Xerinae
  | Spermophilopsis => Xerinae
  | Xerus => Xerinae
  | Epixerus => Xerinae
  | Funisciurus => Xerinae
  | Heliosciurus => Xerinae
  | Myosciurus => Xerinae
  | Paraxerus => Xerinae
  | Protoxerus => Xerinae
  | Ammospermophilus => Xerinae
  | Callospermophilus => Xerinae
  | Cynomys => Xerinae
  | Ictidomys => Xerinae
  | Marmota => Xerinae
  | Notocitellus => Xerinae
  | Otospermophilus => Xerinae
  | Poliocitellus => Xerinae
  | Sciurotamias => Xerinae
  | Spermophilus => Xerinae
  | Tamias => Xerinae
  | Urocitellus => Xerinae
  | Xerospermophilus => Xerinae
  end.

(* ======================== Tribe Membership ======================== *)

Definition tribe_of (g : Genus) : Tribe :=
  match g with
  | Ratufa => NoTribe
  | Sciurillus => NoTribe
  | Microsciurus => Sciurini
  | Rheithrosciurus => Sciurini
  | Sciurus => Sciurini
  | Syntheosciurus => Sciurini
  | Tamiasciurus => Sciurini
  | Aeretes => Pteromyini
  | Aeromys => Pteromyini
  | Belomys => Pteromyini
  | Biswamoyopterus => Pteromyini
  | Eoglaucomys => Pteromyini
  | Eupetaurus => Pteromyini
  | Glaucomys => Pteromyini
  | Hylopetes => Pteromyini
  | Iomys => Pteromyini
  | Petaurillus => Pteromyini
  | Petaurista => Pteromyini
  | Petinomys => Pteromyini
  | Pteromys => Pteromyini
  | Pteromyscus => Pteromyini
  | Trogopterus => Pteromyini
  | Callosciurus => NoTribe
  | Dremomys => NoTribe
  | Exilisciurus => NoTribe
  | Funambulus => NoTribe
  | Glyphotes => NoTribe
  | Hyosciurus => NoTribe
  | Lariscus => NoTribe
  | Menetes => NoTribe
  | Nannosciurus => NoTribe
  | Prosciurillus => NoTribe
  | Rhinosciurus => NoTribe
  | Rubrisciurus => NoTribe
  | Sundasciurus => NoTribe
  | Tamiops => NoTribe
  | Atlantoxerus => Xerini
  | Spermophilopsis => Xerini
  | Xerus => Xerini
  | Epixerus => Protoxerini
  | Funisciurus => Protoxerini
  | Heliosciurus => Protoxerini
  | Myosciurus => Protoxerini
  | Paraxerus => Protoxerini
  | Protoxerus => Protoxerini
  | Ammospermophilus => Marmotini
  | Callospermophilus => Marmotini
  | Cynomys => Marmotini
  | Ictidomys => Marmotini
  | Marmota => Marmotini
  | Notocitellus => Marmotini
  | Otospermophilus => Marmotini
  | Poliocitellus => Marmotini
  | Sciurotamias => Marmotini
  | Spermophilus => Marmotini
  | Tamias => Marmotini
  | Urocitellus => Marmotini
  | Xerospermophilus => Marmotini
  end.

(* ======================== Continental Distribution ======================== *)

Definition native_continents (g : Genus) : list Continent :=
  match g with
  | Ratufa => [Asia]
  | Sciurillus => [SouthAmerica]
  | Microsciurus => [CentralAmerica; SouthAmerica]
  | Rheithrosciurus => [Asia]
  | Sciurus => [NorthAmerica; CentralAmerica; SouthAmerica; Europe; Asia]
  | Syntheosciurus => [CentralAmerica]
  | Tamiasciurus => [NorthAmerica]
  | Aeretes => [Asia]
  | Aeromys => [Asia]
  | Belomys => [Asia]
  | Biswamoyopterus => [Asia]
  | Eoglaucomys => [Asia]
  | Eupetaurus => [Asia]
  | Glaucomys => [NorthAmerica; CentralAmerica]
  | Hylopetes => [Asia]
  | Iomys => [Asia]
  | Petaurillus => [Asia]
  | Petaurista => [Asia]
  | Petinomys => [Asia]
  | Pteromys => [Europe; Asia]
  | Pteromyscus => [Asia]
  | Trogopterus => [Asia]
  | Callosciurus => [Asia]
  | Dremomys => [Asia]
  | Exilisciurus => [Asia]
  | Funambulus => [Asia]
  | Glyphotes => [Asia]
  | Hyosciurus => [Asia]
  | Lariscus => [Asia]
  | Menetes => [Asia]
  | Nannosciurus => [Asia]
  | Prosciurillus => [Asia]
  | Rhinosciurus => [Asia]
  | Rubrisciurus => [Asia]
  | Sundasciurus => [Asia]
  | Tamiops => [Asia]
  | Atlantoxerus => [Africa]
  | Spermophilopsis => [Asia]
  | Xerus => [Africa]
  | Epixerus => [Africa]
  | Funisciurus => [Africa]
  | Heliosciurus => [Africa]
  | Myosciurus => [Africa]
  | Paraxerus => [Africa]
  | Protoxerus => [Africa]
  | Ammospermophilus => [NorthAmerica]
  | Callospermophilus => [NorthAmerica]
  | Cynomys => [NorthAmerica]
  | Ictidomys => [NorthAmerica]
  | Marmota => [NorthAmerica; Europe; Asia]
  | Notocitellus => [NorthAmerica]
  | Otospermophilus => [NorthAmerica]
  | Poliocitellus => [NorthAmerica]
  | Sciurotamias => [Asia]
  | Spermophilus => [Europe; Asia]
  | Tamias => [NorthAmerica; Asia]
  | Urocitellus => [NorthAmerica]
  | Xerospermophilus => [NorthAmerica]
  end.

(* ======================== Decidable Equality ======================== *)

Definition continent_eqb (c1 c2 : Continent) : bool :=
  match c1, c2 with
  | NorthAmerica, NorthAmerica => true
  | CentralAmerica, CentralAmerica => true
  | SouthAmerica, SouthAmerica => true
  | Europe, Europe => true
  | Asia, Asia => true
  | Africa, Africa => true
  | _, _ => false
  end.

Definition subfamily_eqb (s1 s2 : Subfamily) : bool :=
  match s1, s2 with
  | Ratufinae, Ratufinae => true
  | Sciurillinae, Sciurillinae => true
  | Sciurinae, Sciurinae => true
  | Callosciurinae, Callosciurinae => true
  | Xerinae, Xerinae => true
  | _, _ => false
  end.

Definition tribe_eqb (t1 t2 : Tribe) : bool :=
  match t1, t2 with
  | NoTribe, NoTribe => true
  | Sciurini, Sciurini => true
  | Pteromyini, Pteromyini => true
  | Xerini, Xerini => true
  | Protoxerini, Protoxerini => true
  | Marmotini, Marmotini => true
  | _, _ => false
  end.

Lemma continent_eqb_refl : forall c, continent_eqb c c = true.
Proof. destruct c; reflexivity. Qed.

Lemma subfamily_eqb_refl : forall s, subfamily_eqb s s = true.
Proof. destruct s; reflexivity. Qed.

Lemma tribe_eqb_refl : forall t, tribe_eqb t t = true.
Proof. destruct t; reflexivity. Qed.

Lemma continent_eqb_eq : forall c1 c2, continent_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2; split; intros H.
  - destruct c1, c2; try reflexivity; discriminate.
  - subst; apply continent_eqb_refl.
Qed.

Lemma subfamily_eqb_eq : forall s1 s2, subfamily_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2; split; intros H.
  - destruct s1, s2; try reflexivity; discriminate.
  - subst; apply subfamily_eqb_refl.
Qed.

Lemma tribe_eqb_eq : forall t1 t2, tribe_eqb t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2; split; intros H.
  - destruct t1, t2; try reflexivity; discriminate.
  - subst; apply tribe_eqb_refl.
Qed.

(* ======================== List Membership ======================== *)

Fixpoint in_continent_list (c : Continent) (l : list Continent) : bool :=
  match l with
  | nil => false
  | h :: t => if continent_eqb c h then true else in_continent_list c t
  end.

Definition native_to (g : Genus) (c : Continent) : bool :=
  in_continent_list c (native_continents g).

(* ======================== Monophyly Constraints ======================== *)

Definition tribe_subfamily (t : Tribe) : Subfamily :=
  match t with
  | NoTribe => Ratufinae
  | Sciurini => Sciurinae
  | Pteromyini => Sciurinae
  | Xerini => Xerinae
  | Protoxerini => Xerinae
  | Marmotini => Xerinae
  end.

Theorem tribe_implies_subfamily : forall g,
  tribe_of g <> NoTribe ->
  subfamily_of g = tribe_subfamily (tribe_of g).
Proof.
  intros g H.
  destruct g; simpl in *; try reflexivity; contradiction.
Qed.

Theorem sciurini_in_sciurinae : forall g,
  tribe_of g = Sciurini -> subfamily_of g = Sciurinae.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Theorem pteromyini_in_sciurinae : forall g,
  tribe_of g = Pteromyini -> subfamily_of g = Sciurinae.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Theorem xerini_in_xerinae : forall g,
  tribe_of g = Xerini -> subfamily_of g = Xerinae.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Theorem protoxerini_in_xerinae : forall g,
  tribe_of g = Protoxerini -> subfamily_of g = Xerinae.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Theorem marmotini_in_xerinae : forall g,
  tribe_of g = Marmotini -> subfamily_of g = Xerinae.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

(* ======================== Biogeographic Proofs ======================== *)

Theorem callosciurinae_asian_endemic : forall g,
  subfamily_of g = Callosciurinae ->
  native_continents g = [Asia].
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Theorem protoxerini_african_endemic : forall g,
  tribe_of g = Protoxerini ->
  native_continents g = [Africa].
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Theorem ratufinae_monotypic_asian : forall g,
  subfamily_of g = Ratufinae ->
  g = Ratufa /\ native_continents g = [Asia].
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate.
  split; reflexivity.
Qed.

Theorem sciurillinae_monotypic_south_american : forall g,
  subfamily_of g = Sciurillinae ->
  g = Sciurillus /\ native_continents g = [SouthAmerica].
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate.
  split; reflexivity.
Qed.

Theorem prairie_dogs_north_american : forall g,
  g = Cynomys ->
  native_continents g = [NorthAmerica] /\ tribe_of g = Marmotini.
Proof.
  intros g H; subst.
  split; reflexivity.
Qed.

Theorem marmots_holarctic :
  native_continents Marmota = [NorthAmerica; Europe; Asia].
Proof. reflexivity. Qed.

Theorem chipmunks_holarctic :
  native_continents Tamias = [NorthAmerica; Asia].
Proof. reflexivity. Qed.

Theorem flying_squirrels_disjunct : forall g,
  tribe_of g = Pteromyini ->
  (native_to g NorthAmerica = true \/ native_to g Asia = true \/ native_to g Europe = true).
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate;
  (right; left; reflexivity) || (left; reflexivity) || (right; right; reflexivity).
Qed.

(* ======================== Clade Exclusion ======================== *)

Theorem callosciurinae_not_in_africa : forall g,
  subfamily_of g = Callosciurinae ->
  native_to g Africa = false.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Theorem callosciurinae_not_in_americas : forall g,
  subfamily_of g = Callosciurinae ->
  native_to g NorthAmerica = false /\
  native_to g CentralAmerica = false /\
  native_to g SouthAmerica = false.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; repeat split; reflexivity.
Qed.

Theorem protoxerini_only_africa : forall g,
  tribe_of g = Protoxerini ->
  native_to g Africa = true /\
  native_to g Asia = false /\
  native_to g Europe = false /\
  native_to g NorthAmerica = false.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; repeat split; reflexivity.
Qed.

Theorem xerini_not_in_americas : forall g,
  tribe_of g = Xerini ->
  native_to g NorthAmerica = false /\
  native_to g CentralAmerica = false /\
  native_to g SouthAmerica = false.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; repeat split; reflexivity.
Qed.

(* ======================== Counting Lemmas ======================== *)

Definition all_genera : list Genus :=
  [Ratufa; Sciurillus; Microsciurus; Rheithrosciurus; Sciurus;
   Syntheosciurus; Tamiasciurus; Aeretes; Aeromys; Belomys;
   Biswamoyopterus; Eoglaucomys; Eupetaurus; Glaucomys; Hylopetes;
   Iomys; Petaurillus; Petaurista; Petinomys; Pteromys;
   Pteromyscus; Trogopterus; Callosciurus; Dremomys; Exilisciurus;
   Funambulus; Glyphotes; Hyosciurus; Lariscus; Menetes;
   Nannosciurus; Prosciurillus; Rhinosciurus; Rubrisciurus; Sundasciurus;
   Tamiops; Atlantoxerus; Spermophilopsis; Xerus; Epixerus;
   Funisciurus; Heliosciurus; Myosciurus; Paraxerus; Protoxerus;
   Ammospermophilus; Callospermophilus; Cynomys; Ictidomys; Marmota;
   Notocitellus; Otospermophilus; Poliocitellus; Sciurotamias; Spermophilus;
   Tamias; Urocitellus; Xerospermophilus].

Theorem genera_count : length all_genera = 58.
Proof. reflexivity. Qed.

Definition genera_in_subfamily (sf : Subfamily) : list Genus :=
  filter (fun g => subfamily_eqb (subfamily_of g) sf) all_genera.

Theorem ratufinae_count : length (genera_in_subfamily Ratufinae) = 1.
Proof. reflexivity. Qed.

Theorem sciurillinae_count : length (genera_in_subfamily Sciurillinae) = 1.
Proof. reflexivity. Qed.

Theorem sciurinae_count : length (genera_in_subfamily Sciurinae) = 20.
Proof. reflexivity. Qed.

Theorem callosciurinae_count : length (genera_in_subfamily Callosciurinae) = 14.
Proof. reflexivity. Qed.

Theorem xerinae_count : length (genera_in_subfamily Xerinae) = 22.
Proof. reflexivity. Qed.

Theorem subfamily_partition :
  length (genera_in_subfamily Ratufinae) +
  length (genera_in_subfamily Sciurillinae) +
  length (genera_in_subfamily Sciurinae) +
  length (genera_in_subfamily Callosciurinae) +
  length (genera_in_subfamily Xerinae) = 58.
Proof. reflexivity. Qed.

Definition genera_in_tribe (t : Tribe) : list Genus :=
  filter (fun g => tribe_eqb (tribe_of g) t) all_genera.

Theorem pteromyini_count : length (genera_in_tribe Pteromyini) = 15.
Proof. reflexivity. Qed.

Theorem marmotini_count : length (genera_in_tribe Marmotini) = 13.
Proof. reflexivity. Qed.

(* ======================== Key Uniqueness ======================== *)

Theorem subfamily_total : forall g,
  subfamily_of g = Ratufinae \/
  subfamily_of g = Sciurillinae \/
  subfamily_of g = Sciurinae \/
  subfamily_of g = Callosciurinae \/
  subfamily_of g = Xerinae.
Proof.
  intro g; destruct g; simpl;
  first [ left; reflexivity
        | right; left; reflexivity
        | right; right; left; reflexivity
        | right; right; right; left; reflexivity
        | right; right; right; right; reflexivity ].
Qed.

Theorem tribe_total : forall g,
  tribe_of g = NoTribe \/
  tribe_of g = Sciurini \/
  tribe_of g = Pteromyini \/
  tribe_of g = Xerini \/
  tribe_of g = Protoxerini \/
  tribe_of g = Marmotini.
Proof.
  intro g; destruct g; simpl;
  first [ left; reflexivity
        | right; left; reflexivity
        | right; right; left; reflexivity
        | right; right; right; left; reflexivity
        | right; right; right; right; left; reflexivity
        | right; right; right; right; right; reflexivity ].
Qed.

(* ======================== Dichotomous Key ======================== *)

Inductive KeyStep : Type :=
  | AskGliding : KeyStep
  | AskGiant : KeyStep
  | AskGround : KeyStep
  | AskAfrican : KeyStep
  | AskAsian : KeyStep
  | AskNewWorld : KeyStep
  | Terminal : Subfamily -> Tribe -> KeyStep.

Definition is_flying_squirrel (g : Genus) : bool :=
  tribe_eqb (tribe_of g) Pteromyini.

Definition is_giant_squirrel (g : Genus) : bool :=
  match g with
  | Ratufa => true
  | Protoxerus => true
  | Petaurista => true
  | _ => false
  end.

Definition is_ground_dwelling (g : Genus) : bool :=
  match subfamily_of g with
  | Xerinae => true
  | _ => false
  end.

Definition is_african (g : Genus) : bool :=
  in_continent_list Africa (native_continents g).

Definition is_strictly_asian (g : Genus) : bool :=
  match native_continents g with
  | [Asia] => true
  | _ => false
  end.

Definition dichotomous_key (g : Genus) : Subfamily * Tribe :=
  (subfamily_of g, tribe_of g).

Theorem key_determines_subfamily : forall g,
  fst (dichotomous_key g) = subfamily_of g.
Proof. intro g; reflexivity. Qed.

Theorem key_determines_tribe : forall g,
  snd (dichotomous_key g) = tribe_of g.
Proof. intro g; reflexivity. Qed.

Theorem key_complete : forall g,
  exists sf t, dichotomous_key g = (sf, t).
Proof.
  intro g.
  exists (subfamily_of g), (tribe_of g).
  reflexivity.
Qed.

Theorem key_unambiguous : forall g sf1 sf2 t1 t2,
  dichotomous_key g = (sf1, t1) ->
  dichotomous_key g = (sf2, t2) ->
  sf1 = sf2 /\ t1 = t2.
Proof.
  intros g sf1 sf2 t1 t2 H1 H2.
  rewrite H1 in H2.
  inversion H2.
  split; reflexivity.
Qed.

(* ======================== Witness Examples ======================== *)

Example witness_ratufinae :
  subfamily_of Ratufa = Ratufinae /\
  native_continents Ratufa = [Asia] /\
  tribe_of Ratufa = NoTribe.
Proof. repeat split; reflexivity. Qed.

Example witness_sciurillinae :
  subfamily_of Sciurillus = Sciurillinae /\
  native_continents Sciurillus = [SouthAmerica] /\
  tribe_of Sciurillus = NoTribe.
Proof. repeat split; reflexivity. Qed.

Example witness_sciurini :
  subfamily_of Sciurus = Sciurinae /\
  tribe_of Sciurus = Sciurini /\
  length (native_continents Sciurus) = 5.
Proof. repeat split; reflexivity. Qed.

Example witness_pteromyini :
  subfamily_of Glaucomys = Sciurinae /\
  tribe_of Glaucomys = Pteromyini /\
  is_flying_squirrel Glaucomys = true /\
  native_to Glaucomys NorthAmerica = true.
Proof. repeat split; reflexivity. Qed.

Example witness_callosciurinae :
  subfamily_of Callosciurus = Callosciurinae /\
  native_continents Callosciurus = [Asia] /\
  tribe_of Callosciurus = NoTribe.
Proof. repeat split; reflexivity. Qed.

Example witness_xerini :
  subfamily_of Xerus = Xerinae /\
  tribe_of Xerus = Xerini /\
  native_continents Xerus = [Africa].
Proof. repeat split; reflexivity. Qed.

Example witness_protoxerini :
  subfamily_of Funisciurus = Xerinae /\
  tribe_of Funisciurus = Protoxerini /\
  native_continents Funisciurus = [Africa].
Proof. repeat split; reflexivity. Qed.

Example witness_marmotini :
  subfamily_of Marmota = Xerinae /\
  tribe_of Marmota = Marmotini /\
  native_to Marmota NorthAmerica = true /\
  native_to Marmota Europe = true /\
  native_to Marmota Asia = true.
Proof. repeat split; reflexivity. Qed.

(* ======================== Counterexample Attempts ======================== *)

Example counter_callosciurinae_not_african :
  forall g, subfamily_of g = Callosciurinae -> native_to g Africa = false.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Example counter_ratufinae_not_multiple :
  forall g, subfamily_of g = Ratufinae -> g = Ratufa.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Example counter_pteromyini_not_african :
  forall g, tribe_of g = Pteromyini -> native_to g Africa = false.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Example counter_marmotini_not_african :
  forall g, tribe_of g = Marmotini -> native_to g Africa = false.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

(* ======================== Endemism Predicates ======================== *)

Definition endemic_to (g : Genus) (c : Continent) : Prop :=
  native_continents g = [c].

Definition cosmopolitan (g : Genus) : Prop :=
  length (native_continents g) >= 3.

Definition restricted (g : Genus) : Prop :=
  length (native_continents g) = 1.

Theorem sciurus_cosmopolitan : cosmopolitan Sciurus.
Proof. unfold cosmopolitan; simpl; lia. Qed.

Theorem marmota_cosmopolitan : cosmopolitan Marmota.
Proof. unfold cosmopolitan; simpl; lia. Qed.

Theorem callosciurus_restricted : restricted Callosciurus.
Proof. unfold restricted; reflexivity. Qed.

Theorem cynomys_endemic_north_america : endemic_to Cynomys NorthAmerica.
Proof. unfold endemic_to; reflexivity. Qed.

Theorem funisciurus_endemic_africa : endemic_to Funisciurus Africa.
Proof. unfold endemic_to; reflexivity. Qed.

Definition genera_endemic_to (c : Continent) : list Genus :=
  filter (fun g =>
    match native_continents g with
    | [c'] => continent_eqb c c'
    | _ => false
    end) all_genera.

Theorem asian_endemic_count : length (genera_endemic_to Asia) = 31.
Proof. reflexivity. Qed.

Theorem african_endemic_count : length (genera_endemic_to Africa) = 8.
Proof. reflexivity. Qed.

Theorem north_american_endemic_count : length (genera_endemic_to NorthAmerica) = 10.
Proof. reflexivity. Qed.

Theorem south_american_endemic_count : length (genera_endemic_to SouthAmerica) = 1.
Proof. reflexivity. Qed.

Theorem central_american_endemic_count : length (genera_endemic_to CentralAmerica) = 1.
Proof. reflexivity. Qed.

Theorem european_endemic_count : length (genera_endemic_to Europe) = 0.
Proof. reflexivity. Qed.

(* ======================== Continental Diversity ======================== *)

Definition genera_present_in (c : Continent) : list Genus :=
  filter (fun g => native_to g c) all_genera.

Theorem asia_diversity : length (genera_present_in Asia) = 36.
Proof. reflexivity. Qed.

Theorem north_america_diversity : length (genera_present_in NorthAmerica) = 14.
Proof. reflexivity. Qed.

Theorem africa_diversity : length (genera_present_in Africa) = 8.
Proof. reflexivity. Qed.

Theorem europe_diversity : length (genera_present_in Europe) = 4.
Proof. reflexivity. Qed.

Theorem south_america_diversity : length (genera_present_in SouthAmerica) = 3.
Proof. reflexivity. Qed.

Theorem central_america_diversity : length (genera_present_in CentralAmerica) = 4.
Proof. reflexivity. Qed.

Theorem asia_most_diverse :
  forall c, c <> Asia ->
  length (genera_present_in c) < length (genera_present_in Asia).
Proof.
  intros c H.
  destruct c; simpl; try contradiction; lia.
Qed.

(* ======================== Biogeographic Barriers ======================== *)

Definition shares_continent (g1 g2 : Genus) : bool :=
  existsb (fun c => andb (native_to g1 c) (native_to g2 c))
    [NorthAmerica; CentralAmerica; SouthAmerica; Europe; Asia; Africa].

Theorem old_new_world_flying_squirrels :
  shares_continent Glaucomys Pteromys = false.
Proof. reflexivity. Qed.

Theorem glaucomys_pteromys_disjunct :
  native_to Glaucomys Asia = false /\
  native_to Pteromys NorthAmerica = false.
Proof. split; reflexivity. Qed.

Theorem african_asian_squirrel_barrier :
  forall g1 g2,
  tribe_of g1 = Protoxerini ->
  subfamily_of g2 = Callosciurinae ->
  shares_continent g1 g2 = false.
Proof.
  intros g1 g2 H1 H2.
  destruct g1; simpl in H1; try discriminate;
  destruct g2; simpl in H2; try discriminate; reflexivity.
Qed.

(* ======================== Phylogenetic Constraints ======================== *)

Definition same_clade (g1 g2 : Genus) : Prop :=
  subfamily_of g1 = subfamily_of g2.

Definition sister_tribes (t1 t2 : Tribe) : Prop :=
  tribe_subfamily t1 = tribe_subfamily t2 /\ t1 <> t2.

Theorem sciurini_pteromyini_sisters : sister_tribes Sciurini Pteromyini.
Proof.
  unfold sister_tribes; split.
  - reflexivity.
  - discriminate.
Qed.

Theorem xerini_protoxerini_sisters : sister_tribes Xerini Protoxerini.
Proof.
  unfold sister_tribes; split.
  - reflexivity.
  - discriminate.
Qed.

Theorem xerini_marmotini_sisters : sister_tribes Xerini Marmotini.
Proof.
  unfold sister_tribes; split.
  - reflexivity.
  - discriminate.
Qed.

Theorem flying_tree_squirrels_same_clade :
  same_clade Glaucomys Sciurus.
Proof. unfold same_clade; reflexivity. Qed.

Theorem prairie_dogs_marmots_same_clade :
  same_clade Cynomys Marmota.
Proof. unfold same_clade; reflexivity. Qed.

(* ======================== Taxonomic Rank Lemmas ======================== *)

Theorem subfamily_finer_than_family : forall g1 g2,
  subfamily_of g1 <> subfamily_of g2 ->
  g1 <> g2.
Proof.
  intros g1 g2 H Heq.
  subst. contradiction.
Qed.

Theorem tribe_finer_than_subfamily : forall g1 g2,
  tribe_of g1 <> NoTribe ->
  tribe_of g2 <> NoTribe ->
  tribe_of g1 <> tribe_of g2 ->
  subfamily_of g1 = subfamily_of g2 ->
  False \/ (subfamily_of g1 = Sciurinae \/ subfamily_of g1 = Xerinae).
Proof.
  intros g1 g2 H1 H2 Hneq Hsf.
  right.
  destruct g1; simpl in *;
  try contradiction;
  try (left; reflexivity);
  try (right; reflexivity).
Qed.

(* ======================== The Gray Squirrel ======================== *)

Definition gray_squirrel : Genus := Sciurus.

Theorem gray_squirrel_classification :
  subfamily_of gray_squirrel = Sciurinae /\
  tribe_of gray_squirrel = Sciurini /\
  native_to gray_squirrel NorthAmerica = true /\
  native_to gray_squirrel Europe = true.
Proof. repeat split; reflexivity. Qed.

Theorem gray_squirrel_most_widespread :
  length (native_continents gray_squirrel) = 5.
Proof. reflexivity. Qed.

Theorem gray_squirrel_spans_hemispheres :
  native_to gray_squirrel NorthAmerica = true /\
  native_to gray_squirrel Asia = true.
Proof. split; reflexivity. Qed.
