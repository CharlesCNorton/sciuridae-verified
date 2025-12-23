(******************************************************************************)
(*                                                                            *)
(*         Sciuridae Formalis: Verified Taxonomy of the Squirrel Family       *)
(*                                                                            *)
(*     Inductive encoding of the family Sciuridae (63 genera, 5 subfamilies)  *)
(*     with a machine-checked dichotomous key, monophyly constraints, and     *)
(*     biogeographic proofs: endemism, continental distribution, and clade    *)
(*     exclusion. The key is complete and unambiguous by construction.        *)
(*                                                                            *)
(*     The gray squirrel is peculiarly a product of the woods;                *)
(*     he seems to be the spirit of the trees made visible.                   *)
(*                                  -- John Burroughs, 1900                   *)
(*                                                                            *)
(*     In memoriam: the small lives lost beneath our wheels.                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 22, 2025                                                *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.
Local Open Scope string_scope.

Ltac genus_destruct g := destruct g; simpl in *; try discriminate; auto.
Ltac genus_exhaust := intros; match goal with | g : _ |- _ => genus_destruct g end.

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
  | Neotamias
  | Urocitellus
  | Xerospermophilus
  | Douglassciurus
  | Hesperopetes
  | Palaeosciurus
  | Protosciurus.

Definition common_name (g : Genus) : string :=
  match g with
  | Ratufa => "Giant squirrels"
  | Sciurillus => "Neotropical pygmy squirrel"
  | Microsciurus => "Dwarf squirrels"
  | Rheithrosciurus => "Tufted ground squirrel"
  | Sciurus => "Tree squirrels"
  | Syntheosciurus => "Bangs's mountain squirrel"
  | Tamiasciurus => "Pine squirrels"
  | Aeretes => "Groove-toothed flying squirrel"
  | Aeromys => "Black flying squirrels"
  | Belomys => "Hairy-footed flying squirrel"
  | Biswamoyopterus => "Namdapha flying squirrel"
  | Eoglaucomys => "Kashmir flying squirrel"
  | Eupetaurus => "Woolly flying squirrel"
  | Glaucomys => "New World flying squirrels"
  | Hylopetes => "Arrow-tailed flying squirrels"
  | Iomys => "Javanese flying squirrel"
  | Petaurillus => "Pygmy flying squirrels"
  | Petaurista => "Giant flying squirrels"
  | Petinomys => "Dwarf flying squirrels"
  | Pteromys => "Old World flying squirrels"
  | Pteromyscus => "Smoky flying squirrel"
  | Trogopterus => "Complex-toothed flying squirrel"
  | Callosciurus => "Beautiful squirrels"
  | Dremomys => "Red-cheeked squirrels"
  | Exilisciurus => "Philippine pygmy squirrels"
  | Funambulus => "Palm squirrels"
  | Glyphotes => "Sculptor squirrel"
  | Hyosciurus => "Sulawesi long-nosed squirrels"
  | Lariscus => "Striped ground squirrels"
  | Menetes => "Berdmore's ground squirrel"
  | Nannosciurus => "Black-eared squirrel"
  | Prosciurillus => "Sulawesi dwarf squirrels"
  | Rhinosciurus => "Shrew-faced squirrel"
  | Rubrisciurus => "Sulawesi giant squirrel"
  | Sundasciurus => "Sunda squirrels"
  | Tamiops => "Asiatic striped squirrels"
  | Atlantoxerus => "Barbary ground squirrel"
  | Spermophilopsis => "Long-clawed ground squirrel"
  | Xerus => "African ground squirrels"
  | Epixerus => "African palm squirrels"
  | Funisciurus => "Rope squirrels"
  | Heliosciurus => "Sun squirrels"
  | Myosciurus => "African pygmy squirrel"
  | Paraxerus => "Bush squirrels"
  | Protoxerus => "African giant squirrels"
  | Ammospermophilus => "Antelope squirrels"
  | Callospermophilus => "Golden-mantled ground squirrels"
  | Cynomys => "Prairie dogs"
  | Ictidomys => "Thirteen-lined ground squirrels"
  | Marmota => "Marmots"
  | Notocitellus => "Tropical ground squirrels"
  | Otospermophilus => "Rock squirrels"
  | Poliocitellus => "Franklin's ground squirrel"
  | Sciurotamias => "Chinese rock squirrels"
  | Spermophilus => "Ground squirrels"
  | Tamias => "Chipmunks"
  | Neotamias => "Western chipmunks"
  | Urocitellus => "Holarctic ground squirrels"
  | Xerospermophilus => "Spotted ground squirrels"
  | Douglassciurus => "Douglass's squirrel (fossil)"
  | Hesperopetes => "Western flying squirrel (fossil)"
  | Palaeosciurus => "Ancient ground squirrel (fossil)"
  | Protosciurus => "Proto-squirrel (fossil)"
  end.

(* ======================== Species ======================== *)

Inductive Species : Genus -> Type :=
  | Ratufa_affinis : Species Ratufa
  | Ratufa_bicolor : Species Ratufa
  | Ratufa_indica : Species Ratufa
  | Ratufa_macroura : Species Ratufa
  | Sciurillus_pusillus : Species Sciurillus
  | Microsciurus_alfari : Species Microsciurus
  | Microsciurus_flaviventer : Species Microsciurus
  | Microsciurus_mimulus : Species Microsciurus
  | Microsciurus_santanderensis : Species Microsciurus
  | Rheithrosciurus_macrotis : Species Rheithrosciurus
  | Sciurus_aberti : Species Sciurus
  | Sciurus_alleni : Species Sciurus
  | Sciurus_anomalus : Species Sciurus
  | Sciurus_arizonensis : Species Sciurus
  | Sciurus_aureogaster : Species Sciurus
  | Sciurus_carolinensis : Species Sciurus
  | Sciurus_colliaei : Species Sciurus
  | Sciurus_deppei : Species Sciurus
  | Sciurus_flammifer : Species Sciurus
  | Sciurus_gilvigularis : Species Sciurus
  | Sciurus_granatensis : Species Sciurus
  | Sciurus_griseus : Species Sciurus
  | Sciurus_igniventris : Species Sciurus
  | Sciurus_lis : Species Sciurus
  | Sciurus_nayaritensis : Species Sciurus
  | Sciurus_niger : Species Sciurus
  | Sciurus_oculatus : Species Sciurus
  | Sciurus_pucheranii : Species Sciurus
  | Sciurus_pyrrhinus : Species Sciurus
  | Sciurus_richmondi : Species Sciurus
  | Sciurus_sanborni : Species Sciurus
  | Sciurus_spadiceus : Species Sciurus
  | Sciurus_stramineus : Species Sciurus
  | Sciurus_variegatoides : Species Sciurus
  | Sciurus_vulgaris : Species Sciurus
  | Sciurus_yucatanensis : Species Sciurus
  | Syntheosciurus_brochus : Species Syntheosciurus
  | Tamiasciurus_douglasii : Species Tamiasciurus
  | Tamiasciurus_fremonti : Species Tamiasciurus
  | Tamiasciurus_hudsonicus : Species Tamiasciurus
  | Tamiasciurus_mearnsi : Species Tamiasciurus
  | Aeretes_melanopterus : Species Aeretes
  | Aeromys_tephromelas : Species Aeromys
  | Aeromys_thomasi : Species Aeromys
  | Belomys_pearsonii : Species Belomys
  | Biswamoyopterus_biswasi : Species Biswamoyopterus
  | Biswamoyopterus_laoensis : Species Biswamoyopterus
  | Eoglaucomys_fimbriatus : Species Eoglaucomys
  | Eupetaurus_cinereus : Species Eupetaurus
  | Glaucomys_oregonensis : Species Glaucomys
  | Glaucomys_sabrinus : Species Glaucomys
  | Glaucomys_volans : Species Glaucomys
  | Hylopetes_alboniger : Species Hylopetes
  | Hylopetes_baberi : Species Hylopetes
  | Hylopetes_bartelsi : Species Hylopetes
  | Hylopetes_lepidus : Species Hylopetes
  | Hylopetes_nigripes : Species Hylopetes
  | Hylopetes_phayrei : Species Hylopetes
  | Hylopetes_platyurus : Species Hylopetes
  | Hylopetes_sipora : Species Hylopetes
  | Hylopetes_spadiceus : Species Hylopetes
  | Hylopetes_winstoni : Species Hylopetes
  | Iomys_horsfieldii : Species Iomys
  | Iomys_sipora : Species Iomys
  | Petaurillus_emiliae : Species Petaurillus
  | Petaurillus_hosei : Species Petaurillus
  | Petaurillus_kinlochii : Species Petaurillus
  | Petaurista_alborufus : Species Petaurista
  | Petaurista_elegans : Species Petaurista
  | Petaurista_leucogenys : Species Petaurista
  | Petaurista_magnificus : Species Petaurista
  | Petaurista_mechukaensis : Species Petaurista
  | Petaurista_mishmiensis : Species Petaurista
  | Petaurista_nobilis : Species Petaurista
  | Petaurista_petaurista : Species Petaurista
  | Petaurista_philippensis : Species Petaurista
  | Petaurista_xanthotis : Species Petaurista
  | Petaurista_yunanensis : Species Petaurista
  | Petinomys_crinitus : Species Petinomys
  | Petinomys_fuscocapillus : Species Petinomys
  | Petinomys_genibarbis : Species Petinomys
  | Petinomys_hageni : Species Petinomys
  | Petinomys_lugens : Species Petinomys
  | Petinomys_mindanensis : Species Petinomys
  | Petinomys_sagitta : Species Petinomys
  | Petinomys_setosus : Species Petinomys
  | Petinomys_vordermanni : Species Petinomys
  | Pteromys_momonga : Species Pteromys
  | Pteromys_volans : Species Pteromys
  | Pteromyscus_pulverulentus : Species Pteromyscus
  | Trogopterus_xanthipes : Species Trogopterus
  | Callosciurus_adamsi : Species Callosciurus
  | Callosciurus_albescens : Species Callosciurus
  | Callosciurus_baluensis : Species Callosciurus
  | Callosciurus_caniceps : Species Callosciurus
  | Callosciurus_erythraeus : Species Callosciurus
  | Callosciurus_finlaysonii : Species Callosciurus
  | Callosciurus_inornatus : Species Callosciurus
  | Callosciurus_melanogaster : Species Callosciurus
  | Callosciurus_nigrovittatus : Species Callosciurus
  | Callosciurus_notatus : Species Callosciurus
  | Callosciurus_orestes : Species Callosciurus
  | Callosciurus_phayrei : Species Callosciurus
  | Callosciurus_prevostii : Species Callosciurus
  | Callosciurus_pygerythrus : Species Callosciurus
  | Callosciurus_quinquestriatus : Species Callosciurus
  | Dremomys_everetti : Species Dremomys
  | Dremomys_gularis : Species Dremomys
  | Dremomys_lokriah : Species Dremomys
  | Dremomys_pernyi : Species Dremomys
  | Dremomys_pyrrhomerus : Species Dremomys
  | Dremomys_rufigenis : Species Dremomys
  | Exilisciurus_concinnus : Species Exilisciurus
  | Exilisciurus_exilis : Species Exilisciurus
  | Exilisciurus_whiteheadi : Species Exilisciurus
  | Funambulus_layardi : Species Funambulus
  | Funambulus_palmarum : Species Funambulus
  | Funambulus_pennantii : Species Funambulus
  | Funambulus_sublineatus : Species Funambulus
  | Funambulus_tristriatus : Species Funambulus
  | Glyphotes_simus : Species Glyphotes
  | Hyosciurus_heinrichi : Species Hyosciurus
  | Hyosciurus_ileile : Species Hyosciurus
  | Lariscus_hosei : Species Lariscus
  | Lariscus_insignis : Species Lariscus
  | Lariscus_niobe : Species Lariscus
  | Lariscus_obscurus : Species Lariscus
  | Menetes_berdmorei : Species Menetes
  | Nannosciurus_melanotis : Species Nannosciurus
  | Prosciurillus_abstrusus : Species Prosciurillus
  | Prosciurillus_leucomus : Species Prosciurillus
  | Prosciurillus_murinus : Species Prosciurillus
  | Prosciurillus_topapuensis : Species Prosciurillus
  | Prosciurillus_weberi : Species Prosciurillus
  | Rhinosciurus_laticaudatus : Species Rhinosciurus
  | Rubrisciurus_rubriventer : Species Rubrisciurus
  | Sundasciurus_brookei : Species Sundasciurus
  | Sundasciurus_davensis : Species Sundasciurus
  | Sundasciurus_fraterculus : Species Sundasciurus
  | Sundasciurus_hippurus : Species Sundasciurus
  | Sundasciurus_hoogstraali : Species Sundasciurus
  | Sundasciurus_jentinki : Species Sundasciurus
  | Sundasciurus_juvencus : Species Sundasciurus
  | Sundasciurus_lowii : Species Sundasciurus
  | Sundasciurus_mindanensis : Species Sundasciurus
  | Sundasciurus_moellendorffi : Species Sundasciurus
  | Sundasciurus_philippinensis : Species Sundasciurus
  | Sundasciurus_rabori : Species Sundasciurus
  | Sundasciurus_samarensis : Species Sundasciurus
  | Sundasciurus_steerii : Species Sundasciurus
  | Sundasciurus_tenuis : Species Sundasciurus
  | Tamiops_mcclellandii : Species Tamiops
  | Tamiops_maritimus : Species Tamiops
  | Tamiops_rodolphii : Species Tamiops
  | Tamiops_swinhoei : Species Tamiops
  | Atlantoxerus_getulus : Species Atlantoxerus
  | Spermophilopsis_leptodactylus : Species Spermophilopsis
  | Xerus_erythropus : Species Xerus
  | Xerus_inauris : Species Xerus
  | Xerus_princeps : Species Xerus
  | Xerus_rutilus : Species Xerus
  | Epixerus_ebii : Species Epixerus
  | Epixerus_wilsoni : Species Epixerus
  | Funisciurus_anerythrus : Species Funisciurus
  | Funisciurus_bayonii : Species Funisciurus
  | Funisciurus_carruthersi : Species Funisciurus
  | Funisciurus_congicus : Species Funisciurus
  | Funisciurus_isabella : Species Funisciurus
  | Funisciurus_lemniscatus : Species Funisciurus
  | Funisciurus_leucogenys : Species Funisciurus
  | Funisciurus_pyrropus : Species Funisciurus
  | Funisciurus_substriatus : Species Funisciurus
  | Heliosciurus_gambianus : Species Heliosciurus
  | Heliosciurus_mutabilis : Species Heliosciurus
  | Heliosciurus_punctatus : Species Heliosciurus
  | Heliosciurus_rufobrachium : Species Heliosciurus
  | Heliosciurus_ruwenzorii : Species Heliosciurus
  | Heliosciurus_undulatus : Species Heliosciurus
  | Myosciurus_pumilio : Species Myosciurus
  | Paraxerus_alexandri : Species Paraxerus
  | Paraxerus_boehmi : Species Paraxerus
  | Paraxerus_cepapi : Species Paraxerus
  | Paraxerus_cooperi : Species Paraxerus
  | Paraxerus_flavovittis : Species Paraxerus
  | Paraxerus_lucifer : Species Paraxerus
  | Paraxerus_ochraceus : Species Paraxerus
  | Paraxerus_palliatus : Species Paraxerus
  | Paraxerus_poensis : Species Paraxerus
  | Paraxerus_vexillarius : Species Paraxerus
  | Paraxerus_vincenti : Species Paraxerus
  | Protoxerus_aubinnii : Species Protoxerus
  | Protoxerus_stangeri : Species Protoxerus
  | Ammospermophilus_harrisii : Species Ammospermophilus
  | Ammospermophilus_insularis : Species Ammospermophilus
  | Ammospermophilus_interpres : Species Ammospermophilus
  | Ammospermophilus_leucurus : Species Ammospermophilus
  | Ammospermophilus_nelsoni : Species Ammospermophilus
  | Callospermophilus_lateralis : Species Callospermophilus
  | Callospermophilus_madrensis : Species Callospermophilus
  | Callospermophilus_saturatus : Species Callospermophilus
  | Cynomys_gunnisoni : Species Cynomys
  | Cynomys_leucurus : Species Cynomys
  | Cynomys_ludovicianus : Species Cynomys
  | Cynomys_mexicanus : Species Cynomys
  | Cynomys_parvidens : Species Cynomys
  | Ictidomys_mexicanus : Species Ictidomys
  | Ictidomys_parvidens : Species Ictidomys
  | Ictidomys_tridecemlineatus : Species Ictidomys
  | Marmota_baibacina : Species Marmota
  | Marmota_bobak : Species Marmota
  | Marmota_broweri : Species Marmota
  | Marmota_caligata : Species Marmota
  | Marmota_camtschatica : Species Marmota
  | Marmota_caudata : Species Marmota
  | Marmota_flaviventris : Species Marmota
  | Marmota_himalayana : Species Marmota
  | Marmota_marmota : Species Marmota
  | Marmota_menzbieri : Species Marmota
  | Marmota_monax : Species Marmota
  | Marmota_olympus : Species Marmota
  | Marmota_sibirica : Species Marmota
  | Marmota_vancouverensis : Species Marmota
  | Notocitellus_adocetus : Species Notocitellus
  | Notocitellus_annulatus : Species Notocitellus
  | Otospermophilus_atricapillus : Species Otospermophilus
  | Otospermophilus_beecheyi : Species Otospermophilus
  | Otospermophilus_variegatus : Species Otospermophilus
  | Poliocitellus_franklinii : Species Poliocitellus
  | Sciurotamias_davidianus : Species Sciurotamias
  | Sciurotamias_forresti : Species Sciurotamias
  | Spermophilus_alashanicus : Species Spermophilus
  | Spermophilus_brevicauda : Species Spermophilus
  | Spermophilus_citellus : Species Spermophilus
  | Spermophilus_dauricus : Species Spermophilus
  | Spermophilus_erythrogenys : Species Spermophilus
  | Spermophilus_fulvus : Species Spermophilus
  | Spermophilus_major : Species Spermophilus
  | Spermophilus_musicus : Species Spermophilus
  | Spermophilus_pallidiccauda : Species Spermophilus
  | Spermophilus_pygmaeus : Species Spermophilus
  | Spermophilus_ralli : Species Spermophilus
  | Spermophilus_relictus : Species Spermophilus
  | Spermophilus_suslicus : Species Spermophilus
  | Spermophilus_taurensis : Species Spermophilus
  | Spermophilus_xanthoprymnus : Species Spermophilus
  | Tamias_sibiricus : Species Tamias
  | Tamias_striatus : Species Tamias
  | Neotamias_alpinus : Species Neotamias
  | Neotamias_amoenus : Species Neotamias
  | Neotamias_bulleri : Species Neotamias
  | Neotamias_canipes : Species Neotamias
  | Neotamias_cinereicollis : Species Neotamias
  | Neotamias_dorsalis : Species Neotamias
  | Neotamias_durangae : Species Neotamias
  | Neotamias_merriami : Species Neotamias
  | Neotamias_minimus : Species Neotamias
  | Neotamias_obscurus : Species Neotamias
  | Neotamias_ochrogenys : Species Neotamias
  | Neotamias_palmeri : Species Neotamias
  | Neotamias_panamintinus : Species Neotamias
  | Neotamias_quadrimaculatus : Species Neotamias
  | Neotamias_quadrivittatus : Species Neotamias
  | Neotamias_ruficaudus : Species Neotamias
  | Neotamias_rufus : Species Neotamias
  | Neotamias_senex : Species Neotamias
  | Neotamias_siskiyou : Species Neotamias
  | Neotamias_sonomae : Species Neotamias
  | Neotamias_speciosus : Species Neotamias
  | Neotamias_townsendii : Species Neotamias
  | Neotamias_umbrinus : Species Neotamias
  | Urocitellus_armatus : Species Urocitellus
  | Urocitellus_beldingi : Species Urocitellus
  | Urocitellus_brunneus : Species Urocitellus
  | Urocitellus_canus : Species Urocitellus
  | Urocitellus_columbianus : Species Urocitellus
  | Urocitellus_elegans : Species Urocitellus
  | Urocitellus_endemicus : Species Urocitellus
  | Urocitellus_mollis : Species Urocitellus
  | Urocitellus_parryii : Species Urocitellus
  | Urocitellus_richardsonii : Species Urocitellus
  | Urocitellus_townsendii : Species Urocitellus
  | Urocitellus_undulatus : Species Urocitellus
  | Urocitellus_washingtoni : Species Urocitellus
  | Xerospermophilus_mohavensis : Species Xerospermophilus
  | Xerospermophilus_perotensis : Species Xerospermophilus
  | Xerospermophilus_spilosoma : Species Xerospermophilus
  | Xerospermophilus_tereticaudus : Species Xerospermophilus.

Definition genus_of {g : Genus} (s : Species g) : Genus := g.

Definition AnySpecies : Type := { g : Genus & Species g }.
Definition pack_species {g : Genus} (s : Species g) : AnySpecies := existT Species g s.
Definition genus_of_any (sp : AnySpecies) : Genus := projT1 sp.

(* ======================== Subfamily Membership ======================== *)

Definition subfamily_of (g : Genus) : Subfamily :=
  match g with
  | Ratufa => Ratufinae
  | Sciurillus => Sciurillinae
  | Microsciurus | Rheithrosciurus | Sciurus | Syntheosciurus | Tamiasciurus => Sciurinae
  | Aeretes | Aeromys | Belomys | Biswamoyopterus | Eoglaucomys | Eupetaurus => Sciurinae
  | Glaucomys | Hylopetes | Iomys | Petaurillus | Petaurista | Petinomys => Sciurinae
  | Pteromys | Pteromyscus | Trogopterus => Sciurinae
  | Callosciurus | Dremomys | Exilisciurus | Funambulus | Glyphotes | Hyosciurus => Callosciurinae
  | Lariscus | Menetes | Nannosciurus | Prosciurillus | Rhinosciurus => Callosciurinae
  | Rubrisciurus | Sundasciurus | Tamiops => Callosciurinae
  | Atlantoxerus | Spermophilopsis | Xerus => Xerinae
  | Epixerus | Funisciurus | Heliosciurus | Myosciurus | Paraxerus | Protoxerus => Xerinae
  | Ammospermophilus | Callospermophilus | Cynomys | Ictidomys | Marmota => Xerinae
  | Notocitellus | Otospermophilus | Poliocitellus | Sciurotamias | Spermophilus => Xerinae
  | Tamias | Neotamias | Urocitellus | Xerospermophilus => Xerinae
  | Douglassciurus | Hesperopetes | Protosciurus => Sciurinae
  | Palaeosciurus => Xerinae
  end.

(* ======================== Tribe Membership ======================== *)

Definition tribe_of (g : Genus) : Tribe :=
  match g with
  | Ratufa | Sciurillus => NoTribe
  | Microsciurus | Rheithrosciurus | Sciurus | Syntheosciurus | Tamiasciurus => Sciurini
  | Aeretes | Aeromys | Belomys | Biswamoyopterus | Eoglaucomys | Eupetaurus => Pteromyini
  | Glaucomys | Hylopetes | Iomys | Petaurillus | Petaurista | Petinomys => Pteromyini
  | Pteromys | Pteromyscus | Trogopterus => Pteromyini
  | Callosciurus | Dremomys | Exilisciurus | Funambulus | Glyphotes | Hyosciurus => NoTribe
  | Lariscus | Menetes | Nannosciurus | Prosciurillus | Rhinosciurus => NoTribe
  | Rubrisciurus | Sundasciurus | Tamiops => NoTribe
  | Atlantoxerus | Spermophilopsis | Xerus => Xerini
  | Epixerus | Funisciurus | Heliosciurus | Myosciurus | Paraxerus | Protoxerus => Protoxerini
  | Ammospermophilus | Callospermophilus | Cynomys | Ictidomys | Marmota => Marmotini
  | Notocitellus | Otospermophilus | Poliocitellus | Sciurotamias | Spermophilus => Marmotini
  | Tamias | Neotamias | Urocitellus | Xerospermophilus => Marmotini
  | Douglassciurus | Hesperopetes => Pteromyini
  | Palaeosciurus => Marmotini
  | Protosciurus => NoTribe
  end.

(* ======================== Continental Distribution ======================== *)

Definition native_continents (g : Genus) : list Continent :=
  match g with
  | Ratufa | Rheithrosciurus => [Asia]
  | Sciurillus => [SouthAmerica]
  | Microsciurus => [CentralAmerica; SouthAmerica]
  | Sciurus => [NorthAmerica; CentralAmerica; SouthAmerica; Europe; Asia]
  | Syntheosciurus => [CentralAmerica]
  | Tamiasciurus => [NorthAmerica]
  | Aeretes | Aeromys | Belomys | Biswamoyopterus | Eoglaucomys | Eupetaurus => [Asia]
  | Glaucomys => [NorthAmerica; CentralAmerica]
  | Hylopetes | Iomys | Petaurillus | Petaurista | Petinomys => [Asia]
  | Pteromys => [Europe; Asia]
  | Pteromyscus | Trogopterus => [Asia]
  | Callosciurus | Dremomys | Exilisciurus | Funambulus | Glyphotes => [Asia]
  | Hyosciurus | Lariscus | Menetes | Nannosciurus | Prosciurillus => [Asia]
  | Rhinosciurus | Rubrisciurus | Sundasciurus | Tamiops => [Asia]
  | Atlantoxerus => [Africa]
  | Spermophilopsis => [Asia]
  | Xerus | Epixerus | Funisciurus | Heliosciurus | Myosciurus | Paraxerus | Protoxerus => [Africa]
  | Ammospermophilus | Callospermophilus | Cynomys | Ictidomys => [NorthAmerica]
  | Marmota => [NorthAmerica; Europe; Asia]
  | Notocitellus | Otospermophilus | Poliocitellus => [NorthAmerica]
  | Sciurotamias => [Asia]
  | Spermophilus => [Europe; Asia]
  | Tamias => [NorthAmerica; Asia]
  | Neotamias | Urocitellus | Xerospermophilus => [NorthAmerica]
  | Douglassciurus | Hesperopetes | Protosciurus => [NorthAmerica]
  | Palaeosciurus => [Europe]
  end.

(* ======================== Derived Species Classification ======================== *)

Definition subfamily_of_species {g : Genus} (s : Species g) : Subfamily := subfamily_of g.
Definition tribe_of_species {g : Genus} (s : Species g) : Tribe := tribe_of g.
Definition native_continents_species {g : Genus} (s : Species g) : list Continent := native_continents g.
Definition subfamily_of_any (sp : AnySpecies) : Subfamily := subfamily_of (genus_of_any sp).
Definition tribe_of_any (sp : AnySpecies) : Tribe := tribe_of (genus_of_any sp).

Theorem genus_of_pack : forall g (s : Species g), genus_of_any (pack_species s) = g.
Proof. intros; reflexivity. Qed.

Theorem subfamily_preserved : forall g (s : Species g),
  subfamily_of_any (pack_species s) = subfamily_of g.
Proof. intros; reflexivity. Qed.

(* ======================== Decidable Equality ======================== *)

Definition continent_eqb (c1 c2 : Continent) : bool :=
  match c1, c2 with
  | NorthAmerica, NorthAmerica | CentralAmerica, CentralAmerica
  | SouthAmerica, SouthAmerica | Europe, Europe | Asia, Asia | Africa, Africa => true
  | _, _ => false
  end.

Definition subfamily_eqb (s1 s2 : Subfamily) : bool :=
  match s1, s2 with
  | Ratufinae, Ratufinae | Sciurillinae, Sciurillinae | Sciurinae, Sciurinae
  | Callosciurinae, Callosciurinae | Xerinae, Xerinae => true
  | _, _ => false
  end.

Definition tribe_eqb (t1 t2 : Tribe) : bool :=
  match t1, t2 with
  | NoTribe, NoTribe | Sciurini, Sciurini | Pteromyini, Pteromyini
  | Xerini, Xerini | Protoxerini, Protoxerini | Marmotini, Marmotini => true
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

Definition genus_eqb (g1 g2 : Genus) : bool :=
  match g1, g2 with
  | Ratufa, Ratufa => true
  | Sciurillus, Sciurillus => true
  | Microsciurus, Microsciurus => true
  | Rheithrosciurus, Rheithrosciurus => true
  | Sciurus, Sciurus => true
  | Syntheosciurus, Syntheosciurus => true
  | Tamiasciurus, Tamiasciurus => true
  | Aeretes, Aeretes => true
  | Aeromys, Aeromys => true
  | Belomys, Belomys => true
  | Biswamoyopterus, Biswamoyopterus => true
  | Eoglaucomys, Eoglaucomys => true
  | Eupetaurus, Eupetaurus => true
  | Glaucomys, Glaucomys => true
  | Hylopetes, Hylopetes => true
  | Iomys, Iomys => true
  | Petaurillus, Petaurillus => true
  | Petaurista, Petaurista => true
  | Petinomys, Petinomys => true
  | Pteromys, Pteromys => true
  | Pteromyscus, Pteromyscus => true
  | Trogopterus, Trogopterus => true
  | Callosciurus, Callosciurus => true
  | Dremomys, Dremomys => true
  | Exilisciurus, Exilisciurus => true
  | Funambulus, Funambulus => true
  | Glyphotes, Glyphotes => true
  | Hyosciurus, Hyosciurus => true
  | Lariscus, Lariscus => true
  | Menetes, Menetes => true
  | Nannosciurus, Nannosciurus => true
  | Prosciurillus, Prosciurillus => true
  | Rhinosciurus, Rhinosciurus => true
  | Rubrisciurus, Rubrisciurus => true
  | Sundasciurus, Sundasciurus => true
  | Tamiops, Tamiops => true
  | Atlantoxerus, Atlantoxerus => true
  | Spermophilopsis, Spermophilopsis => true
  | Xerus, Xerus => true
  | Epixerus, Epixerus => true
  | Funisciurus, Funisciurus => true
  | Heliosciurus, Heliosciurus => true
  | Myosciurus, Myosciurus => true
  | Paraxerus, Paraxerus => true
  | Protoxerus, Protoxerus => true
  | Ammospermophilus, Ammospermophilus => true
  | Callospermophilus, Callospermophilus => true
  | Cynomys, Cynomys => true
  | Ictidomys, Ictidomys => true
  | Marmota, Marmota => true
  | Notocitellus, Notocitellus => true
  | Otospermophilus, Otospermophilus => true
  | Poliocitellus, Poliocitellus => true
  | Sciurotamias, Sciurotamias => true
  | Spermophilus, Spermophilus => true
  | Tamias, Tamias => true
  | Neotamias, Neotamias => true
  | Urocitellus, Urocitellus => true
  | Xerospermophilus, Xerospermophilus => true
  | Douglassciurus, Douglassciurus => true
  | Hesperopetes, Hesperopetes => true
  | Palaeosciurus, Palaeosciurus => true
  | Protosciurus, Protosciurus => true
  | _, _ => false
  end.

Lemma genus_eqb_refl : forall g, genus_eqb g g = true.
Proof.
  intro g; destruct g; simpl; reflexivity.
Qed.

Lemma genus_eqb_eq : forall g1 g2, genus_eqb g1 g2 = true <-> g1 = g2.
Proof.
  intros g1 g2; split; intros H.
  - destruct g1, g2; simpl in H; try reflexivity; discriminate.
  - subst; apply genus_eqb_refl.
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

Definition tribe_subfamily (t : Tribe) : option Subfamily :=
  match t with
  | NoTribe => None
  | Sciurini | Pteromyini => Some Sciurinae
  | Xerini | Protoxerini | Marmotini => Some Xerinae
  end.

Theorem tribe_implies_subfamily : forall g,
  tribe_of g <> NoTribe -> tribe_subfamily (tribe_of g) = Some (subfamily_of g).
Proof. intros g H; destruct g; simpl in *; try reflexivity; contradiction. Qed.

Theorem tribe_subfamily_some : forall g sf,
  tribe_subfamily (tribe_of g) = Some sf -> subfamily_of g = sf.
Proof. intros g sf H; destruct g; simpl in *; inversion H; reflexivity. Qed.

Theorem sciurini_in_sciurinae : forall g,
  tribe_of g = Sciurini -> subfamily_of g = Sciurinae.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem pteromyini_in_sciurinae : forall g,
  tribe_of g = Pteromyini -> subfamily_of g = Sciurinae.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem xerini_in_xerinae : forall g,
  tribe_of g = Xerini -> subfamily_of g = Xerinae.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem protoxerini_in_xerinae : forall g,
  tribe_of g = Protoxerini -> subfamily_of g = Xerinae.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem marmotini_in_xerinae : forall g,
  tribe_of g = Marmotini -> subfamily_of g = Xerinae.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

(* ======================== Biogeographic Proofs ======================== *)

Theorem callosciurinae_asian_endemic : forall g,
  subfamily_of g = Callosciurinae -> native_continents g = [Asia].
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem protoxerini_african_endemic : forall g,
  tribe_of g = Protoxerini -> native_continents g = [Africa].
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem ratufinae_monotypic_asian : forall g,
  subfamily_of g = Ratufinae -> g = Ratufa /\ native_continents g = [Asia].
Proof. intros g H; destruct g; simpl in *; try discriminate; split; reflexivity. Qed.

Theorem sciurillinae_monotypic_south_american : forall g,
  subfamily_of g = Sciurillinae -> g = Sciurillus /\ native_continents g = [SouthAmerica].
Proof. intros g H; destruct g; simpl in *; try discriminate; split; reflexivity. Qed.

Theorem prairie_dogs_north_american : forall g,
  g = Cynomys -> native_continents g = [NorthAmerica] /\ tribe_of g = Marmotini.
Proof. intros g H; subst; split; reflexivity. Qed.

Theorem marmots_holarctic : native_continents Marmota = [NorthAmerica; Europe; Asia].
Proof. reflexivity. Qed.

Theorem chipmunks_holarctic : native_continents Tamias = [NorthAmerica; Asia].
Proof. reflexivity. Qed.

Theorem flying_squirrels_disjunct : forall g,
  tribe_of g = Pteromyini ->
  (native_to g NorthAmerica = true \/ native_to g Asia = true \/ native_to g Europe = true).
Proof.
  intros g H; destruct g; simpl in *; try discriminate;
  (right; left; reflexivity) || (left; reflexivity) || (right; right; reflexivity).
Qed.

(* ======================== Clade Exclusion ======================== *)

Theorem callosciurinae_not_in_africa : forall g,
  subfamily_of g = Callosciurinae -> native_to g Africa = false.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem callosciurinae_not_in_americas : forall g,
  subfamily_of g = Callosciurinae ->
  native_to g NorthAmerica = false /\
  native_to g CentralAmerica = false /\
  native_to g SouthAmerica = false.
Proof. intros g H; destruct g; simpl in *; try discriminate; repeat split; reflexivity. Qed.

Theorem protoxerini_only_africa : forall g,
  tribe_of g = Protoxerini ->
  native_to g Africa = true /\
  native_to g Asia = false /\
  native_to g Europe = false /\
  native_to g NorthAmerica = false.
Proof. intros g H; destruct g; simpl in *; try discriminate; repeat split; reflexivity. Qed.

Theorem xerini_not_in_americas : forall g,
  tribe_of g = Xerini ->
  native_to g NorthAmerica = false /\
  native_to g CentralAmerica = false /\
  native_to g SouthAmerica = false.
Proof. intros g H; destruct g; simpl in *; try discriminate; repeat split; reflexivity. Qed.

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
   Tamias; Neotamias; Urocitellus; Xerospermophilus;
   Douglassciurus; Hesperopetes; Palaeosciurus; Protosciurus].

Theorem genera_count : List.length all_genera = 63.
Proof. reflexivity. Qed.

Theorem all_genera_complete : forall g, In g all_genera.
Proof. destruct g; simpl; auto 70. Qed.

Theorem all_genera_nodup : NoDup all_genera.
Proof. unfold all_genera; repeat constructor; simpl; intuition discriminate. Qed.

Inductive ExtinctStatus : Type := Extant | Extinct.

Definition extinction_status (g : Genus) : ExtinctStatus :=
  match g with
  | Douglassciurus | Hesperopetes | Palaeosciurus | Protosciurus => Extinct
  | _ => Extant
  end.

Definition extant_genera : list Genus :=
  filter (fun g => match extinction_status g with Extant => true | Extinct => false end) all_genera.

Definition fossil_genera : list Genus :=
  filter (fun g => match extinction_status g with Extinct => true | Extant => false end) all_genera.

Theorem extant_genera_count : List.length extant_genera = 59.
Proof. reflexivity. Qed.

Theorem fossil_genera_count : List.length fossil_genera = 4.
Proof. reflexivity. Qed.

Definition genera_in_subfamily (sf : Subfamily) : list Genus :=
  filter (fun g => subfamily_eqb (subfamily_of g) sf) all_genera.

Theorem ratufinae_count : List.length (genera_in_subfamily Ratufinae) = 1.
Proof. reflexivity. Qed.

Theorem sciurillinae_count : List.length (genera_in_subfamily Sciurillinae) = 1.
Proof. reflexivity. Qed.

Theorem sciurinae_count : List.length (genera_in_subfamily Sciurinae) = 23.
Proof. reflexivity. Qed.

Theorem callosciurinae_count : List.length (genera_in_subfamily Callosciurinae) = 14.
Proof. reflexivity. Qed.

Theorem xerinae_count : List.length (genera_in_subfamily Xerinae) = 24.
Proof. reflexivity. Qed.

Theorem subfamily_partition :
  List.length (genera_in_subfamily Ratufinae) +
  List.length (genera_in_subfamily Sciurillinae) +
  List.length (genera_in_subfamily Sciurinae) +
  List.length (genera_in_subfamily Callosciurinae) +
  List.length (genera_in_subfamily Xerinae) = 63.
Proof. reflexivity. Qed.

Definition genera_in_tribe (t : Tribe) : list Genus :=
  filter (fun g => tribe_eqb (tribe_of g) t) all_genera.

Theorem pteromyini_count : List.length (genera_in_tribe Pteromyini) = 17.
Proof. reflexivity. Qed.

Theorem marmotini_count : List.length (genera_in_tribe Marmotini) = 15.
Proof. reflexivity. Qed.

Definition is_african (g : Genus) : bool := native_to g Africa.
Definition is_strictly_asian (g : Genus) : bool :=
  native_to g Asia && negb (native_to g Europe) && negb (native_to g NorthAmerica).

Definition is_new_world_continent (c : Continent) : bool :=
  match c with NorthAmerica | CentralAmerica | SouthAmerica => true | _ => false end.

Definition is_african_continent (c : Continent) : bool :=
  match c with Africa => true | _ => false end.

Definition is_asian_continent (c : Continent) : bool :=
  match c with Asia => true | _ => false end.

Definition is_european_continent (c : Continent) : bool :=
  match c with Europe => true | _ => false end.

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
Proof. intro g; exists (subfamily_of g), (tribe_of g); reflexivity. Qed.

Theorem key_unambiguous : forall g sf1 sf2 t1 t2,
  dichotomous_key g = (sf1, t1) ->
  dichotomous_key g = (sf2, t2) ->
  sf1 = sf2 /\ t1 = t2.
Proof.
  intros g sf1 sf2 t1 t2 H1 H2.
  rewrite H1 in H2; inversion H2; split; reflexivity.
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
  List.length (native_continents Sciurus) = 5.
Proof. repeat split; reflexivity. Qed.

Example witness_pteromyini :
  subfamily_of Glaucomys = Sciurinae /\
  tribe_of Glaucomys = Pteromyini /\
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
Proof. intros g H; destruct g; simpl in H; try discriminate; reflexivity. Qed.

Example counter_ratufinae_not_multiple :
  forall g, subfamily_of g = Ratufinae -> g = Ratufa.
Proof. intros g H; destruct g; simpl in H; try discriminate; reflexivity. Qed.

Example counter_pteromyini_not_african :
  forall g, tribe_of g = Pteromyini -> native_to g Africa = false.
Proof. intros g H; destruct g; simpl in H; try discriminate; reflexivity. Qed.

Example counter_marmotini_not_african :
  forall g, tribe_of g = Marmotini -> native_to g Africa = false.
Proof. intros g H; destruct g; simpl in H; try discriminate; reflexivity. Qed.

(* ======================== Endemism Predicates ======================== *)

Definition endemic_to (g : Genus) (c : Continent) : Prop :=
  native_continents g = [c].

Definition cosmopolitan (g : Genus) : Prop :=
  List.length (native_continents g) >= 3.

Definition restricted (g : Genus) : Prop :=
  List.length (native_continents g) = 1.

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

Theorem asian_endemic_count : List.length (genera_endemic_to Asia) = 31.
Proof. reflexivity. Qed.

Theorem african_endemic_count : List.length (genera_endemic_to Africa) = 8.
Proof. reflexivity. Qed.

Theorem north_american_endemic_count : List.length (genera_endemic_to NorthAmerica) = 14.
Proof. reflexivity. Qed.

Theorem south_american_endemic_count : List.length (genera_endemic_to SouthAmerica) = 1.
Proof. reflexivity. Qed.

Theorem central_american_endemic_count : List.length (genera_endemic_to CentralAmerica) = 1.
Proof. reflexivity. Qed.

Theorem european_endemic_count : List.length (genera_endemic_to Europe) = 1.
Proof. reflexivity. Qed.

(* ======================== Continental Diversity ======================== *)

Definition genera_present_in (c : Continent) : list Genus :=
  filter (fun g => native_to g c) all_genera.

Theorem asia_diversity : List.length (genera_present_in Asia) = 36.
Proof. reflexivity. Qed.

Theorem north_america_diversity : List.length (genera_present_in NorthAmerica) = 18.
Proof. reflexivity. Qed.

Theorem africa_diversity : List.length (genera_present_in Africa) = 8.
Proof. reflexivity. Qed.

Theorem europe_diversity : List.length (genera_present_in Europe) = 5.
Proof. reflexivity. Qed.

Theorem south_america_diversity : List.length (genera_present_in SouthAmerica) = 3.
Proof. reflexivity. Qed.

Theorem central_america_diversity : List.length (genera_present_in CentralAmerica) = 4.
Proof. reflexivity. Qed.

Theorem asia_most_diverse :
  forall c, c <> Asia ->
  List.length (genera_present_in c) < List.length (genera_present_in Asia).
Proof. intros c H; destruct c; simpl; try contradiction; lia. Qed.

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
Proof. unfold sister_tribes; split; [reflexivity | discriminate]. Qed.

Theorem xerini_protoxerini_sisters : sister_tribes Xerini Protoxerini.
Proof. unfold sister_tribes; split; [reflexivity | discriminate]. Qed.

Theorem xerini_marmotini_sisters : sister_tribes Xerini Marmotini.
Proof. unfold sister_tribes; split; [reflexivity | discriminate]. Qed.

Theorem flying_tree_squirrels_same_clade : same_clade Glaucomys Sciurus.
Proof. unfold same_clade; reflexivity. Qed.

Theorem prairie_dogs_marmots_same_clade : same_clade Cynomys Marmota.
Proof. unfold same_clade; reflexivity. Qed.

(* ======================== Taxonomic Rank Lemmas ======================== *)

Theorem subfamily_finer_than_family : forall g1 g2,
  subfamily_of g1 <> subfamily_of g2 -> g1 <> g2.
Proof. intros g1 g2 H Heq; subst; contradiction. Qed.

Theorem tribe_finer_than_subfamily : forall g1 g2,
  tribe_of g1 <> NoTribe ->
  tribe_of g2 <> NoTribe ->
  tribe_of g1 <> tribe_of g2 ->
  subfamily_of g1 = subfamily_of g2 ->
  False \/ (subfamily_of g1 = Sciurinae \/ subfamily_of g1 = Xerinae).
Proof.
  intros g1 g2 H1 H2 Hneq Hsf.
  right; destruct g1; simpl in *;
  try contradiction;
  try (left; reflexivity);
  try (right; reflexivity).
Qed.

(* ======================== The Gray Squirrel ======================== *)

Definition gray_squirrel_species : Species Sciurus := Sciurus_carolinensis.

Theorem gray_squirrel_genus : genus_of gray_squirrel_species = Sciurus.
Proof. reflexivity. Qed.

Theorem gray_squirrel_subfamily : subfamily_of_species gray_squirrel_species = Sciurinae.
Proof. reflexivity. Qed.

Theorem gray_squirrel_tribe : tribe_of_species gray_squirrel_species = Sciurini.
Proof. reflexivity. Qed.

Theorem gray_squirrel_type_guarantee :
  forall (s : Species Sciurus), genus_of s = Sciurus.
Proof. intros s; reflexivity. Qed.

Theorem species_genus_injective :
  forall g1 g2 (s1 : Species g1) (s2 : Species g2),
  g1 <> g2 -> existT Species g1 s1 <> existT Species g2 s2.
Proof. intros g1 g2 s1 s2 Hneq Heq; inversion Heq; contradiction. Qed.

Definition all_species : list AnySpecies :=
  [pack_species Ratufa_affinis; pack_species Ratufa_bicolor;
   pack_species Ratufa_indica; pack_species Ratufa_macroura;
   pack_species Sciurillus_pusillus;
   pack_species Microsciurus_alfari; pack_species Microsciurus_flaviventer;
   pack_species Microsciurus_mimulus; pack_species Microsciurus_santanderensis;
   pack_species Rheithrosciurus_macrotis;
   pack_species Sciurus_aberti; pack_species Sciurus_alleni;
   pack_species Sciurus_anomalus; pack_species Sciurus_arizonensis;
   pack_species Sciurus_aureogaster; pack_species Sciurus_carolinensis;
   pack_species Sciurus_colliaei; pack_species Sciurus_deppei;
   pack_species Sciurus_flammifer; pack_species Sciurus_gilvigularis;
   pack_species Sciurus_granatensis; pack_species Sciurus_griseus;
   pack_species Sciurus_igniventris; pack_species Sciurus_lis;
   pack_species Sciurus_nayaritensis; pack_species Sciurus_niger;
   pack_species Sciurus_oculatus; pack_species Sciurus_pucheranii;
   pack_species Sciurus_pyrrhinus; pack_species Sciurus_richmondi;
   pack_species Sciurus_sanborni; pack_species Sciurus_spadiceus;
   pack_species Sciurus_stramineus; pack_species Sciurus_variegatoides;
   pack_species Sciurus_vulgaris; pack_species Sciurus_yucatanensis;
   pack_species Syntheosciurus_brochus;
   pack_species Tamiasciurus_douglasii; pack_species Tamiasciurus_fremonti;
   pack_species Tamiasciurus_hudsonicus; pack_species Tamiasciurus_mearnsi;
   pack_species Aeretes_melanopterus;
   pack_species Aeromys_tephromelas; pack_species Aeromys_thomasi;
   pack_species Belomys_pearsonii;
   pack_species Biswamoyopterus_biswasi; pack_species Biswamoyopterus_laoensis;
   pack_species Eoglaucomys_fimbriatus;
   pack_species Eupetaurus_cinereus;
   pack_species Glaucomys_oregonensis; pack_species Glaucomys_sabrinus;
   pack_species Glaucomys_volans;
   pack_species Hylopetes_alboniger; pack_species Hylopetes_baberi;
   pack_species Hylopetes_bartelsi; pack_species Hylopetes_lepidus;
   pack_species Hylopetes_nigripes; pack_species Hylopetes_phayrei;
   pack_species Hylopetes_platyurus; pack_species Hylopetes_sipora;
   pack_species Hylopetes_spadiceus; pack_species Hylopetes_winstoni;
   pack_species Iomys_horsfieldii; pack_species Iomys_sipora;
   pack_species Petaurillus_emiliae; pack_species Petaurillus_hosei;
   pack_species Petaurillus_kinlochii;
   pack_species Petaurista_alborufus; pack_species Petaurista_elegans;
   pack_species Petaurista_leucogenys; pack_species Petaurista_magnificus;
   pack_species Petaurista_mechukaensis; pack_species Petaurista_mishmiensis;
   pack_species Petaurista_nobilis; pack_species Petaurista_petaurista;
   pack_species Petaurista_philippensis; pack_species Petaurista_xanthotis;
   pack_species Petaurista_yunanensis;
   pack_species Petinomys_crinitus; pack_species Petinomys_fuscocapillus;
   pack_species Petinomys_genibarbis; pack_species Petinomys_hageni;
   pack_species Petinomys_lugens; pack_species Petinomys_mindanensis;
   pack_species Petinomys_sagitta; pack_species Petinomys_setosus;
   pack_species Petinomys_vordermanni;
   pack_species Pteromys_momonga; pack_species Pteromys_volans;
   pack_species Pteromyscus_pulverulentus;
   pack_species Trogopterus_xanthipes;
   pack_species Callosciurus_adamsi; pack_species Callosciurus_albescens;
   pack_species Callosciurus_baluensis; pack_species Callosciurus_caniceps;
   pack_species Callosciurus_erythraeus; pack_species Callosciurus_finlaysonii;
   pack_species Callosciurus_inornatus; pack_species Callosciurus_melanogaster;
   pack_species Callosciurus_nigrovittatus; pack_species Callosciurus_notatus;
   pack_species Callosciurus_orestes; pack_species Callosciurus_phayrei;
   pack_species Callosciurus_prevostii; pack_species Callosciurus_pygerythrus;
   pack_species Callosciurus_quinquestriatus;
   pack_species Dremomys_everetti; pack_species Dremomys_gularis;
   pack_species Dremomys_lokriah; pack_species Dremomys_pernyi;
   pack_species Dremomys_pyrrhomerus; pack_species Dremomys_rufigenis;
   pack_species Exilisciurus_concinnus; pack_species Exilisciurus_exilis;
   pack_species Exilisciurus_whiteheadi;
   pack_species Funambulus_layardi; pack_species Funambulus_palmarum;
   pack_species Funambulus_pennantii; pack_species Funambulus_sublineatus;
   pack_species Funambulus_tristriatus;
   pack_species Glyphotes_simus;
   pack_species Hyosciurus_heinrichi; pack_species Hyosciurus_ileile;
   pack_species Lariscus_hosei; pack_species Lariscus_insignis;
   pack_species Lariscus_niobe; pack_species Lariscus_obscurus;
   pack_species Menetes_berdmorei;
   pack_species Nannosciurus_melanotis;
   pack_species Prosciurillus_abstrusus; pack_species Prosciurillus_leucomus;
   pack_species Prosciurillus_murinus; pack_species Prosciurillus_topapuensis;
   pack_species Prosciurillus_weberi;
   pack_species Rhinosciurus_laticaudatus;
   pack_species Rubrisciurus_rubriventer;
   pack_species Sundasciurus_brookei; pack_species Sundasciurus_davensis;
   pack_species Sundasciurus_fraterculus; pack_species Sundasciurus_hippurus;
   pack_species Sundasciurus_hoogstraali; pack_species Sundasciurus_jentinki;
   pack_species Sundasciurus_juvencus; pack_species Sundasciurus_lowii;
   pack_species Sundasciurus_mindanensis; pack_species Sundasciurus_moellendorffi;
   pack_species Sundasciurus_philippinensis; pack_species Sundasciurus_rabori;
   pack_species Sundasciurus_samarensis; pack_species Sundasciurus_steerii;
   pack_species Sundasciurus_tenuis;
   pack_species Tamiops_mcclellandii; pack_species Tamiops_maritimus;
   pack_species Tamiops_rodolphii; pack_species Tamiops_swinhoei;
   pack_species Atlantoxerus_getulus;
   pack_species Spermophilopsis_leptodactylus;
   pack_species Xerus_erythropus; pack_species Xerus_inauris;
   pack_species Xerus_princeps; pack_species Xerus_rutilus;
   pack_species Epixerus_ebii; pack_species Epixerus_wilsoni;
   pack_species Funisciurus_anerythrus; pack_species Funisciurus_bayonii;
   pack_species Funisciurus_carruthersi; pack_species Funisciurus_congicus;
   pack_species Funisciurus_isabella; pack_species Funisciurus_lemniscatus;
   pack_species Funisciurus_leucogenys; pack_species Funisciurus_pyrropus;
   pack_species Funisciurus_substriatus;
   pack_species Heliosciurus_gambianus; pack_species Heliosciurus_mutabilis;
   pack_species Heliosciurus_punctatus; pack_species Heliosciurus_rufobrachium;
   pack_species Heliosciurus_ruwenzorii; pack_species Heliosciurus_undulatus;
   pack_species Myosciurus_pumilio;
   pack_species Paraxerus_alexandri; pack_species Paraxerus_boehmi;
   pack_species Paraxerus_cepapi; pack_species Paraxerus_cooperi;
   pack_species Paraxerus_flavovittis; pack_species Paraxerus_lucifer;
   pack_species Paraxerus_ochraceus; pack_species Paraxerus_palliatus;
   pack_species Paraxerus_poensis; pack_species Paraxerus_vexillarius;
   pack_species Paraxerus_vincenti;
   pack_species Protoxerus_aubinnii; pack_species Protoxerus_stangeri;
   pack_species Ammospermophilus_harrisii; pack_species Ammospermophilus_insularis;
   pack_species Ammospermophilus_interpres; pack_species Ammospermophilus_leucurus;
   pack_species Ammospermophilus_nelsoni;
   pack_species Callospermophilus_lateralis; pack_species Callospermophilus_madrensis;
   pack_species Callospermophilus_saturatus;
   pack_species Cynomys_gunnisoni; pack_species Cynomys_leucurus;
   pack_species Cynomys_ludovicianus; pack_species Cynomys_mexicanus;
   pack_species Cynomys_parvidens;
   pack_species Ictidomys_mexicanus; pack_species Ictidomys_parvidens;
   pack_species Ictidomys_tridecemlineatus;
   pack_species Marmota_baibacina; pack_species Marmota_bobak;
   pack_species Marmota_broweri; pack_species Marmota_caligata;
   pack_species Marmota_camtschatica; pack_species Marmota_caudata;
   pack_species Marmota_flaviventris; pack_species Marmota_himalayana;
   pack_species Marmota_marmota; pack_species Marmota_menzbieri;
   pack_species Marmota_monax; pack_species Marmota_olympus;
   pack_species Marmota_sibirica; pack_species Marmota_vancouverensis;
   pack_species Notocitellus_adocetus; pack_species Notocitellus_annulatus;
   pack_species Otospermophilus_atricapillus; pack_species Otospermophilus_beecheyi;
   pack_species Otospermophilus_variegatus;
   pack_species Poliocitellus_franklinii;
   pack_species Sciurotamias_davidianus; pack_species Sciurotamias_forresti;
   pack_species Spermophilus_alashanicus; pack_species Spermophilus_brevicauda;
   pack_species Spermophilus_citellus; pack_species Spermophilus_dauricus;
   pack_species Spermophilus_erythrogenys; pack_species Spermophilus_fulvus;
   pack_species Spermophilus_major; pack_species Spermophilus_musicus;
   pack_species Spermophilus_pallidiccauda; pack_species Spermophilus_pygmaeus;
   pack_species Spermophilus_ralli; pack_species Spermophilus_relictus;
   pack_species Spermophilus_suslicus; pack_species Spermophilus_taurensis;
   pack_species Spermophilus_xanthoprymnus;
   pack_species Tamias_sibiricus; pack_species Tamias_striatus;
   pack_species Neotamias_alpinus; pack_species Neotamias_amoenus;
   pack_species Neotamias_bulleri; pack_species Neotamias_canipes;
   pack_species Neotamias_cinereicollis; pack_species Neotamias_dorsalis;
   pack_species Neotamias_durangae; pack_species Neotamias_merriami;
   pack_species Neotamias_minimus; pack_species Neotamias_obscurus;
   pack_species Neotamias_ochrogenys; pack_species Neotamias_palmeri;
   pack_species Neotamias_panamintinus; pack_species Neotamias_quadrimaculatus;
   pack_species Neotamias_quadrivittatus; pack_species Neotamias_ruficaudus;
   pack_species Neotamias_rufus; pack_species Neotamias_senex;
   pack_species Neotamias_siskiyou; pack_species Neotamias_sonomae;
   pack_species Neotamias_speciosus; pack_species Neotamias_townsendii;
   pack_species Neotamias_umbrinus;
   pack_species Urocitellus_armatus; pack_species Urocitellus_beldingi;
   pack_species Urocitellus_brunneus; pack_species Urocitellus_canus;
   pack_species Urocitellus_columbianus; pack_species Urocitellus_elegans;
   pack_species Urocitellus_endemicus; pack_species Urocitellus_mollis;
   pack_species Urocitellus_parryii; pack_species Urocitellus_richardsonii;
   pack_species Urocitellus_townsendii; pack_species Urocitellus_undulatus;
   pack_species Urocitellus_washingtoni;
   pack_species Xerospermophilus_mohavensis; pack_species Xerospermophilus_perotensis;
   pack_species Xerospermophilus_spilosoma; pack_species Xerospermophilus_tereticaudus].

Theorem species_count : List.length all_species = 287.
Proof. reflexivity. Qed.

Theorem all_species_complete : forall g (s : Species g),
  In (pack_species s) all_species.
Proof.
  intros g s; destruct s; simpl; auto 300.
Qed.

Definition species_to_nat {g : Genus} (s : Species g) : nat :=
  match s with
  | Ratufa_affinis => 0 | Ratufa_bicolor => 1 | Ratufa_indica => 2 | Ratufa_macroura => 3
  | Sciurillus_pusillus => 4
  | Microsciurus_alfari => 5 | Microsciurus_flaviventer => 6 | Microsciurus_mimulus => 7 | Microsciurus_santanderensis => 8
  | Rheithrosciurus_macrotis => 9
  | Sciurus_aberti => 10 | Sciurus_alleni => 11 | Sciurus_anomalus => 12 | Sciurus_arizonensis => 13
  | Sciurus_aureogaster => 14 | Sciurus_carolinensis => 15 | Sciurus_colliaei => 16 | Sciurus_deppei => 17
  | Sciurus_flammifer => 18 | Sciurus_gilvigularis => 19 | Sciurus_granatensis => 20 | Sciurus_griseus => 21
  | Sciurus_igniventris => 22 | Sciurus_lis => 23 | Sciurus_nayaritensis => 24 | Sciurus_niger => 25
  | Sciurus_oculatus => 26 | Sciurus_pucheranii => 27 | Sciurus_pyrrhinus => 28 | Sciurus_richmondi => 29
  | Sciurus_sanborni => 30 | Sciurus_spadiceus => 31 | Sciurus_stramineus => 32 | Sciurus_variegatoides => 33
  | Sciurus_vulgaris => 34 | Sciurus_yucatanensis => 35
  | Syntheosciurus_brochus => 36
  | Tamiasciurus_douglasii => 37 | Tamiasciurus_fremonti => 38 | Tamiasciurus_hudsonicus => 39 | Tamiasciurus_mearnsi => 40
  | Aeretes_melanopterus => 41
  | Aeromys_tephromelas => 42 | Aeromys_thomasi => 43
  | Belomys_pearsonii => 44
  | Biswamoyopterus_biswasi => 45 | Biswamoyopterus_laoensis => 46
  | Eoglaucomys_fimbriatus => 47
  | Eupetaurus_cinereus => 48
  | Glaucomys_oregonensis => 49 | Glaucomys_sabrinus => 50 | Glaucomys_volans => 51
  | Hylopetes_alboniger => 52 | Hylopetes_baberi => 53 | Hylopetes_bartelsi => 54 | Hylopetes_lepidus => 55
  | Hylopetes_nigripes => 56 | Hylopetes_phayrei => 57 | Hylopetes_platyurus => 58 | Hylopetes_sipora => 59
  | Hylopetes_spadiceus => 60 | Hylopetes_winstoni => 61
  | Iomys_horsfieldii => 62 | Iomys_sipora => 63
  | Petaurillus_emiliae => 64 | Petaurillus_hosei => 65 | Petaurillus_kinlochii => 66
  | Petaurista_alborufus => 67 | Petaurista_elegans => 68 | Petaurista_leucogenys => 69 | Petaurista_magnificus => 70
  | Petaurista_mechukaensis => 71 | Petaurista_mishmiensis => 72 | Petaurista_nobilis => 73 | Petaurista_petaurista => 74
  | Petaurista_philippensis => 75 | Petaurista_xanthotis => 76 | Petaurista_yunanensis => 77
  | Petinomys_crinitus => 78 | Petinomys_fuscocapillus => 79 | Petinomys_genibarbis => 80 | Petinomys_hageni => 81
  | Petinomys_lugens => 82 | Petinomys_mindanensis => 83 | Petinomys_sagitta => 84 | Petinomys_setosus => 85 | Petinomys_vordermanni => 86
  | Pteromys_momonga => 87 | Pteromys_volans => 88
  | Pteromyscus_pulverulentus => 89
  | Trogopterus_xanthipes => 90
  | Callosciurus_adamsi => 91 | Callosciurus_albescens => 92 | Callosciurus_baluensis => 93 | Callosciurus_caniceps => 94
  | Callosciurus_erythraeus => 95 | Callosciurus_finlaysonii => 96 | Callosciurus_inornatus => 97 | Callosciurus_melanogaster => 98
  | Callosciurus_nigrovittatus => 99 | Callosciurus_notatus => 100 | Callosciurus_orestes => 101 | Callosciurus_phayrei => 102
  | Callosciurus_prevostii => 103 | Callosciurus_pygerythrus => 104 | Callosciurus_quinquestriatus => 105
  | Dremomys_everetti => 106 | Dremomys_gularis => 107 | Dremomys_lokriah => 108 | Dremomys_pernyi => 109
  | Dremomys_pyrrhomerus => 110 | Dremomys_rufigenis => 111
  | Exilisciurus_concinnus => 112 | Exilisciurus_exilis => 113 | Exilisciurus_whiteheadi => 114
  | Funambulus_layardi => 115 | Funambulus_palmarum => 116 | Funambulus_pennantii => 117 | Funambulus_sublineatus => 118 | Funambulus_tristriatus => 119
  | Glyphotes_simus => 120
  | Hyosciurus_heinrichi => 121 | Hyosciurus_ileile => 122
  | Lariscus_hosei => 123 | Lariscus_insignis => 124 | Lariscus_niobe => 125 | Lariscus_obscurus => 126
  | Menetes_berdmorei => 127
  | Nannosciurus_melanotis => 128
  | Prosciurillus_abstrusus => 129 | Prosciurillus_leucomus => 130 | Prosciurillus_murinus => 131
  | Prosciurillus_topapuensis => 132 | Prosciurillus_weberi => 133
  | Rhinosciurus_laticaudatus => 134
  | Rubrisciurus_rubriventer => 135
  | Sundasciurus_brookei => 136 | Sundasciurus_davensis => 137 | Sundasciurus_fraterculus => 138 | Sundasciurus_hippurus => 139
  | Sundasciurus_hoogstraali => 140 | Sundasciurus_jentinki => 141 | Sundasciurus_juvencus => 142 | Sundasciurus_lowii => 143
  | Sundasciurus_mindanensis => 144 | Sundasciurus_moellendorffi => 145 | Sundasciurus_philippinensis => 146 | Sundasciurus_rabori => 147
  | Sundasciurus_samarensis => 148 | Sundasciurus_steerii => 149 | Sundasciurus_tenuis => 150
  | Tamiops_mcclellandii => 151 | Tamiops_maritimus => 152 | Tamiops_rodolphii => 153 | Tamiops_swinhoei => 154
  | Atlantoxerus_getulus => 155
  | Spermophilopsis_leptodactylus => 156
  | Xerus_erythropus => 157 | Xerus_inauris => 158 | Xerus_princeps => 159 | Xerus_rutilus => 160
  | Epixerus_ebii => 161 | Epixerus_wilsoni => 162
  | Funisciurus_anerythrus => 163 | Funisciurus_bayonii => 164 | Funisciurus_carruthersi => 165 | Funisciurus_congicus => 166
  | Funisciurus_isabella => 167 | Funisciurus_lemniscatus => 168 | Funisciurus_leucogenys => 169 | Funisciurus_pyrropus => 170 | Funisciurus_substriatus => 171
  | Heliosciurus_gambianus => 172 | Heliosciurus_mutabilis => 173 | Heliosciurus_punctatus => 174
  | Heliosciurus_rufobrachium => 175 | Heliosciurus_ruwenzorii => 176 | Heliosciurus_undulatus => 177
  | Myosciurus_pumilio => 178
  | Paraxerus_alexandri => 179 | Paraxerus_boehmi => 180 | Paraxerus_cepapi => 181 | Paraxerus_cooperi => 182
  | Paraxerus_flavovittis => 183 | Paraxerus_lucifer => 184 | Paraxerus_ochraceus => 185 | Paraxerus_palliatus => 186
  | Paraxerus_poensis => 187 | Paraxerus_vexillarius => 188 | Paraxerus_vincenti => 189
  | Protoxerus_aubinnii => 190 | Protoxerus_stangeri => 191
  | Ammospermophilus_harrisii => 192 | Ammospermophilus_insularis => 193 | Ammospermophilus_interpres => 194
  | Ammospermophilus_leucurus => 195 | Ammospermophilus_nelsoni => 196
  | Callospermophilus_lateralis => 197 | Callospermophilus_madrensis => 198 | Callospermophilus_saturatus => 199
  | Cynomys_gunnisoni => 200 | Cynomys_leucurus => 201 | Cynomys_ludovicianus => 202 | Cynomys_mexicanus => 203 | Cynomys_parvidens => 204
  | Ictidomys_mexicanus => 205 | Ictidomys_parvidens => 206 | Ictidomys_tridecemlineatus => 207
  | Marmota_baibacina => 208 | Marmota_bobak => 209 | Marmota_broweri => 210 | Marmota_caligata => 211
  | Marmota_camtschatica => 212 | Marmota_caudata => 213 | Marmota_flaviventris => 214 | Marmota_himalayana => 215
  | Marmota_marmota => 216 | Marmota_menzbieri => 217 | Marmota_monax => 218 | Marmota_olympus => 219
  | Marmota_sibirica => 220 | Marmota_vancouverensis => 221
  | Notocitellus_adocetus => 222 | Notocitellus_annulatus => 223
  | Otospermophilus_atricapillus => 224 | Otospermophilus_beecheyi => 225 | Otospermophilus_variegatus => 226
  | Poliocitellus_franklinii => 227
  | Sciurotamias_davidianus => 228 | Sciurotamias_forresti => 229
  | Spermophilus_alashanicus => 230 | Spermophilus_brevicauda => 231 | Spermophilus_citellus => 232 | Spermophilus_dauricus => 233
  | Spermophilus_erythrogenys => 234 | Spermophilus_fulvus => 235 | Spermophilus_major => 236 | Spermophilus_musicus => 237
  | Spermophilus_pallidiccauda => 238 | Spermophilus_pygmaeus => 239 | Spermophilus_ralli => 240 | Spermophilus_relictus => 241
  | Spermophilus_suslicus => 242 | Spermophilus_taurensis => 243 | Spermophilus_xanthoprymnus => 244
  | Tamias_sibiricus => 245 | Tamias_striatus => 246
  | Neotamias_alpinus => 247 | Neotamias_amoenus => 248 | Neotamias_bulleri => 249 | Neotamias_canipes => 250
  | Neotamias_cinereicollis => 251 | Neotamias_dorsalis => 252 | Neotamias_durangae => 253 | Neotamias_merriami => 254
  | Neotamias_minimus => 255 | Neotamias_obscurus => 256 | Neotamias_ochrogenys => 257 | Neotamias_palmeri => 258
  | Neotamias_panamintinus => 259 | Neotamias_quadrimaculatus => 260 | Neotamias_quadrivittatus => 261 | Neotamias_ruficaudus => 262
  | Neotamias_rufus => 263 | Neotamias_senex => 264 | Neotamias_siskiyou => 265 | Neotamias_sonomae => 266
  | Neotamias_speciosus => 267 | Neotamias_townsendii => 268 | Neotamias_umbrinus => 269
  | Urocitellus_armatus => 270 | Urocitellus_beldingi => 271 | Urocitellus_brunneus => 272 | Urocitellus_canus => 273
  | Urocitellus_columbianus => 274 | Urocitellus_elegans => 275 | Urocitellus_endemicus => 276 | Urocitellus_mollis => 277
  | Urocitellus_parryii => 278 | Urocitellus_richardsonii => 279 | Urocitellus_townsendii => 280 | Urocitellus_undulatus => 281 | Urocitellus_washingtoni => 282
  | Xerospermophilus_mohavensis => 283 | Xerospermophilus_perotensis => 284 | Xerospermophilus_spilosoma => 285 | Xerospermophilus_tereticaudus => 286
  end.

Definition anyspecies_to_nat (sp : AnySpecies) : nat :=
  match sp with existT _ _ s => species_to_nat s end.

Fixpoint nodup_nat_list (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (Nat.eqb x) xs) && nodup_nat_list xs
  end.

Definition all_species_indices : list nat := map anyspecies_to_nat all_species.

Lemma all_species_indices_nodup_check : nodup_nat_list all_species_indices = true.
Proof. native_compute. reflexivity. Qed.

Lemma species_to_nat_injective : forall g1 g2 (s1 : Species g1) (s2 : Species g2),
  species_to_nat s1 = species_to_nat s2 -> existT _ g1 s1 = existT _ g2 s2.
Proof.
  intros g1 g2 s1 s2 H.
  destruct s1, s2; simpl in H; try discriminate; reflexivity.
Qed.

Lemma nodup_nat_implies_NoDup : forall (l : list nat),
  nodup_nat_list l = true -> NoDup l.
Proof.
  induction l as [|x xs IH]; intros H.
  - constructor.
  - simpl in H.
    apply andb_prop in H as [Hnin Hrest].
    constructor.
    + intro Hin.
      assert (Hfalse : existsb (Nat.eqb x) xs = true).
      { apply existsb_exists. exists x. split; [exact Hin | apply Nat.eqb_refl]. }
      rewrite Hfalse in Hnin. discriminate.
    + apply IH; exact Hrest.
Qed.

Lemma NoDup_map_injective : forall {A B} (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup (map f l) -> NoDup l.
Proof.
  intros A B f l Hinj Hnd.
  induction l as [|x xs IH]; [constructor|].
  simpl in Hnd.
  inversion Hnd as [|? ? Hnin Hrest]; subst.
  constructor.
  - intro Hin.
    apply Hnin.
    apply in_map.
    exact Hin.
  - apply IH; exact Hrest.
Qed.

Theorem all_species_nodup : NoDup all_species.
Proof.
  apply NoDup_map_injective with (f := anyspecies_to_nat).
  - intros [g1 s1] [g2 s2] Heq.
    apply species_to_nat_injective; exact Heq.
  - apply nodup_nat_implies_NoDup.
    exact all_species_indices_nodup_check.
Qed.

(* ======================== Morphological Characters ======================== *)

Inductive BodySize : Type := Tiny | Small | Medium | Large | Giant.
Inductive TailType : Type := Bushy | Thin | Flat | Furred.
Inductive Habitat : Type := Arboreal | Terrestrial | Fossorial | Gliding.
Inductive CheekPouches : Type := Present | Absent.
Inductive SnoutShape : Type := Elongated | Normal | Blunt.
Inductive TailRatio : Type := TailShort | TailModerate | TailLong | TailVeryLong.
Inductive PelagePattern : Type := Uniform | PelageStriped | Spotted | Banded | Grizzled.
Inductive EarShape : Type := Rounded | Pointed | EarTufted.
Inductive TailTip : Type := TipBlack | TipWhite | TipSame | TipBanded.
Inductive VentralColor : Type := VentralWhite | VentralOrange | VentralGray | VentralBuff.
Inductive StripeCount : Type := NoStripes | OneStripe | ThreeStripes | FiveStripes | SevenStripes.

Record Morphology : Type := {
  body_size : BodySize;
  tail_type : TailType;
  habitat : Habitat;
  cheek_pouches : CheekPouches;
  has_patagium : bool;
  has_ear_tufts : bool;
  is_striped : bool
}.

Record ExtendedMorphology : Type := {
  base_morph : Morphology;
  snout_shape : SnoutShape;
  tail_ratio : TailRatio;
  pelage_pattern : PelagePattern;
  ear_shape : EarShape;
  has_postauricular_patch : bool;
  has_dorsal_stripe : bool;
  has_white_eye_ring : bool;
  num_mammae : nat
}.

(* ======================== Morphology Archetypes ======================== *)

Definition tree_squirrel_morph : Morphology :=
  {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
     cheek_pouches := Absent; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition ground_squirrel_morph : Morphology :=
  {| body_size := Medium; tail_type := Thin; habitat := Terrestrial;
     cheek_pouches := Present; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition flying_squirrel_morph : Morphology :=
  {| body_size := Small; tail_type := Flat; habitat := Gliding;
     cheek_pouches := Absent; has_patagium := true;
     has_ear_tufts := false; is_striped := false |}.

Definition chipmunk_morph : Morphology :=
  {| body_size := Small; tail_type := Bushy; habitat := Terrestrial;
     cheek_pouches := Present; has_patagium := false;
     has_ear_tufts := false; is_striped := true |}.

Definition marmot_morph : Morphology :=
  {| body_size := Large; tail_type := Bushy; habitat := Fossorial;
     cheek_pouches := Present; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition prairie_dog_morph : Morphology :=
  {| body_size := Medium; tail_type := Thin; habitat := Fossorial;
     cheek_pouches := Present; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition pygmy_squirrel_morph : Morphology :=
  {| body_size := Tiny; tail_type := Bushy; habitat := Arboreal;
     cheek_pouches := Absent; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition giant_squirrel_morph : Morphology :=
  {| body_size := Giant; tail_type := Bushy; habitat := Arboreal;
     cheek_pouches := Absent; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition palm_squirrel_morph : Morphology :=
  {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
     cheek_pouches := Absent; has_patagium := false;
     has_ear_tufts := false; is_striped := true |}.

Definition morphology_of (g : Genus) : Morphology :=
  match g with
  | Ratufa => giant_squirrel_morph
  | Sciurillus => pygmy_squirrel_morph
  | Microsciurus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                       cheek_pouches := Absent; has_patagium := false;
                       has_ear_tufts := false; is_striped := false |}
  | Rheithrosciurus => {| body_size := Large; tail_type := Bushy; habitat := Arboreal;
                          cheek_pouches := Absent; has_patagium := false;
                          has_ear_tufts := true; is_striped := false |}
  | Sciurus => tree_squirrel_morph
  | Syntheosciurus => tree_squirrel_morph
  | Tamiasciurus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                       cheek_pouches := Absent; has_patagium := false;
                       has_ear_tufts := true; is_striped := false |}
  | Aeretes => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                  cheek_pouches := Absent; has_patagium := true;
                  has_ear_tufts := false; is_striped := false |}
  | Aeromys => {| body_size := Large; tail_type := Flat; habitat := Gliding;
                  cheek_pouches := Absent; has_patagium := true;
                  has_ear_tufts := false; is_striped := false |}
  | Belomys => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                  cheek_pouches := Absent; has_patagium := true;
                  has_ear_tufts := false; is_striped := false |}
  | Biswamoyopterus => {| body_size := Large; tail_type := Flat; habitat := Gliding;
                          cheek_pouches := Absent; has_patagium := true;
                          has_ear_tufts := false; is_striped := false |}
  | Eoglaucomys => flying_squirrel_morph
  | Eupetaurus => {| body_size := Large; tail_type := Flat; habitat := Gliding;
                     cheek_pouches := Absent; has_patagium := true;
                     has_ear_tufts := true; is_striped := false |}
  | Glaucomys => {| body_size := Small; tail_type := Flat; habitat := Gliding;
                    cheek_pouches := Absent; has_patagium := true;
                    has_ear_tufts := false; is_striped := false |}
  | Hylopetes => flying_squirrel_morph
  | Iomys => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                cheek_pouches := Absent; has_patagium := true;
                has_ear_tufts := false; is_striped := false |}
  | Petinomys => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                    cheek_pouches := Absent; has_patagium := true;
                    has_ear_tufts := false; is_striped := false |}
  | Pteromyscus => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                      cheek_pouches := Absent; has_patagium := true;
                      has_ear_tufts := false; is_striped := false |}
  | Petaurillus => {| body_size := Tiny; tail_type := Flat; habitat := Gliding;
                      cheek_pouches := Absent; has_patagium := true;
                      has_ear_tufts := false; is_striped := false |}
  | Petaurista => {| body_size := Giant; tail_type := Flat; habitat := Gliding;
                     cheek_pouches := Absent; has_patagium := true;
                     has_ear_tufts := false; is_striped := false |}
  | Pteromys => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                   cheek_pouches := Absent; has_patagium := true;
                   has_ear_tufts := false; is_striped := false |}
  | Trogopterus => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                      cheek_pouches := Absent; has_patagium := true;
                      has_ear_tufts := false; is_striped := false |}
  | Callosciurus | Dremomys | Sundasciurus => tree_squirrel_morph
  | Exilisciurus | Nannosciurus => pygmy_squirrel_morph
  | Funambulus | Tamiops => palm_squirrel_morph
  | Glyphotes | Prosciurillus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                                    cheek_pouches := Absent; has_patagium := false;
                                    has_ear_tufts := false; is_striped := false |}
  | Hyosciurus => {| body_size := Medium; tail_type := Bushy; habitat := Terrestrial;
                     cheek_pouches := Absent; has_patagium := false;
                     has_ear_tufts := false; is_striped := false |}
  | Lariscus | Menetes => {| body_size := Small; tail_type := Bushy; habitat := Terrestrial;
                             cheek_pouches := Absent; has_patagium := false;
                             has_ear_tufts := false; is_striped := true |}
  | Rhinosciurus => {| body_size := Small; tail_type := Thin; habitat := Terrestrial;
                       cheek_pouches := Absent; has_patagium := false;
                       has_ear_tufts := false; is_striped := false |}
  | Rubrisciurus => {| body_size := Large; tail_type := Bushy; habitat := Arboreal;
                       cheek_pouches := Absent; has_patagium := false;
                       has_ear_tufts := false; is_striped := false |}
  | Atlantoxerus => {| body_size := Small; tail_type := Bushy; habitat := Terrestrial;
                       cheek_pouches := Present; has_patagium := false;
                       has_ear_tufts := false; is_striped := true |}
  | Spermophilopsis => ground_squirrel_morph
  | Xerus => {| body_size := Medium; tail_type := Bushy; habitat := Terrestrial;
                cheek_pouches := Present; has_patagium := false;
                has_ear_tufts := false; is_striped := true |}
  | Epixerus | Heliosciurus => tree_squirrel_morph
  | Funisciurus => palm_squirrel_morph
  | Myosciurus => pygmy_squirrel_morph
  | Paraxerus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                    cheek_pouches := Absent; has_patagium := false;
                    has_ear_tufts := false; is_striped := false |}
  | Protoxerus => {| body_size := Large; tail_type := Bushy; habitat := Arboreal;
                     cheek_pouches := Absent; has_patagium := false;
                     has_ear_tufts := true; is_striped := false |}
  | Ammospermophilus | Callospermophilus => {| body_size := Small; tail_type := Thin; habitat := Terrestrial;
                                               cheek_pouches := Present; has_patagium := false;
                                               has_ear_tufts := false; is_striped := true |}
  | Cynomys => prairie_dog_morph
  | Ictidomys | Notocitellus | Otospermophilus | Poliocitellus => ground_squirrel_morph
  | Marmota => {| body_size := Giant; tail_type := Bushy; habitat := Fossorial;
                  cheek_pouches := Present; has_patagium := false;
                  has_ear_tufts := false; is_striped := false |}
  | Sciurotamias | Spermophilus | Urocitellus | Xerospermophilus => ground_squirrel_morph
  | Tamias | Neotamias => chipmunk_morph
  | Douglassciurus | Hesperopetes => flying_squirrel_morph
  | Palaeosciurus => ground_squirrel_morph
  | Protosciurus => tree_squirrel_morph
  end.

Definition is_flying_squirrel (g : Genus) : bool :=
  has_patagium (morphology_of g).

Definition is_giant_squirrel (g : Genus) : bool :=
  match body_size (morphology_of g) with Giant => true | _ => false end.

Definition is_ground_dwelling (g : Genus) : bool :=
  match habitat (morphology_of g) with
  | Terrestrial | Fossorial => true
  | _ => false
  end.

Definition morphology_of_species {g : Genus} (s : Species g) : Morphology :=
  morphology_of g.

Definition morphology_of_any (sp : AnySpecies) : Morphology :=
  morphology_of (genus_of_any sp).

(* ======================== Morphological Theorems ======================== *)

Theorem patagium_implies_pteromyini : forall g,
  has_patagium (morphology_of g) = true -> tribe_of g = Pteromyini.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem fossorial_implies_xerinae : forall g,
  habitat (morphology_of g) = Fossorial -> subfamily_of g = Xerinae.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem giant_body_implies_special : forall g,
  body_size (morphology_of g) = Giant ->
  (g = Ratufa \/ g = Petaurista \/ g = Marmota).
Proof. intros g H; destruct g; simpl in *; try discriminate; auto. Qed.

Theorem cheek_pouches_distribution : forall g,
  cheek_pouches (morphology_of g) = Present ->
  (subfamily_of g = Xerinae \/ g = Atlantoxerus).
Proof.
  intros g H; destruct g; simpl in *; try discriminate;
  try (left; reflexivity); try (right; reflexivity).
Qed.

Theorem striped_genera : forall g,
  is_striped (morphology_of g) = true ->
  (g = Funambulus \/ g = Tamiops \/ g = Lariscus \/ g = Menetes \/
   g = Atlantoxerus \/ g = Xerus \/ g = Funisciurus \/
   g = Ammospermophilus \/ g = Callospermophilus \/ g = Tamias \/ g = Neotamias).
Proof. intros g H; destruct g; simpl in *; try discriminate; auto 15. Qed.

Theorem flying_squirrels_have_patagium : forall g,
  tribe_of g = Pteromyini -> has_patagium (morphology_of g) = true.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem marmotini_have_cheek_pouches : forall g,
  tribe_of g = Marmotini -> cheek_pouches (morphology_of g) = Present.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem xerini_have_cheek_pouches : forall g,
  tribe_of g = Xerini -> cheek_pouches (morphology_of g) = Present.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem gliding_implies_patagium : forall g,
  habitat (morphology_of g) = Gliding -> has_patagium (morphology_of g) = true.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem patagium_implies_sciurinae : forall g,
  has_patagium (morphology_of g) = true -> subfamily_of g = Sciurinae.
Proof. intros g H; destruct g; simpl in *; try discriminate; reflexivity. Qed.

Theorem species_morph_refines_genus : forall g (s : Species g),
  morphology_of_species s = morphology_of g.
Proof. intros; reflexivity. Qed.

Example counter_flying_not_fossorial : forall g,
  is_flying_squirrel g = true -> habitat (morphology_of g) <> Fossorial.
Proof. intros g H Hf; destruct g; simpl in *; discriminate. Qed.

Example counter_giant_not_fossorial : forall g,
  is_giant_squirrel g = true -> g <> Marmota -> habitat (morphology_of g) <> Fossorial.
Proof.
  intros g Hg Hne Hf; destruct g; simpl in *; try discriminate.
  contradiction Hne; reflexivity.
Qed.

(* ======================== Fine-Grained Geographic Regions ======================== *)

Inductive Region : Type :=
  | Palearctic | Nearctic | Neotropical | Ethiopian | Oriental | Australasian
  | Sulawesi | Borneo | Philippines | Taiwan | Japan | India | China
  | WestAfrica | EastAfrica | SouthernAfrica | NorthAfrica
  | Mexico | CentralAmericaRegion | Andes | Amazon.

Definition primary_region (g : Genus) : Region :=
  match g with
  | Ratufa => Oriental
  | Sciurillus => Amazon
  | Microsciurus => Neotropical
  | Rheithrosciurus => Borneo
  | Sciurus => Nearctic
  | Syntheosciurus => CentralAmericaRegion
  | Tamiasciurus => Nearctic
  | Aeretes => China
  | Aeromys => Borneo
  | Belomys => Taiwan
  | Biswamoyopterus => India
  | Eoglaucomys => India
  | Eupetaurus => India
  | Glaucomys => Nearctic
  | Hylopetes => Oriental
  | Iomys => Borneo
  | Petaurillus => Borneo
  | Petaurista => Oriental
  | Petinomys => Oriental
  | Pteromys => Palearctic
  | Pteromyscus => Borneo
  | Trogopterus => China
  | Callosciurus => Oriental
  | Dremomys => Oriental
  | Exilisciurus => Philippines
  | Funambulus => India
  | Glyphotes => Borneo
  | Hyosciurus => Sulawesi
  | Lariscus => Borneo
  | Menetes => Oriental
  | Nannosciurus => Borneo
  | Prosciurillus => Sulawesi
  | Rhinosciurus => Borneo
  | Rubrisciurus => Sulawesi
  | Sundasciurus => Oriental
  | Tamiops => Oriental
  | Atlantoxerus => NorthAfrica
  | Spermophilopsis => Palearctic
  | Xerus => Ethiopian
  | Epixerus => WestAfrica
  | Funisciurus => Ethiopian
  | Heliosciurus => Ethiopian
  | Myosciurus => WestAfrica
  | Paraxerus => Ethiopian
  | Protoxerus => WestAfrica
  | Ammospermophilus => Nearctic
  | Callospermophilus => Nearctic
  | Cynomys => Nearctic
  | Ictidomys => Nearctic
  | Marmota => Palearctic
  | Notocitellus => Mexico
  | Otospermophilus => Nearctic
  | Poliocitellus => Nearctic
  | Sciurotamias => China
  | Spermophilus => Palearctic
  | Tamias => Nearctic
  | Neotamias => Nearctic
  | Urocitellus => Nearctic
  | Xerospermophilus => Nearctic
  | Douglassciurus => Nearctic
  | Hesperopetes => Nearctic
  | Palaeosciurus => Palearctic
  | Protosciurus => Nearctic
  end.

Definition region_eqb (r1 r2 : Region) : bool :=
  match r1, r2 with
  | Palearctic, Palearctic | Nearctic, Nearctic | Neotropical, Neotropical
  | Ethiopian, Ethiopian | Oriental, Oriental | Australasian, Australasian
  | Sulawesi, Sulawesi | Borneo, Borneo | Philippines, Philippines
  | Taiwan, Taiwan | Japan, Japan | India, India | China, China
  | WestAfrica, WestAfrica | EastAfrica, EastAfrica
  | SouthernAfrica, SouthernAfrica | NorthAfrica, NorthAfrica
  | Mexico, Mexico | CentralAmericaRegion, CentralAmericaRegion
  | Andes, Andes | Amazon, Amazon => true
  | _, _ => false
  end.

(* ======================== Fine Morphology ======================== *)

Record FineMorphology : Type := {
  ext_morph : ExtendedMorphology;
  region : Region;
  tail_tip : TailTip;
  ventral_color : VentralColor;
  stripe_count : StripeCount;
  is_island_endemic : bool;
  has_white_tail_border : bool;
  has_facial_markings : bool
}.

Definition snout_eqb (s1 s2 : SnoutShape) : bool :=
  match s1, s2 with
  | Elongated, Elongated | Normal, Normal | Blunt, Blunt => true
  | _, _ => false
  end.

Definition tail_eqb (t1 t2 : TailRatio) : bool :=
  match t1, t2 with
  | TailShort, TailShort | TailModerate, TailModerate
  | TailLong, TailLong | TailVeryLong, TailVeryLong => true
  | _, _ => false
  end.

Definition pelage_eqb (p1 p2 : PelagePattern) : bool :=
  match p1, p2 with
  | Uniform, Uniform | PelageStriped, PelageStriped | Spotted, Spotted
  | Banded, Banded | Grizzled, Grizzled => true
  | _, _ => false
  end.

Definition ear_eqb (e1 e2 : EarShape) : bool :=
  match e1, e2 with
  | Rounded, Rounded | Pointed, Pointed | EarTufted, EarTufted => true
  | _, _ => false
  end.

Definition body_eqb (b1 b2 : BodySize) : bool :=
  match b1, b2 with
  | Tiny, Tiny | Small, Small | Medium, Medium | Large, Large | Giant, Giant => true
  | _, _ => false
  end.

Definition habitat_eqb (h1 h2 : Habitat) : bool :=
  match h1, h2 with
  | Arboreal, Arboreal | Terrestrial, Terrestrial
  | Fossorial, Fossorial | Gliding, Gliding => true
  | _, _ => false
  end.

Definition tail_tip_eqb (t1 t2 : TailTip) : bool :=
  match t1, t2 with
  | TipBlack, TipBlack | TipWhite, TipWhite | TipSame, TipSame | TipBanded, TipBanded => true
  | _, _ => false
  end.

Definition ventral_eqb (v1 v2 : VentralColor) : bool :=
  match v1, v2 with
  | VentralWhite, VentralWhite | VentralOrange, VentralOrange
  | VentralGray, VentralGray | VentralBuff, VentralBuff => true
  | _, _ => false
  end.

Definition stripe_eqb (s1 s2 : StripeCount) : bool :=
  match s1, s2 with
  | NoStripes, NoStripes | OneStripe, OneStripe | ThreeStripes, ThreeStripes
  | FiveStripes, FiveStripes | SevenStripes, SevenStripes => true
  | _, _ => false
  end.

Definition extended_morphology_of (g : Genus) : ExtendedMorphology :=
  match g with
  | Ratufa => {| base_morph := morphology_of Ratufa;
                 snout_shape := Normal; tail_ratio := TailLong;
                 pelage_pattern := Uniform; ear_shape := EarTufted;
                 has_postauricular_patch := true; has_dorsal_stripe := false;
                 has_white_eye_ring := false; num_mammae := 2 |}
  | Rhinosciurus => {| base_morph := morphology_of Rhinosciurus;
                       snout_shape := Elongated; tail_ratio := TailShort;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Hyosciurus => {| base_morph := morphology_of Hyosciurus;
                     snout_shape := Elongated; tail_ratio := TailModerate;
                     pelage_pattern := Uniform; ear_shape := Rounded;
                     has_postauricular_patch := false; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 4 |}
  | Sciurus => {| base_morph := morphology_of Sciurus;
                  snout_shape := Normal; tail_ratio := TailLong;
                  pelage_pattern := Uniform; ear_shape := EarTufted;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 8 |}
  | Tamiasciurus => {| base_morph := morphology_of Tamiasciurus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := EarTufted;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 8 |}
  | Glaucomys => {| base_morph := morphology_of Glaucomys;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := true; num_mammae := 8 |}
  | Petaurista => {| base_morph := morphology_of Petaurista;
                     snout_shape := Normal; tail_ratio := TailVeryLong;
                     pelage_pattern := Uniform; ear_shape := Rounded;
                     has_postauricular_patch := false; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 4 |}
  | Eupetaurus => {| base_morph := morphology_of Eupetaurus;
                     snout_shape := Normal; tail_ratio := TailLong;
                     pelage_pattern := Uniform; ear_shape := EarTufted;
                     has_postauricular_patch := false; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 4 |}
  | Pteromys => {| base_morph := morphology_of Pteromys;
                   snout_shape := Normal; tail_ratio := TailModerate;
                   pelage_pattern := Uniform; ear_shape := Rounded;
                   has_postauricular_patch := false; has_dorsal_stripe := false;
                   has_white_eye_ring := false; num_mammae := 8 |}
  | Funambulus => {| base_morph := morphology_of Funambulus;
                     snout_shape := Normal; tail_ratio := TailLong;
                     pelage_pattern := PelageStriped; ear_shape := Rounded;
                     has_postauricular_patch := false; has_dorsal_stripe := true;
                     has_white_eye_ring := false; num_mammae := 6 |}
  | Tamiops => {| base_morph := morphology_of Tamiops;
                  snout_shape := Normal; tail_ratio := TailModerate;
                  pelage_pattern := PelageStriped; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := true;
                  has_white_eye_ring := false; num_mammae := 4 |}
  | Tamias => {| base_morph := morphology_of Tamias;
                 snout_shape := Normal; tail_ratio := TailModerate;
                 pelage_pattern := PelageStriped; ear_shape := Rounded;
                 has_postauricular_patch := false; has_dorsal_stripe := true;
                 has_white_eye_ring := false; num_mammae := 8 |}
  | Neotamias => {| base_morph := morphology_of Neotamias;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := PelageStriped; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := true;
                    has_white_eye_ring := false; num_mammae := 8 |}
  | Marmota => {| base_morph := morphology_of Marmota;
                  snout_shape := Normal; tail_ratio := TailShort;
                  pelage_pattern := Grizzled; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 10 |}
  | Cynomys => {| base_morph := morphology_of Cynomys;
                  snout_shape := Normal; tail_ratio := TailShort;
                  pelage_pattern := Uniform; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 10 |}
  | Xerus => {| base_morph := morphology_of Xerus;
                snout_shape := Normal; tail_ratio := TailLong;
                pelage_pattern := PelageStriped; ear_shape := Rounded;
                has_postauricular_patch := false; has_dorsal_stripe := true;
                has_white_eye_ring := false; num_mammae := 4 |}
  | Atlantoxerus => {| base_morph := morphology_of Atlantoxerus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := PelageStriped; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := true;
                       has_white_eye_ring := false; num_mammae := 6 |}
  | Funisciurus => {| base_morph := morphology_of Funisciurus;
                      snout_shape := Normal; tail_ratio := TailLong;
                      pelage_pattern := PelageStriped; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := true;
                      has_white_eye_ring := false; num_mammae := 6 |}
  | Protoxerus => {| base_morph := morphology_of Protoxerus;
                     snout_shape := Normal; tail_ratio := TailLong;
                     pelage_pattern := Grizzled; ear_shape := EarTufted;
                     has_postauricular_patch := false; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 6 |}
  | Rheithrosciurus => {| base_morph := morphology_of Rheithrosciurus;
                          snout_shape := Normal; tail_ratio := TailVeryLong;
                          pelage_pattern := Uniform; ear_shape := EarTufted;
                          has_postauricular_patch := false; has_dorsal_stripe := false;
                          has_white_eye_ring := false; num_mammae := 6 |}
  | Callosciurus => {| base_morph := morphology_of Callosciurus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Banded; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 6 |}
  | Dremomys => {| base_morph := morphology_of Dremomys;
                   snout_shape := Normal; tail_ratio := TailModerate;
                   pelage_pattern := Uniform; ear_shape := Rounded;
                   has_postauricular_patch := true; has_dorsal_stripe := false;
                   has_white_eye_ring := false; num_mammae := 6 |}
  | Heliosciurus => {| base_morph := morphology_of Heliosciurus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Banded; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 6 |}
  | Paraxerus => {| base_morph := morphology_of Paraxerus;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 6 |}
  | Sundasciurus => {| base_morph := morphology_of Sundasciurus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Ammospermophilus => {| base_morph := morphology_of Ammospermophilus;
                           snout_shape := Normal; tail_ratio := TailShort;
                           pelage_pattern := PelageStriped; ear_shape := Rounded;
                           has_postauricular_patch := false; has_dorsal_stripe := true;
                           has_white_eye_ring := true; num_mammae := 10 |}
  | Callospermophilus => {| base_morph := morphology_of Callospermophilus;
                            snout_shape := Normal; tail_ratio := TailModerate;
                            pelage_pattern := PelageStriped; ear_shape := Rounded;
                            has_postauricular_patch := false; has_dorsal_stripe := true;
                            has_white_eye_ring := false; num_mammae := 10 |}
  | Ictidomys => {| base_morph := morphology_of Ictidomys;
                    snout_shape := Normal; tail_ratio := TailShort;
                    pelage_pattern := Spotted; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 10 |}
  | Otospermophilus => {| base_morph := morphology_of Otospermophilus;
                          snout_shape := Normal; tail_ratio := TailLong;
                          pelage_pattern := Grizzled; ear_shape := Rounded;
                          has_postauricular_patch := false; has_dorsal_stripe := false;
                          has_white_eye_ring := false; num_mammae := 10 |}
  | Spermophilus => {| base_morph := morphology_of Spermophilus;
                       snout_shape := Normal; tail_ratio := TailShort;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 10 |}
  | Xerospermophilus => {| base_morph := morphology_of Xerospermophilus;
                           snout_shape := Normal; tail_ratio := TailShort;
                           pelage_pattern := Spotted; ear_shape := Rounded;
                           has_postauricular_patch := false; has_dorsal_stripe := false;
                           has_white_eye_ring := false; num_mammae := 10 |}
  | Lariscus => {| base_morph := morphology_of Lariscus;
                   snout_shape := Normal; tail_ratio := TailModerate;
                   pelage_pattern := PelageStriped; ear_shape := Rounded;
                   has_postauricular_patch := false; has_dorsal_stripe := true;
                   has_white_eye_ring := false; num_mammae := 4 |}
  | Sciurillus => {| base_morph := morphology_of Sciurillus;
                     snout_shape := Normal; tail_ratio := TailModerate;
                     pelage_pattern := Uniform; ear_shape := Rounded;
                     has_postauricular_patch := false; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 6 |}
  | Microsciurus => {| base_morph := morphology_of Microsciurus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 6 |}
  | Syntheosciurus => {| base_morph := morphology_of Syntheosciurus;
                         snout_shape := Normal; tail_ratio := TailLong;
                         pelage_pattern := Uniform; ear_shape := Rounded;
                         has_postauricular_patch := false; has_dorsal_stripe := false;
                         has_white_eye_ring := false; num_mammae := 8 |}
  | Aeretes => {| base_morph := morphology_of Aeretes;
                  snout_shape := Normal; tail_ratio := TailLong;
                  pelage_pattern := Uniform; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 4 |}
  | Aeromys => {| base_morph := morphology_of Aeromys;
                  snout_shape := Normal; tail_ratio := TailLong;
                  pelage_pattern := Uniform; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 4 |}
  | Belomys => {| base_morph := morphology_of Belomys;
                  snout_shape := Normal; tail_ratio := TailModerate;
                  pelage_pattern := Uniform; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 4 |}
  | Biswamoyopterus => {| base_morph := morphology_of Biswamoyopterus;
                          snout_shape := Normal; tail_ratio := TailLong;
                          pelage_pattern := Uniform; ear_shape := Rounded;
                          has_postauricular_patch := false; has_dorsal_stripe := false;
                          has_white_eye_ring := false; num_mammae := 4 |}
  | Eoglaucomys => {| base_morph := morphology_of Eoglaucomys;
                      snout_shape := Normal; tail_ratio := TailModerate;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Hylopetes => {| base_morph := morphology_of Hylopetes;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 4 |}
  | Iomys => {| base_morph := morphology_of Iomys;
                snout_shape := Normal; tail_ratio := TailModerate;
                pelage_pattern := Uniform; ear_shape := Rounded;
                has_postauricular_patch := false; has_dorsal_stripe := false;
                has_white_eye_ring := false; num_mammae := 4 |}
  | Petaurillus => {| base_morph := morphology_of Petaurillus;
                      snout_shape := Normal; tail_ratio := TailModerate;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Petinomys => {| base_morph := morphology_of Petinomys;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 4 |}
  | Pteromyscus => {| base_morph := morphology_of Pteromyscus;
                      snout_shape := Normal; tail_ratio := TailModerate;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Trogopterus => {| base_morph := morphology_of Trogopterus;
                      snout_shape := Normal; tail_ratio := TailModerate;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Exilisciurus => {| base_morph := morphology_of Exilisciurus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Glyphotes => {| base_morph := morphology_of Glyphotes;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 4 |}
  | Menetes => {| base_morph := morphology_of Menetes;
                  snout_shape := Normal; tail_ratio := TailModerate;
                  pelage_pattern := PelageStriped; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := true;
                  has_white_eye_ring := false; num_mammae := 4 |}
  | Nannosciurus => {| base_morph := morphology_of Nannosciurus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Prosciurillus => {| base_morph := morphology_of Prosciurillus;
                        snout_shape := Normal; tail_ratio := TailModerate;
                        pelage_pattern := Uniform; ear_shape := Rounded;
                        has_postauricular_patch := false; has_dorsal_stripe := false;
                        has_white_eye_ring := false; num_mammae := 4 |}
  | Rubrisciurus => {| base_morph := morphology_of Rubrisciurus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Epixerus => {| base_morph := morphology_of Epixerus;
                   snout_shape := Normal; tail_ratio := TailLong;
                   pelage_pattern := Uniform; ear_shape := Rounded;
                   has_postauricular_patch := false; has_dorsal_stripe := false;
                   has_white_eye_ring := false; num_mammae := 6 |}
  | Myosciurus => {| base_morph := morphology_of Myosciurus;
                     snout_shape := Normal; tail_ratio := TailModerate;
                     pelage_pattern := Uniform; ear_shape := Rounded;
                     has_postauricular_patch := false; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 4 |}
  | Notocitellus => {| base_morph := morphology_of Notocitellus;
                       snout_shape := Normal; tail_ratio := TailShort;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 10 |}
  | Poliocitellus => {| base_morph := morphology_of Poliocitellus;
                        snout_shape := Normal; tail_ratio := TailModerate;
                        pelage_pattern := Uniform; ear_shape := Rounded;
                        has_postauricular_patch := false; has_dorsal_stripe := false;
                        has_white_eye_ring := false; num_mammae := 10 |}
  | Sciurotamias => {| base_morph := morphology_of Sciurotamias;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 10 |}
  | Urocitellus => {| base_morph := morphology_of Urocitellus;
                      snout_shape := Normal; tail_ratio := TailShort;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 10 |}
  | Spermophilopsis => {| base_morph := morphology_of Spermophilopsis;
                          snout_shape := Normal; tail_ratio := TailModerate;
                          pelage_pattern := Uniform; ear_shape := Rounded;
                          has_postauricular_patch := false; has_dorsal_stripe := false;
                          has_white_eye_ring := false; num_mammae := 8 |}
  | Douglassciurus => {| base_morph := morphology_of Douglassciurus;
                         snout_shape := Normal; tail_ratio := TailModerate;
                         pelage_pattern := Uniform; ear_shape := Rounded;
                         has_postauricular_patch := false; has_dorsal_stripe := false;
                         has_white_eye_ring := false; num_mammae := 8 |}
  | Hesperopetes => {| base_morph := morphology_of Hesperopetes;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 8 |}
  | Palaeosciurus => {| base_morph := morphology_of Palaeosciurus;
                        snout_shape := Normal; tail_ratio := TailShort;
                        pelage_pattern := Uniform; ear_shape := Rounded;
                        has_postauricular_patch := false; has_dorsal_stripe := false;
                        has_white_eye_ring := false; num_mammae := 8 |}
  | Protosciurus => {| base_morph := morphology_of Protosciurus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 8 |}
  end.

Theorem elongated_snout_iff : forall g,
  snout_shape (extended_morphology_of g) = Elongated <->
  (g = Rhinosciurus \/ g = Hyosciurus).
Proof.
  intro g; split; intro H.
  - destruct g; simpl in H; try discriminate; auto.
  - destruct H; subst; reflexivity.
Qed.

Theorem tufted_ears_iff : forall g,
  ear_shape (extended_morphology_of g) = EarTufted <->
  (g = Ratufa \/ g = Sciurus \/ g = Tamiasciurus \/ g = Eupetaurus \/
   g = Protoxerus \/ g = Rheithrosciurus).
Proof.
  intro g; split; intro H.
  - destruct g; simpl in H; try discriminate; auto 10.
  - destruct H as [H|[H|[H|[H|[H|H]]]]]; subst; reflexivity.
Qed.

Theorem mammae_count_distinguishes : forall g1 g2,
  num_mammae (extended_morphology_of g1) <> num_mammae (extended_morphology_of g2) ->
  g1 <> g2.
Proof. intros g1 g2 H Heq; subst; contradiction. Qed.

Theorem ratufa_unique_mammae : forall g,
  num_mammae (extended_morphology_of g) = 2 -> g = Ratufa.
Proof. intros g H; destruct g; simpl in H; try discriminate; reflexivity. Qed.

Theorem high_mammae_genera : forall g,
  num_mammae (extended_morphology_of g) = 10 ->
  (g = Marmota \/ g = Cynomys \/ g = Ammospermophilus \/ g = Callospermophilus \/
   g = Ictidomys \/ g = Notocitellus \/ g = Otospermophilus \/ g = Poliocitellus \/
   g = Sciurotamias \/ g = Spermophilus \/ g = Urocitellus \/ g = Xerospermophilus).
Proof. intros g H; destruct g; simpl in H; try discriminate; auto 20. Qed.

Theorem dorsal_stripe_genera : forall g,
  has_dorsal_stripe (extended_morphology_of g) = true ->
  (g = Funambulus \/ g = Tamiops \/ g = Tamias \/ g = Neotamias \/ g = Xerus \/
   g = Atlantoxerus \/ g = Funisciurus \/ g = Lariscus \/ g = Menetes \/
   g = Ammospermophilus \/ g = Callospermophilus).
Proof. intros g H; destruct g; simpl in H; try discriminate; auto 15. Qed.

Definition fine_morphology_of (g : Genus) : FineMorphology :=
  match g with
  | Ratufa => {| ext_morph := extended_morphology_of Ratufa;
                 region := Oriental; tail_tip := TipSame; ventral_color := VentralBuff;
                 stripe_count := NoStripes; is_island_endemic := false;
                 has_white_tail_border := false; has_facial_markings := true |}
  | Sciurillus => {| ext_morph := extended_morphology_of Sciurillus;
                     region := Amazon; tail_tip := TipSame; ventral_color := VentralOrange;
                     stripe_count := NoStripes; is_island_endemic := false;
                     has_white_tail_border := false; has_facial_markings := false |}
  | Rheithrosciurus => {| ext_morph := extended_morphology_of Rheithrosciurus;
                          region := Borneo; tail_tip := TipWhite; ventral_color := VentralWhite;
                          stripe_count := NoStripes; is_island_endemic := true;
                          has_white_tail_border := true; has_facial_markings := true |}
  | Aeretes => {| ext_morph := extended_morphology_of Aeretes;
                  region := China; tail_tip := TipBlack; ventral_color := VentralWhite;
                  stripe_count := NoStripes; is_island_endemic := false;
                  has_white_tail_border := false; has_facial_markings := false |}
  | Aeromys => {| ext_morph := extended_morphology_of Aeromys;
                  region := Borneo; tail_tip := TipBlack; ventral_color := VentralGray;
                  stripe_count := NoStripes; is_island_endemic := true;
                  has_white_tail_border := false; has_facial_markings := false |}
  | Belomys => {| ext_morph := extended_morphology_of Belomys;
                  region := Taiwan; tail_tip := TipSame; ventral_color := VentralOrange;
                  stripe_count := NoStripes; is_island_endemic := false;
                  has_white_tail_border := false; has_facial_markings := true |}
  | Biswamoyopterus => {| ext_morph := extended_morphology_of Biswamoyopterus;
                          region := India; tail_tip := TipBlack; ventral_color := VentralBuff;
                          stripe_count := NoStripes; is_island_endemic := false;
                          has_white_tail_border := false; has_facial_markings := false |}
  | Eoglaucomys => {| ext_morph := extended_morphology_of Eoglaucomys;
                      region := India; tail_tip := TipSame; ventral_color := VentralWhite;
                      stripe_count := NoStripes; is_island_endemic := false;
                      has_white_tail_border := true; has_facial_markings := false |}
  | Eupetaurus => {| ext_morph := extended_morphology_of Eupetaurus;
                     region := India; tail_tip := TipSame; ventral_color := VentralGray;
                     stripe_count := NoStripes; is_island_endemic := false;
                     has_white_tail_border := false; has_facial_markings := false |}
  | Glaucomys => {| ext_morph := extended_morphology_of Glaucomys;
                    region := Nearctic; tail_tip := TipSame; ventral_color := VentralWhite;
                    stripe_count := NoStripes; is_island_endemic := false;
                    has_white_tail_border := false; has_facial_markings := true |}
  | Hylopetes => {| ext_morph := extended_morphology_of Hylopetes;
                    region := Oriental; tail_tip := TipSame; ventral_color := VentralWhite;
                    stripe_count := NoStripes; is_island_endemic := false;
                    has_white_tail_border := false; has_facial_markings := false |}
  | Iomys => {| ext_morph := extended_morphology_of Iomys;
                region := Borneo; tail_tip := TipBlack; ventral_color := VentralOrange;
                stripe_count := NoStripes; is_island_endemic := true;
                has_white_tail_border := false; has_facial_markings := false |}
  | Petaurillus => {| ext_morph := extended_morphology_of Petaurillus;
                      region := Borneo; tail_tip := TipSame; ventral_color := VentralWhite;
                      stripe_count := NoStripes; is_island_endemic := true;
                      has_white_tail_border := false; has_facial_markings := false |}
  | Petaurista => {| ext_morph := extended_morphology_of Petaurista;
                     region := Oriental; tail_tip := TipBlack; ventral_color := VentralOrange;
                     stripe_count := NoStripes; is_island_endemic := false;
                     has_white_tail_border := false; has_facial_markings := true |}
  | Petinomys => {| ext_morph := extended_morphology_of Petinomys;
                    region := Oriental; tail_tip := TipBlack; ventral_color := VentralGray;
                    stripe_count := NoStripes; is_island_endemic := false;
                    has_white_tail_border := false; has_facial_markings := false |}
  | Pteromys => {| ext_morph := extended_morphology_of Pteromys;
                   region := Palearctic; tail_tip := TipSame; ventral_color := VentralWhite;
                   stripe_count := NoStripes; is_island_endemic := false;
                   has_white_tail_border := false; has_facial_markings := false |}
  | Pteromyscus => {| ext_morph := extended_morphology_of Pteromyscus;
                      region := Borneo; tail_tip := TipSame; ventral_color := VentralGray;
                      stripe_count := NoStripes; is_island_endemic := true;
                      has_white_tail_border := false; has_facial_markings := false |}
  | Trogopterus => {| ext_morph := extended_morphology_of Trogopterus;
                      region := China; tail_tip := TipSame; ventral_color := VentralBuff;
                      stripe_count := NoStripes; is_island_endemic := false;
                      has_white_tail_border := false; has_facial_markings := false |}
  | Exilisciurus => {| ext_morph := extended_morphology_of Exilisciurus;
                       region := Philippines; tail_tip := TipSame; ventral_color := VentralWhite;
                       stripe_count := NoStripes; is_island_endemic := true;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Glyphotes => {| ext_morph := extended_morphology_of Glyphotes;
                    region := Borneo; tail_tip := TipSame; ventral_color := VentralBuff;
                    stripe_count := NoStripes; is_island_endemic := true;
                    has_white_tail_border := false; has_facial_markings := false |}
  | Hyosciurus => {| ext_morph := extended_morphology_of Hyosciurus;
                     region := Sulawesi; tail_tip := TipSame; ventral_color := VentralGray;
                     stripe_count := NoStripes; is_island_endemic := true;
                     has_white_tail_border := false; has_facial_markings := false |}
  | Lariscus => {| ext_morph := extended_morphology_of Lariscus;
                   region := Borneo; tail_tip := TipSame; ventral_color := VentralBuff;
                   stripe_count := ThreeStripes; is_island_endemic := false;
                   has_white_tail_border := false; has_facial_markings := false |}
  | Menetes => {| ext_morph := extended_morphology_of Menetes;
                  region := Oriental; tail_tip := TipSame; ventral_color := VentralBuff;
                  stripe_count := OneStripe; is_island_endemic := false;
                  has_white_tail_border := false; has_facial_markings := false |}
  | Nannosciurus => {| ext_morph := extended_morphology_of Nannosciurus;
                       region := Borneo; tail_tip := TipBlack; ventral_color := VentralWhite;
                       stripe_count := NoStripes; is_island_endemic := true;
                       has_white_tail_border := false; has_facial_markings := true |}
  | Prosciurillus => {| ext_morph := extended_morphology_of Prosciurillus;
                        region := Sulawesi; tail_tip := TipSame; ventral_color := VentralBuff;
                        stripe_count := NoStripes; is_island_endemic := true;
                        has_white_tail_border := false; has_facial_markings := false |}
  | Rhinosciurus => {| ext_morph := extended_morphology_of Rhinosciurus;
                       region := Borneo; tail_tip := TipSame; ventral_color := VentralWhite;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Rubrisciurus => {| ext_morph := extended_morphology_of Rubrisciurus;
                       region := Sulawesi; tail_tip := TipSame; ventral_color := VentralOrange;
                       stripe_count := NoStripes; is_island_endemic := true;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Funambulus => {| ext_morph := extended_morphology_of Funambulus;
                     region := India; tail_tip := TipSame; ventral_color := VentralWhite;
                     stripe_count := ThreeStripes; is_island_endemic := false;
                     has_white_tail_border := false; has_facial_markings := false |}
  | Tamiops => {| ext_morph := extended_morphology_of Tamiops;
                  region := Oriental; tail_tip := TipSame; ventral_color := VentralBuff;
                  stripe_count := FiveStripes; is_island_endemic := false;
                  has_white_tail_border := false; has_facial_markings := false |}
  | Tamias => {| ext_morph := extended_morphology_of Tamias;
                 region := Nearctic; tail_tip := TipSame; ventral_color := VentralWhite;
                 stripe_count := FiveStripes; is_island_endemic := false;
                 has_white_tail_border := false; has_facial_markings := true |}
  | Neotamias => {| ext_morph := extended_morphology_of Neotamias;
                    region := Nearctic; tail_tip := TipSame; ventral_color := VentralBuff;
                    stripe_count := FiveStripes; is_island_endemic := false;
                    has_white_tail_border := false; has_facial_markings := true |}
  | Ammospermophilus => {| ext_morph := extended_morphology_of Ammospermophilus;
                           region := Nearctic; tail_tip := TipBlack; ventral_color := VentralWhite;
                           stripe_count := OneStripe; is_island_endemic := false;
                           has_white_tail_border := true; has_facial_markings := false |}
  | Callospermophilus => {| ext_morph := extended_morphology_of Callospermophilus;
                            region := Nearctic; tail_tip := TipBlack; ventral_color := VentralBuff;
                            stripe_count := OneStripe; is_island_endemic := false;
                            has_white_tail_border := false; has_facial_markings := false |}
  | Ictidomys => {| ext_morph := extended_morphology_of Ictidomys;
                    region := Nearctic; tail_tip := TipSame; ventral_color := VentralWhite;
                    stripe_count := NoStripes; is_island_endemic := false;
                    has_white_tail_border := false; has_facial_markings := false |}
  | Notocitellus => {| ext_morph := extended_morphology_of Notocitellus;
                       region := Mexico; tail_tip := TipSame; ventral_color := VentralBuff;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Otospermophilus => {| ext_morph := extended_morphology_of Otospermophilus;
                          region := Nearctic; tail_tip := TipBlack; ventral_color := VentralBuff;
                          stripe_count := NoStripes; is_island_endemic := false;
                          has_white_tail_border := true; has_facial_markings := false |}
  | Poliocitellus => {| ext_morph := extended_morphology_of Poliocitellus;
                        region := Nearctic; tail_tip := TipBlack; ventral_color := VentralGray;
                        stripe_count := NoStripes; is_island_endemic := false;
                        has_white_tail_border := false; has_facial_markings := false |}
  | Sciurotamias => {| ext_morph := extended_morphology_of Sciurotamias;
                       region := China; tail_tip := TipBlack; ventral_color := VentralWhite;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := true |}
  | Spermophilus => {| ext_morph := extended_morphology_of Spermophilus;
                       region := Palearctic; tail_tip := TipSame; ventral_color := VentralBuff;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Urocitellus => {| ext_morph := extended_morphology_of Urocitellus;
                      region := Nearctic; tail_tip := TipBlack; ventral_color := VentralWhite;
                      stripe_count := NoStripes; is_island_endemic := false;
                      has_white_tail_border := false; has_facial_markings := false |}
  | Xerospermophilus => {| ext_morph := extended_morphology_of Xerospermophilus;
                           region := Nearctic; tail_tip := TipSame; ventral_color := VentralWhite;
                           stripe_count := NoStripes; is_island_endemic := false;
                           has_white_tail_border := false; has_facial_markings := true |}
  | Douglassciurus => {| ext_morph := extended_morphology_of Douglassciurus;
                         region := Nearctic; tail_tip := TipBanded; ventral_color := VentralGray;
                         stripe_count := NoStripes; is_island_endemic := false;
                         has_white_tail_border := false; has_facial_markings := false |}
  | Hesperopetes => {| ext_morph := extended_morphology_of Hesperopetes;
                       region := Nearctic; tail_tip := TipWhite; ventral_color := VentralGray;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Palaeosciurus => {| ext_morph := extended_morphology_of Palaeosciurus;
                        region := Palearctic; tail_tip := TipBanded; ventral_color := VentralGray;
                        stripe_count := NoStripes; is_island_endemic := false;
                        has_white_tail_border := false; has_facial_markings := false |}
  | Protosciurus => {| ext_morph := extended_morphology_of Protosciurus;
                       region := Nearctic; tail_tip := TipBanded; ventral_color := VentralOrange;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Microsciurus => {| ext_morph := extended_morphology_of Microsciurus;
                       region := Neotropical; tail_tip := TipSame; ventral_color := VentralBuff;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Sciurus => {| ext_morph := extended_morphology_of Sciurus;
                  region := Nearctic; tail_tip := TipSame; ventral_color := VentralWhite;
                  stripe_count := NoStripes; is_island_endemic := false;
                  has_white_tail_border := false; has_facial_markings := false |}
  | Syntheosciurus => {| ext_morph := extended_morphology_of Syntheosciurus;
                         region := CentralAmericaRegion; tail_tip := TipSame; ventral_color := VentralBuff;
                         stripe_count := NoStripes; is_island_endemic := false;
                         has_white_tail_border := false; has_facial_markings := false |}
  | Tamiasciurus => {| ext_morph := extended_morphology_of Tamiasciurus;
                       region := Nearctic; tail_tip := TipSame; ventral_color := VentralWhite;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Callosciurus => {| ext_morph := extended_morphology_of Callosciurus;
                       region := Oriental; tail_tip := TipSame; ventral_color := VentralOrange;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Dremomys => {| ext_morph := extended_morphology_of Dremomys;
                   region := Oriental; tail_tip := TipSame; ventral_color := VentralOrange;
                   stripe_count := NoStripes; is_island_endemic := false;
                   has_white_tail_border := false; has_facial_markings := false |}
  | Sundasciurus => {| ext_morph := extended_morphology_of Sundasciurus;
                       region := Oriental; tail_tip := TipSame; ventral_color := VentralBuff;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Atlantoxerus => {| ext_morph := extended_morphology_of Atlantoxerus;
                       region := NorthAfrica; tail_tip := TipSame; ventral_color := VentralWhite;
                       stripe_count := ThreeStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Spermophilopsis => {| ext_morph := extended_morphology_of Spermophilopsis;
                          region := Palearctic; tail_tip := TipSame; ventral_color := VentralBuff;
                          stripe_count := NoStripes; is_island_endemic := false;
                          has_white_tail_border := false; has_facial_markings := false |}
  | Xerus => {| ext_morph := extended_morphology_of Xerus;
                region := Ethiopian; tail_tip := TipSame; ventral_color := VentralWhite;
                stripe_count := OneStripe; is_island_endemic := false;
                has_white_tail_border := false; has_facial_markings := false |}
  | Epixerus => {| ext_morph := extended_morphology_of Epixerus;
                   region := WestAfrica; tail_tip := TipSame; ventral_color := VentralBuff;
                   stripe_count := NoStripes; is_island_endemic := false;
                   has_white_tail_border := false; has_facial_markings := false |}
  | Funisciurus => {| ext_morph := extended_morphology_of Funisciurus;
                      region := Ethiopian; tail_tip := TipSame; ventral_color := VentralBuff;
                      stripe_count := OneStripe; is_island_endemic := false;
                      has_white_tail_border := false; has_facial_markings := false |}
  | Heliosciurus => {| ext_morph := extended_morphology_of Heliosciurus;
                       region := Ethiopian; tail_tip := TipSame; ventral_color := VentralBuff;
                       stripe_count := NoStripes; is_island_endemic := false;
                       has_white_tail_border := false; has_facial_markings := false |}
  | Myosciurus => {| ext_morph := extended_morphology_of Myosciurus;
                     region := WestAfrica; tail_tip := TipSame; ventral_color := VentralWhite;
                     stripe_count := NoStripes; is_island_endemic := false;
                     has_white_tail_border := false; has_facial_markings := false |}
  | Paraxerus => {| ext_morph := extended_morphology_of Paraxerus;
                    region := Ethiopian; tail_tip := TipSame; ventral_color := VentralBuff;
                    stripe_count := NoStripes; is_island_endemic := false;
                    has_white_tail_border := false; has_facial_markings := false |}
  | Protoxerus => {| ext_morph := extended_morphology_of Protoxerus;
                     region := WestAfrica; tail_tip := TipSame; ventral_color := VentralBuff;
                     stripe_count := NoStripes; is_island_endemic := false;
                     has_white_tail_border := false; has_facial_markings := false |}
  | Cynomys => {| ext_morph := extended_morphology_of Cynomys;
                  region := Nearctic; tail_tip := TipBlack; ventral_color := VentralBuff;
                  stripe_count := NoStripes; is_island_endemic := false;
                  has_white_tail_border := false; has_facial_markings := false |}
  | Marmota => {| ext_morph := extended_morphology_of Marmota;
                  region := Palearctic; tail_tip := TipSame; ventral_color := VentralBuff;
                  stripe_count := NoStripes; is_island_endemic := false;
                  has_white_tail_border := false; has_facial_markings := false |}
  end.

(* ======================== Genus Identification Key ======================== *)

Definition genus_key (g : Genus) : Genus :=
  let fm := fine_morphology_of g in
  let em := ext_morph fm in
  let m := base_morph em in
  let reg := region fm in
  if has_patagium m then
    match body_size m with
    | Giant => Petaurista
    | Large =>
        if region_eqb reg Borneo then Aeromys
        else if region_eqb reg India then
          if ear_eqb (ear_shape em) EarTufted then Eupetaurus else Biswamoyopterus
        else Petaurista
    | Medium =>
        if region_eqb reg Nearctic then
          if tail_tip_eqb (tail_tip fm) TipBanded then Douglassciurus
          else if tail_tip_eqb (tail_tip fm) TipWhite then Hesperopetes
          else Glaucomys
        else if region_eqb reg Palearctic then Pteromys
        else if region_eqb reg China then
          if tail_tip_eqb (tail_tip fm) TipBlack then Aeretes else Trogopterus
        else if region_eqb reg India then
          if ear_eqb (ear_shape em) EarTufted then Eupetaurus
          else if has_white_tail_border fm then Eoglaucomys
          else Biswamoyopterus
        else if region_eqb reg Taiwan then Belomys
        else if region_eqb reg Borneo then
          if ventral_eqb (ventral_color fm) VentralOrange then Iomys
          else if ventral_eqb (ventral_color fm) VentralGray then Pteromyscus
          else Hylopetes
        else if region_eqb reg Oriental then
          if tail_tip_eqb (tail_tip fm) TipBlack then Petinomys else Hylopetes
        else Hylopetes
    | Small =>
        if region_eqb reg Nearctic then
          if tail_tip_eqb (tail_tip fm) TipBanded then Douglassciurus
          else if tail_tip_eqb (tail_tip fm) TipWhite then Hesperopetes
          else Glaucomys
        else if region_eqb reg Palearctic then Pteromys
        else if region_eqb reg India then Eoglaucomys
        else Hylopetes
    | Tiny => Petaurillus
    end
  else if snout_eqb (snout_shape em) Elongated then
    if region_eqb reg Sulawesi then Hyosciurus else Rhinosciurus
  else if Nat.eqb (num_mammae em) 2 then Ratufa
  else if region_eqb reg Sulawesi then
    if body_eqb (body_size m) Large then Rubrisciurus
    else Prosciurillus
  else if region_eqb reg Amazon then Sciurillus
  else if region_eqb reg Borneo then
    if ear_eqb (ear_shape em) EarTufted then Rheithrosciurus
    else if body_eqb (body_size m) Tiny then Nannosciurus
    else if has_dorsal_stripe em then Lariscus
    else if body_eqb (body_size m) Small then
      if is_island_endemic fm then Glyphotes else Sundasciurus
    else Callosciurus
  else if region_eqb reg Philippines then Exilisciurus
  else match cheek_pouches m with
  | Present =>
      if habitat_eqb (habitat m) Fossorial then
        if body_eqb (body_size m) Giant then Marmota
        else if body_eqb (body_size m) Large then Marmota
        else Cynomys
      else if region_eqb reg NorthAfrica then Atlantoxerus
      else if region_eqb reg Ethiopian then Xerus
      else if region_eqb reg Palearctic then
        if Nat.eqb (num_mammae em) 10 then Spermophilus
        else if tail_tip_eqb (tail_tip fm) TipBanded then Palaeosciurus
        else Spermophilopsis
      else if region_eqb reg China then Sciurotamias
      else if region_eqb reg Mexico then Notocitellus
      else if stripe_eqb (stripe_count fm) FiveStripes then
        if ventral_eqb (ventral_color fm) VentralBuff then Neotamias else Tamias
      else if stripe_eqb (stripe_count fm) OneStripe then
        if has_white_tail_border fm then Ammospermophilus else Callospermophilus
      else if pelage_eqb (pelage_pattern em) Spotted then
        if has_facial_markings fm then Xerospermophilus else Ictidomys
      else if pelage_eqb (pelage_pattern em) Grizzled then Otospermophilus
      else if ventral_eqb (ventral_color fm) VentralGray then Poliocitellus
      else if tail_tip_eqb (tail_tip fm) TipBlack then Urocitellus
      else Spermophilus
  | Absent =>
      if body_eqb (body_size m) Giant then
        if region_eqb reg Oriental then Ratufa
        else Protoxerus
      else if body_eqb (body_size m) Tiny then
        if region_eqb reg WestAfrica then Myosciurus
        else if region_eqb reg Philippines then Exilisciurus
        else if region_eqb reg Amazon then Sciurillus
        else Exilisciurus
      else if region_eqb reg WestAfrica then
        if body_eqb (body_size m) Large then Protoxerus
        else if pelage_eqb (pelage_pattern em) Grizzled then Protoxerus
        else Epixerus
      else if region_eqb reg Ethiopian then
        if has_dorsal_stripe em then Funisciurus
        else if pelage_eqb (pelage_pattern em) Banded then Heliosciurus
        else Paraxerus
      else if region_eqb reg India then
        if stripe_eqb (stripe_count fm) ThreeStripes then Funambulus
        else if has_postauricular_patch em then Dremomys
        else Funambulus
      else if region_eqb reg Oriental then
        if stripe_eqb (stripe_count fm) FiveStripes then Tamiops
        else if stripe_eqb (stripe_count fm) OneStripe then Menetes
        else if has_postauricular_patch em then Dremomys
        else if pelage_eqb (pelage_pattern em) Banded then Callosciurus
        else if Nat.eqb (num_mammae em) 4 then Sundasciurus
        else Callosciurus
      else if region_eqb reg CentralAmericaRegion then
        if body_eqb (body_size m) Small then Microsciurus
        else Syntheosciurus
      else if region_eqb reg Neotropical then Microsciurus
      else if region_eqb reg Nearctic then
        if tail_tip_eqb (tail_tip fm) TipBanded then Protosciurus
        else if body_eqb (body_size m) Small then Tamiasciurus
        else Sciurus
      else Sciurus
  end.

(* ======================== Key Correctness ======================== *)

Definition key_correct (g : Genus) : bool := genus_eqb (genus_key g) g.

Definition count_key_correct : nat :=
  List.length (filter key_correct all_genera).

Definition misclassified_genera : list Genus :=
  filter (fun g => negb (key_correct g)) all_genera.

Eval compute in count_key_correct.
Eval compute in misclassified_genera.

Theorem key_100_percent_accuracy : count_key_correct = 63.
Proof. reflexivity. Qed.

Theorem key_no_misclassifications : misclassified_genera = [].
Proof. reflexivity. Qed.

Theorem key_complete_proof : forall g : Genus, key_correct g = true.
Proof. intro g; destruct g; reflexivity. Qed.

Theorem key_identifies_genus : forall g : Genus, genus_key g = g.
Proof. intro g; destruct g; reflexivity. Qed.

(* ======================== Species-Level Data ======================== *)

Inductive ConservationStatus : Type :=
  | LC | NT | VU | EN | CR | DD | NE.

Record SpeciesData : Type := {
  body_length_min_mm : nat;
  body_length_max_mm : nat;
  tail_length_min_mm : nat;
  tail_length_max_mm : nat;
  mass_min_g : nat;
  mass_max_g : nat;
  conservation : ConservationStatus;
  distribution_note : string
}.

Definition default_species_data : SpeciesData :=
  {| body_length_min_mm := 0; body_length_max_mm := 0;
     tail_length_min_mm := 0; tail_length_max_mm := 0;
     mass_min_g := 0; mass_max_g := 0;
     conservation := NE; distribution_note := "" |}.

Definition species_data {g : Genus} (s : Species g) : SpeciesData :=
  match s with
  | Ratufa_affinis => {| body_length_min_mm := 320; body_length_max_mm := 380;
      tail_length_min_mm := 310; tail_length_max_mm := 370;
      mass_min_g := 900; mass_max_g := 1500; conservation := NT;
      distribution_note := "Malay Peninsula, Sumatra, Borneo" |}
  | Ratufa_bicolor => {| body_length_min_mm := 350; body_length_max_mm := 400;
      tail_length_min_mm := 400; tail_length_max_mm := 450;
      mass_min_g := 1100; mass_max_g := 1800; conservation := NT;
      distribution_note := "South and Southeast Asia forests" |}
  | Ratufa_indica => {| body_length_min_mm := 360; body_length_max_mm := 450;
      tail_length_min_mm := 500; tail_length_max_mm := 610;
      mass_min_g := 1500; mass_max_g := 2000; conservation := LC;
      distribution_note := "Indian subcontinent deciduous forests" |}
  | Ratufa_macroura => {| body_length_min_mm := 250; body_length_max_mm := 350;
      tail_length_min_mm := 250; tail_length_max_mm := 340;
      mass_min_g := 700; mass_max_g := 1100; conservation := NT;
      distribution_note := "Sri Lanka and southern India" |}
  | Sciurillus_pusillus => {| body_length_min_mm := 90; body_length_max_mm := 110;
      tail_length_min_mm := 90; tail_length_max_mm := 120;
      mass_min_g := 33; mass_max_g := 45; conservation := LC;
      distribution_note := "Amazon basin" |}
  | Sciurus_carolinensis => {| body_length_min_mm := 230; body_length_max_mm := 300;
      tail_length_min_mm := 190; tail_length_max_mm := 250;
      mass_min_g := 400; mass_max_g := 600; conservation := LC;
      distribution_note := "Eastern North America, introduced Europe" |}
  | Sciurus_vulgaris => {| body_length_min_mm := 190; body_length_max_mm := 230;
      tail_length_min_mm := 150; tail_length_max_mm := 200;
      mass_min_g := 250; mass_max_g := 350; conservation := LC;
      distribution_note := "Eurasia boreal and temperate forests" |}
  | Sciurus_niger => {| body_length_min_mm := 250; body_length_max_mm := 380;
      tail_length_min_mm := 200; tail_length_max_mm := 330;
      mass_min_g := 500; mass_max_g := 1000; conservation := LC;
      distribution_note := "Eastern and central North America" |}
  | Tamias_striatus => {| body_length_min_mm := 125; body_length_max_mm := 150;
      tail_length_min_mm := 75; tail_length_max_mm := 100;
      mass_min_g := 70; mass_max_g := 140; conservation := LC;
      distribution_note := "Eastern North America deciduous forests" |}
  | Marmota_monax => {| body_length_min_mm := 400; body_length_max_mm := 650;
      tail_length_min_mm := 100; tail_length_max_mm := 180;
      mass_min_g := 2000; mass_max_g := 6300; conservation := LC;
      distribution_note := "Eastern North America" |}
  | Marmota_marmota => {| body_length_min_mm := 500; body_length_max_mm := 580;
      tail_length_min_mm := 130; tail_length_max_mm := 160;
      mass_min_g := 4000; mass_max_g := 8000; conservation := LC;
      distribution_note := "European Alps, Carpathians, Pyrenees" |}
  | Cynomys_ludovicianus => {| body_length_min_mm := 280; body_length_max_mm := 330;
      tail_length_min_mm := 75; tail_length_max_mm := 100;
      mass_min_g := 700; mass_max_g := 1400; conservation := LC;
      distribution_note := "North American Great Plains" |}
  | Glaucomys_volans => {| body_length_min_mm := 130; body_length_max_mm := 150;
      tail_length_min_mm := 80; tail_length_max_mm := 120;
      mass_min_g := 45; mass_max_g := 82; conservation := LC;
      distribution_note := "Eastern North America" |}
  | Petaurista_petaurista => {| body_length_min_mm := 340; body_length_max_mm := 600;
      tail_length_min_mm := 390; tail_length_max_mm := 635;
      mass_min_g := 1000; mass_max_g := 2500; conservation := LC;
      distribution_note := "South and Southeast Asia" |}
  | Callosciurus_prevostii => {| body_length_min_mm := 200; body_length_max_mm := 280;
      tail_length_min_mm := 200; tail_length_max_mm := 250;
      mass_min_g := 350; mass_max_g := 500; conservation := LC;
      distribution_note := "Thai-Malay Peninsula, Sumatra, Borneo" |}
  | Funambulus_palmarum => {| body_length_min_mm := 110; body_length_max_mm := 180;
      tail_length_min_mm := 110; tail_length_max_mm := 180;
      mass_min_g := 100; mass_max_g := 120; conservation := LC;
      distribution_note := "India and Sri Lanka" |}
  | Xerus_inauris => {| body_length_min_mm := 220; body_length_max_mm := 260;
      tail_length_min_mm := 200; tail_length_max_mm := 250;
      mass_min_g := 500; mass_max_g := 1000; conservation := LC;
      distribution_note := "Southern Africa semi-arid regions" |}
  | Biswamoyopterus_biswasi => {| body_length_min_mm := 400; body_length_max_mm := 450;
      tail_length_min_mm := 600; tail_length_max_mm := 610;
      mass_min_g := 1500; mass_max_g := 1800; conservation := CR;
      distribution_note := "Arunachal Pradesh, India (single specimen)" |}
  | Rheithrosciurus_macrotis => {| body_length_min_mm := 300; body_length_max_mm := 350;
      tail_length_min_mm := 300; tail_length_max_mm := 350;
      mass_min_g := 1000; mass_max_g := 1500; conservation := VU;
      distribution_note := "Borneo montane forests" |}
  | _ => default_species_data
  end.

Theorem species_data_preserves_genus_size : forall g (s : Species g),
  body_length_min_mm (species_data s) > 0 ->
  body_size (morphology_of g) = Giant ->
  body_length_max_mm (species_data s) >= 300.
Proof.
  intros g s Hpos Hgiant.
  destruct s; simpl in *; try discriminate; try lia.
Qed.

Definition count_species_with_data : nat :=
  List.length (filter (fun sp =>
    match sp with
    | existT _ _ s => Nat.ltb 0 (body_length_min_mm (species_data s))
    end) all_species).

Lemma at_least_some_species_have_data : count_species_with_data >= 19.
Proof. native_compute. lia. Qed.

Definition species_conservation {g : Genus} (s : Species g) : ConservationStatus :=
  conservation (species_data s).

Lemma ratufa_species_have_data :
  Nat.ltb 0 (body_length_min_mm (species_data Ratufa_affinis)) = true /\
  Nat.ltb 0 (body_length_min_mm (species_data Ratufa_bicolor)) = true /\
  Nat.ltb 0 (body_length_min_mm (species_data Ratufa_indica)) = true /\
  Nat.ltb 0 (body_length_min_mm (species_data Ratufa_macroura)) = true.
Proof. repeat split; reflexivity. Qed.

(* ======================== Phylogenetic Tree Structure ======================== *)

Inductive PhyloNode : Type :=
  | Leaf : Genus -> PhyloNode
  | Clade : string -> list PhyloNode -> PhyloNode.

Definition pteromyini_clade : PhyloNode :=
  Clade "Pteromyini" [
    Leaf Glaucomys; Leaf Pteromys; Leaf Petaurista; Leaf Aeromys;
    Leaf Hylopetes; Leaf Petinomys; Leaf Petaurillus; Leaf Aeretes;
    Leaf Belomys; Leaf Biswamoyopterus; Leaf Eoglaucomys; Leaf Eupetaurus;
    Leaf Iomys; Leaf Pteromyscus; Leaf Trogopterus;
    Leaf Douglassciurus; Leaf Hesperopetes
  ].

Definition sciurini_clade : PhyloNode :=
  Clade "Sciurini" [
    Leaf Sciurus; Leaf Tamiasciurus; Leaf Microsciurus;
    Leaf Syntheosciurus; Leaf Rheithrosciurus
  ].

Definition marmotini_clade : PhyloNode :=
  Clade "Marmotini" [
    Leaf Marmota; Leaf Cynomys; Leaf Tamias; Leaf Neotamias;
    Leaf Spermophilus; Leaf Urocitellus; Leaf Ammospermophilus;
    Leaf Callospermophilus; Leaf Ictidomys; Leaf Notocitellus;
    Leaf Otospermophilus; Leaf Poliocitellus; Leaf Sciurotamias;
    Leaf Xerospermophilus; Leaf Palaeosciurus
  ].

Definition xerini_clade : PhyloNode :=
  Clade "Xerini" [Leaf Xerus; Leaf Atlantoxerus; Leaf Spermophilopsis].

Definition protoxerini_clade : PhyloNode :=
  Clade "Protoxerini" [
    Leaf Funisciurus; Leaf Heliosciurus; Leaf Paraxerus;
    Leaf Protoxerus; Leaf Epixerus; Leaf Myosciurus
  ].

Definition callosciurinae_clade : PhyloNode :=
  Clade "Callosciurinae" [
    Leaf Callosciurus; Leaf Dremomys; Leaf Exilisciurus;
    Leaf Funambulus; Leaf Glyphotes; Leaf Hyosciurus;
    Leaf Lariscus; Leaf Menetes; Leaf Nannosciurus;
    Leaf Prosciurillus; Leaf Rhinosciurus; Leaf Rubrisciurus;
    Leaf Sundasciurus; Leaf Tamiops
  ].

Definition sciuridae_tree : PhyloNode :=
  Clade "Sciuridae" [
    Clade "Ratufinae" [Leaf Ratufa];
    Clade "Sciurillinae" [Leaf Sciurillus];
    Clade "Sciurinae" [sciurini_clade; pteromyini_clade; Leaf Protosciurus];
    callosciurinae_clade;
    Clade "Xerinae" [xerini_clade; protoxerini_clade; marmotini_clade]
  ].

Fixpoint tree_genera (t : PhyloNode) : list Genus :=
  match t with
  | Leaf g => [g]
  | Clade _ children => flat_map tree_genera children
  end.

Theorem tree_contains_all_genera :
  List.length (tree_genera sciuridae_tree) = 63.
Proof. reflexivity. Qed.

Fixpoint in_tree (g : Genus) (t : PhyloNode) : bool :=
  match t with
  | Leaf g' => genus_eqb g g'
  | Clade _ children => existsb (in_tree g) children
  end.

Definition clade_monophyletic_for_tribe (c : PhyloNode) (tr : Tribe) : Prop :=
  forall g, In g (tree_genera c) -> tribe_of g = tr.

Definition clade_monophyletic_for_subfamily (c : PhyloNode) (sf : Subfamily) : Prop :=
  forall g, In g (tree_genera c) -> subfamily_of g = sf.

Theorem pteromyini_monophyly : clade_monophyletic_for_tribe pteromyini_clade Pteromyini.
Proof.
  unfold clade_monophyletic_for_tribe, pteromyini_clade; simpl.
  intros g H.
  repeat (destruct H as [H|H]; [subst; reflexivity|]).
  destruct H.
Qed.

Theorem sciurini_monophyly : clade_monophyletic_for_tribe sciurini_clade Sciurini.
Proof.
  unfold clade_monophyletic_for_tribe, sciurini_clade; simpl.
  intros g H.
  repeat (destruct H as [H|H]; [subst; reflexivity|]).
  destruct H.
Qed.

Theorem marmotini_monophyly : clade_monophyletic_for_tribe marmotini_clade Marmotini.
Proof.
  unfold clade_monophyletic_for_tribe, marmotini_clade; simpl.
  intros g H.
  repeat (destruct H as [H|H]; [subst; reflexivity|]).
  destruct H.
Qed.

Theorem xerini_monophyly : clade_monophyletic_for_tribe xerini_clade Xerini.
Proof.
  unfold clade_monophyletic_for_tribe, xerini_clade; simpl.
  intros g H.
  repeat (destruct H as [H|H]; [subst; reflexivity|]).
  destruct H.
Qed.

Theorem protoxerini_monophyly : clade_monophyletic_for_tribe protoxerini_clade Protoxerini.
Proof.
  unfold clade_monophyletic_for_tribe, protoxerini_clade; simpl.
  intros g H.
  repeat (destruct H as [H|H]; [subst; reflexivity|]).
  destruct H.
Qed.

Theorem callosciurinae_monophyly : clade_monophyletic_for_subfamily callosciurinae_clade Callosciurinae.
Proof.
  unfold clade_monophyletic_for_subfamily, callosciurinae_clade; simpl.
  intros g H.
  repeat (destruct H as [H|H]; [subst; reflexivity|]).
  destruct H.
Qed.

Definition sciurinae_clade : PhyloNode :=
  Clade "Sciurinae" [sciurini_clade; pteromyini_clade; Leaf Protosciurus].

Theorem sciurinae_monophyly : clade_monophyletic_for_subfamily sciurinae_clade Sciurinae.
Proof.
  unfold clade_monophyletic_for_subfamily, sciurinae_clade; simpl.
  intros g H.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H|H]
  | H : _ = _ |- _ => subst; reflexivity
  | H : False |- _ => destruct H
  end.
Qed.

Definition xerinae_clade : PhyloNode :=
  Clade "Xerinae" [xerini_clade; protoxerini_clade; marmotini_clade].

Theorem xerinae_monophyly : clade_monophyletic_for_subfamily xerinae_clade Xerinae.
Proof.
  unfold clade_monophyletic_for_subfamily, xerinae_clade; simpl.
  intros g H.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H|H]
  | H : _ = _ |- _ => subst; reflexivity
  | H : False |- _ => destruct H
  end.
Qed.

Theorem tree_tribes_consistent : forall g tr,
  tribe_of g = tr -> tr <> NoTribe ->
  exists c, in_tree g c = true /\ clade_monophyletic_for_tribe c tr.
Proof.
  intros g tr Htribe Hnotrivial.
  destruct tr; try contradiction.
  - exists sciurini_clade; split; [|exact sciurini_monophyly].
    destruct g; simpl in Htribe; try discriminate; reflexivity.
  - exists pteromyini_clade; split; [|exact pteromyini_monophyly].
    destruct g; simpl in Htribe; try discriminate; reflexivity.
  - exists xerini_clade; split; [|exact xerini_monophyly].
    destruct g; simpl in Htribe; try discriminate; reflexivity.
  - exists protoxerini_clade; split; [|exact protoxerini_monophyly].
    destruct g; simpl in Htribe; try discriminate; reflexivity.
  - exists marmotini_clade; split; [|exact marmotini_monophyly].
    destruct g; simpl in Htribe; try discriminate; reflexivity.
Qed.

Theorem tree_subfamilies_consistent : forall g sf,
  subfamily_of g = sf ->
  (sf = Sciurinae -> in_tree g sciurinae_clade = true) /\
  (sf = Callosciurinae -> in_tree g callosciurinae_clade = true) /\
  (sf = Xerinae -> in_tree g xerinae_clade = true).
Proof.
  intros g sf Hsf.
  destruct g; simpl in Hsf; subst; repeat split; intro H; try discriminate; reflexivity.
Qed.
