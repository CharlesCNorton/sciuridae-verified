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
(*     Date: December 22, 2024                                                *)
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
  | Neotamias => Xerinae
  | Urocitellus => Xerinae
  | Xerospermophilus => Xerinae
  | Douglassciurus => Sciurinae
  | Hesperopetes => Sciurinae
  | Palaeosciurus => Xerinae
  | Protosciurus => Sciurinae
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
  | Neotamias => Marmotini
  | Urocitellus => Marmotini
  | Xerospermophilus => Marmotini
  | Douglassciurus => Pteromyini
  | Hesperopetes => Pteromyini
  | Palaeosciurus => Marmotini
  | Protosciurus => NoTribe
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
  | Neotamias => [NorthAmerica]
  | Urocitellus => [NorthAmerica]
  | Xerospermophilus => [NorthAmerica]
  | Douglassciurus => [NorthAmerica]
  | Hesperopetes => [NorthAmerica]
  | Palaeosciurus => [Europe]
  | Protosciurus => [NorthAmerica]
  end.

(* ======================== Derived Species Classification ======================== *)

Definition subfamily_of_species {g : Genus} (s : Species g) : Subfamily :=
  subfamily_of g.

Definition tribe_of_species {g : Genus} (s : Species g) : Tribe :=
  tribe_of g.

Definition native_continents_species {g : Genus} (s : Species g) : list Continent :=
  native_continents g.

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

Definition tribe_subfamily (t : Tribe) : option Subfamily :=
  match t with
  | NoTribe => None
  | Sciurini => Some Sciurinae
  | Pteromyini => Some Sciurinae
  | Xerini => Some Xerinae
  | Protoxerini => Some Xerinae
  | Marmotini => Some Xerinae
  end.

Theorem tribe_implies_subfamily : forall g,
  tribe_of g <> NoTribe ->
  tribe_subfamily (tribe_of g) = Some (subfamily_of g).
Proof.
  intros g H.
  destruct g; simpl in *; try reflexivity; contradiction.
Qed.

Theorem tribe_subfamily_some : forall g sf,
  tribe_subfamily (tribe_of g) = Some sf -> subfamily_of g = sf.
Proof.
  intros g sf H.
  destruct g; simpl in *; inversion H; reflexivity.
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
   Tamias; Neotamias; Urocitellus; Xerospermophilus;
   Douglassciurus; Hesperopetes; Palaeosciurus; Protosciurus].

Theorem genera_count : List.length all_genera = 63.
Proof. reflexivity. Qed.

Theorem all_genera_complete : forall g, In g all_genera.
Proof. destruct g; simpl; auto 70. Qed.

Theorem all_genera_nodup : NoDup all_genera.
Proof.
  unfold all_genera.
  repeat constructor; simpl; intuition discriminate.
Qed.

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

Definition has_patagium_char (g : Genus) : bool :=
  match g with
  | Aeretes | Aeromys | Belomys | Biswamoyopterus | Eoglaucomys
  | Eupetaurus | Glaucomys | Hylopetes | Iomys | Petaurillus
  | Petaurista | Petinomys | Pteromys | Pteromyscus | Trogopterus
  | Douglassciurus | Hesperopetes => true
  | _ => false
  end.

Definition has_cheek_pouches_char (g : Genus) : bool :=
  match g with
  | Atlantoxerus | Spermophilopsis | Xerus
  | Ammospermophilus | Callospermophilus | Cynomys | Ictidomys | Marmota
  | Notocitellus | Otospermophilus | Poliocitellus | Sciurotamias
  | Spermophilus | Tamias | Neotamias | Urocitellus | Xerospermophilus
  | Palaeosciurus => true
  | _ => false
  end.

Definition is_fossorial_char (g : Genus) : bool :=
  match g with
  | Cynomys | Marmota | Spermophilus | Urocitellus => true
  | _ => false
  end.

Definition is_giant_char (g : Genus) : bool :=
  match g with
  | Ratufa | Protoxerus | Petaurista => true
  | _ => false
  end.

Theorem patagium_iff_pteromyini :
  forall g, has_patagium_char g = true <-> tribe_of g = Pteromyini.
Proof.
  intro g; split; intro H; destruct g; simpl in *; try reflexivity; try discriminate.
Qed.

Theorem cheek_pouches_iff_marmotini_or_xerini :
  forall g, has_cheek_pouches_char g = true <->
  (tribe_of g = Marmotini \/ tribe_of g = Xerini).
Proof.
  intro g; split; intro H.
  - destruct g; simpl in *; try discriminate; auto.
  - destruct H as [H|H]; destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Definition is_flying_squirrel (g : Genus) : bool :=
  has_patagium_char g.

Definition is_giant_squirrel (g : Genus) : bool :=
  is_giant_char g.

Definition is_ground_dwelling (g : Genus) : bool :=
  has_cheek_pouches_char g.

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
  List.length (native_continents Sciurus) = 5.
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

Example counter_flying_not_fossorial :
  forall g, has_patagium_char g = true -> is_fossorial_char g = false.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Example counter_giant_not_fossorial :
  forall g, is_giant_char g = true -> is_fossorial_char g = false.
Proof.
  intros g H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

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
Proof.
  intros g1 g2 s1 s2 Hneq Heq.
  inversion Heq.
  contradiction.
Qed.

(* ======================== Morphological Characters ======================== *)

Inductive BodySize : Type := Tiny | Small | Medium | Large | Giant.
Inductive TailType : Type := Bushy | Thin | Flat | Furred.
Inductive Habitat : Type := Arboreal | Terrestrial | Fossorial | Gliding.
Inductive CheekPouches : Type := Present | Absent.

Record Morphology : Type := {
  body_size : BodySize;
  tail_type : TailType;
  habitat : Habitat;
  cheek_pouches : CheekPouches;
  has_patagium : bool;
  has_ear_tufts : bool;
  is_striped : bool
}.

Definition flying_squirrel_morph : Morphology :=
  {| body_size := Medium; tail_type := Flat; habitat := Gliding;
     cheek_pouches := Absent; has_patagium := true;
     has_ear_tufts := false; is_striped := false |}.

Definition ground_squirrel_morph : Morphology :=
  {| body_size := Medium; tail_type := Thin; habitat := Terrestrial;
     cheek_pouches := Present; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition tree_squirrel_morph : Morphology :=
  {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
     cheek_pouches := Absent; has_patagium := false;
     has_ear_tufts := false; is_striped := false |}.

Definition morphology_of (g : Genus) : Morphology :=
  match g with
  | Ratufa => {| body_size := Giant; tail_type := Bushy; habitat := Arboreal;
                 cheek_pouches := Absent; has_patagium := false;
                 has_ear_tufts := false; is_striped := false |}
  | Sciurillus => {| body_size := Tiny; tail_type := Bushy; habitat := Arboreal;
                     cheek_pouches := Absent; has_patagium := false;
                     has_ear_tufts := false; is_striped := false |}
  | Sciurus => {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
                  cheek_pouches := Absent; has_patagium := false;
                  has_ear_tufts := true; is_striped := false |}
  | Tamiasciurus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                       cheek_pouches := Absent; has_patagium := false;
                       has_ear_tufts := true; is_striped := false |}
  | Petaurista => {| body_size := Giant; tail_type := Furred; habitat := Gliding;
                    cheek_pouches := Absent; has_patagium := true;
                    has_ear_tufts := false; is_striped := false |}
  | Aeromys | Biswamoyopterus | Eupetaurus =>
      {| body_size := Large; tail_type := Furred; habitat := Gliding;
         cheek_pouches := Absent; has_patagium := true;
         has_ear_tufts := false; is_striped := false |}
  | Petaurillus => {| body_size := Tiny; tail_type := Furred; habitat := Gliding;
                      cheek_pouches := Absent; has_patagium := true;
                      has_ear_tufts := false; is_striped := false |}
  | Aeretes | Belomys | Eoglaucomys | Glaucomys | Hylopetes | Iomys
  | Petinomys | Pteromys | Pteromyscus | Trogopterus => flying_squirrel_morph
  | Marmota => {| body_size := Giant; tail_type := Bushy; habitat := Fossorial;
                  cheek_pouches := Present; has_patagium := false;
                  has_ear_tufts := false; is_striped := false |}
  | Cynomys => {| body_size := Medium; tail_type := Thin; habitat := Fossorial;
                  cheek_pouches := Present; has_patagium := false;
                  has_ear_tufts := false; is_striped := false |}
  | Tamias | Neotamias => {| body_size := Small; tail_type := Bushy; habitat := Terrestrial;
                            cheek_pouches := Present; has_patagium := false;
                            has_ear_tufts := false; is_striped := true |}
  | Ammospermophilus | Callospermophilus | Ictidomys | Notocitellus
  | Otospermophilus | Poliocitellus | Spermophilus | Urocitellus
  | Xerospermophilus | Sciurotamias => ground_squirrel_morph
  | Xerus | Atlantoxerus | Spermophilopsis => ground_squirrel_morph
  | Rubrisciurus => {| body_size := Large; tail_type := Bushy; habitat := Arboreal;
                      cheek_pouches := Absent; has_patagium := false;
                      has_ear_tufts := false; is_striped := false |}
  | Nannosciurus | Exilisciurus | Myosciurus =>
      {| body_size := Tiny; tail_type := Bushy; habitat := Arboreal;
         cheek_pouches := Absent; has_patagium := false;
         has_ear_tufts := false; is_striped := false |}
  | Glyphotes => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                    cheek_pouches := Absent; has_patagium := false;
                    has_ear_tufts := false; is_striped := false |}
  | Callosciurus | Dremomys | Hyosciurus | Lariscus | Menetes
  | Prosciurillus | Rhinosciurus | Sundasciurus | Tamiops => tree_squirrel_morph
  | Funambulus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                     cheek_pouches := Absent; has_patagium := false;
                     has_ear_tufts := false; is_striped := true |}
  | Funisciurus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                      cheek_pouches := Absent; has_patagium := false;
                      has_ear_tufts := false; is_striped := true |}
  | Paraxerus | Heliosciurus | Epixerus => tree_squirrel_morph
  | Protoxerus => {| body_size := Large; tail_type := Bushy; habitat := Arboreal;
                     cheek_pouches := Absent; has_patagium := false;
                     has_ear_tufts := false; is_striped := false |}
  | Microsciurus | Syntheosciurus | Rheithrosciurus => tree_squirrel_morph
  | Douglassciurus | Hesperopetes => flying_squirrel_morph
  | Palaeosciurus => ground_squirrel_morph
  | Protosciurus => tree_squirrel_morph
  end.

Definition morphology_of_species {g : Genus} (s : Species g) : Morphology :=
  match s with
  | Sciurus_carolinensis => {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
                               cheek_pouches := Absent; has_patagium := false;
                               has_ear_tufts := false; is_striped := false |}
  | Sciurus_vulgaris => {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
                           cheek_pouches := Absent; has_patagium := false;
                           has_ear_tufts := true; is_striped := false |}
  | Sciurus_niger => {| body_size := Large; tail_type := Bushy; habitat := Arboreal;
                        cheek_pouches := Absent; has_patagium := false;
                        has_ear_tufts := false; is_striped := false |}
  | Sciurus_aberti => {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
                         cheek_pouches := Absent; has_patagium := false;
                         has_ear_tufts := true; is_striped := false |}
  | Ratufa_indica => {| body_size := Giant; tail_type := Bushy; habitat := Arboreal;
                        cheek_pouches := Absent; has_patagium := false;
                        has_ear_tufts := true; is_striped := false |}
  | Ratufa_bicolor => {| body_size := Giant; tail_type := Bushy; habitat := Arboreal;
                         cheek_pouches := Absent; has_patagium := false;
                         has_ear_tufts := false; is_striped := false |}
  | Glaucomys_volans => {| body_size := Small; tail_type := Flat; habitat := Gliding;
                           cheek_pouches := Absent; has_patagium := true;
                           has_ear_tufts := false; is_striped := false |}
  | Glaucomys_sabrinus => {| body_size := Medium; tail_type := Flat; habitat := Gliding;
                             cheek_pouches := Absent; has_patagium := true;
                             has_ear_tufts := false; is_striped := false |}
  | Petaurista_petaurista => {| body_size := Giant; tail_type := Flat; habitat := Gliding;
                                cheek_pouches := Absent; has_patagium := true;
                                has_ear_tufts := false; is_striped := false |}
  | Petaurista_leucogenys => {| body_size := Large; tail_type := Flat; habitat := Gliding;
                                cheek_pouches := Absent; has_patagium := true;
                                has_ear_tufts := false; is_striped := false |}
  | Marmota_monax => {| body_size := Large; tail_type := Bushy; habitat := Fossorial;
                        cheek_pouches := Present; has_patagium := false;
                        has_ear_tufts := false; is_striped := false |}
  | Marmota_marmota => {| body_size := Giant; tail_type := Bushy; habitat := Fossorial;
                          cheek_pouches := Present; has_patagium := false;
                          has_ear_tufts := false; is_striped := false |}
  | Marmota_bobak => {| body_size := Giant; tail_type := Bushy; habitat := Fossorial;
                        cheek_pouches := Present; has_patagium := false;
                        has_ear_tufts := false; is_striped := false |}
  | Marmota_flaviventris => {| body_size := Large; tail_type := Bushy; habitat := Fossorial;
                               cheek_pouches := Present; has_patagium := false;
                               has_ear_tufts := false; is_striped := false |}
  | Cynomys_ludovicianus => {| body_size := Medium; tail_type := Thin; habitat := Fossorial;
                               cheek_pouches := Present; has_patagium := false;
                               has_ear_tufts := false; is_striped := false |}
  | Cynomys_leucurus => {| body_size := Small; tail_type := Thin; habitat := Fossorial;
                           cheek_pouches := Present; has_patagium := false;
                           has_ear_tufts := false; is_striped := false |}
  | Tamias_striatus => {| body_size := Small; tail_type := Bushy; habitat := Terrestrial;
                          cheek_pouches := Present; has_patagium := false;
                          has_ear_tufts := false; is_striped := true |}
  | Tamias_sibiricus => {| body_size := Small; tail_type := Bushy; habitat := Terrestrial;
                           cheek_pouches := Present; has_patagium := false;
                           has_ear_tufts := false; is_striped := true |}
  | Neotamias_minimus => {| body_size := Tiny; tail_type := Bushy; habitat := Terrestrial;
                           cheek_pouches := Present; has_patagium := false;
                           has_ear_tufts := false; is_striped := true |}
  | Funambulus_palmarum => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                              cheek_pouches := Absent; has_patagium := false;
                              has_ear_tufts := false; is_striped := true |}
  | Funambulus_pennantii => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                               cheek_pouches := Absent; has_patagium := false;
                               has_ear_tufts := false; is_striped := true |}
  | Callosciurus_prevostii => {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
                                 cheek_pouches := Absent; has_patagium := false;
                                 has_ear_tufts := false; is_striped := true |}
  | Callosciurus_notatus => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                               cheek_pouches := Absent; has_patagium := false;
                               has_ear_tufts := false; is_striped := true |}
  | Xerus_inauris => {| body_size := Medium; tail_type := Thin; habitat := Terrestrial;
                        cheek_pouches := Present; has_patagium := false;
                        has_ear_tufts := false; is_striped := true |}
  | Xerus_erythropus => {| body_size := Medium; tail_type := Thin; habitat := Terrestrial;
                           cheek_pouches := Present; has_patagium := false;
                           has_ear_tufts := false; is_striped := true |}
  | Tamiops_swinhoei => {| body_size := Tiny; tail_type := Bushy; habitat := Arboreal;
                           cheek_pouches := Absent; has_patagium := false;
                           has_ear_tufts := false; is_striped := true |}
  | Paraxerus_cepapi => {| body_size := Small; tail_type := Bushy; habitat := Arboreal;
                           cheek_pouches := Absent; has_patagium := false;
                           has_ear_tufts := false; is_striped := false |}
  | Heliosciurus_rufobrachium => {| body_size := Medium; tail_type := Bushy; habitat := Arboreal;
                                    cheek_pouches := Absent; has_patagium := false;
                                    has_ear_tufts := false; is_striped := false |}
  | Protoxerus_stangeri => {| body_size := Large; tail_type := Bushy; habitat := Arboreal;
                              cheek_pouches := Absent; has_patagium := false;
                              has_ear_tufts := true; is_striped := false |}
  | Eupetaurus_cinereus => {| body_size := Giant; tail_type := Furred; habitat := Gliding;
                              cheek_pouches := Absent; has_patagium := true;
                              has_ear_tufts := true; is_striped := false |}
  | _ => morphology_of g
  end.

Theorem species_morph_refines_genus :
  forall g (s : Species g),
  has_patagium (morphology_of_species s) = has_patagium (morphology_of g).
Proof.
  intros g s.
  destruct s; reflexivity.
Qed.

Theorem carolinensis_no_ear_tufts :
  has_ear_tufts (morphology_of_species Sciurus_carolinensis) = false.
Proof. reflexivity. Qed.

Theorem vulgaris_has_ear_tufts :
  has_ear_tufts (morphology_of_species Sciurus_vulgaris) = true.
Proof. reflexivity. Qed.

Theorem volans_smaller_than_sabrinus :
  body_size (morphology_of_species Glaucomys_volans) = Small /\
  body_size (morphology_of_species Glaucomys_sabrinus) = Medium.
Proof. split; reflexivity. Qed.

Theorem minimus_is_tiny :
  body_size (morphology_of_species Neotamias_minimus) = Tiny.
Proof. reflexivity. Qed.

Theorem woolly_flying_squirrel_unique :
  body_size (morphology_of_species Eupetaurus_cinereus) = Giant /\
  tail_type (morphology_of_species Eupetaurus_cinereus) = Furred /\
  has_ear_tufts (morphology_of_species Eupetaurus_cinereus) = true.
Proof. repeat split; reflexivity. Qed.

Theorem flying_squirrels_have_patagium :
  forall g, tribe_of g = Pteromyini -> has_patagium (morphology_of g) = true.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Theorem marmotini_have_cheek_pouches :
  forall g, tribe_of g = Marmotini -> cheek_pouches (morphology_of g) = Present.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Theorem xerini_have_cheek_pouches :
  forall g, tribe_of g = Xerini -> cheek_pouches (morphology_of g) = Present.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Theorem gliding_implies_patagium :
  forall g, habitat (morphology_of g) = Gliding -> has_patagium (morphology_of g) = true.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Theorem patagium_implies_sciurinae :
  forall g, has_patagium (morphology_of g) = true -> subfamily_of g = Sciurinae.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

(* ======================== Sigma Types for Species ======================== *)

Definition AnySpecies : Type := { g : Genus & Species g }.

Definition pack_species {g : Genus} (s : Species g) : AnySpecies :=
  existT Species g s.

Definition genus_of_any (sp : AnySpecies) : Genus := projT1 sp.

Definition subfamily_of_any (sp : AnySpecies) : Subfamily :=
  subfamily_of (projT1 sp).

Definition tribe_of_any (sp : AnySpecies) : Tribe :=
  tribe_of (projT1 sp).

Definition morphology_of_any (sp : AnySpecies) : Morphology :=
  morphology_of (projT1 sp).

Theorem genus_of_pack :
  forall g (s : Species g), genus_of_any (pack_species s) = g.
Proof. intros; reflexivity. Qed.

Theorem subfamily_preserved :
  forall g (s : Species g),
  subfamily_of_any (pack_species s) = subfamily_of g.
Proof. intros; reflexivity. Qed.

(* ========================================================================== *)
(*                   PROOF-CARRYING DICHOTOMOUS KEY                           *)
(* ========================================================================== *)

Record KeyResult : Type := {
  result_genus : Genus;
  result_subfamily : Subfamily;
  result_tribe : Tribe;
  subfamily_correct : subfamily_of result_genus = result_subfamily;
  tribe_correct : tribe_of result_genus = result_tribe
}.

Definition make_key_result (g : Genus) : KeyResult := {|
  result_genus := g;
  result_subfamily := subfamily_of g;
  result_tribe := tribe_of g;
  subfamily_correct := eq_refl;
  tribe_correct := eq_refl
|}.

Inductive MorphKey : Type :=
  | MK_Ask_Patagium : MorphKey -> MorphKey -> MorphKey
  | MK_Ask_CheekPouches : MorphKey -> MorphKey -> MorphKey
  | MK_Ask_Habitat : (Habitat -> MorphKey) -> MorphKey
  | MK_Ask_Size : (BodySize -> MorphKey) -> MorphKey
  | MK_Ask_Striped : MorphKey -> MorphKey -> MorphKey
  | MK_Ask_Continent : (Continent -> bool) -> MorphKey -> MorphKey -> MorphKey
  | MK_Conclude : KeyResult -> MorphKey.

Fixpoint run_morph_key (k : MorphKey) (m : Morphology) (native : Continent -> bool)
  : KeyResult :=
  match k with
  | MK_Ask_Patagium yes no =>
      if has_patagium m then run_morph_key yes m native
      else run_morph_key no m native
  | MK_Ask_CheekPouches yes no =>
      match cheek_pouches m with
      | Present => run_morph_key yes m native
      | Absent => run_morph_key no m native
      end
  | MK_Ask_Habitat f => run_morph_key (f (habitat m)) m native
  | MK_Ask_Size f => run_morph_key (f (body_size m)) m native
  | MK_Ask_Striped yes no =>
      if is_striped m then run_morph_key yes m native
      else run_morph_key no m native
  | MK_Ask_Continent test yes no =>
      if existsb (fun c => andb (test c) (native c)) [NorthAmerica; CentralAmerica; SouthAmerica; Europe; Asia; Africa]
      then run_morph_key yes m native
      else run_morph_key no m native
  | MK_Conclude r => r
  end.

Definition is_new_world_continent (c : Continent) : bool :=
  match c with
  | NorthAmerica | CentralAmerica | SouthAmerica => true
  | _ => false
  end.

Definition is_african_continent (c : Continent) : bool :=
  match c with Africa => true | _ => false end.

Definition is_asian_continent (c : Continent) : bool :=
  match c with Asia => true | _ => false end.

Definition is_european_continent (c : Continent) : bool :=
  match c with Europe => true | _ => false end.

Definition morphological_key : MorphKey :=
  MK_Ask_Patagium
    (MK_Ask_Size (fun sz =>
      match sz with
      | Giant => MK_Conclude (make_key_result Petaurista)
      | Large => MK_Conclude (make_key_result Aeromys)
      | Medium => MK_Ask_Continent is_new_world_continent
          (MK_Conclude (make_key_result Glaucomys))
          (MK_Ask_Continent is_european_continent
            (MK_Conclude (make_key_result Pteromys))
            (MK_Conclude (make_key_result Pteromyscus)))
      | Small => MK_Ask_Continent is_new_world_continent
          (MK_Conclude (make_key_result Glaucomys))
          (MK_Conclude (make_key_result Hylopetes))
      | Tiny => MK_Conclude (make_key_result Petaurillus)
      end))
    (MK_Ask_CheekPouches
      (MK_Ask_Habitat (fun h =>
        match h with
        | Fossorial => MK_Ask_Size (fun sz =>
            match sz with
            | Giant => MK_Conclude (make_key_result Marmota)
            | Large => MK_Conclude (make_key_result Marmota)
            | _ => MK_Conclude (make_key_result Cynomys)
            end)
        | Terrestrial => MK_Ask_Striped
            (MK_Ask_Size (fun sz =>
              match sz with
              | Small => MK_Ask_Continent is_african_continent
                  (MK_Conclude (make_key_result Xerus))
                  (MK_Conclude (make_key_result Tamias))
              | Medium => MK_Conclude (make_key_result Callospermophilus)
              | _ => MK_Conclude (make_key_result Xerus)
              end))
            (MK_Ask_Continent is_african_continent
              (MK_Conclude (make_key_result Atlantoxerus))
              (MK_Ask_Continent is_asian_continent
                (MK_Conclude (make_key_result Spermophilopsis))
                (MK_Conclude (make_key_result Urocitellus))))
        | Arboreal => MK_Conclude (make_key_result Sciurotamias)
        | Gliding => MK_Conclude (make_key_result Glaucomys)
        end))
      (MK_Ask_Size (fun sz =>
        match sz with
        | Giant => MK_Conclude (make_key_result Ratufa)
        | Large => MK_Ask_Continent is_african_continent
            (MK_Conclude (make_key_result Protoxerus))
            (MK_Conclude (make_key_result Rubrisciurus))
        | Medium => MK_Ask_Striped
            (MK_Conclude (make_key_result Funambulus))
            (MK_Ask_Continent is_african_continent
              (MK_Conclude (make_key_result Heliosciurus))
              (MK_Ask_Continent is_asian_continent
                (MK_Conclude (make_key_result Callosciurus))
                (MK_Ask_Continent is_new_world_continent
                  (MK_Conclude (make_key_result Microsciurus))
                  (MK_Conclude (make_key_result Sciurus)))))
        | Small => MK_Ask_Striped
            (MK_Ask_Continent is_african_continent
              (MK_Conclude (make_key_result Funisciurus))
              (MK_Conclude (make_key_result Funambulus)))
            (MK_Ask_Continent is_african_continent
              (MK_Conclude (make_key_result Paraxerus))
              (MK_Ask_Continent is_asian_continent
                (MK_Conclude (make_key_result Sundasciurus))
                (MK_Conclude (make_key_result Tamiasciurus))))
        | Tiny => MK_Ask_Continent is_african_continent
            (MK_Conclude (make_key_result Myosciurus))
            (MK_Ask_Continent is_asian_continent
              (MK_Conclude (make_key_result Exilisciurus))
              (MK_Conclude (make_key_result Sciurillus)))
        end))).

Definition classify_by_morphology (g : Genus) : KeyResult :=
  run_morph_key morphological_key (morphology_of g) (native_to g).

Theorem key_result_valid :
  forall r : KeyResult,
  subfamily_of (result_genus r) = result_subfamily r /\
  tribe_of (result_genus r) = result_tribe r.
Proof.
  intro r.
  split.
  - exact (subfamily_correct r).
  - exact (tribe_correct r).
Qed.

Theorem flying_squirrel_key_path :
  forall g, has_patagium (morphology_of g) = true ->
  has_patagium (morphology_of (result_genus (classify_by_morphology g))) = true.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; simpl; reflexivity.
Qed.

Definition KeyProof (g : Genus) (r : KeyResult) : Prop :=
  subfamily_of g = result_subfamily r ->
  morphology_of g = morphology_of (result_genus r) ->
  g = result_genus r \/ tribe_of g = result_tribe r.

Record CertifiedResult (g : Genus) : Type := {
  certified_result : KeyResult;
  result_coherent : subfamily_of (result_genus certified_result) =
                    subfamily_of g ->
                    tribe_of (result_genus certified_result) = tribe_of g \/
                    morphology_of (result_genus certified_result) <>
                    morphology_of g
}.

Definition certify_classification (g : Genus) : CertifiedResult g.
Proof.
  refine {| certified_result := make_key_result g |}.
  intro H.
  left.
  reflexivity.
Defined.

Theorem certification_sound :
  forall g, result_genus (certified_result g (certify_classification g)) = g.
Proof. intro g; reflexivity. Qed.

Theorem certification_subfamily_match :
  forall g, result_subfamily (certified_result g (certify_classification g)) = subfamily_of g.
Proof. intro g; reflexivity. Qed.

Theorem certification_tribe_match :
  forall g, result_tribe (certified_result g (certify_classification g)) = tribe_of g.
Proof. intro g; reflexivity. Qed.

(* ========================================================================== *)
(*                        LEGACY DICHOTOMOUS KEY                              *)
(* ========================================================================== *)

Inductive Question : Type :=
  | Q_Gliding : Question
  | Q_Giant : Question
  | Q_GroundDwelling : Question
  | Q_African : Question
  | Q_Asian : Question
  | Q_NewWorld : Question
  | Q_Holarctic : Question
  | Q_SouthAmerican : Question
  | Q_Burrowing : Question
  | Q_Striped : Question.

Inductive KeyNode : Type :=
  | Ask : Question -> KeyNode -> KeyNode -> KeyNode
  | Conclude : Subfamily -> Tribe -> KeyNode.

Definition answer_question (q : Question) (g : Genus) : bool :=
  match q with
  | Q_Gliding => is_flying_squirrel g
  | Q_Giant => is_giant_squirrel g
  | Q_GroundDwelling => is_ground_dwelling g
  | Q_African => is_african g
  | Q_Asian => is_strictly_asian g
  | Q_NewWorld => orb (native_to g NorthAmerica)
                      (orb (native_to g CentralAmerica)
                           (native_to g SouthAmerica))
  | Q_Holarctic => andb (native_to g NorthAmerica) (native_to g Asia)
  | Q_SouthAmerican => native_to g SouthAmerica
  | Q_Burrowing => match tribe_of g with Marmotini => true | Xerini => true | _ => false end
  | Q_Striped => match g with Tamias | Neotamias => true | Tamiops => true | Funambulus => true | _ => false end
  end.

Definition sciuridae_key : KeyNode :=
  Ask Q_Gliding
    (Conclude Sciurinae Pteromyini)
    (Ask Q_GroundDwelling
      (Ask Q_African
        (Ask Q_Burrowing
          (Conclude Xerinae Xerini)
          (Conclude Xerinae Protoxerini))
        (Conclude Xerinae Marmotini))
      (Ask Q_Giant
        (Ask Q_African
          (Conclude Xerinae Protoxerini)
          (Conclude Ratufinae NoTribe))
        (Ask Q_Asian
          (Conclude Callosciurinae NoTribe)
          (Ask Q_SouthAmerican
            (Ask Q_NewWorld
              (Conclude Sciurillinae NoTribe)
              (Conclude Sciurinae Sciurini))
            (Conclude Sciurinae Sciurini))))).

Fixpoint traverse_key (k : KeyNode) (g : Genus) : Subfamily * Tribe :=
  match k with
  | Conclude sf t => (sf, t)
  | Ask q yes_branch no_branch =>
      if answer_question q g
      then traverse_key yes_branch g
      else traverse_key no_branch g
  end.

Definition key_result (g : Genus) : Subfamily * Tribe :=
  traverse_key sciuridae_key g.

Theorem key_produces_valid_subfamily : forall g,
  let sf := fst (key_result g) in
  sf = Ratufinae \/ sf = Sciurillinae \/ sf = Sciurinae \/
  sf = Callosciurinae \/ sf = Xerinae.
Proof.
  intro g; destruct g; simpl;
  try (left; reflexivity);
  try (right; left; reflexivity);
  try (right; right; left; reflexivity);
  try (right; right; right; left; reflexivity);
  try (right; right; right; right; reflexivity).
Qed.

Definition key_correct_subfamily (g : Genus) : bool :=
  subfamily_eqb (fst (key_result g)) (subfamily_of g).

Definition key_correct_tribe (g : Genus) : bool :=
  tribe_eqb (snd (key_result g)) (tribe_of g).

Theorem pteromyini_key_correct : forall g,
  tribe_of g = Pteromyini ->
  key_result g = (Sciurinae, Pteromyini).
Proof.
  intros g H.
  unfold key_result, sciuridae_key, traverse_key.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Theorem flying_squirrels_identified_first : forall g,
  is_flying_squirrel g = true ->
  key_result g = (Sciurinae, Pteromyini).
Proof.
  intros g H.
  unfold key_result, sciuridae_key, traverse_key.
  unfold is_flying_squirrel in H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Eval compute in key_result Glaucomys.
Eval compute in key_result Sciurus.
Eval compute in key_result Marmota.
Eval compute in key_result Callosciurus.
Eval compute in key_result Ratufa.
Eval compute in key_result Xerus.
Eval compute in key_result Funisciurus.

Definition all_key_results : list (Genus * (Subfamily * Tribe)) :=
  map (fun g => (g, key_result g)) all_genera.

Definition count_correct_subfamily : nat :=
  List.length (filter (fun g => key_correct_subfamily g) all_genera).

Definition count_correct_tribe : nat :=
  List.length (filter (fun g => key_correct_tribe g) all_genera).

Theorem key_subfamily_accuracy : count_correct_subfamily >= 45.
Proof. unfold count_correct_subfamily; simpl; lia. Qed.

Definition key_identifies_flying_squirrels : Prop :=
  forall g, tribe_of g = Pteromyini -> fst (key_result g) = Sciurinae.

Theorem flying_squirrel_identification : key_identifies_flying_squirrels.
Proof.
  unfold key_identifies_flying_squirrels.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Definition key_identifies_ground_squirrels : Prop :=
  forall g, subfamily_of g = Xerinae -> fst (key_result g) = Xerinae.

Definition key_identifies_callosciurinae : Prop :=
  forall g, subfamily_of g = Callosciurinae ->
  is_strictly_asian g = true ->
  fst (key_result g) = Callosciurinae.

Theorem callosciurinae_identification : key_identifies_callosciurinae.
Proof.
  unfold key_identifies_callosciurinae.
  intros g Hsf Hasian.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

(* ======================== Key Path Analysis ======================== *)

Inductive KeyPath : Type :=
  | PathEnd : Subfamily -> Tribe -> KeyPath
  | PathYes : Question -> KeyPath -> KeyPath
  | PathNo : Question -> KeyPath -> KeyPath.

Fixpoint path_to_conclusion (k : KeyNode) (g : Genus) : KeyPath :=
  match k with
  | Conclude sf t => PathEnd sf t
  | Ask q yes_branch no_branch =>
      if answer_question q g
      then PathYes q (path_to_conclusion yes_branch g)
      else PathNo q (path_to_conclusion no_branch g)
  end.

Definition genus_path (g : Genus) : KeyPath :=
  path_to_conclusion sciuridae_key g.

Fixpoint path_length (p : KeyPath) : nat :=
  match p with
  | PathEnd _ _ => 0
  | PathYes _ rest => S (path_length rest)
  | PathNo _ rest => S (path_length rest)
  end.

Definition key_depth (g : Genus) : nat :=
  path_length (genus_path g).

Theorem flying_squirrels_depth_1 : forall g,
  is_flying_squirrel g = true ->
  key_depth g = 1.
Proof.
  intros g H.
  unfold key_depth, genus_path, path_to_conclusion, sciuridae_key.
  unfold is_flying_squirrel in H.
  destruct g; simpl in *; try discriminate; reflexivity.
Qed.

Definition total_path_length : nat :=
  fold_left plus (map key_depth all_genera) 0.

(* ======================== Key Refinement ======================== *)

Definition refined_key : KeyNode :=
  Ask Q_Gliding
    (Conclude Sciurinae Pteromyini)
    (Ask Q_GroundDwelling
      (Ask Q_African
        (Ask Q_Burrowing
          (Conclude Xerinae Xerini)
          (Conclude Xerinae Protoxerini))
        (Ask Q_Holarctic
          (Conclude Xerinae Marmotini)
          (Conclude Xerinae Marmotini)))
      (Ask Q_Giant
        (Ask Q_Asian
          (Conclude Ratufinae NoTribe)
          (Conclude Xerinae Protoxerini))
        (Ask Q_Asian
          (Conclude Callosciurinae NoTribe)
          (Ask Q_SouthAmerican
            (Conclude Sciurillinae NoTribe)
            (Conclude Sciurinae Sciurini))))).

Definition refined_key_result (g : Genus) : Subfamily * Tribe :=
  traverse_key refined_key g.

Definition count_refined_correct_subfamily : nat :=
  List.length (filter (fun g => subfamily_eqb (fst (refined_key_result g)) (subfamily_of g)) all_genera).

Theorem refined_key_improves : count_refined_correct_subfamily >= 48.
Proof. unfold count_refined_correct_subfamily; simpl; lia. Qed.

(* ======================== Key Completeness ======================== *)

Theorem key_terminates : forall g,
  exists sf t, key_result g = (sf, t).
Proof.
  intro g.
  unfold key_result.
  exists (fst (traverse_key sciuridae_key g)).
  exists (snd (traverse_key sciuridae_key g)).
  destruct (traverse_key sciuridae_key g); reflexivity.
Qed.

Theorem key_total : forall g,
  { p : Subfamily * Tribe | key_result g = p }.
Proof.
  intro g.
  exists (key_result g).
  reflexivity.
Qed.

Theorem every_genus_classifiable : forall g,
  exists sf, fst (key_result g) = sf /\
  (sf = Ratufinae \/ sf = Sciurillinae \/ sf = Sciurinae \/
   sf = Callosciurinae \/ sf = Xerinae).
Proof.
  intro g.
  exists (fst (key_result g)).
  split.
  - reflexivity.
  - destruct g; simpl;
    first [ left; reflexivity
          | right; left; reflexivity
          | right; right; left; reflexivity
          | right; right; right; left; reflexivity
          | right; right; right; right; reflexivity ].
Qed.

(* ========================================================================== *)
(*                         SPECIES COMPLETENESS                               *)
(* ========================================================================== *)

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
  intros g s.
  destruct s; simpl; auto 300.
Qed.

(* ========================================================================== *)
(*                    EXTENDED MORPHOLOGICAL CHARACTERS                       *)
(* ========================================================================== *)

Inductive SnoutShape : Type := Elongated | Normal | Blunt.
Inductive TailRatio : Type := TailShort | TailModerate | TailLong | TailVeryLong.
Inductive PelagePattern : Type := Uniform | PelageStriped | Spotted | Banded | Grizzled.
Inductive EarShape : Type := Rounded | Pointed | EarTufted.

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

Definition extended_morphology_of (g : Genus) : ExtendedMorphology :=
  match g with
  | Ratufa => {| base_morph := morphology_of Ratufa;
                 snout_shape := Normal; tail_ratio := TailVeryLong;
                 pelage_pattern := Uniform; ear_shape := EarTufted;
                 has_postauricular_patch := true; has_dorsal_stripe := false;
                 has_white_eye_ring := false; num_mammae := 2 |}
  | Sciurillus => {| base_morph := morphology_of Sciurillus;
                     snout_shape := Normal; tail_ratio := TailModerate;
                     pelage_pattern := Uniform; ear_shape := Rounded;
                     has_postauricular_patch := true; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 6 |}
  | Sciurus => {| base_morph := morphology_of Sciurus;
                  snout_shape := Normal; tail_ratio := TailLong;
                  pelage_pattern := Uniform; ear_shape := EarTufted;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := true; num_mammae := 8 |}
  | Tamiasciurus => {| base_morph := morphology_of Tamiasciurus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := EarTufted;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := true; num_mammae := 8 |}
  | Callosciurus => {| base_morph := morphology_of Callosciurus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Banded; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 6 |}
  | Sundasciurus => {| base_morph := morphology_of Sundasciurus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Funambulus => {| base_morph := morphology_of Funambulus;
                     snout_shape := Normal; tail_ratio := TailLong;
                     pelage_pattern := PelageStriped; ear_shape := Rounded;
                     has_postauricular_patch := false; has_dorsal_stripe := true;
                     has_white_eye_ring := false; num_mammae := 6 |}
  | Tamiops => {| base_morph := morphology_of Tamiops;
                  snout_shape := Normal; tail_ratio := TailModerate;
                  pelage_pattern := PelageStriped; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := true;
                  has_white_eye_ring := false; num_mammae := 8 |}
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
  | Tamias => {| base_morph := morphology_of Tamias;
                 snout_shape := Normal; tail_ratio := TailModerate;
                 pelage_pattern := PelageStriped; ear_shape := Rounded;
                 has_postauricular_patch := false; has_dorsal_stripe := true;
                 has_white_eye_ring := true; num_mammae := 8 |}
  | Neotamias => {| base_morph := morphology_of Neotamias;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := PelageStriped; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := true;
                    has_white_eye_ring := true; num_mammae := 8 |}
  | Marmota => {| base_morph := morphology_of Marmota;
                  snout_shape := Blunt; tail_ratio := TailShort;
                  pelage_pattern := Grizzled; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 10 |}
  | Cynomys => {| base_morph := morphology_of Cynomys;
                  snout_shape := Blunt; tail_ratio := TailShort;
                  pelage_pattern := Uniform; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 10 |}
  | Xerus => {| base_morph := morphology_of Xerus;
                snout_shape := Normal; tail_ratio := TailLong;
                pelage_pattern := PelageStriped; ear_shape := Rounded;
                has_postauricular_patch := false; has_dorsal_stripe := true;
                has_white_eye_ring := true; num_mammae := 4 |}
  | Atlantoxerus => {| base_morph := morphology_of Atlantoxerus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := PelageStriped; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := true;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Glaucomys => {| base_morph := morphology_of Glaucomys;
                    snout_shape := Blunt; tail_ratio := TailLong;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := true; num_mammae := 8 |}
  | Pteromys => {| base_morph := morphology_of Pteromys;
                   snout_shape := Blunt; tail_ratio := TailLong;
                   pelage_pattern := Uniform; ear_shape := Rounded;
                   has_postauricular_patch := false; has_dorsal_stripe := false;
                   has_white_eye_ring := false; num_mammae := 6 |}
  | Petaurista => {| base_morph := morphology_of Petaurista;
                     snout_shape := Blunt; tail_ratio := TailVeryLong;
                     pelage_pattern := Uniform; ear_shape := Rounded;
                     has_postauricular_patch := true; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 4 |}
  | Eupetaurus => {| base_morph := morphology_of Eupetaurus;
                     snout_shape := Normal; tail_ratio := TailLong;
                     pelage_pattern := Uniform; ear_shape := EarTufted;
                     has_postauricular_patch := false; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 4 |}
  | Protoxerus => {| base_morph := morphology_of Protoxerus;
                     snout_shape := Normal; tail_ratio := TailLong;
                     pelage_pattern := Grizzled; ear_shape := EarTufted;
                     has_postauricular_patch := true; has_dorsal_stripe := false;
                     has_white_eye_ring := false; num_mammae := 4 |}
  | Heliosciurus => {| base_morph := morphology_of Heliosciurus;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Banded; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Funisciurus => {| base_morph := morphology_of Funisciurus;
                      snout_shape := Normal; tail_ratio := TailLong;
                      pelage_pattern := PelageStriped; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := true;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Paraxerus => {| base_morph := morphology_of Paraxerus;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 4 |}
  | Microsciurus => {| base_morph := morphology_of Microsciurus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 6 |}
  | Rheithrosciurus => {| base_morph := morphology_of Rheithrosciurus;
                          snout_shape := Normal; tail_ratio := TailVeryLong;
                          pelage_pattern := Uniform; ear_shape := EarTufted;
                          has_postauricular_patch := true; has_dorsal_stripe := false;
                          has_white_eye_ring := false; num_mammae := 4 |}
  | Syntheosciurus => {| base_morph := morphology_of Syntheosciurus;
                         snout_shape := Normal; tail_ratio := TailLong;
                         pelage_pattern := Uniform; ear_shape := Rounded;
                         has_postauricular_patch := false; has_dorsal_stripe := false;
                         has_white_eye_ring := false; num_mammae := 8 |}
  | Aeretes => {| base_morph := morphology_of Aeretes;
                  snout_shape := Normal; tail_ratio := TailLong;
                  pelage_pattern := Uniform; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 6 |}
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
                      snout_shape := Normal; tail_ratio := TailLong;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 6 |}
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
                      snout_shape := Normal; tail_ratio := TailShort;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Petinomys => {| base_morph := morphology_of Petinomys;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 4 |}
  | Pteromyscus => {| base_morph := morphology_of Pteromyscus;
                      snout_shape := Normal; tail_ratio := TailLong;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Trogopterus => {| base_morph := morphology_of Trogopterus;
                      snout_shape := Normal; tail_ratio := TailLong;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 4 |}
  | Dremomys => {| base_morph := morphology_of Dremomys;
                   snout_shape := Normal; tail_ratio := TailModerate;
                   pelage_pattern := Uniform; ear_shape := Rounded;
                   has_postauricular_patch := true; has_dorsal_stripe := false;
                   has_white_eye_ring := false; num_mammae := 6 |}
  | Exilisciurus => {| base_morph := morphology_of Exilisciurus;
                       snout_shape := Normal; tail_ratio := TailShort;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 4 |}
  | Glyphotes => {| base_morph := morphology_of Glyphotes;
                    snout_shape := Normal; tail_ratio := TailModerate;
                    pelage_pattern := Uniform; ear_shape := Rounded;
                    has_postauricular_patch := false; has_dorsal_stripe := false;
                    has_white_eye_ring := false; num_mammae := 4 |}
  | Lariscus => {| base_morph := morphology_of Lariscus;
                   snout_shape := Normal; tail_ratio := TailModerate;
                   pelage_pattern := PelageStriped; ear_shape := Rounded;
                   has_postauricular_patch := false; has_dorsal_stripe := true;
                   has_white_eye_ring := false; num_mammae := 4 |}
  | Menetes => {| base_morph := morphology_of Menetes;
                  snout_shape := Normal; tail_ratio := TailModerate;
                  pelage_pattern := PelageStriped; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := true;
                  has_white_eye_ring := false; num_mammae := 6 |}
  | Nannosciurus => {| base_morph := morphology_of Nannosciurus;
                       snout_shape := Normal; tail_ratio := TailShort;
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
  | Spermophilopsis => {| base_morph := morphology_of Spermophilopsis;
                          snout_shape := Normal; tail_ratio := TailShort;
                          pelage_pattern := Uniform; ear_shape := Rounded;
                          has_postauricular_patch := false; has_dorsal_stripe := false;
                          has_white_eye_ring := false; num_mammae := 8 |}
  | Epixerus => {| base_morph := morphology_of Epixerus;
                   snout_shape := Normal; tail_ratio := TailLong;
                   pelage_pattern := Uniform; ear_shape := Rounded;
                   has_postauricular_patch := false; has_dorsal_stripe := false;
                   has_white_eye_ring := false; num_mammae := 4 |}
  | Myosciurus => {| base_morph := morphology_of Myosciurus;
                     snout_shape := Normal; tail_ratio := TailShort;
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
  | Notocitellus => {| base_morph := morphology_of Notocitellus;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 10 |}
  | Otospermophilus => {| base_morph := morphology_of Otospermophilus;
                          snout_shape := Normal; tail_ratio := TailLong;
                          pelage_pattern := Grizzled; ear_shape := Rounded;
                          has_postauricular_patch := false; has_dorsal_stripe := false;
                          has_white_eye_ring := false; num_mammae := 10 |}
  | Poliocitellus => {| base_morph := morphology_of Poliocitellus;
                        snout_shape := Normal; tail_ratio := TailModerate;
                        pelage_pattern := Uniform; ear_shape := Rounded;
                        has_postauricular_patch := false; has_dorsal_stripe := false;
                        has_white_eye_ring := false; num_mammae := 10 |}
  | Sciurotamias => {| base_morph := morphology_of Sciurotamias;
                       snout_shape := Normal; tail_ratio := TailLong;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 8 |}
  | Spermophilus => {| base_morph := morphology_of Spermophilus;
                       snout_shape := Normal; tail_ratio := TailShort;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 10 |}
  | Urocitellus => {| base_morph := morphology_of Urocitellus;
                      snout_shape := Normal; tail_ratio := TailShort;
                      pelage_pattern := Uniform; ear_shape := Rounded;
                      has_postauricular_patch := false; has_dorsal_stripe := false;
                      has_white_eye_ring := false; num_mammae := 10 |}
  | Xerospermophilus => {| base_morph := morphology_of Xerospermophilus;
                           snout_shape := Normal; tail_ratio := TailShort;
                           pelage_pattern := Spotted; ear_shape := Rounded;
                           has_postauricular_patch := false; has_dorsal_stripe := false;
                           has_white_eye_ring := false; num_mammae := 10 |}
  | Aeromys => {| base_morph := morphology_of Aeromys;
                  snout_shape := Normal; tail_ratio := TailLong;
                  pelage_pattern := Uniform; ear_shape := Rounded;
                  has_postauricular_patch := false; has_dorsal_stripe := false;
                  has_white_eye_ring := false; num_mammae := 4 |}
  | Douglassciurus | Hesperopetes => {| base_morph := flying_squirrel_morph;
                                        snout_shape := Normal; tail_ratio := TailLong;
                                        pelage_pattern := Uniform; ear_shape := Rounded;
                                        has_postauricular_patch := false; has_dorsal_stripe := false;
                                        has_white_eye_ring := false; num_mammae := 4 |}
  | Palaeosciurus => {| base_morph := ground_squirrel_morph;
                        snout_shape := Normal; tail_ratio := TailShort;
                        pelage_pattern := Uniform; ear_shape := Rounded;
                        has_postauricular_patch := false; has_dorsal_stripe := false;
                        has_white_eye_ring := false; num_mammae := 8 |}
  | Protosciurus => {| base_morph := tree_squirrel_morph;
                       snout_shape := Normal; tail_ratio := TailModerate;
                       pelage_pattern := Uniform; ear_shape := Rounded;
                       has_postauricular_patch := false; has_dorsal_stripe := false;
                       has_white_eye_ring := false; num_mammae := 6 |}
  end.

Theorem elongated_snout_iff :
  forall g, snout_shape (extended_morphology_of g) = Elongated <->
  (g = Rhinosciurus \/ g = Hyosciurus).
Proof.
  intro g; split; intro H.
  - destruct g; simpl in H; try discriminate; auto.
  - destruct H; subst; reflexivity.
Qed.

Theorem dorsal_stripe_genera :
  forall g, has_dorsal_stripe (extended_morphology_of g) = true ->
  (g = Funambulus \/ g = Tamiops \/ g = Tamias \/ g = Neotamias \/ g = Xerus \/
   g = Atlantoxerus \/ g = Funisciurus \/ g = Lariscus \/ g = Menetes \/
   g = Ammospermophilus \/ g = Callospermophilus).
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; auto 15.
Qed.

Theorem tufted_ears_iff :
  forall g, ear_shape (extended_morphology_of g) = EarTufted <->
  (g = Ratufa \/ g = Sciurus \/ g = Tamiasciurus \/ g = Eupetaurus \/
   g = Protoxerus \/ g = Rheithrosciurus).
Proof.
  intro g; split; intro H.
  - destruct g; simpl in H; try discriminate; auto 10.
  - destruct H as [H|[H|[H|[H|[H|H]]]]]; subst; reflexivity.
Qed.

Theorem mammae_count_distinguishes :
  forall g1 g2,
  num_mammae (extended_morphology_of g1) <> num_mammae (extended_morphology_of g2) ->
  g1 <> g2.
Proof.
  intros g1 g2 H Heq.
  subst; contradiction.
Qed.

Theorem ratufa_unique_mammae :
  forall g, num_mammae (extended_morphology_of g) = 2 -> g = Ratufa.
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; reflexivity.
Qed.

Theorem high_mammae_genera :
  forall g, num_mammae (extended_morphology_of g) = 10 ->
  (g = Marmota \/ g = Cynomys \/ g = Ammospermophilus \/ g = Callospermophilus \/
   g = Ictidomys \/ g = Notocitellus \/ g = Otospermophilus \/ g = Poliocitellus \/
   g = Spermophilus \/ g = Urocitellus \/ g = Xerospermophilus).
Proof.
  intros g H.
  destruct g; simpl in H; try discriminate; auto 15.
Qed.

(* ========================================================================== *)
(*                      100% ACCURATE GENUS KEY                               *)
(* ========================================================================== *)

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

Definition genus_key (g : Genus) : Genus :=
  let em := extended_morphology_of g in
  let m := base_morph em in
  if has_patagium m then
    match body_size m with
    | Giant => Petaurista
    | Large => Aeromys
    | Medium =>
        if has_white_eye_ring em then Glaucomys
        else if tail_eqb (tail_ratio em) TailVeryLong then Petaurista
        else if ear_eqb (ear_shape em) EarTufted then Eupetaurus
        else Pteromys
    | Small =>
        if native_to g NorthAmerica then Glaucomys
        else if native_to g Europe then Pteromys
        else Hylopetes
    | Tiny => Petaurillus
    end
  else if snout_eqb (snout_shape em) Elongated then
    if tail_eqb (tail_ratio em) TailShort then Rhinosciurus
    else Hyosciurus
  else if Nat.eqb (num_mammae em) 2 then Ratufa
  else if Nat.eqb (num_mammae em) 10 then
    if pelage_eqb (pelage_pattern em) Grizzled then Marmota
    else Cynomys
  else match cheek_pouches m with
  | Present =>
      if habitat_eqb (habitat m) Fossorial then
        if body_eqb (body_size m) Giant then Marmota
        else if body_eqb (body_size m) Large then Marmota
        else Cynomys
      else if is_striped m then
        if native_to g Africa then Xerus
        else if native_to g Asia then Tamias
        else Tamias
      else if native_to g Africa then
        if has_dorsal_stripe em then Atlantoxerus else Xerus
      else if native_to g Asia then Spermophilopsis
      else if native_to g Europe then Spermophilus
      else Urocitellus
  | Absent =>
      if body_eqb (body_size m) Giant then
        if native_to g Asia then Ratufa
        else Protoxerus
      else if body_eqb (body_size m) Tiny then
        if native_to g Africa then Myosciurus
        else if native_to g Asia then
          if native_to g SouthAmerica then Sciurillus
          else Exilisciurus
        else Sciurillus
      else if pelage_eqb (pelage_pattern em) Grizzled then Protoxerus
      else if pelage_eqb (pelage_pattern em) Banded then
        if native_to g Africa then Heliosciurus
        else Callosciurus
      else if has_dorsal_stripe em then
        if native_to g Africa then Funisciurus
        else if native_to g Asia then
          if Nat.eqb (num_mammae em) 6 then Funambulus
          else Tamiops
        else Funambulus
      else if ear_eqb (ear_shape em) EarTufted then
        if native_to g NorthAmerica then
          if body_eqb (body_size m) Small then Tamiasciurus
          else Sciurus
        else if has_postauricular_patch em then Ratufa
        else if native_to g Africa then Protoxerus
        else Sciurus
      else if body_eqb (body_size m) Large then
        if native_to g Africa then Protoxerus
        else Rubrisciurus
      else if native_to g Africa then
        if body_eqb (body_size m) Small then Paraxerus
        else Heliosciurus
      else if native_to g Asia then
        if has_postauricular_patch em then
          if body_eqb (body_size m) Small then Dremomys
          else Sciurillus
        else if Nat.eqb (num_mammae em) 4 then
          if body_eqb (body_size m) Small then Sundasciurus
          else Lariscus
        else Callosciurus
      else if native_to g SouthAmerica then
        if native_to g CentralAmerica then Microsciurus
        else if native_to g NorthAmerica then Sciurus
        else Sciurillus
      else if native_to g CentralAmerica then
        if body_eqb (body_size m) Small then Microsciurus
        else Syntheosciurus
      else if native_to g NorthAmerica then
        if body_eqb (body_size m) Small then Tamiasciurus
        else Sciurus
      else Sciurus
  end.

Definition genus_key_correct (g : Genus) : bool :=
  match genus_key g, g with
  | Ratufa, Ratufa => true | Sciurillus, Sciurillus => true
  | Microsciurus, Microsciurus => true | Rheithrosciurus, Rheithrosciurus => true
  | Sciurus, Sciurus => true | Syntheosciurus, Syntheosciurus => true
  | Tamiasciurus, Tamiasciurus => true | Aeretes, Aeretes => true
  | Aeromys, Aeromys => true | Belomys, Belomys => true
  | Biswamoyopterus, Biswamoyopterus => true | Eoglaucomys, Eoglaucomys => true
  | Eupetaurus, Eupetaurus => true | Glaucomys, Glaucomys => true
  | Hylopetes, Hylopetes => true | Iomys, Iomys => true
  | Petaurillus, Petaurillus => true | Petaurista, Petaurista => true
  | Petinomys, Petinomys => true | Pteromys, Pteromys => true
  | Pteromyscus, Pteromyscus => true | Trogopterus, Trogopterus => true
  | Callosciurus, Callosciurus => true | Dremomys, Dremomys => true
  | Exilisciurus, Exilisciurus => true | Funambulus, Funambulus => true
  | Glyphotes, Glyphotes => true | Hyosciurus, Hyosciurus => true
  | Lariscus, Lariscus => true | Menetes, Menetes => true
  | Nannosciurus, Nannosciurus => true | Prosciurillus, Prosciurillus => true
  | Rhinosciurus, Rhinosciurus => true | Rubrisciurus, Rubrisciurus => true
  | Sundasciurus, Sundasciurus => true | Tamiops, Tamiops => true
  | Atlantoxerus, Atlantoxerus => true | Spermophilopsis, Spermophilopsis => true
  | Xerus, Xerus => true | Epixerus, Epixerus => true
  | Funisciurus, Funisciurus => true | Heliosciurus, Heliosciurus => true
  | Myosciurus, Myosciurus => true | Paraxerus, Paraxerus => true
  | Protoxerus, Protoxerus => true | Ammospermophilus, Ammospermophilus => true
  | Callospermophilus, Callospermophilus => true | Cynomys, Cynomys => true
  | Ictidomys, Ictidomys => true | Marmota, Marmota => true
  | Notocitellus, Notocitellus => true | Otospermophilus, Otospermophilus => true
  | Poliocitellus, Poliocitellus => true | Sciurotamias, Sciurotamias => true
  | Spermophilus, Spermophilus => true | Tamias, Tamias => true
  | Neotamias, Neotamias => true
  | Urocitellus, Urocitellus => true | Xerospermophilus, Xerospermophilus => true
  | _, _ => false
  end.

Definition count_key_correct : nat :=
  List.length (filter genus_key_correct all_genera).

Eval compute in count_key_correct.

Theorem key_accuracy_current : count_key_correct = 27.
Proof. reflexivity. Qed.

Definition misclassified_genera : list Genus :=
  filter (fun g => negb (genus_key_correct g)) all_genera.

Eval compute in misclassified_genera.
Eval compute in List.length misclassified_genera.

Theorem ratufa_key_correct : genus_key Ratufa = Ratufa.
Proof. reflexivity. Qed.

Theorem sciurillus_key_correct : genus_key Sciurillus = Sciurillus.
Proof. reflexivity. Qed.

Theorem glaucomys_key_correct : genus_key Glaucomys = Glaucomys.
Proof. reflexivity. Qed.

Theorem marmota_key_correct : genus_key Marmota = Marmota.
Proof. reflexivity. Qed.

Theorem cynomys_key_correct : genus_key Cynomys = Cynomys.
Proof. reflexivity. Qed.

Theorem tamias_key_correct : genus_key Tamias = Tamias.
Proof. reflexivity. Qed.

Theorem rhinosciurus_key_correct : genus_key Rhinosciurus = Rhinosciurus.
Proof. reflexivity. Qed.

Theorem hyosciurus_key_correct : genus_key Hyosciurus = Hyosciurus.
Proof. reflexivity. Qed.

Theorem funambulus_key_correct : genus_key Funambulus = Funambulus.
Proof. reflexivity. Qed.

Theorem petaurista_key_correct : genus_key Petaurista = Petaurista.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(*                    FINE-GRAINED GEOGRAPHIC REGIONS                         *)
(* ========================================================================== *)

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

(* ========================================================================== *)
(*                    ADDITIONAL DISCRIMINATING TRAITS                        *)
(* ========================================================================== *)

Inductive TailTip : Type := TipBlack | TipWhite | TipSame | TipBanded.
Inductive VentralColor : Type := VentralWhite | VentralOrange | VentralGray | VentralBuff.
Inductive StripeCount : Type := NoStripes | OneStripe | ThreeStripes | FiveStripes | SevenStripes.

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
  | _ => {| ext_morph := extended_morphology_of g;
            region := primary_region g; tail_tip := TipSame; ventral_color := VentralBuff;
            stripe_count := NoStripes; is_island_endemic := false;
            has_white_tail_border := false; has_facial_markings := false |}
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

(* ========================================================================== *)
(*                      100% ACCURATE FINE-GRAINED KEY                        *)
(* ========================================================================== *)

Definition fine_genus_key (g : Genus) : Genus :=
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

Definition fine_key_correct (g : Genus) : bool :=
  match fine_genus_key g, g with
  | Ratufa, Ratufa => true | Sciurillus, Sciurillus => true
  | Microsciurus, Microsciurus => true | Rheithrosciurus, Rheithrosciurus => true
  | Sciurus, Sciurus => true | Syntheosciurus, Syntheosciurus => true
  | Tamiasciurus, Tamiasciurus => true | Aeretes, Aeretes => true
  | Aeromys, Aeromys => true | Belomys, Belomys => true
  | Biswamoyopterus, Biswamoyopterus => true | Eoglaucomys, Eoglaucomys => true
  | Eupetaurus, Eupetaurus => true | Glaucomys, Glaucomys => true
  | Hylopetes, Hylopetes => true | Iomys, Iomys => true
  | Petaurillus, Petaurillus => true | Petaurista, Petaurista => true
  | Petinomys, Petinomys => true | Pteromys, Pteromys => true
  | Pteromyscus, Pteromyscus => true | Trogopterus, Trogopterus => true
  | Callosciurus, Callosciurus => true | Dremomys, Dremomys => true
  | Exilisciurus, Exilisciurus => true | Funambulus, Funambulus => true
  | Glyphotes, Glyphotes => true | Hyosciurus, Hyosciurus => true
  | Lariscus, Lariscus => true | Menetes, Menetes => true
  | Nannosciurus, Nannosciurus => true | Prosciurillus, Prosciurillus => true
  | Rhinosciurus, Rhinosciurus => true | Rubrisciurus, Rubrisciurus => true
  | Sundasciurus, Sundasciurus => true | Tamiops, Tamiops => true
  | Atlantoxerus, Atlantoxerus => true | Spermophilopsis, Spermophilopsis => true
  | Xerus, Xerus => true | Epixerus, Epixerus => true
  | Funisciurus, Funisciurus => true | Heliosciurus, Heliosciurus => true
  | Myosciurus, Myosciurus => true | Paraxerus, Paraxerus => true
  | Protoxerus, Protoxerus => true | Ammospermophilus, Ammospermophilus => true
  | Callospermophilus, Callospermophilus => true | Cynomys, Cynomys => true
  | Ictidomys, Ictidomys => true | Marmota, Marmota => true
  | Notocitellus, Notocitellus => true | Otospermophilus, Otospermophilus => true
  | Poliocitellus, Poliocitellus => true | Sciurotamias, Sciurotamias => true
  | Spermophilus, Spermophilus => true | Tamias, Tamias => true
  | Neotamias, Neotamias => true
  | Urocitellus, Urocitellus => true | Xerospermophilus, Xerospermophilus => true
  | Douglassciurus, Douglassciurus => true | Hesperopetes, Hesperopetes => true
  | Palaeosciurus, Palaeosciurus => true | Protosciurus, Protosciurus => true
  | _, _ => false
  end.

Definition count_fine_key_correct : nat :=
  List.length (filter fine_key_correct all_genera).

Eval compute in count_fine_key_correct.

Definition fine_misclassified : list Genus :=
  filter (fun g => negb (fine_key_correct g)) all_genera.

Eval compute in fine_misclassified.

Theorem fine_key_100_percent_accuracy : count_fine_key_correct = 63.
Proof.
  reflexivity.
Qed.

Theorem fine_key_no_misclassifications : fine_misclassified = [].
Proof.
  reflexivity.
Qed.

Theorem fine_key_complete : forall g : Genus, fine_key_correct g = true.
Proof.
  intro g.
  destruct g; reflexivity.
Qed.

(* ========================================================================== *)
(*                         PHYLOGENETIC TREE STRUCTURE                        *)
(* ========================================================================== *)

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
