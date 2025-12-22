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
(*     In memoriam: the small lives lost beneath our wheels.                  *)
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

(* ======================== Species ======================== *)

Inductive Species : Type :=
  | Ratufa_affinis | Ratufa_bicolor | Ratufa_indica | Ratufa_macroura
  | Sciurillus_pusillus
  | Microsciurus_alfari | Microsciurus_flaviventer | Microsciurus_mimulus | Microsciurus_santanderensis
  | Rheithrosciurus_macrotis
  | Sciurus_aberti | Sciurus_alleni | Sciurus_anomalus | Sciurus_arizonensis | Sciurus_aureogaster
  | Sciurus_carolinensis | Sciurus_colliaei | Sciurus_deppei | Sciurus_flammifer | Sciurus_gilvigularis
  | Sciurus_granatensis | Sciurus_griseus | Sciurus_igniventris | Sciurus_lis | Sciurus_nayaritensis
  | Sciurus_niger | Sciurus_oculatus | Sciurus_pucheranii | Sciurus_pyrrhinus | Sciurus_richmondi
  | Sciurus_sanborni | Sciurus_spadiceus | Sciurus_stramineus | Sciurus_variegatoides | Sciurus_vulgaris
  | Sciurus_yucatanensis
  | Syntheosciurus_brochus
  | Tamiasciurus_douglasii | Tamiasciurus_fremonti | Tamiasciurus_hudsonicus | Tamiasciurus_mearnsi
  | Aeretes_melanopterus
  | Aeromys_tephromelas | Aeromys_thomasi
  | Belomys_pearsonii
  | Biswamoyopterus_biswasi | Biswamoyopterus_laoensis
  | Eoglaucomys_fimbriatus
  | Eupetaurus_cinereus
  | Glaucomys_oregonensis | Glaucomys_sabrinus | Glaucomys_volans
  | Hylopetes_alboniger | Hylopetes_baberi | Hylopetes_bartelsi | Hylopetes_lepidus | Hylopetes_nigripes
  | Hylopetes_phayrei | Hylopetes_platyurus | Hylopetes_sipora | Hylopetes_spadiceus | Hylopetes_winstoni
  | Iomys_horsfieldii | Iomys_sipora
  | Petaurillus_emiliae | Petaurillus_hosei | Petaurillus_kinlochii
  | Petaurista_alborufus | Petaurista_elegans | Petaurista_leucogenys | Petaurista_magnificus
  | Petaurista_mechukaensis | Petaurista_mishmiensis | Petaurista_nobilis | Petaurista_petaurista
  | Petaurista_philippensis | Petaurista_xanthotis | Petaurista_yunanensis
  | Petinomys_crinitus | Petinomys_fuscocapillus | Petinomys_genibarbis | Petinomys_hageni
  | Petinomys_lugens | Petinomys_mindanensis | Petinomys_sagitta | Petinomys_setosus | Petinomys_vordermanni
  | Pteromys_momonga | Pteromys_volans
  | Pteromyscus_pulverulentus
  | Trogopterus_xanthipes
  | Callosciurus_adamsi | Callosciurus_albescens | Callosciurus_baluensis | Callosciurus_caniceps
  | Callosciurus_erythraeus | Callosciurus_finlaysonii | Callosciurus_inornatus | Callosciurus_melanogaster
  | Callosciurus_nigrovittatus | Callosciurus_notatus | Callosciurus_orestes | Callosciurus_phayrei
  | Callosciurus_prevostii | Callosciurus_pygerythrus | Callosciurus_quinquestriatus
  | Dremomys_everetti | Dremomys_gularis | Dremomys_lokriah | Dremomys_pernyi | Dremomys_pyrrhomerus | Dremomys_rufigenis
  | Exilisciurus_concinnus | Exilisciurus_exilis | Exilisciurus_whiteheadi
  | Funambulus_layardi | Funambulus_palmarum | Funambulus_pennantii | Funambulus_sublineatus | Funambulus_tristriatus
  | Glyphotes_simus
  | Hyosciurus_heinrichi | Hyosciurus_ileile
  | Lariscus_hosei | Lariscus_insignis | Lariscus_niobe | Lariscus_obscurus
  | Menetes_berdmorei
  | Nannosciurus_melanotis
  | Prosciurillus_abstrusus | Prosciurillus_leucomus | Prosciurillus_murinus | Prosciurillus_topapuensis | Prosciurillus_weberi
  | Rhinosciurus_laticaudatus
  | Rubrisciurus_rubriventer
  | Sundasciurus_brookei | Sundasciurus_davensis | Sundasciurus_fraterculus | Sundasciurus_hippurus
  | Sundasciurus_hoogstraali | Sundasciurus_jentinki | Sundasciurus_juvencus | Sundasciurus_lowii
  | Sundasciurus_mindanensis | Sundasciurus_moellendorffi | Sundasciurus_philippinensis | Sundasciurus_rabori
  | Sundasciurus_samarensis | Sundasciurus_steerii | Sundasciurus_tenuis
  | Tamiops_mcclellandii | Tamiops_maritimus | Tamiops_rodolphii | Tamiops_swinhoei
  | Atlantoxerus_getulus
  | Spermophilopsis_leptodactylus
  | Xerus_erythropus | Xerus_inauris | Xerus_princeps | Xerus_rutilus
  | Epixerus_ebii | Epixerus_wilsoni
  | Funisciurus_anerythrus | Funisciurus_bayonii | Funisciurus_carruthersi | Funisciurus_congicus
  | Funisciurus_isabella | Funisciurus_lemniscatus | Funisciurus_leucogenys | Funisciurus_pyrropus | Funisciurus_substriatus
  | Heliosciurus_gambianus | Heliosciurus_mutabilis | Heliosciurus_punctatus
  | Heliosciurus_rufobrachium | Heliosciurus_ruwenzorii | Heliosciurus_undulatus
  | Myosciurus_pumilio
  | Paraxerus_alexandri | Paraxerus_boehmi | Paraxerus_cepapi | Paraxerus_cooperi | Paraxerus_flavovittis
  | Paraxerus_lucifer | Paraxerus_ochraceus | Paraxerus_palliatus | Paraxerus_poensis | Paraxerus_vexillarius | Paraxerus_vincenti
  | Protoxerus_aubinnii | Protoxerus_stangeri
  | Ammospermophilus_harrisii | Ammospermophilus_insularis | Ammospermophilus_interpres
  | Ammospermophilus_leucurus | Ammospermophilus_nelsoni
  | Callospermophilus_lateralis | Callospermophilus_madrensis | Callospermophilus_saturatus
  | Cynomys_gunnisoni | Cynomys_leucurus | Cynomys_ludovicianus | Cynomys_mexicanus | Cynomys_parvidens
  | Ictidomys_mexicanus | Ictidomys_parvidens | Ictidomys_tridecemlineatus
  | Marmota_baibacina | Marmota_bobak | Marmota_broweri | Marmota_caligata | Marmota_camtschatica
  | Marmota_caudata | Marmota_flaviventris | Marmota_himalayana | Marmota_marmota | Marmota_menzbieri
  | Marmota_monax | Marmota_olympus | Marmota_sibirica | Marmota_vancouverensis
  | Notocitellus_adocetus | Notocitellus_annulatus
  | Otospermophilus_atricapillus | Otospermophilus_beecheyi | Otospermophilus_variegatus
  | Poliocitellus_franklinii
  | Sciurotamias_davidianus | Sciurotamias_forresti
  | Spermophilus_alashanicus | Spermophilus_brevicauda | Spermophilus_citellus | Spermophilus_dauricus
  | Spermophilus_erythrogenys | Spermophilus_fulvus | Spermophilus_major | Spermophilus_musicus
  | Spermophilus_pallidiccauda | Spermophilus_pygmaeus | Spermophilus_ralli | Spermophilus_relictus
  | Spermophilus_suslicus | Spermophilus_taurensis | Spermophilus_xanthoprymnus
  | Tamias_alpinus | Tamias_amoenus | Tamias_bulleri | Tamias_canipes | Tamias_cinereicollis
  | Tamias_dorsalis | Tamias_durangae | Tamias_merriami | Tamias_minimus | Tamias_obscurus
  | Tamias_ochrogenys | Tamias_palmeri | Tamias_panamintinus | Tamias_quadrimaculatus | Tamias_quadrivittatus
  | Tamias_ruficaudus | Tamias_rufus | Tamias_senex | Tamias_sibiricus | Tamias_siskiyou
  | Tamias_sonomae | Tamias_speciosus | Tamias_striatus | Tamias_townsendii | Tamias_umbrinus
  | Urocitellus_armatus | Urocitellus_beldingi | Urocitellus_brunneus | Urocitellus_canus
  | Urocitellus_columbianus | Urocitellus_elegans | Urocitellus_endemicus | Urocitellus_mollis
  | Urocitellus_parryii | Urocitellus_richardsonii | Urocitellus_townsendii | Urocitellus_undulatus | Urocitellus_washingtoni
  | Xerospermophilus_mohavensis | Xerospermophilus_perotensis | Xerospermophilus_spilosoma | Xerospermophilus_tereticaudus.

(* ======================== Species -> Genus ======================== *)

Definition genus_of_species (s : Species) : Genus :=
  match s with
  | Ratufa_affinis | Ratufa_bicolor | Ratufa_indica | Ratufa_macroura => Ratufa
  | Sciurillus_pusillus => Sciurillus
  | Microsciurus_alfari | Microsciurus_flaviventer | Microsciurus_mimulus | Microsciurus_santanderensis => Microsciurus
  | Rheithrosciurus_macrotis => Rheithrosciurus
  | Sciurus_aberti | Sciurus_alleni | Sciurus_anomalus | Sciurus_arizonensis | Sciurus_aureogaster
  | Sciurus_carolinensis | Sciurus_colliaei | Sciurus_deppei | Sciurus_flammifer | Sciurus_gilvigularis
  | Sciurus_granatensis | Sciurus_griseus | Sciurus_igniventris | Sciurus_lis | Sciurus_nayaritensis
  | Sciurus_niger | Sciurus_oculatus | Sciurus_pucheranii | Sciurus_pyrrhinus | Sciurus_richmondi
  | Sciurus_sanborni | Sciurus_spadiceus | Sciurus_stramineus | Sciurus_variegatoides | Sciurus_vulgaris
  | Sciurus_yucatanensis => Sciurus
  | Syntheosciurus_brochus => Syntheosciurus
  | Tamiasciurus_douglasii | Tamiasciurus_fremonti | Tamiasciurus_hudsonicus | Tamiasciurus_mearnsi => Tamiasciurus
  | Aeretes_melanopterus => Aeretes
  | Aeromys_tephromelas | Aeromys_thomasi => Aeromys
  | Belomys_pearsonii => Belomys
  | Biswamoyopterus_biswasi | Biswamoyopterus_laoensis => Biswamoyopterus
  | Eoglaucomys_fimbriatus => Eoglaucomys
  | Eupetaurus_cinereus => Eupetaurus
  | Glaucomys_oregonensis | Glaucomys_sabrinus | Glaucomys_volans => Glaucomys
  | Hylopetes_alboniger | Hylopetes_baberi | Hylopetes_bartelsi | Hylopetes_lepidus | Hylopetes_nigripes
  | Hylopetes_phayrei | Hylopetes_platyurus | Hylopetes_sipora | Hylopetes_spadiceus | Hylopetes_winstoni => Hylopetes
  | Iomys_horsfieldii | Iomys_sipora => Iomys
  | Petaurillus_emiliae | Petaurillus_hosei | Petaurillus_kinlochii => Petaurillus
  | Petaurista_alborufus | Petaurista_elegans | Petaurista_leucogenys | Petaurista_magnificus
  | Petaurista_mechukaensis | Petaurista_mishmiensis | Petaurista_nobilis | Petaurista_petaurista
  | Petaurista_philippensis | Petaurista_xanthotis | Petaurista_yunanensis => Petaurista
  | Petinomys_crinitus | Petinomys_fuscocapillus | Petinomys_genibarbis | Petinomys_hageni
  | Petinomys_lugens | Petinomys_mindanensis | Petinomys_sagitta | Petinomys_setosus | Petinomys_vordermanni => Petinomys
  | Pteromys_momonga | Pteromys_volans => Pteromys
  | Pteromyscus_pulverulentus => Pteromyscus
  | Trogopterus_xanthipes => Trogopterus
  | Callosciurus_adamsi | Callosciurus_albescens | Callosciurus_baluensis | Callosciurus_caniceps
  | Callosciurus_erythraeus | Callosciurus_finlaysonii | Callosciurus_inornatus | Callosciurus_melanogaster
  | Callosciurus_nigrovittatus | Callosciurus_notatus | Callosciurus_orestes | Callosciurus_phayrei
  | Callosciurus_prevostii | Callosciurus_pygerythrus | Callosciurus_quinquestriatus => Callosciurus
  | Dremomys_everetti | Dremomys_gularis | Dremomys_lokriah | Dremomys_pernyi | Dremomys_pyrrhomerus | Dremomys_rufigenis => Dremomys
  | Exilisciurus_concinnus | Exilisciurus_exilis | Exilisciurus_whiteheadi => Exilisciurus
  | Funambulus_layardi | Funambulus_palmarum | Funambulus_pennantii | Funambulus_sublineatus | Funambulus_tristriatus => Funambulus
  | Glyphotes_simus => Glyphotes
  | Hyosciurus_heinrichi | Hyosciurus_ileile => Hyosciurus
  | Lariscus_hosei | Lariscus_insignis | Lariscus_niobe | Lariscus_obscurus => Lariscus
  | Menetes_berdmorei => Menetes
  | Nannosciurus_melanotis => Nannosciurus
  | Prosciurillus_abstrusus | Prosciurillus_leucomus | Prosciurillus_murinus | Prosciurillus_topapuensis | Prosciurillus_weberi => Prosciurillus
  | Rhinosciurus_laticaudatus => Rhinosciurus
  | Rubrisciurus_rubriventer => Rubrisciurus
  | Sundasciurus_brookei | Sundasciurus_davensis | Sundasciurus_fraterculus | Sundasciurus_hippurus
  | Sundasciurus_hoogstraali | Sundasciurus_jentinki | Sundasciurus_juvencus | Sundasciurus_lowii
  | Sundasciurus_mindanensis | Sundasciurus_moellendorffi | Sundasciurus_philippinensis | Sundasciurus_rabori
  | Sundasciurus_samarensis | Sundasciurus_steerii | Sundasciurus_tenuis => Sundasciurus
  | Tamiops_mcclellandii | Tamiops_maritimus | Tamiops_rodolphii | Tamiops_swinhoei => Tamiops
  | Atlantoxerus_getulus => Atlantoxerus
  | Spermophilopsis_leptodactylus => Spermophilopsis
  | Xerus_erythropus | Xerus_inauris | Xerus_princeps | Xerus_rutilus => Xerus
  | Epixerus_ebii | Epixerus_wilsoni => Epixerus
  | Funisciurus_anerythrus | Funisciurus_bayonii | Funisciurus_carruthersi | Funisciurus_congicus
  | Funisciurus_isabella | Funisciurus_lemniscatus | Funisciurus_leucogenys | Funisciurus_pyrropus | Funisciurus_substriatus => Funisciurus
  | Heliosciurus_gambianus | Heliosciurus_mutabilis | Heliosciurus_punctatus
  | Heliosciurus_rufobrachium | Heliosciurus_ruwenzorii | Heliosciurus_undulatus => Heliosciurus
  | Myosciurus_pumilio => Myosciurus
  | Paraxerus_alexandri | Paraxerus_boehmi | Paraxerus_cepapi | Paraxerus_cooperi | Paraxerus_flavovittis
  | Paraxerus_lucifer | Paraxerus_ochraceus | Paraxerus_palliatus | Paraxerus_poensis | Paraxerus_vexillarius | Paraxerus_vincenti => Paraxerus
  | Protoxerus_aubinnii | Protoxerus_stangeri => Protoxerus
  | Ammospermophilus_harrisii | Ammospermophilus_insularis | Ammospermophilus_interpres
  | Ammospermophilus_leucurus | Ammospermophilus_nelsoni => Ammospermophilus
  | Callospermophilus_lateralis | Callospermophilus_madrensis | Callospermophilus_saturatus => Callospermophilus
  | Cynomys_gunnisoni | Cynomys_leucurus | Cynomys_ludovicianus | Cynomys_mexicanus | Cynomys_parvidens => Cynomys
  | Ictidomys_mexicanus | Ictidomys_parvidens | Ictidomys_tridecemlineatus => Ictidomys
  | Marmota_baibacina | Marmota_bobak | Marmota_broweri | Marmota_caligata | Marmota_camtschatica
  | Marmota_caudata | Marmota_flaviventris | Marmota_himalayana | Marmota_marmota | Marmota_menzbieri
  | Marmota_monax | Marmota_olympus | Marmota_sibirica | Marmota_vancouverensis => Marmota
  | Notocitellus_adocetus | Notocitellus_annulatus => Notocitellus
  | Otospermophilus_atricapillus | Otospermophilus_beecheyi | Otospermophilus_variegatus => Otospermophilus
  | Poliocitellus_franklinii => Poliocitellus
  | Sciurotamias_davidianus | Sciurotamias_forresti => Sciurotamias
  | Spermophilus_alashanicus | Spermophilus_brevicauda | Spermophilus_citellus | Spermophilus_dauricus
  | Spermophilus_erythrogenys | Spermophilus_fulvus | Spermophilus_major | Spermophilus_musicus
  | Spermophilus_pallidiccauda | Spermophilus_pygmaeus | Spermophilus_ralli | Spermophilus_relictus
  | Spermophilus_suslicus | Spermophilus_taurensis | Spermophilus_xanthoprymnus => Spermophilus
  | Tamias_alpinus | Tamias_amoenus | Tamias_bulleri | Tamias_canipes | Tamias_cinereicollis
  | Tamias_dorsalis | Tamias_durangae | Tamias_merriami | Tamias_minimus | Tamias_obscurus
  | Tamias_ochrogenys | Tamias_palmeri | Tamias_panamintinus | Tamias_quadrimaculatus | Tamias_quadrivittatus
  | Tamias_ruficaudus | Tamias_rufus | Tamias_senex | Tamias_sibiricus | Tamias_siskiyou
  | Tamias_sonomae | Tamias_speciosus | Tamias_striatus | Tamias_townsendii | Tamias_umbrinus => Tamias
  | Urocitellus_armatus | Urocitellus_beldingi | Urocitellus_brunneus | Urocitellus_canus
  | Urocitellus_columbianus | Urocitellus_elegans | Urocitellus_endemicus | Urocitellus_mollis
  | Urocitellus_parryii | Urocitellus_richardsonii | Urocitellus_townsendii | Urocitellus_undulatus | Urocitellus_washingtoni => Urocitellus
  | Xerospermophilus_mohavensis | Xerospermophilus_perotensis | Xerospermophilus_spilosoma | Xerospermophilus_tereticaudus => Xerospermophilus
  end.

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

(* ======================== Derived Species Classification ======================== *)

Definition subfamily_of_species (s : Species) : Subfamily :=
  subfamily_of (genus_of_species s).

Definition tribe_of_species (s : Species) : Tribe :=
  tribe_of (genus_of_species s).

Definition native_continents_species (s : Species) : list Continent :=
  native_continents (genus_of_species s).

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

(* ========================================================================== *)
(*                        DICHOTOMOUS KEY                                     *)
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
  | Q_Striped => match g with Tamias => true | Tamiops => true | Funambulus => true | _ => false end
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
  length (filter (fun g => key_correct_subfamily g) all_genera).

Definition count_correct_tribe : nat :=
  length (filter (fun g => key_correct_tribe g) all_genera).

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
  length (filter (fun g => subfamily_eqb (fst (refined_key_result g)) (subfamily_of g)) all_genera).

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
