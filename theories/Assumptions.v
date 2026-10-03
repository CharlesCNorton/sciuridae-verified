(* Axiom audit, run by tools/check_assumptions.sh (and CI).  Every theorem
   listed must print "Closed under the global context": no axioms, no
   admitted lemmas, no parameters. *)

From Sciuridae Require Import Lib.Base Phylo.Clusters Phylo.Tree Key.Key Key.Matrix
  Classification Biogeography Conservation Phylogeny Paleontology Identification.

(* Generic theory *)
Print Assumptions clusters_hierarchy.
Print Assumptions conflict_excludes_monophyly.
Print Assumptions resolution_non_monophyly.
Print Assumptions resolution_sisters.
Print Assumptions undecided_is_consistent.
Print Assumptions key_sound.
Print Assumptions identify_exact.
Print Assumptions key_resolves.
Print Assumptions no_resolving_key.
Print Assumptions decide_sound.

(* Classification *)
Print Assumptions ranks_nest.
Print Assumptions genus_count.
Print Assumptions species_count.
Print Assumptions species_per_subfamily.
Print Assumptions sciurus_largest.

(* Biogeography and conservation *)
Print Assumptions genus_realms_spec.
Print Assumptions urocitellus_holarctic.
Print Assumptions holarctic_genera.
Print Assumptions african_squirrels_are_xerine.
Print Assumptions nannosciurinae_asian.
Print Assumptions asia_richest.
Print Assumptions china_richest_in_genera.
Print Assumptions critically_endangered.

(* Phylogeny *)
Print Assumptions evidence_consistent.
Print Assumptions testable_tribes_monophyletic.
Print Assumptions testable_subfamilies_monophyletic.
Print Assumptions sciurus_not_monophyletic.
Print Assumptions spermophilus_sensu_lato_not_monophyletic.
Print Assumptions xerini_protoxerini_not_sisters.
Print Assumptions sciurillinae_sciurinae_not_sisters.
Print Assumptions nannosciurinae_xerinae_sisters.

(* Paleontology *)
Print Assumptions placements_tested.
Print Assumptions douglassciurus_predates_crown_squirrels.
Print Assumptions no_fossil_shows_gliding.

(* Identification *)
Print Assumptions genus_key_sound.
Print Assumptions identification_exact.
Print Assumptions identification_unique_or_residual.
Print Assumptions residual_cannot_be_separated.
Print Assumptions every_genus_identifiable.
