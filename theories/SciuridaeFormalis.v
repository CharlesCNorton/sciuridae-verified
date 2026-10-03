(******************************************************************************)
(*                                                                            *)
(*         Sciuridae Formalis: Verified Taxonomy of the Squirrel Family       *)
(*                                                                            *)
(*     The squirrel family as recognised by the Mammal Diversity Database    *)
(*     v2.5 (2026): 5 subfamilies, 10 tribes, 64 genera, 321 species, with   *)
(*     native ranges and Red List status; the classification tested against *)
(*     the molecular phylogeny of Upham, Esselstyn & Jetz (2019); and a      *)
(*     dichotomous key to the genera whose correctness is proved for every   *)
(*     observation consistent with sourced character data.                  *)
(*                                                                            *)
(*     The gray squirrel is peculiarly a product of the woods;                *)
(*     he seems to be the spirit of the trees made visible.                   *)
(*                                  -- John Burroughs, 1900                   *)
(*                                                                            *)
(*     In memoriam: the small lives lost beneath our wheels.                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*                                                                            *)
(******************************************************************************)

(* Importing this module brings the whole development into scope.

   Generic theories (no squirrel data):
     Lib.Base         boolean equality, finite types, list sets, reflection
     Phylo.Clusters   hierarchies, monophyly, sister groups, robustness
     Phylo.Tree       annotated binary trees and their supported clades
     Key.Key          dichotomous keys: soundness, exactness, resolution
     Key.Matrix       character matrices with polymorphic states

   Data (generated from data/ by tools/gen_coq.py; never edited by hand):
     Data.Geography, Data.Taxonomy, Data.Species   MDD v2.5
     Data.Upham2019                                Upham et al. 2019 tree
     Data.Characters, Data.GenusKey                sourced characters, key
     Data.Fossils                                  sourced fossil record

   Results:
     Classification, Biogeography, Conservation, Phylogeny,
     Paleontology, Identification *)

From Sciuridae Require Export Lib.Base Phylo.Clusters Phylo.Tree Key.Key Key.Matrix
  Data.Geography Data.Taxonomy Data.Species Data.Upham2019 Data.Fossils
  Data.Characters Data.GenusKey
  Classification Biogeography Conservation Phylogeny Paleontology Identification.
