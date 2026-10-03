# Sciuridae Formalis

A machine-checked taxonomy of the squirrel family (Sciuridae) in Coq, built on
cited data:

- **Classification and ranges** from the Mammal Diversity Database v2.5 (2026):
  5 subfamilies, 10 tribes, 64 genera, 321 species, with native countries,
  continents, biogeographic realms and IUCN status for every species.
- **Phylogeny** from the DNA-only, node-dated maximum clade credibility tree of
  Upham, Esselstyn & Jetz (2019), used to test the classification.
- **Morphology** for every genus, compiled from the taxonomic literature with a
  citation and quotation for each coded state, feeding a dichotomous key whose
  correctness is proved for all observations.
- **Fossil genera** (*Douglassciurus*, *Hesperopetes*, *Palaeosciurus*,
  *Protosciurus*) kept apart from extant taxa and tested against the dated tree.

Nothing about squirrels is asserted by hand in the Coq sources: the data
modules in `theories/Data/` are generated from `data/` (see
[`data/SOURCES.md`](data/SOURCES.md)), and every theorem about them is
checked by computation against those tables.

## What is proved

| Module | Highlights |
|---|---|
| `Phylo/Clusters.v`, `Phylo/Tree.v` | Clusters of any tree with distinct tips form a hierarchy. A group that is a well-supported clade is monophyletic in **every** fully resolved tree containing the well-supported clades; a group that conflicts with one is monophyletic in **none**; undecided groups are shown to be consistent with the evidence. Same for sister groups. |
| `Key/Key.v`, `Key/Matrix.v` | For any dichotomous key and character matrix with polymorphic states: soundness for every consistent observation (complete or partial), exact identification (the key plus a consistency filter returns exactly the matching taxa), uniqueness on complete observations for resolved keys, and a proof that taxa sharing a complete observation can be separated by no sound key at all. |
| `Classification.v` | Ranks nest by construction; counts per subfamily and tribe; *Sciurus* is the largest genus; the 24 monotypic genera; the MDD splits of *Tamias* and *Xerus*. |
| `Biogeography.v` | Genus ranges are unions of species ranges by definition. Every African squirrel is a xerine; Nannosciurinae is entirely Asian; Protoxerini is Afrotropical; exactly three genera are Holarctic (*Sciurus*, *Marmota*, *Urocitellus*); *Glaucomys volans* is the only Neotropical flying squirrel; Asia and China are the richest continent and country. |
| `Conservation.v` | Red List tally, the four Critically Endangered species, statuses assessed under former names. |
| `Phylogeny.v` | Against Upham et al. at posterior ≥ 0.95: every testable MDD subfamily and tribe is monophyletic; *Sciurus*, *Microsciurus* and *Hylopetes* are not; *Spermophilus* in the pre-2009 sense is not (the refuting clade contains the prairie dogs); Nannosciurinae + Xerinae and Marmotini + Tamiini are sister pairs; Xerini is **not** sister to Protoxerini nor to Marmotini, and *Sciurillus* is not sister to Sciurinae. |
| `Paleontology.v` | No fossil genus preserves evidence of gliding. Comparing each published placement with crown-node 95% HPD ages: *Douglassciurus* and *Hesperopetes* predate crown Sciuridae; placing *Douglassciurus* or *Palaeosciurus* in crown Sciurinae, or *Protosciurus* in crown Sciurini, conflicts with the dating. |
| `Identification.v` | The genus key is checked sound against the sourced profiles; identification is exact for every observation; on a complete observation the key returns one genus except within residual groups, each of which is proved inseparable by any sound key over the current data. |

`theories/Assumptions.v` prints the assumptions of the headline theorems; CI
fails if any depends on an axiom.

## Status of the key

With the data committed now, the key (`docs/KEY.md`; 104 couplets, at most 10
deep) identifies 51 of the 64 genera uniquely on every complete observation.
The remaining 13 genera fall into small residual groups (for example
*Sundasciurus* with *Callosciurus*, *Dremomys* or *Tamiops*; *Hylopetes* with
*Eoglaucomys* or *Priapomys*; *Spermophilus* with *Urocitellus*) for which the
literature consulted so far gives no character that holds across every species
of both genera. `Identification.v` proves that each residual group is forced by
the data: its genera share a complete observation, so no sound key over these
characters could separate them. Further targeted research is in progress.

## Building

Requires Coq 8.18, 8.19 or 8.20 (all three are built in CI) and `make`.

```sh
make                         # build everything (about 30 s)
sh tools/check_assumptions.sh  # axiom audit
python3 tools/gen_coq.py --check   # generated files match data/
```

To regenerate `theories/Data/` after editing `data/`: `python3 tools/gen_coq.py`.
To re-derive the extracts in `data/` from the upstream files:
`sh tools/fetch_sources.sh && python3 tools/extract_sources.py` (needs `dendropy`).

## Layout

```
data/                 sourced inputs (MDD extract, Upham subtree, characters, fossils)
tools/                extraction and code generation (Python, stdlib only)
theories/Lib          finite types and list sets with reflection
theories/Phylo        hierarchies, monophyly, sister groups, dated trees
theories/Key          dichotomous keys and character matrices
theories/Data         generated data modules (do not edit)
theories/*.v          results about Sciuridae
docs/KEY.md           the key for people, with per-genus citations
```

## Changes from the first version

The first version (one hand-written file, still in the git history) encoded 63
genera and 292 species from memory. It contained factual errors that this
version corrects from sources: *Urocitellus* was restricted to North America;
*Ictidomys* (thirteen-lined ground squirrels) was coded unstriped; the Eocene
stem squirrel *Douglassciurus* was coded as a gliding flying squirrel; fossil
genera had invented fur colours used by the key; several species were
duplicates or misspelled; five current genera were missing. Its "100%
accurate" key was only checked on the 63 profiles it was fitted to.

## Licence

Code: MIT (see `LICENSE`). Data: MDD v2.5 is CC BY 4.0; the Upham et al. (2019)
tree is CC0. Quotations in `data/characters/` are short excerpts cited for
verification.

---

*The gray squirrel is peculiarly a product of the woods; he seems to be the
spirit of the trees made visible.* — John Burroughs, 1900

In memoriam: the small lives lost beneath our wheels.
