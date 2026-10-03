# Data sources

Everything the Coq development knows about squirrels comes from the files in
this directory. `tools/gen_coq.py` turns them into `theories/Data/*.v`; CI
regenerates those files and fails if they differ from what is committed.

## 1. Mammal Diversity Database v2.5 (taxonomy, ranges, Red List status)

- Mammal Diversity Database (2026). *Mammal Diversity Database* (Version 2.5)
  [Data set]. Zenodo. https://doi.org/10.5281/zenodo.21654811 . Released
  2026-07-28. Licence: CC BY 4.0.
- Upstream file `MDD_v2.5_6904species.csv`,
  SHA-256 `0d07a7e9409712fa86c1e3afadcf4c67bf4f9e16d5693a878e11ec1bf6860493`.
- `mdd/MDD_v2.5_Sciuridae.csv` holds the 321 rows with `family = Sciuridae`
  and a subset of the columns (taxonomy, authority, native country /
  continent / realm, IUCN status). Rows and values are unchanged.

## 2. Upham, Esselstyn & Jetz (2019) mammal phylogeny

- Upham N.S., Esselstyn J.A., Jetz W. (2019). Inferring the mammal tree:
  species-level sets of phylogenies for questions in ecology, evolution, and
  conservation. *PLoS Biology* 17(12): e3000494.
  https://doi.org/10.1371/journal.pbio.3000494 . Data: Dryad
  https://doi.org/10.5061/dryad.tb03d03 (CC0).
- Tree used: DNA-only, topology-free, node-dated maximum clade credibility
  tree `MamPhy_fullPosterior_BDvr_DNAonly_4098sp_topoFree_NDexp_MCC_v2_target.tre`
  (copy distributed with https://github.com/n8upham/MamPhy_v1),
  SHA-256 `c738f99eaeddf632deb43f4784a2c332159cc65ff4fbf3b8d0d6e1d66fbfd355`.
- `upham2019/Sciuridae_DNAonly_MCC.nwk` is the subtree of the 207 sciurid
  tips. Sciuridae is a clade of the source tree (posterior 1.0), so this is an
  exact subtree, not a pruning; node posterior, height and 95% HPD are copied
  from the source annotations.
- `upham2019/tip_map.csv` maps each tip (named under the 2018 MDD v1.0
  taxonomy) to its MDD v2.5 species and genus; every renamed tip cites the
  MDD v2.5 note that justifies it.

`tools/fetch_sources.sh` downloads both upstream files and checks the
checksums; `tools/extract_sources.py` (needs `dendropy`) recreates the two
extracts.

## 3. Character data for the genus key

`characters/*.json`: one file per group of genera, compiled for this project
from the taxonomic literature. Every coded state carries its evidence: a
citation, a URL and a quotation. Quotations marked `"verbatim": true` were
checked by script to be exact substrings (up to whitespace) of the retrieved
text; OCR errors in old scans are preserved. The main sources are:

- Ellerman J.R. (1940). *The Families and Genera of Living Rodents*, vol. 1.
- Moore J.C. (1958, 1959); Moore J.C. & Tate G.H.H. (1965), *Fieldiana Zoology* 48.
- Thomas O. (1908, 1909) and other original genus descriptions.
- Helgen K.M. et al. (2009). Generic revision in the Holarctic ground squirrel
  genus *Spermophilus*. *Journal of Mammalogy* 90: 270-305.
- Kryštufek B. et al. (2016). A review of bristly ground squirrels Xerini and a
  generic revision in the African genus *Xerus*. *Mammalia* 80: 521-540.
- Kryštufek B. & Vohralík V. (2012, 2013). Taxonomic revisions of Palaearctic
  rodents.
- Li Q. et al. (2021). Phylogenetic and morphological significance of an
  overlooked flying squirrel (Pteromyini) from the eastern Himalayas.
  *Zoological Research* (incl. Table S6).
- Musser G.G. et al. (2010). Sulawesi squirrels (*Rubrisciurus*,
  *Prosciurillus*, *Hyosciurus*).
- Heaney L.R. (1985). Pygmy squirrels *Exilisciurus* and *Nannosciurus*.
- Hawkins M.T.R. et al. (2016). *Dremomys* revision. *Molecular
  Phylogenetics and Evolution* 94: 752-764.
- Koprowski J.L. et al. (2016). Family Sciuridae. In *Handbook of the Mammals
  of the World* vol. 6 (species accounts, via Plazi TreatmentBank).
- Kruskop S.V. et al. (2022). *Olisthomys*. *Diversity* 14: 610.
- de Abreu-Júnior E.F. et al. (2020); Mammalian Species accounts; Animal
  Diversity Web (as a secondary source).

The per-genus citations appear in `docs/KEY.md`.

`characters/curation.json` lists every adjustment made to those codings, each
with its reason. Adjustments only correct a figure the evidence itself shows
to be something else (for example a total length reported as head-and-body
length) or widen a coding that an observer could score either way.

## 4. Fossil genera

`fossils.json`: type species, age, material, gliding evidence and published
placements of *Douglassciurus*, *Hesperopetes*, *Palaeosciurus* and
*Protosciurus*, with quotations from:

- Black C.C. (1963). A review of the North American Tertiary Sciuridae.
  *Bulletin of the Museum of Comparative Zoology* 130: 109-248.
- Emry R.J. & Thorington R.W. Jr. (1982). Descriptive and comparative
  osteology of the oldest fossil squirrel, *Protosciurus*. *Smithsonian
  Contributions to Paleobiology* 47 (the skeleton is now *Douglassciurus*).
- Emry R.J. & Korth W.W. (2007). A new genus of squirrel from the mid-Cenozoic
  of North America. *Journal of Vertebrate Paleontology* 27: 693-698.
- Casanovas-Vilar I. et al. (2018). Oldest skeleton of a fossil flying
  squirrel casts new light on the phylogeny of the group. *eLife* 7: e39270.
- Li Q. et al. (2023). Two large squirrels from the Junggar Basin.
- The Paleobiology Database (paleobiodb.org) taxon and occurrence records,
  retrieved 2026-10-03.

## Policies

- **Unknown is never guessed.** A character with no sourced state admits every
  state. A character documented for only some species of a genus is treated as
  unknown for that genus, as is a length range that misses species.
- **Several sources are unioned.** If two sources give different states for a
  genus, its profile contains both.
- **Uncertain MDD records are included** in the ranges the key uses
  ("documented" ranges) and excluded from "confirmed" ranges.
