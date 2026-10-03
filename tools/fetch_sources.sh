#!/bin/sh
# Download the two pinned upstream sources into .cache/ and verify them.
# Only needed to re-run tools/extract_sources.py; the extracts in data/ are committed.
set -eu
cd "$(dirname "$0")/.."
mkdir -p .cache
MDD=.cache/MDD_v2.5_6904species.csv
TREE=.cache/MamPhy_fullPosterior_BDvr_DNAonly_4098sp_topoFree_NDexp_MCC_v2_target.tre
[ -f "$MDD" ] || curl -fsSL -o "$MDD" \
  "https://zenodo.org/api/records/21654811/files/MDD_v2.5_6904species.csv/content"
[ -f "$TREE" ] || curl -fsSL -o "$TREE" \
  "https://raw.githubusercontent.com/n8upham/MamPhy_v1/master/_DATA/MamPhy_fullPosterior_BDvr_DNAonly_4098sp_topoFree_NDexp_MCC_v2_target.tre"
sha256sum -c <<EOF
0d07a7e9409712fa86c1e3afadcf4c67bf4f9e16d5693a878e11ec1bf6860493  $MDD
c738f99eaeddf632deb43f4784a2c332159cc65ff4fbf3b8d0d6e1d66fbfd355  $TREE
EOF
