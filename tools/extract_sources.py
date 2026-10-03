#!/usr/bin/env python3
"""Extract the Sciuridae subset of the two pinned upstream sources.

Inputs (downloaded by tools/fetch_sources.sh, checked against SHA-256):
  * Mammal Diversity Database v2.5 (2026-07-28), MDD_v2.5_6904species.csv
  * Upham, Esselstyn & Jetz 2019, DNA-only, topology-free node-dated MCC tree
    MamPhy_fullPosterior_BDvr_DNAonly_4098sp_topoFree_NDexp_MCC_v2_target.tre

Outputs (committed to the repository, consumed by tools/gen_coq.py):
  * data/mdd/MDD_v2.5_Sciuridae.csv          -- the 321 sciurid rows, selected columns
  * data/upham2019/Sciuridae_DNAonly_MCC.nwk -- the sciurid subtree with posterior and height
  * data/upham2019/tip_map.csv               -- each tip mapped to MDD v2.5 species and genus

Requires dendropy (only for reading the upstream NEXUS file).  Everything
downstream uses the Python standard library only.
"""
import csv, hashlib, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CACHE = os.path.join(ROOT, '.cache')
MDD_FILE = os.path.join(CACHE, 'MDD_v2.5_6904species.csv')
TREE_FILE = os.path.join(CACHE, 'MamPhy_fullPosterior_BDvr_DNAonly_4098sp_topoFree_NDexp_MCC_v2_target.tre')
SHA256 = {
    MDD_FILE: '0d07a7e9409712fa86c1e3afadcf4c67bf4f9e16d5693a878e11ec1bf6860493',
    TREE_FILE: 'c738f99eaeddf632deb43f4784a2c332159cc65ff4fbf3b8d0d6e1d66fbfd355',
}

MDD_COLUMNS = ['sciName', 'id', 'phylosort', 'mainCommonName', 'subfamily', 'tribe', 'genus',
               'subgenus', 'specificEpithet', 'authoritySpeciesAuthor', 'authoritySpeciesYear',
               'authorityParentheses', 'originalNameCombination', 'countryDistribution',
               'continentDistribution', 'biogeographicRealm', 'iucnStatus', 'extinct']

# Upham et al. (2019) used the MDD v1.0 (2018) names.  Tips whose binomial is not an
# MDD v2.5 species are mapped here; every entry is justified by MDD v2.5 itself
# (taxonomyNotes or nominalNames of the target species).
TIP_RENAMES = {
    'Eutamias_sibiricus':           ('Tamias_sibiricus', 'moved from Tamias to Eutamias (Patterson & Norris 2016)'),
    'Euxerus_erythropus':           ('Xerus_erythropus', 'moved from Xerus to Euxerus (Krystufek et al. 2016)'),
    'Geosciurus_inauris':           ('Xerus_inauris', 'moved from Xerus to Geosciurus (Krystufek et al. 2016)'),
    'Geosciurus_princeps':          ('Xerus_princeps', 'moved from Xerus to Geosciurus (Krystufek et al. 2016)'),
    'Hylopetes_sagitta':            ('Hylopetes_lepidus', 'MDD: H. sagitta includes lepidus'),
    'Sciurus_aestuans':             ('Sciurus_gilvigularis', 'MDD: S. aestuans includes gilvigularis'),
    'Spermophilopsis_leptodactyla': ('Spermophilopsis_leptodactylus', 'gender agreement of epithet'),
    'Spermophilus_alaschanicus':    ('Spermophilus_alashanicus', 'original spelling restored'),
    'Tamiops_mcclellandii':         ('Tamiops_macclellandii', 'MDD: macclellandii is an incorrect subsequent spelling'),
    'Petaurista_hainanus':          ('Petaurista_hainana', 'gender agreement of epithet'),
    'Otospermophilus_beecheyi':     ('Otospermophilus_atricapillus', 'MDD: beecheyi includes atricapillus'),
    'Petaurista_nobilis':           ('Petaurista_yunanensis', 'MDD: nobilis includes yunanensis'),
    'Tamiasciurus_douglasii':       ('Tamiasciurus_mearnsi', 'MDD: douglasii includes mearnsi'),
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def check_inputs():
    for path, digest in SHA256.items():
        if not os.path.exists(path):
            sys.exit(f'missing {path}; run tools/fetch_sources.sh first')
        got = sha256(path)
        if got != digest:
            sys.exit(f'checksum mismatch for {path}: {got}')


def extract_mdd():
    with open(MDD_FILE, encoding='utf-8') as f:
        rows = [r for r in csv.DictReader(f) if r['family'].upper() == 'SCIURIDAE']
    rows.sort(key=lambda r: int(r['phylosort']))
    out = os.path.join(ROOT, 'data', 'mdd', 'MDD_v2.5_Sciuridae.csv')
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w', encoding='utf-8', newline='') as f:
        w = csv.DictWriter(f, fieldnames=MDD_COLUMNS, lineterminator='\n')
        w.writeheader()
        for r in rows:
            w.writerow({k: r[k] for k in MDD_COLUMNS})
    return {r['sciName']: r for r in rows}


def newick(node, ann):
    """Serialise with [&posterior=...,height=...,hpd=lo:hi] after every internal node."""
    if node.is_leaf():
        return node.taxon.label
    kids = ','.join(newick(c, ann) for c in node.child_nodes())
    p, h, lo, hi = ann(node)
    return f'({kids})[&posterior={p},height={h},hpd={lo}:{hi}]'


def extract_tree(mdd):
    import dendropy
    tree = dendropy.Tree.get(path=TREE_FILE, schema='nexus', preserve_underscores=True)
    sq = [l.taxon for l in tree.leaf_nodes() if '_SCIURIDAE_' in l.taxon.label]
    root = tree.mrca(taxa=sq)
    inside = [l.taxon.label for l in root.leaf_nodes()]
    assert len(inside) == len(sq) and all('_SCIURIDAE_' in x for x in inside), \
        'Sciuridae is not a clade of the source tree; extraction would not be a subtree'

    def ann(node):
        a = {x.name: x.value for x in node.annotations}
        lo, hi = a['height_95%_HPD']
        return a['posterior'], a['height'], lo, hi

    rev = {old: new for new, (old, _) in TIP_RENAMES.items()}
    reasons = {old: why for new, (old, why) in TIP_RENAMES.items()}
    tips = []
    for label in inside:
        binomial = '_'.join(label.split('_')[:2])
        if binomial in mdd:
            target, note = binomial, ''
        elif binomial in rev:
            target, note = rev[binomial], reasons[binomial]
        elif binomial.startswith('Tamias_') and 'Neotamias_' + binomial.split('_')[1] in mdd:
            target, note = 'Neotamias_' + binomial.split('_')[1], 'moved from Tamias to Neotamias (Patterson & Norris 2016)'
        else:
            sys.exit(f'unmapped tip {label}')
        tips.append((label, binomial, target, mdd[target]['genus'], note))

    outdir = os.path.join(ROOT, 'data', 'upham2019')
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, 'Sciuridae_DNAonly_MCC.nwk'), 'w') as f:
        f.write(newick(root, ann) + ';\n')
    with open(os.path.join(outdir, 'tip_map.csv'), 'w', newline='') as f:
        w = csv.writer(f, lineterminator='\n')
        w.writerow(['tip_label', 'upham_binomial', 'mdd_v2_5_species', 'mdd_v2_5_genus', 'mapping_note'])
        w.writerows(tips)
    return len(tips)


if __name__ == '__main__':
    check_inputs()
    mdd = extract_mdd()
    n = extract_tree(mdd)
    print(f'MDD: {len(mdd)} sciurid species; Upham 2019 subtree: {n} tips')
