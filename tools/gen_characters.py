"""Character matrix and identification key (imported by tools/gen_coq.py).

Inputs
  data/characters/<group>.json   sourced character states (one file per group of
                                  genera; every state carries citations)
  data/characters/curation.json  explicit, reasoned adjustments to those codings
  data/mdd/...                    realms and countries (native ranges, MDD v2.5)

Policy (applied uniformly; it can only make profiles larger, never smaller):
  * a character coded "unknown" lists every state;
  * a character whose sources cover only some species of the genus
    ("scope": "partial") lists every state unless a curation entry says
    otherwise;
  * MDD records marked uncertain are included in a genus's geography.
A larger profile never makes the key unsound; it can only make it less
discriminating.  The key built here is checked independently in Coq
(theories/Identification.v), so a bug in this builder cannot produce a key
that Coq accepts as sound.

Outputs
  theories/Data/Characters.v   characters, states, genus profiles
  theories/Data/GenusKey.v     the dichotomous key
  docs/KEY.md                  the key rendered for people, with citations
"""
import csv, json, os, re

STANDARD = [
    ('patagium', ['absent', 'present'], 'gliding membrane between fore- and hind-limbs'),
    ('dorsal_stripes', ['absent', 'present'], 'longitudinal stripes along the back'),
    ('flank_stripe', ['absent', 'present'], 'pale or dark line along the side of the body'),
    ('dorsal_spots', ['absent', 'present'], 'rows of spots or dapples on the back'),
    ('ear_tufts', ['absent', 'present'], 'tufts of long hair at the ear tips'),
    ('tail_rings', ['absent', 'present'], 'tail ringed with alternating light and dark bands'),
    ('tail_distichous', ['no', 'yes'], 'tail flattened, hairs spreading to the sides'),
    ('snout_elongate', ['no', 'yes'], 'markedly elongated, shrew-like snout'),
    ('hairy_soles', ['no', 'yes'], 'soles of the hind feet densely furred'),
    ('cheek_pouches', ['absent', 'present'], 'internal cheek pouches'),
    ('upper_premolars', ['1', '2'], 'upper premolars per side'),
    ('upper_incisor_groove', ['smooth', 'grooved'], 'longitudinal groove on the front of the upper incisors'),
    ('hypsodont_cheek_teeth', ['no', 'yes'], 'high-crowned cheek teeth'),
]
REALMS = ['Afrotropic', 'Antarctic', 'Australasia', 'Indomalaya', 'Nearctic', 'Neotropic', 'Oceania', 'Palearctic']
LEN_UNKNOWN = (0, 2000)
MIN_GAP_MM = 15          # a length couplet needs clear space between the two groups:
GAP_FRACTION = 0.10      # at least max(MIN_GAP_MM, GAP_FRACTION * threshold) mm


def ident(name):
    s = re.sub(r'[^0-9A-Za-z]+', '_', name).strip('_')
    return s if s and s[0].isalpha() else 'X_' + s


def coq_string(s):
    return '"' + s.replace('"', '""') + '"'


class Matrix:
    def __init__(self, data_dir, genera, mdd_rows):
        self.genera = genera
        self.chars = []          # (key, states, description, kind)
        self.profiles = {g: {} for g in genera}
        self.length = {g: LEN_UNKNOWN for g in genera}
        self.evidence = {g: {} for g in genera}
        self.len_sourced = set()
        self.notes = []
        self.narrow = []
        cdir = os.path.join(data_dir, 'characters')
        groups = {}
        for fn in sorted(os.listdir(cdir)) if os.path.isdir(cdir) else []:
            if fn.endswith('.json') and fn not in ('curation.json', 'fossils.json'):
                with open(os.path.join(cdir, fn), encoding='utf-8') as f:
                    groups[fn] = json.load(f)
        self.groups = groups
        curation = []
        cpath = os.path.join(cdir, 'curation.json')
        if os.path.exists(cpath):
            with open(cpath, encoding='utf-8') as f:
                curation = json.load(f)['adjustments']
        self.curation = curation

        # --- collect extra characters (union of declared states) ---
        extras = {}
        for fn, d in groups.items():
            for g, gd in d['genera'].items():
                for k, x in gd.get('extra_characters', {}).items():
                    st = [str(s) for s in x['possible_states']]
                    if k in extras:
                        for s in st:
                            if s not in extras[k][0]:
                                extras[k][0].append(s)
                    else:
                        extras[k] = (st, x.get('notes', '') or k.replace('_', ' '))
        self.chars.append(('realm', REALMS, 'biogeographic realm of origin (native range, MDD v2.5)', 'geo'))
        for k, st, desc in STANDARD:
            self.chars.append((k, st, desc, 'std'))
        for k in sorted(extras):
            self.chars.append((k, extras[k][0], k.replace('_', ' '), 'extra'))
        countries = sorted({c.strip().rstrip('?').strip() for r in mdd_rows
                            for c in r['countryDistribution'].split('|') if c.strip()})
        self.chars.append(('country', countries, 'country of origin (native range, MDD v2.5)', 'geo'))
        self.char_index = {c[0]: i for i, c in enumerate(self.chars)}

        # --- geography from MDD ---
        for r in mdd_rows:
            g = r['genus']
            for fld, key in (('biogeographicRealm', 'realm'), ('countryDistribution', 'country')):
                states = self.chars[self.char_index[key]][1]
                for v in r[fld].split('|'):
                    v = v.strip().rstrip('?').strip()
                    if v:
                        self.profiles[g].setdefault(key, set()).add(states.index(v))

        # --- morphology from the research files ---
        for fn, d in groups.items():
            for g, gd in d['genera'].items():
                assert g in self.profiles, f'{fn}: unknown genus {g}'
                for k, x in gd.get('characters', {}).items():
                    if k == 'hb_length_mm':
                        st = x.get('states')
                        if isinstance(st, dict) and x.get('scope') != 'partial':
                            lo, hi = int(st['min']), int(st['max'])
                            if g in self.len_sourced:          # several sources: take the union
                                lo, hi = min(lo, self.length[g][0]), max(hi, self.length[g][1])
                            self.length[g] = (lo, hi)
                            self.len_sourced.add(g)
                            self.evidence[g][k] = self.evidence[g].get(k, []) + x.get('evidence', [])
                        elif isinstance(st, dict):
                            self.notes.append(f'{g}: length range covers only some species; treated as unknown')
                        continue
                    self._set(g, k, x, fn)
                for k, x in gd.get('extra_characters', {}).items():
                    self._set(g, k, x, fn)
        for adj in curation:
            k = adj['character']
            targets = genera if adj['genus'] == '*' else [adj['genus']]
            for g in targets:
                if k == 'hb_length_mm':
                    self.length[g] = (adj['states']['min'], adj['states']['max'])
                else:
                    states = self.chars[self.char_index[k]][1]
                    self.profiles[g][k] = (set(range(len(states))) if adj['states'] == 'all'
                                           else {states.index(str(s)) for s in adj['states']})
                self.evidence[g][k] = self.evidence[g].get(k, []) + [{'curation': adj['reason']}]
        # unknown = every state
        for g in genera:
            for k, st, _, _ in self.chars:
                if not self.profiles[g].get(k):
                    self.profiles[g][k] = set(range(len(st)))

    def _set(self, g, k, x, fn):
        if k not in self.char_index:
            return
        states_all = self.chars[self.char_index[k]][1]
        st = x.get('states')
        if st == 'unknown' or st is None or not isinstance(st, list) or not st:
            return
        if x.get('scope') == 'partial' and len(set(map(str, st))) < len(states_all):
            self.notes.append(f'{g}.{k}: sources cover only some species; treated as unknown')
            return
        idx = set()
        for s in st:
            s = str(s)
            assert s in states_all, f'{fn}: {g}.{k} has undeclared state {s}'
            idx.add(states_all.index(s))
        # several sources for the same character: union of their states
        self.profiles[g][k] = self.profiles[g].get(k, set()) | idx
        self.evidence[g][k] = self.evidence[g].get(k, []) + x.get('evidence', [])

    # ------------------------------------------------------------- key

    def build_key(self):
        """Greedy: at each node pick the couplet that shrinks both sides most.
        Genera the couplet does not decide (variable or undocumented) are sent
        down both branches; a couplet is only used if each side loses at least
        one genus, so the recursion terminates."""
        order = [c[0] for c in self.chars]

        def full(g, k):
            return len(self.profiles[g][k]) == len(self.chars[self.char_index[k]][1])

        def evaluate(S, yes, no):
            both = [g for g in S if g not in yes and g not in no]
            if not yes or not no:
                return None
            return (max(len(yes), len(no)) + len(both), len(both), yes + both, no + both)

        def len_candidates(S, strict=True):
            out = []
            for t in sorted({self.length[g][1] for g in S}):
                yes = [g for g in S if self.length[g][1] <= t]
                no = [g for g in S if self.length[g][0] > t]
                if not yes or not no:
                    continue
                gap = min(self.length[g][0] for g in no) - max(self.length[g][1] for g in yes)
                cut = max(self.length[g][1] for g in yes) + gap // 2
                if gap < 1 or (strict and gap < max(MIN_GAP_MM, GAP_FRACTION * cut)):
                    continue
                r = evaluate(S, yes, no)
                if r:
                    out.append((r, ('len', cut)))
            return out

        def state_candidates(S, k):
            informative = [g for g in S if not full(g, k)]
            if not informative:
                return []
            vsets = set()
            for g in informative:
                vsets.add(frozenset(self.profiles[g][k]))
            # connected blocks of states among informative genera
            blocks = []
            for g in informative:
                st = set(self.profiles[g][k])
                merged = [b for b in blocks if b & st]
                blocks = [b for b in blocks if b not in merged] + [st.union(*merged)]
            for b in blocks:
                vsets.add(frozenset(b))
            out = []
            for V in vsets:
                yes = [g for g in S if self.profiles[g][k] <= V]
                no = [g for g in S if not (self.profiles[g][k] & V)]
                r = evaluate(S, yes, no)
                if r:
                    out.append((r, ('state', k, sorted(V))))
            return out

        def build(S):
            if len(S) == 1:
                return ('leaf', S)
            cands = []
            for pri, k in enumerate(order):
                for r, q in state_candidates(S, k):
                    cands.append((r[0], r[1], pri, q, r[2], r[3]))
            for r, q in len_candidates(S):
                cands.append((r[0], r[1], 1.5, q, r[2], r[3]))
            if not cands:
                # last resort: a size couplet with less clearance than the policy wants;
                # still sound for the data, recorded as narrow in docs/KEY.md
                for r, q in len_candidates(S, strict=False):
                    self.narrow.append((q[1], sorted(r[2]), sorted(r[3])))
                    cands.append((r[0], r[1], 1.5, q, r[2], r[3]))
                    break
            if not cands:
                return ('leaf', S)
            cands.sort(key=lambda c: (c[0], c[1], c[2], str(c[3])))
            _, _, _, q, yes, no = cands[0]
            key = lambda g: self.genera.index(g)
            return ('couplet', q, build(sorted(yes, key=key)), build(sorted(no, key=key)))

        return build(list(self.genera))

    # ------------------------------------------------------------- Coq

    def coq_characters(self, header):
        cons = ['C_' + ident(k) for k, *_ in self.chars]
        out = [header.format(src='data/characters/*.json + MDD v2.5 (see docs/KEY.md for citations)')]
        out.append('''
From Coq Require Import List String.
From Sciuridae Require Import Lib.Base Key.Matrix Data.Taxonomy.
Import ListNotations.
Local Open Scope string_scope.

(* The characters of the identification matrix.  [realm] and [country] are
   the specimen's place of origin (native range); the others are external,
   cranial or dental characters taken from the sources cited in docs/KEY.md. *)
''')
        out.append('Inductive Character : Type :=')
        out += [f'| {c}' for c in cons]
        out[-1] += '.'
        out.append('')
        out.append('Definition character_index (c : Character) : nat :=\n  match c with')
        out += [f'  | {c} => {i}' for i, c in enumerate(cons)]
        out.append('  end.\n')
        out.append('Definition character_table : list Character := [' + '; '.join(cons) + '].\n')
        out.append('Lemma character_table_index : forall x, nth_error character_table (character_index x) = Some x.')
        out.append('Proof. solve_table_index. Qed.\n')
        out.append('Lemma character_indices : map character_index character_table = seq 0 (List.length character_table).')
        out.append('Proof. vm_compute. reflexivity. Qed.\n')
        out.append('#[export] Instance Beq_Character : Beq Character :=\n'
                   '  {| beq := table_beq Character character_index;\n'
                   '     beq_spec := table_beq_spec Character character_index character_table character_table_index |}.\n')
        out.append('#[export] Instance Finite_Character : Finite Character :=\n'
                   '  {| enum := character_table;\n'
                   '     enum_complete := table_complete Character character_index character_table character_table_index;\n'
                   '     enum_nodup := table_nodup Character character_index character_table character_indices |}.\n')
        out.append('Definition character_name (c : Character) : string :=\n  match c with')
        out += [f'  | {c} => {coq_string(k)}' for c, (k, *_) in zip(cons, self.chars)]
        out.append('  end.\n')
        out.append('(* State names; a state is coded by its position in this list. *)')
        out.append('Definition state_names (c : Character) : list string :=\n  match c with')
        out += [f'  | {c} => [' + '; '.join(coq_string(s) for s in st) + ']' for c, (k, st, *_) in zip(cons, self.chars)]
        out.append('  end.\n')
        out.append('Definition nstates (c : Character) : nat := List.length (state_names c).\n')
        out.append('(* Genus profiles: every documented state of every character, and the')
        out.append('   adult head-and-body length range in mm ([0, 2000] when unsourced). *)')
        out.append('Definition genus_profile (g : Genus) : profile Character :=\n  match g with')
        for g in self.genera:
            lo, hi = self.length[g]
            rows = []
            for k, st, *_ in self.chars:
                rows.append('[' + '; '.join(str(i) for i in sorted(self.profiles[g][k])) + ']')
            tbl = '; '.join(rows)
            out.append(f'  | {g} => {{| p_min := {lo}; p_max := {hi};\n'
                       f'      p_states := fun c => nth (character_index c) [{tbl}] [] |}}')
        out.append('  end.\n')
        return '\n'.join(out), cons

    def coq_key(self, key, header, cons):
        cmap = {k: c for (k, *_), c in zip(self.chars, cons)}

        def emit(node, depth):
            pad = '  ' * depth
            if node[0] == 'leaf':
                return f'{pad}(Leaf [' + '; '.join(node[1]) + '])'
            q = node[1]
            if q[0] == 'len':
                qs = f'(LenAtMost {q[1]})'
            else:
                qs = f'(StateIn {cmap[q[1]]} [' + '; '.join(map(str, q[2])) + '])'
            return f'{pad}(Couplet {qs}\n' + emit(node[2], depth + 1) + '\n' + emit(node[3], depth + 1) + ')'

        out = [header.format(src='built by tools/gen_characters.py from Data/Characters.v profiles')]
        out.append('''
From Coq Require Import List.
From Sciuridae Require Import Lib.Base Key.Key Key.Matrix Data.Taxonomy Data.Characters.
Import ListNotations.

(* A dichotomous key to the genera.  It was produced by a greedy builder, but
   nothing about it is trusted: Identification.v checks it against the
   profiles. *)
Definition genus_key : @key Genus (question Character) :=
''')
        out.append(emit(key, 1) + '.')
        return '\n'.join(out) + '\n'

    # ------------------------------------------------------------- docs

    def render_key(self, key):
        lines, counter = [], [0]
        names = {k: (st, desc) for k, st, desc, _ in self.chars}

        def label(node):
            return node[1][0] if node[0] == 'leaf' and len(node[1]) == 1 else None

        def describe(q, yes):
            if q[0] == 'len':
                return (f'head-and-body length at most {q[1]} mm' if yes
                        else f'head-and-body length more than {q[1]} mm')
            st, desc = names[q[1]]
            used = set().union(*(self.profiles[g][q[1]] for g in self.genera))
            idx = q[2] if yes else [i for i in range(len(st)) if i not in q[2]]
            chosen = [st[i] for i in idx if i in used]
            if q[1] == 'country' and not yes:
                return f'{desc}: any other country'
            return f'{desc}: ' + ' or '.join(chosen)

        def walk(node):
            counter[0] += 1
            n = counter[0]
            entry = {'n': n}
            lines.append(entry)
            q = node[1]
            for side, child in (('a', node[2]), ('b', node[3])):
                tgt = label(child)
                if tgt is None and child[0] == 'leaf':
                    tgt = ' / '.join(child[1]) + ' (not separated)'
                entry[side] = (describe(q, side == 'a'), tgt if tgt else walk(child))
            return n

        if key[0] == 'couplet':
            walk(key)
        md = []
        for e in sorted(lines, key=lambda e: e['n']):
            for side in ('a', 'b'):
                text, tgt = e[side]
                dest = f'*{tgt}*' if isinstance(tgt, str) else f'go to {tgt}'
                md.append(f'{e["n"]}{side}. {text} ... {dest}')
            md.append('')
        return '\n'.join(md)


def generate(data_dir, genera, mdd_rows, header):
    m = Matrix(data_dir, genera, mdd_rows)
    if not m.groups:
        return []
    key = m.build_key()
    chars_v, cons = m.coq_characters(header)
    key_v = m.coq_key(key, header, cons)
    docs = os.path.join(os.path.dirname(data_dir), 'docs')
    os.makedirs(docs, exist_ok=True)
    with open(os.path.join(docs, 'KEY.md'), 'w', encoding='utf-8') as f:
        f.write(render_doc(m, key))
    return [('Characters.v', chars_v), ('GenusKey.v', key_v)]


def render_doc(m, key):
    out = ['# Key to the genera of Sciuridae', '',
           'Generated by `tools/gen_characters.py`; the same key is `genus_key` in',
           '`theories/Data/GenusKey.v`. `theories/Identification.v` proves that it returns',
           'exactly the genera whose profiles (below) are consistent with an observation,',
           'for every observation, and that a complete observation fits at most one genus.', '',
           'Use it with an adult specimen from its native range. "Realm" and "country"',
           'are where the specimen originates (MDD v2.5 native ranges). A genus that varies in',
           'a character, or whose state is undocumented, keys out on both sides of that couplet.', '',
           '## Key', '', m.render_key(key), '',
           '## Genus profiles and sources', '',
           'Only informative characters are listed (a character not listed admits every state,',
           'usually because no source documents it). Lengths are adult head-and-body, mm.', '']
    for g in m.genera:
        out.append(f'### {g}')
        lo, hi = m.length[g]
        lines = []
        lines.append(f'- **head-and-body length**: ' + (f'{lo}-{hi} mm' if (lo, hi) != LEN_UNKNOWN else 'not sourced')
                     + cite(m.evidence[g].get('hb_length_mm', [])))
        for k, st, desc, kind in m.chars:
            if kind == 'geo':
                continue
            v = m.profiles[g][k]
            if len(v) == len(st):
                continue
            lines.append(f'- **{k.replace("_", " ")}**: ' + ' or '.join(st[i] for i in sorted(v))
                         + cite(m.evidence[g].get(k, [])))
        out += lines + ['']
    if m.narrow:
        out += ['## Size couplets with little clearance', '',
                'These couplets separate genera whose documented size ranges barely miss each other;',
                'they are correct for the data but sensitive to undocumented variation.', '']
        out += [f'- at {t} mm: {", ".join(a)} versus {", ".join(b)}' for t, a, b in m.narrow] + ['']
    out += ['## Coding notes', '']
    out += [f'- {n}' for n in sorted(set(m.notes))] or ['- none']
    return '\n'.join(out) + '\n'


def cite(evidence, limit=3):
    seen, parts = set(), []
    for e in evidence:
        if 'curation' in e:
            label = 'curation: ' + e['curation']
            if label not in seen:
                seen.add(label)
                parts.append(label)
            continue
        c = (e.get('citation') or '').strip()
        short = c.split(',')[0][:60] if c else ''
        key = (short, e.get('url'))
        if not short or key in seen:
            continue
        seen.add(key)
        parts.append(f'[{short}]({e["url"]})' if e.get('url') else short)
    if not parts:
        return ''
    more = '' if len(parts) <= limit else f' (+{len(parts) - limit} more in data/characters)'
    return ' — ' + '; '.join(parts[:limit]) + more
