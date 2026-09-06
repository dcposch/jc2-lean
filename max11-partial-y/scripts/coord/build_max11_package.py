#!/usr/bin/env python3
"""Assemble ONE self-contained Lake package for the Max-11 Palomar submission.

Copies the transitive import closure of the headline module (and the
challenge module) out of max11-partial-y (tracked modules only) and the
sibling gcd3-69-composition package into a fresh directory, and writes a
lakefile with every module as a lib root (the Comparator sandbox only lets
the root package's own .lake be written, so sibling srcDir libs are out).

The package is also checked against the mechanical requirements in
PalomarPolicy/CONTRIBUTING.md before it is declared good:

  * §2 expected file set, incl. exactly one conventional licence file at the
    package root (CONTRIBUTING.md:316-323).  The licence lives at the git
    root of this monorepo, not in max11-partial-y, so it has to be searched
    for and copied explicitly.
  * §2.1 a committed lake-manifest.json whose top-level `name` matches the
    generated lakefile's package name.  The generated lakefile has a *git*
    require on mathlib, so the "TOML project without a manifest" exception of
    §6.3 (contained path dependencies only) does not apply and the manifest
    is mandatory.
  * §2.1/§4 every git package pinned to a full 40-char lowercase SHA on a
    credential-free public https://github.com/owner/repo URL.
  * §2.2 Challenge size caps (100 KiB / 1000 lines hard, 32 KiB / 300 lines
    warning).
  * §2.3 comparator.json: one JSON object, <= 1 MiB, four required keys,
    permitted_axioms a subset of the standard trio, and its challenge/solution
    modules equal to the ones this package actually builds.
  * §3 formalization.yaml <= 256 KiB, UTF-8, and its project.license equal to
    the SPDX identifier of the licence file.
  * §2 the package tree <= 500 MiB and free of compiled-artifact suffixes.

Hard failures exit non-zero; warnings are printed and do not.
"""
import argparse, json, os, re, shutil, subprocess, sys
ap = argparse.ArgumentParser()
ap.add_argument('--src', required=True); ap.add_argument('--comp', required=True)
ap.add_argument('--out', required=True)
ap.add_argument('--headline', default='Max11Assembly'); ap.add_argument('--challenge', default='Max11Challenge')
ap.add_argument('--name', default='jc2_max11')
ap.add_argument('--licence', default=None,
                help='path to the licence file to copy; default: search --src then the git root')
ap.add_argument('--check-only', action='store_true',
                help='run the CONTRIBUTING.md checks against an existing --out and exit')
a = ap.parse_args()
src, comp, out = map(os.path.abspath, (a.src, a.comp, a.out))

PROBLEMS = []; WARNINGS = []
def bad(msg): PROBLEMS.append(msg)
def warn(msg): WARNINGS.append(msg)

# ---------------------------------------------------------------- licence
# CONTRIBUTING.md:316-323 -- exactly one conventional licence file at the
# repository root, case-insensitive, optionally suffixed .md/.markdown/.txt.
LICENCE_STEMS = ('license', 'licence', 'copying', 'unlicense', 'ofl')
LICENCE_SUFFIXES = ('', '.md', '.markdown', '.txt')
def licence_candidates(d):
    try: entries = os.listdir(d)
    except OSError: return []
    hits = []
    for e in entries:
        low = e.lower()
        for stem in LICENCE_STEMS:
            if any(low == stem + suf for suf in LICENCE_SUFFIXES):
                p = os.path.join(d, e)
                if os.path.isfile(p) and not os.path.islink(p): hits.append(p)
    return hits
def git_root(d):
    try:
        return subprocess.check_output(['git','-C',d,'rev-parse','--show-toplevel']).decode().strip()
    except Exception:
        return None
def find_licence():
    if a.licence:
        if not os.path.isfile(a.licence): bad(f'--licence {a.licence} is not a regular file')
        return a.licence
    for d in [src, git_root(src)]:
        if not d: continue
        hits = licence_candidates(d)
        if len(hits) > 1:
            bad(f'{d} contains {len(hits)} conventional licence files: {sorted(hits)}; '
                'CONTRIBUTING.md:316 requires exactly one -- pass --licence')
            return None
        if hits: return hits[0]
    bad('no conventional licence file found in --src or its git root; CONTRIBUTING.md:316 '
        'requires exactly one (LICENSE/LICENCE/COPYING/UNLICENSE/OFL, optionally .md/.markdown/.txt)')
    return None

# Deliberately conservative: recognise only the licences this project might
# plausibly ship, and refuse to guess.  Palomar runs a real SPDX detector; this
# check only catches the mismatch between the licence file and
# formalization.yaml's project.license before submission.
SPDX_MARKERS = (
    ('Apache-2.0', ('Apache License', 'Version 2.0, January 2004')),
    ('MIT',        ('Permission is hereby granted, free of charge',)),
    ('BSD-3-Clause', ('Redistributions in binary form must reproduce',
                      'Neither the name of the copyright holder')),
    ('CC0-1.0',    ('CC0 1.0 Universal',)),
)
def spdx_of(path):
    try: txt = open(path, encoding='utf-8').read()
    except (OSError, UnicodeDecodeError) as e:
        bad(f'licence file {path} is not readable UTF-8: {e}'); return None
    if not txt.strip(): bad(f'licence file {path} is empty'); return None
    if len(txt.encode()) > 1024**2: bad(f'licence file {path} exceeds 1 MiB')
    found = [spdx for spdx, marks in SPDX_MARKERS if all(m in txt for m in marks)]
    if len(found) != 1:
        warn(f'could not identify a unique SPDX id in {path} (matched {found or "nothing"}); '
             'Palomar runs its own detector -- verify project.license by hand')
        return None
    return found[0]

# ---------------------------------------------------------------- closure
tracked = set(l for l in subprocess.check_output(['git','-C',src,'ls-files','*.lean']).decode().split() if '/' not in l)
IMP = re.compile(r'^import\s+([A-Za-z0-9_.]+)\s*$', re.M)
def locate(m):
    p = os.path.join(src, m + '.lean')
    if m + '.lean' in tracked and os.path.exists(p): return p, 'src'
    p2 = os.path.join(comp, m + '.lean')
    if os.path.exists(p2): return p2, 'comp'
    if os.path.exists(p): return p, 'src-untracked'
    return None, None
seen = {}
stack = [a.headline, a.challenge]
while stack:
    m = stack.pop()
    if m in seen: continue
    p, where = locate(m)
    if p is None: print('MISSING module', m, file=sys.stderr); sys.exit(1)
    seen[m] = (p, where)
    for d in IMP.findall(open(p).read()):
        if not d.startswith('Mathlib'): stack.append(d)
untracked = [m for m,(p,w) in seen.items() if w == 'src-untracked']
if untracked: print('UNTRACKED modules in closure:', untracked, file=sys.stderr); sys.exit(1)

licence_src = find_licence()

# ---------------------------------------------------------------- emit
if not a.check_only:
    if os.path.exists(out): shutil.rmtree(out)
    os.makedirs(out)
    for m,(p,w) in seen.items(): shutil.copy2(p, os.path.join(out, m + '.lean'))
    for f in ('lean-toolchain','comparator.json','formalization.yaml','README.md'):
        if os.path.exists(os.path.join(src,f)): shutil.copy2(os.path.join(src,f), os.path.join(out,f))
    if licence_src:
        # keep the licence's own conventional basename
        shutil.copy2(licence_src, os.path.join(out, os.path.basename(licence_src)))

    mods = sorted(m for m in seen if m != a.challenge)
    mani = json.load(open(os.path.join(src,'lake-manifest.json')))
    mathlib = next(p for p in mani['packages'] if p['name']=='mathlib')
    lk = [f'name = "{a.name}"', 'version = "0.1.0"', f'defaultTargets = ["{a.challenge}", "{a.headline}"]', '',
          '[[require]]', 'name = "mathlib"', f'git = "{mathlib["url"]}"', f'rev = "{mathlib["rev"]}"', '',
          '[[lean_lib]]', f'name = "{a.challenge}"', f'roots = ["{a.challenge}"]', '',
          '[[lean_lib]]', f'name = "{a.headline}"', 'roots = [']
    lk += [f'  "{m}",' for m in mods] + [']', '']
    open(os.path.join(out,'lakefile.toml'),'w').write('\n'.join(lk))

    # The generated lakefile renames the root package, so the manifest cannot be
    # copied byte-for-byte: Lake matches its top-level `name` against the
    # lakefile's.  Everything else (the pinned dependency set, including
    # mathlib's own transitive packages) is carried over unchanged.
    mani['name'] = a.name
    with open(os.path.join(out,'lake-manifest.json'),'w') as fh:
        json.dump(mani, fh, indent=2); fh.write('\n')
else:
    mods = sorted(m for m in seen if m != a.challenge)

# ---------------------------------------------------------------- checks
def size(p): return os.path.getsize(p) if os.path.exists(p) else None

# §2 expected file set
for f in ('lean-toolchain','lakefile.toml','lake-manifest.json','formalization.yaml','comparator.json'):
    if not os.path.exists(os.path.join(out,f)): bad(f'missing required file {f} (CONTRIBUTING.md:102-111)')
if not licence_candidates(out): bad('package root has no conventional licence file (CONTRIBUTING.md:316)')
elif len(licence_candidates(out)) > 1: bad('package root has more than one conventional licence file')

# §2.1 toolchain
tc_p = os.path.join(out,'lean-toolchain')
if os.path.exists(tc_p):
    tc = open(tc_p).read().strip()
    if not re.fullmatch(r'leanprover/lean4:v\d+\.\d+\.\d+(-rc\d+)?', tc):
        bad(f'lean-toolchain {tc!r} does not match Palomar\'s TOOLCHAIN_RE (verify_submission.py:84-90)')

# §2.1 lakefile size
lf = size(os.path.join(out,'lakefile.toml'))
if lf and lf > 1024**2: bad(f'lakefile.toml is {lf} B, over the 1 MiB cap (CONTRIBUTING.md:176)')

# §2.1/§4 manifest
mp = os.path.join(out,'lake-manifest.json')
if os.path.exists(mp):
    mj = json.load(open(mp))
    if mj.get('name') != a.name:
        bad(f'lake-manifest.json name {mj.get("name")!r} != lakefile name {a.name!r}')
    URL_RE = re.compile(r'^https://github\.com/[^/?#]+/[^/?#]+$')
    for pkg in mj.get('packages', []):
        if pkg.get('type') != 'git': continue
        if not URL_RE.match(pkg.get('url','')):
            bad(f'package {pkg.get("name")}: url {pkg.get("url")!r} is not a credential-free '
                'public https://github.com/owner/repo URL (CONTRIBUTING.md:286)')
        if not re.fullmatch(r'[0-9a-f]{40}', pkg.get('rev','') or ''):
            bad(f'package {pkg.get("name")}: rev {pkg.get("rev")!r} is not a full 40-char lowercase SHA')

# §2.2 Challenge caps
cp = os.path.join(out, a.challenge + '.lean')
if os.path.exists(cp):
    b = size(cp); l = sum(1 for _ in open(cp, encoding='utf-8', errors='replace'))
    if b > 100*1024 or l > 1000: bad(f'{a.challenge}.lean is {b} B / {l} lines, over the 100 KiB / 1000-line cap')
    elif b > 32*1024 or l > 300: warn(f'{a.challenge}.lean is {b} B / {l} lines -- Palomar issues a mechanical warning over 32 KiB / 300 lines')

# §2.3 comparator.json
kp = os.path.join(out,'comparator.json')
if os.path.exists(kp):
    if size(kp) > 1024**2: bad('comparator.json is over the 1 MiB cap')
    try: kj = json.load(open(kp))
    except Exception as e: kj = None; bad(f'comparator.json is not valid JSON: {e}')
    if isinstance(kj, dict):
        for k in ('challenge_module','solution_module','theorem_names','permitted_axioms'):
            if k not in kj: bad(f'comparator.json is missing required key {k!r}')
        if kj.get('challenge_module') != a.challenge:
            bad(f'comparator.json challenge_module {kj.get("challenge_module")!r} != --challenge {a.challenge!r}')
        if kj.get('solution_module') != a.headline:
            bad(f'comparator.json solution_module {kj.get("solution_module")!r} != --headline {a.headline!r}')
        TRIO = {'propext','Quot.sound','Classical.choice'}
        extra = set(kj.get('permitted_axioms') or []) - TRIO
        if extra: bad(f'comparator.json permitted_axioms contains {sorted(extra)}; only {sorted(TRIO)} are allowed')
    elif kj is not None: bad('comparator.json must contain one JSON object')

# §3 formalization.yaml
fp = os.path.join(out,'formalization.yaml')
if os.path.exists(fp):
    if size(fp) > 256*1024: bad('formalization.yaml is over the 256 KiB cap')
    try: ytxt = open(fp, encoding='utf-8').read()
    except UnicodeDecodeError as e: ytxt = ''; bad(f'formalization.yaml is not UTF-8: {e}')
    m = re.search(r'^\s{2}license:\s*"?([A-Za-z0-9.\-]+)"?\s*$', ytxt, re.M)
    declared = m.group(1) if m else None
    lic_files = licence_candidates(out)
    detected = spdx_of(lic_files[0]) if lic_files else None
    if declared and detected and declared != detected:
        bad(f'formalization.yaml project.license {declared!r} != licence file SPDX {detected!r} (CONTRIBUTING.md:311)')
    if not declared: warn('could not read project.license out of formalization.yaml -- check by hand')

# §2 repository size and compiled artefacts
BAD_SUFFIX = ('.olean','.ilean','.a','.bc','.dll','.dylib','.o','.obj','.so','.trace')
total = 0
for root, dirs, files in os.walk(out):
    dirs[:] = [d for d in dirs if d != '.lake']
    for f in files:
        p = os.path.join(root,f)
        if os.path.islink(p): continue
        total += os.path.getsize(p)
        if f.endswith(BAD_SUFFIX): bad(f'compiled artefact in package: {os.path.relpath(p,out)} (CONTRIBUTING.md:290-300)')
if total > 500*1024**2: bad(f'package is {total/1024**2:.0f} MiB, over the 500 MiB cap (CONTRIBUTING.md:118)')

# ---------------------------------------------------------------- report
n_src = sum(1 for m,(p,w) in seen.items() if w=='src'); n_comp = sum(1 for m,(p,w) in seen.items() if w=='comp')
print(f'package {out}: {len(seen)} modules ({n_src} from src, {n_comp} from composition); roots={len(mods)}; {total/1024**2:.1f} MiB')
if licence_src: print(f'licence: {licence_src} -> {os.path.basename(licence_src)}')
for w in WARNINGS: print('WARN ', w)
for p in PROBLEMS: print('FAIL ', p, file=sys.stderr)
if PROBLEMS:
    print(f'{len(PROBLEMS)} CONTRIBUTING.md requirement(s) unmet', file=sys.stderr); sys.exit(2)
print('CONTRIBUTING.md mechanical checks: OK' + (f' ({len(WARNINGS)} warning(s))' if WARNINGS else ''))
