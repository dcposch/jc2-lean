#!/usr/bin/env python3
"""Assemble ONE self-contained Lake package for the Max-11 Palomar submission.

Copies the transitive import closure of the headline module (and the
challenge module) out of max11-partial-y (tracked modules only) and the
sibling gcd3-69-composition package into a fresh directory, and writes a
lakefile with every module as a lib root (the Comparator sandbox only lets
the root package's own .lake be written, so sibling srcDir libs are out).
"""
import argparse, json, os, re, shutil, subprocess, sys
ap = argparse.ArgumentParser()
ap.add_argument('--src', required=True); ap.add_argument('--comp', required=True)
ap.add_argument('--out', required=True)
ap.add_argument('--headline', default='Max11Assembly'); ap.add_argument('--challenge', default='Max11Challenge')
ap.add_argument('--name', default='jc2_max11')
a = ap.parse_args()
src, comp, out = map(os.path.abspath, (a.src, a.comp, a.out))
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
bad = [m for m,(p,w) in seen.items() if w == 'src-untracked']
if bad: print('UNTRACKED modules in closure:', bad, file=sys.stderr); sys.exit(1)
if os.path.exists(out): shutil.rmtree(out)
os.makedirs(out)
for m,(p,w) in seen.items(): shutil.copy2(p, os.path.join(out, m + '.lean'))
for f in ('lean-toolchain','lake-manifest.json','comparator.json','formalization.yaml','README.md'):
    if os.path.exists(os.path.join(src,f)): shutil.copy2(os.path.join(src,f), os.path.join(out,f))
mods = sorted(m for m in seen if m != a.challenge)
mani = json.load(open(os.path.join(src,'lake-manifest.json')))
mathlib = next(p for p in mani['packages'] if p['name']=='mathlib')
lk = [f'name = "{a.name}"', 'version = "0.1.0"', f'defaultTargets = ["{a.challenge}", "{a.headline}"]', '',
      '[[require]]', 'name = "mathlib"', f'git = "{mathlib["url"]}"', f'rev = "{mathlib["rev"]}"', '',
      '[[lean_lib]]', f'name = "{a.challenge}"', f'roots = ["{a.challenge}"]', '',
      '[[lean_lib]]', f'name = "{a.headline}"', 'roots = [']
lk += [f'  "{m}",' for m in mods] + [']', '']
open(os.path.join(out,'lakefile.toml'),'w').write('\n'.join(lk))
n_src = sum(1 for m,(p,w) in seen.items() if w=='src'); n_comp = sum(1 for m,(p,w) in seen.items() if w=='comp')
print(f'package {out}: {len(seen)} modules ({n_src} from src, {n_comp} from composition); roots={len(mods)}')
