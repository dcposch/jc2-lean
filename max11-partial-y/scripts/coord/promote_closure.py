#!/usr/bin/env python3
"""List the import closure of scratch modules for promotion into the lakefile roots.
usage: promote_closure.py MODULE [MODULE...]  (run inside max11-partial-y)
Prints: modules in closure not yet lakefile roots; any untracked or non-green modules."""
import re,subprocess,os,sys,hashlib
mods=sys.argv[1:]
tracked=set(l[:-5] for l in subprocess.check_output(['git','ls-files','*.lean']).decode().split() if '/' not in l)
txt=open('lakefile.toml').read()
roots=set(re.findall(r'"([A-Za-z0-9_]+)"', txt))
ver=set()
for r in os.listdir('.max11-lanes/gates'):
    if r.endswith('.receipt'):
        for l in open('.max11-lanes/gates/'+r):
            if l.startswith('VERIFIED_SHA256='): ver.add(l.strip())
IMP=re.compile(r'^import\s+([A-Za-z0-9_.]+)\s*$',re.M)
seen={}; stack=list(mods)
while stack:
    m=stack.pop()
    if m in seen or m.startswith('Mathlib'): continue
    p=m+'.lean'
    if not os.path.exists(p):
        p2='../gcd3-69-composition/'+m+'.lean'
        seen[m]='comp' if os.path.exists(p2) else 'MISSING'; continue
    seen[m]='local'
    stack.extend(IMP.findall(open(p).read()))
local=[m for m,w in seen.items() if w=='local']
untracked=[m for m in local if m not in tracked]
notroot=[m for m in local if m not in roots]
nogreen=[]
for m in local:
    if m.endswith('Scratch'):
        sha=hashlib.sha256(open(m+'.lean','rb').read()).hexdigest()
        if f'VERIFIED_SHA256={sha} FILE={m}.lean' not in ver: nogreen.append(m)
print('closure local modules:',len(local),' composition:',sum(1 for w in seen.values() if w=='comp'),' MISSING:',[m for m,w in seen.items() if w=='MISSING'])
print('UNTRACKED:',untracked)
print('scratch without green receipt at current SHA:',nogreen)
print('NOT YET lakefile roots (%d):'%len(notroot)); print('\n'.join(sorted(notroot)))
