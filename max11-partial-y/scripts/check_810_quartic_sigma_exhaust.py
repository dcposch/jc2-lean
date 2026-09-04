#!/usr/bin/env python3
"""Structural + semantic self-check of the emitted File A exhaust.

    python3 scripts/check_810_quartic_sigma_exhaust.py \
        Grok810ScaleZeroQuarticSigmaLadderScratch.lean

Checks, all without Lean:

1. `section`/`end` balance and no duplicate declaration names;
2. every `rcases lt_trichotomy` node has exactly three `·` bullets, and every
   hypothesis name a leaf mentions is bound on its own root-to-leaf path
   (and no name is introduced twice on one path);
3. every leaf applies a constructor that the `inductive` actually declares,
   with exactly as many `⟨…⟩` components as the cone definition has conjuncts,
   `Or.inl h_z` exactly for the dead letters and `Or.inr …` for the live ones;
4. **every arithmetic obligation** (each direct hypothesis reference and each
   `by omega`) is implied over ℚ by the branch hypotheses of its path together
   with `QuarticRatioConeA810` and `natDegree ≥ 0`, decided exactly by
   Fourier–Motzkin with a greedy elimination order.  `omega` is complete for
   linear integer arithmetic, so a ℚ-implication is enough.
"""
import re, sys, itertools
from fractions import Fraction as Fr
LET="ABCDEFG"; SIG="BCDEFG"; W={"B":3,"C":4,"D":5,"E":6,"F":7,"G":8}
lines=open(sys.argv[1]).read().split("\n")
STRUCT_PROBLEMS=None

# --------------------------------------------------------- structural checks

def structural(lines):
    import collections
    problems = 0
    stack = []
    for i, ln in enumerate(lines, 1):
        m = re.match(r"^(section|namespace)\s+(\S+)\s*$", ln)
        if m:
            stack.append((m.group(2), i)); continue
        m = re.match(r"^end\s+(\S+)\s*$", ln)
        if m:
            if not stack or stack[-1][0] != m.group(1):
                print(f"SECTION MISMATCH line {i}: end {m.group(1)}"); problems += 1
            elif stack: stack.pop()
            continue
        if re.match(r"^(noncomputable )?section\s*$", ln): stack.append((None, i))
        elif re.match(r"^end\s*$", ln) and stack: stack.pop()
    open_named = [s for s in stack if s[0] is not None]
    if open_named:
        print("UNCLOSED NAMED SECTIONS:", open_named); problems += 1
    names = collections.Counter()
    for ln in lines:
        m = re.match(r"^(?:private |protected )?(theorem|lemma|def|abbrev|inductive|structure)\s+([^\s(:{]+)", ln)
        if m: names[m.group(2)] += 1
    dups = {k: v for k, v in names.items() if v > 1}
    if dups:
        print("DUPLICATE DECLARATIONS:", dups); problems += 1
    print(f"declarations {sum(names.values())}, duplicates {len(dups)}, "
          f"unclosed anonymous sections {len(stack) - len(open_named)}")
    # three bullets per rcases
    nodes = 0
    for i, ln in enumerate(lines):
        if not ln.strip().startswith("rcases lt_trichotomy"): continue
        nodes += 1
        ind = len(ln) - len(ln.lstrip()); cnt = 0; j = i + 1
        while j < len(lines) and lines[j].strip():
            i2 = len(lines[j]) - len(lines[j].lstrip())
            if i2 < ind: break
            if i2 == ind:
                if lines[j].strip().startswith("· "): cnt += 1
                else: break
            j += 1
        if cnt != 3:
            print(f"BAD BULLET COUNT at line {i+1}: {cnt}"); problems += 1
    print(f"rcases nodes {nodes}")
    # hypothesis names bound on their path, none introduced twice per path
    for i, ln in enumerate(lines):
        if not ln.startswith("theorem quarticSigmaSupportCone810_of_live_"): continue
        name = ln.split()[1]; j = i
        while not lines[j].rstrip().endswith(":= by"): j += 1
        bound = set(re.findall(r"\((h[A-Za-z0-9]*) :", "\n".join(lines[i:j])))
        bound |= {"hA", "hApos", "hAB", "hAC", "hAD", "hAE", "hAF", "hAG"}
        j += 1
        path = []
        while j < len(lines) and lines[j].strip():
            s = lines[j].strip(); ind = len(lines[j]) - len(lines[j].lstrip())
            m = re.match(r"rcases lt_trichotomy \(.*\) \(.*\) with (\S+) \| (\S+) \| (\S+)$", s)
            if m:
                path = [(d, n) for (d, n) in path if d < ind]
                for n in m.groups():
                    if n in {n2 for _, n2 in path}:
                        print(f"DUP HYP {name}: {n}"); problems += 1
                    path.append((ind, n))
            else:
                if s.startswith("· "): path = [(d, n) for (d, n) in path if d <= ind]
                term = s[2:] if s.startswith("· ") else s
                if term.startswith("exact QuarticSigmaSupportCone810."):
                    k = j + 1; full = term
                    while full.count("⟨") > full.count("⟩"):
                        full += " " + lines[k].strip(); k += 1
                    if full.count("(") != full.count(")"):
                        print(f"UNBALANCED PARENS {name}"); problems += 1
                    avail = bound | {n for _, n in path}
                    for h in re.findall(r"\b(h[A-Za-z0-9]+)\b", full):
                        if h not in avail:
                            print(f"UNBOUND {name}: {h}"); problems += 1
            j += 1
    print(f"structural problems: {problems}")
    return problems


STRUCT_PROBLEMS=structural(lines)

DEF_RE=re.compile(r"^def (QuarticSigmaCone([A-G]+)810'|QuarticLoadSigmaCone([A-G]+)810|QuarticMixedSigmaCone([A-G]{2})810) \(A B C D E F G : k\[X\]\) : Prop :=$")
cones={}
for i,ln in enumerate(lines):
    m=DEF_RE.match(ln)
    if not m: continue
    body=[]; j=i+1
    while j<len(lines) and lines[j].strip(): body.append(lines[j].strip()); j+=1
    cones[m.group(1)]=[f.strip() for f in re.sub(r"\s+"," "," ".join(body)).split("∧")]
CT={}
inind=False
for ln in lines:
    if ln.startswith("inductive QuarticSigmaSupportCone810"): inind=True; continue
    if inind:
        if not ln.strip(): break
        m=re.match(r"\s+\| (\w+) : (\S+) A B C D E F G →", ln)
        if m: CT[m.group(1)]=m.group(2)

def lin(expr):
    v=[Fr(0)]*7
    for term in expr.split("+"):
        term=term.strip()
        m=re.match(r"^(?:(\d+) \* )?([A-G])\.natDegree$", term)
        assert m, term
        v[LET.index(m.group(2))]+=Fr(int(m.group(1) or 1))
    return v
def sub(u,v): return [x-y for x,y in zip(u,v)]
def neg(u): return [-x for x in u]

CONEA=[(sub([Fr(0)]*7, lin("A.natDegree")), True)]
for expr,rhs in [("2 * B.natDegree","3 * A.natDegree"),("C.natDegree","2 * A.natDegree"),
                 ("2 * D.natDegree","5 * A.natDegree"),("E.natDegree","3 * A.natDegree"),
                 ("2 * F.natDegree","7 * A.natDegree"),("G.natDegree","4 * A.natDegree")]:
    CONEA.append((sub(lin(expr),lin(rhs)), True))
NONNEG=[(neg([Fr(1) if i==k else Fr(0) for i in range(7)]),False) for k in range(7)]

def infeasible(cons):
    cons=[(list(v),s) for v,s in cons]
    left=list(range(7))
    for _ in range(7):
        # greedy: eliminate the variable with the fewest resolvent products
        best=None
        for kk in left:
            np_=sum(1 for v,_ in cons if v[kk]>0); nn=sum(1 for v,_ in cons if v[kk]<0)
            sc=np_*nn-(np_+nn)
            if best is None or sc<best[0]: best=(sc,kk)
        k=best[1]; left.remove(k)
        pos=[];negs=[];zero=[]
        for v,s in cons:
            if v[k]>0: pos.append((v,s))
            elif v[k]<0: negs.append((v,s))
            else: zero.append((v,s))
        new=list(zero)
        for (p,sp) in pos:
            for (q,sq) in negs:
                a=p[k]; b=-q[k]
                comb=[b*p[i]+a*q[i] for i in range(7)]
                new.append((comb, sp or sq))
        cons=[]
        seen=set()
        for v,s in new:
            key=(tuple(v),s)
            if key in seen: continue
            seen.add(key); cons.append((v,s))
        if len(cons)>60000: return None   # give up
    for v,s in cons:
        if all(x==0 for x in v) and s: return True
    return False

MEMO={}
def implies(cons, lhs, op, rhs):
    L,R=lin(lhs),lin(rhs)
    if op=="<":   tests=[[(sub(R,L),False)]]
    elif op=="≤": tests=[[(sub(R,L),True)]]
    else:         tests=[[(sub(L,R),True)],[(sub(R,L),True)]]
    key=(frozenset((tuple(v),s) for v,s in cons), lhs, op, rhs)
    if key in MEMO: return MEMO[key]
    for extra in tests:
        r=infeasible(cons+extra)
        if r is not True:
            MEMO[key]=r; return r
    MEMO[key]=True
    return True

# walk the emitted trees
def parse_block(body):
    ind0=body[0][0]; head=body[0][1]
    m=re.match(r"rcases lt_trichotomy \((.*)\) \((.*)\) with (\S+) \| (\S+) \| (\S+)$", head)
    if m:
        subs=[];cur=None
        for (ind,txt) in body[1:]:
            if ind==ind0 and txt.startswith("· "):
                if cur is not None: subs.append(cur)
                rest=txt[2:]
                cur=[(ind+2,rest)] if not rest.startswith("--") else []
            else: cur.append((ind,txt))
        subs.append(cur)
        return ("node",m.group(1),m.group(2),[parse_block(s) for s in subs])
    joined=" ".join(t for _,t in body)
    m=re.match(r"exact QuarticSigmaSupportCone810\.(\w+) ⟨(.*)⟩$", joined)
    assert m, joined[:100]
    return ("leaf", m.group(1), [p.strip() for p in m.group(2).split(",")])

blocks={}
i=0
while i<len(lines):
    if lines[i].startswith("theorem quarticSigmaSupportCone810_of_live_"):
        name=lines[i].split()[1]; j=i
        while not lines[j].rstrip().endswith(":= by"): j+=1
        j+=2
        body=[]
        while j<len(lines) and lines[j].strip():
            body.append((len(lines[j])-len(lines[j].lstrip()),lines[j].strip())); j+=1
        blocks[name]=parse_block(body); i=j
    else: i+=1

nleaf=0; nfield=0; failures=[]; giveups=0
def walk(t, cons, live, dead):
    global nleaf,nfield,giveups
    if t[0]=="node":
        L,R=t[1],t[2]
        walk(t[3][0], cons+[(sub(lin(L),lin(R)),True)], live, dead)
        walk(t[3][1], cons+[(sub(lin(L),lin(R)),False),(sub(lin(R),lin(L)),False)], live, dead)
        walk(t[3][2], cons+[(sub(lin(R),lin(L)),True)], live, dead)
        return
    nleaf+=1
    fields=cones[CT[t[1]]]
    assert len(fields)==len(t[2]), (t[1],len(fields),len(t[2]))
    for fld,term in zip(fields,t[2]):
        f=fld.strip()
        if f.startswith("QuarticRatioConeA810"):
            assert term=="hA"; continue
        m=re.match(r"^([A-G]) ≠ 0$", f)
        if m:
            assert m.group(1) in live and term=="h"+m.group(1)+"ne", (f,term); continue
        m=re.match(r"^\(([A-G]) = 0 ∨ (.*)\)$", f)
        if m:
            ch,ineq=m.group(1),m.group(2)
            if ch in dead:
                assert term=="Or.inl h"+ch+"z", (f,term); continue
            assert term.startswith("Or.inr "), (f,term)
            f=ineq
        m=re.match(r"^(.*?) (<|=|≤) (.*)$", f)
        nfield+=1
        r=implies(cons,m.group(1),m.group(2),m.group(3))
        if r is None: giveups+=1
        elif not r: failures.append((t[1],f,len(cons)))

for mask in range(1,64):
    live=[ch for i,ch in enumerate(SIG) if mask>>(5-i)&1]
    dead=[ch for ch in SIG if ch not in live]
    name="quarticSigmaSupportCone810_of_live_"+"".join(live)
    walk(blocks[name], list(CONEA)+list(NONNEG), set(live), set(dead))
    print(f"  mask {name[-6:]:>6}: leaves {nleaf}, obligations {nfield}, "
          f"fails {len(failures)}, giveups {giveups}", flush=True)
print(f"leaves checked {nleaf}, arithmetic obligations {nfield}, FM give-ups {giveups}")
print(f"UNPROVABLE obligations: {len(failures)}")
for f in failures[:10]: print("  ", f)
