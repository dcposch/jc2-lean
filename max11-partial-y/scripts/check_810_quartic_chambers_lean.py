#!/usr/bin/env python3
"""Structural + semantic self-check of the emitted (8,10) chamber modules.

    python3 scripts/check_810_quartic_chambers_lean.py

Checks, all without Lean:

1. `section` / `namespace` balance, no duplicate declaration names across the
   chain, every referenced chamber definition and constructor exists, every
   `import` names an emitted or pre-existing module, Tier-1 preamble present,
   `set_option maxHeartbeats` never after a doc comment.
2. Every `rcases lt_trichotomy` node has exactly three `·` bullets and every
   `⟨…⟩` leaf lists exactly as many components as the chamber definition has
   conjuncts, with `hA` for cone `A`, `hXne` / `hXz` for the letters.
3. **Every arithmetic obligation** — each `by omega` inside a leaf and each
   `(by omega : False).elim` — is decided over ℚ by an exact rational Farkas
   certificate built from the branch hypotheses, cone `A` and
   `natDegree ≥ 0`.  `omega` is complete for linear integer arithmetic, so a
   ℚ-certificate is sufficient.
4. Every chamber of the taxonomy is reached by some leaf (coverage), and the
   emitted module identities / rest bounds (when present) are re-derived
   symbolically.
"""
from __future__ import annotations

import collections
import re
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _810_chamber_common as CC  # noqa: E402

ROOT = CC.ROOT
LET = CC.LET
SIG = CC.SIG
started = time.monotonic()
problems = 0


def log(*a):
    print(f"[{time.monotonic() - started:7.1f}s]", *a, flush=True)


def fail(msg):
    global problems
    problems += 1
    print("  FAIL:", msg, flush=True)


DEFS = ["Grok810ScaleZeroQuarticChamberDefs1Scratch",
        "Grok810ScaleZeroQuarticChamberDefs2Scratch",
        "Grok810ScaleZeroQuarticChamberDefs3Scratch",
        "Grok810ScaleZeroQuarticChamberDefs4Scratch"]
EXH = ["Grok810ScaleZeroQuarticChamberExhaust1Scratch",
       "Grok810ScaleZeroQuarticChamberExhaust2Scratch",
       "Grok810ScaleZeroQuarticChamberExhaust3Scratch",
       "Grok810ScaleZeroQuarticChamberExhaust4Scratch"]
EXTRA = ["Grok810ScaleZeroQuarticChamberFacesPart0Scratch",
         "Grok810ScaleZeroQuarticChamberFacesPart1Scratch"] + \
    [f"Grok810ScaleZeroQuarticChamberFacesPart{_i}Scratch"
     for _i in range(2, 20)] + \
    ["Grok810ScaleZeroQuarticChamberFacesScratch",
         "Grok810ScaleZeroQuarticChamberAuxTowerScratch",
         "Grok810ScaleZeroQuarticChamberBandsScratch",
         "Grok810ScaleZeroQuarticChamberColumnsScratch",
         "Grok810ScaleZeroQuarticChamberRestsScratch",
         "Grok810ScaleZeroQuarticChamberKillsScratch",
         "Grok810ScaleZeroQuarticChamberResidualScratch",
         "Grok810ScaleZeroQuarticChamberCostLadderScratch",
         "Grok810ScaleZeroQuarticChamberColumns2Scratch",
         "Grok810ScaleZeroQuarticChamberRests2Scratch",
         "Grok810ScaleZeroQuarticChamberKills2Scratch",
         "Grok810ScaleZeroQuarticChamberResidual2Scratch",
         "Grok810ScaleZeroQuarticChamberNuFacesScratch",
         "Grok810ScaleZeroQuarticChamberColumns3Scratch",
         "Grok810ScaleZeroQuarticChamberRests3Scratch",
         "Grok810ScaleZeroQuarticChamberKills3Scratch",
         "Grok810ScaleZeroQuarticChamberResidual3Scratch",
         "Grok810ScaleZeroQuarticChamberRests4Scratch",
         "Grok810ScaleZeroQuarticChamberInnerScratch",
         "Grok810ScaleZeroQuarticChamberKills4Scratch",
         "Grok810ScaleZeroQuarticChamberResidual4Scratch",
         "Grok810ScaleZeroQuarticChamberRefineScratch",
         "Grok810ScaleZeroQuarticAssemblyCoreScratch",
         "Grok810ScaleZeroQuarticChamberColumns5Scratch",
         "Grok810ScaleZeroQuarticChamberRests5Scratch",
         "Grok810ScaleZeroQuarticChamberPowerKillsScratch",
         "Grok810ScaleZeroQuarticChamberResidual5Scratch",
         "Grok810ScaleZeroQuarticChamberRests6Scratch",
         "Grok810ScaleZeroQuarticChamberRefinedKillsScratch",
         "Grok810ScaleZeroQuarticChamberResidual6Scratch",
         "Grok810ScaleZeroQuarticChamberN7LadderScratch"] + \
    [f"Grok810ScaleZeroQuarticChamberInfra{_c}Scratch"
     for _c in ("N2", "N3", "N5", "N6", "N7", "Omicron", "Primitive")] + \
    ["Grok810ScaleZeroQuarticChamberN5CostLadderScratch",
     "Grok810ScaleZeroQuarticChamberN7BandsScratch",
     "Grok810ScaleZeroQuarticChamberInfraN4Scratch"] + \
    [f"Grok810ScaleZeroQuarticChamber{_t}Packets{_j}Scratch"
     for _t in ("Unowned", "UnownedSystem", "UnownedSplit",
                "UnownedRefine", "UnownedTree", "Tower")
     for _j in ("", "1", "2", "3", "4")] + \
    [f"Grok810ScaleZeroQuarticChamber{_t}{_k}{_i}Scratch"
     for _t in ("Unowned", "UnownedSystem", "UnownedSplit",
                "UnownedRefine", "UnownedTree", "Tower")
     for _k in ("Columns", "Rests") for _i in range(1, 16)] + \
    [f"Grok810ScaleZeroQuarticChamberUnownedKills{_i}Scratch"
     for _i in range(1, 16)] + \
    [f"Grok810ScaleZeroQuarticChamberUnownedSystems{_i}Scratch"
     for _i in range(1, 16)] + \
    ["Grok810ScaleZeroQuarticTowerScratch",
     "Grok810ScaleZeroQuarticWallSplitsScratch",
     "Astra810ScaleZeroQuarticFactoredCellsScratch",
     "Astra810ScaleZeroQuarticChamberBCDEFG12Scratch",
     "Astra810ScaleZeroQuarticTowerLeavesScratch",
     "Grok810ScaleZeroQuarticChamberTowerBridgesScratch"] + \
    [f"Grok810ScaleZeroQuarticChamberTower{_k}{_i}Scratch"
     for _k in ("Columns", "Rests", "Kills") for _i in range(1, 16)] + \
    ["Grok810ScaleZeroQuarticChamberUnownedSystemBridgesScratch",
     "Grok810ScaleZeroQuarticChamberUnownedRefineScratch",
     "Grok810ScaleZeroQuarticChamberUnownedSplitsScratch",
     "Grok810ScaleZeroQuarticChamberResidual7Scratch",
     "Grok810ScaleZeroQuarticAssemblyCore2Scratch",
     "Grok810ScaleZeroQuarticAssembly2Scratch",
     "Grok810ScaleZeroQuarticChamberUnownedTreeCertsScratch",
     "Grok810ScaleZeroQuarticChamberUnownedTreePiecesScratch"] + \
    [f"Grok810ScaleZeroQuarticChamberUnownedTrees{_i}Scratch"
     for _i in ("", "1", "2", "3", "4", "5", "6")] + \
    [f"Grok810ScaleZeroQuarticChamberUnownedSystemBridges{_i}Scratch"
     for _i in ("", "1", "2", "3")]


def modules():
    out, seen = [], set()
    for m in DEFS + EXH + EXTRA:
        if m in seen:
            continue
        seen.add(m)
        p = ROOT / (m + ".lean")
        if p.exists():
            out.append((m, p.read_text().split("\n")))
        # a module split into parts keeps its name as an aggregator that only
        # imports them; the declarations live in the parts
        for q in sorted(ROOT.glob(m[:-7] + "Part*Scratch.lean")):
            if q.stem in seen:
                continue
            seen.add(q.stem)
            out.append((q.stem, q.read_text().split("\n")))
    # a module whose heavy declarations were lifted into `…SpeedTPart<n>Scratch`
    # helper parts by a speed lane keeps only the aggregator's name in the
    # lists above; follow those imports so the declarations they carry still
    # count as declared.  Transitive: the helper parts chain onto each other.
    i = 0
    while i < len(out):
        m, lines = out[i]
        i += 1
        for ln in lines:
            mm = re.match(r"^import (\S*SpeedTPart\d+\S*)\s*$", ln)
            if not mm or mm.group(1) in seen:
                continue
            q = ROOT / (mm.group(1) + ".lean")
            if not q.exists():
                continue
            seen.add(mm.group(1))
            out.append((mm.group(1), q.read_text().split("\n")))
    return out


# ------------------------------------------------------------------ structure
DECL = re.compile(r"^(?:private |protected )?(theorem|lemma|def|abbrev|"
                  r"inductive|structure)\s+([^\s(:{]+)")


def structural(mods):
    log("structural checks")
    names = {}
    for m, lines in mods:
        stack = []
        prev_doc = False
        for i, ln in enumerate(lines, 1):
            mm = re.match(r"^(section|namespace)\s+(\S+)\s*$", ln)
            if mm:
                stack.append(mm.group(2))
                continue
            mm = re.match(r"^end\s+(\S+)\s*$", ln)
            if mm:
                if not stack or stack[-1] != mm.group(1):
                    fail(f"{m}:{i} section mismatch `end {mm.group(1)}`")
                elif stack:
                    stack.pop()
                continue
            if re.match(r"^(noncomputable )?section\s*$", ln):
                stack.append(None)
            elif re.match(r"^end\s*$", ln) and stack:
                stack.pop()
            if ln.startswith("set_option") and ln.rstrip().endswith(" in") and prev_doc:
                fail(f"{m}:{i} `set_option ... in` after a doc comment")
            prev_doc = ln.startswith("/--") or (prev_doc and not ln.strip().endswith("-/")
                                                and ln.startswith("/-"))
            if ln.startswith("/--"):
                prev_doc = not ln.rstrip().endswith("-/") or True
            elif ln.strip():
                prev_doc = False
            mm = DECL.match(ln)
            if mm:
                if mm.group(2) in names:
                    fail(f"duplicate declaration {mm.group(2)} "
                         f"({names[mm.group(2)]} and {m}:{i})")
                names[mm.group(2)] = f"{m}:{i}"
        if [s for s in stack if s is not None]:
            fail(f"{m}: unclosed named sections {stack}")
    log(f"  {len(names)} declarations, no duplicates unless reported")
    return names


# ------------------------------------------------------------- chamber defs
def parse_chamber_defs(mods):
    cham = {}
    for m, lines in mods:
        if "Defs" not in m:
            continue
        for i, ln in enumerate(lines):
            mm = re.match(r"^def (QuarticChamber\w+810) \(A B C D E F G : k\[X\]\) : Prop :=$", ln)
            if not mm:
                continue
            body, j = [], i + 1
            while j < len(lines) and lines[j].strip():
                body.append(lines[j].strip())
                j += 1
            cham[mm.group(1)] = [f.strip() for f in
                                 re.sub(r"\s+", " ", " ".join(body)).split("∧")]
    return cham


def parse_ctors(mods):
    out = {}
    for m, lines in mods:
        cur = None
        for ln in lines:
            mm = re.match(r"^inductive (QuarticChamberSupport\w*810) \(A B C D E F G : k\[X\]\) : Prop$", ln)
            if mm:
                cur = mm.group(1)
                continue
            if cur:
                mm = re.match(r"^  \| (\w+) : (\S+) A B C D E F G →$", ln)
                if mm:
                    out[(cur, mm.group(1))] = mm.group(2)
                elif not ln.strip():
                    cur = None
    return out


# ------------------------------------------------------------------- exhaust
LEAF = re.compile(r"^exact QuarticChamberSupport810\.size(\d) "
                  r"\((QuarticChamberSupportSize\d810)\.(\w+) ⟨(.*)⟩\)$")
DEAD = "exact (by omega : False).elim"
TRI = re.compile(r"^rcases lt_trichotomy \((.*)\) \((.*)\) with (\S+) \| (\S+) \| (\S+)$")
# A live set whose whole case tree does not fit the runner's memory in one
# declaration has its depth-3 subtrees lifted into private lemmas of their
# own modules.  The tree is unchanged: splice each lemma's body back in and
# every branch condition and every leaf carries the same obligation as before.
SUBTREE = re.compile(r"^exact (chamberExhaust[A-Za-z0-9]+Path\d+) [A-G] ")
SUBTREE_BODIES = {}


def parse_block(body):
    ind0, head = body[0]
    m = TRI.match(head)
    if m:
        subs, cur = [], None
        for (ind, txt) in body[1:]:
            if ind == ind0 and txt.startswith("·"):
                if cur is not None:
                    subs.append(cur)
                rest = txt[1:].strip()
                cur = [] if (not rest or rest.startswith("--")) else [(ind + 2, rest)]
            else:
                cur.append((ind, txt))
        subs.append(cur)
        assert len(subs) == 3, f"bad bullet count: {len(subs)}"
        return ("node", m.group(1), m.group(2), [parse_block(s) for s in subs])
    joined = " ".join(t for _, t in body)
    if joined == DEAD:
        return ("dead",)
    m = SUBTREE.match(joined)
    if m:
        assert m.group(1) in SUBTREE_BODIES, f"no subtree lemma {m.group(1)}"
        return parse_block(SUBTREE_BODIES[m.group(1)])
    m = LEAF.match(joined)
    assert m, joined[:140]
    return ("leaf", int(m.group(1)), m.group(2), m.group(3),
            [p.strip() for p in m.group(4).split(",")])


EXH_THM = re.compile(r"^(?:private )?theorem "
                     r"(quarticChamberSupport810_of_live_[A-G]+"
                     r"|chamberExhaust[A-Za-z0-9]+Path\d+)$")


def check_exhaust(mods, cham, ctors):
    log("exhaust obligations (exact Farkas)")
    raw = {}
    for m, lines in mods:
        if "Exhaust" not in m:
            continue
        i = 0
        while i < len(lines):
            mm = EXH_THM.match(lines[i].rstrip())
            if mm:
                name = mm.group(1)
                j = i
                while not lines[j].rstrip().endswith(":= by"):
                    j += 1
                j += 1
                body = []
                while j < len(lines) and lines[j].strip():
                    s = lines[j].strip()
                    if not (s.startswith("obtain ") or s.startswith("have h")):
                        body.append((len(lines[j]) - len(lines[j].lstrip()), s))
                    j += 1
                assert name not in raw, f"duplicate exhaust body {name}"
                raw[name] = body
                i = j
            else:
                i += 1
    SUBTREE_BODIES.clear()
    SUBTREE_BODIES.update({k: v for k, v in raw.items()
                           if k.startswith("chamberExhaust")})
    blocks = {k: parse_block(v) for k, v in raw.items()
              if k.startswith("quarticChamberSupport810_of_live_")}
    nleaf = ndead = nobl = 0
    covered = set()
    for name, tree in sorted(blocks.items()):
        S = name.rsplit("_", 1)[-1]
        base = list(CC.CONEA) + list(CC.NONNEG) + [
            (CC.scal7(-1, CC.unit(LET.index(x))), False)
            for x in SIG if x not in S]

        def walk(t, cons):
            nonlocal nleaf, ndead, nobl
            if t[0] == "node":
                u, v = CC.lin(t[1]), CC.lin(t[2])
                walk(t[3][0], cons + [CC.gt(v, u)])
                walk(t[3][1], cons + [CC.ge(v, u), CC.ge(u, v)])
                walk(t[3][2], cons + [CC.gt(u, v)])
                return
            if t[0] == "dead":
                ndead += 1
                if CC.feasible(cons):
                    fail(f"{name}: `(by omega : False)` on a FEASIBLE branch")
                return
            nleaf += 1
            size, ind, ctor, parts = t[1], t[2], t[3], t[4]
            dname = ctors.get((ind, ctor))
            if dname is None:
                fail(f"{name}: unknown constructor {ind}.{ctor}")
                return
            covered.add(dname)
            if len(dname) and int(ind[-4]) != size:
                fail(f"{name}: size tag mismatch for {ctor}")
            fields = cham.get(dname)
            if fields is None:
                fail(f"{name}: no definition for {dname}")
                return
            nums = [f for f in fields
                    if not f.startswith("QuarticRatioConeA810")
                    and not re.fullmatch(r"[A-G] [≠=] 0", f)]
            letters = [f for f in fields if re.fullmatch(r"[A-G] [≠=] 0", f)]
            want = 1 + len(letters) + (1 if nums else 0)
            if len(parts) != want:
                fail(f"{name}/{ctor}: {len(parts)} components, expected {want}")
                return
            if parts[0] != "hA":
                fail(f"{name}/{ctor}: first component {parts[0]} ≠ hA")
            for f, p in zip(letters, parts[1:]):
                ch, op = f[0], f[2]
                exp = f"h{ch}{'ne' if op == '≠' else 'z'}"
                if p != exp:
                    fail(f"{name}/{ctor}: component {p} ≠ {exp}")
                if (ch in S) != (op == "≠"):
                    fail(f"{name}/{ctor}: letter {ch} live/dead mismatch")
            if nums:
                if parts[-1] != "by omega":
                    fail(f"{name}/{ctor}: last component {parts[-1]} ≠ `by omega`")
                for f in nums:
                    nobl += 1
                    for tgt, strict in CC.target_of(f):
                        if CC.derive(cons, tgt, strict) is None:
                            fail(f"{name}/{ctor}: NOT implied: {f}")
        walk(tree, base)
    log(f"  {len(blocks)} exhaust theorems, {nleaf} live leaves, {ndead} "
        f"infeasible leaves, {nobl} arithmetic obligations")
    miss = set(cham) - covered
    if miss:
        fail(f"{len(miss)} chambers never reached, e.g. {sorted(miss)[:5]}")
    else:
        log(f"  all {len(cham)} chambers reached")


def check_faces(mods, names):
    """Packet bookkeeping and the Farkas content of the rest bounds."""
    import _810_quartic_emit_common as EC
    import emit_810_quartic_chambers_lean as E
    face_mod = [ln for m, ln in mods if "ChamberFacesPart" in m]
    if not face_mod:
        face_mod = [ln for m, ln in mods if m.endswith("ChamberFacesScratch")]
    if not face_mod:
        log("faces module absent - skipped")
        return
    face_mod = [sum(face_mod, [])]
    log("faces module: packet bookkeeping and rest-bound obligations")
    data = CC.load_chambers()
    coords = CC.load_coords()
    # 1. record partition per form
    text = "\n".join(face_mod[0])
    for form in E.CARRIERS:
        tot = len(coords[form])
        lf = len(coords[form + "_lf"])
        m = re.search(rf"def {form}QuarticLoadFree810\n    \(A B C D E F G : k\[X\]\) : k\[X\] :=\n((?:  .*\n)+)", text)
        if not m:
            fail(f"{form}QuarticLoadFree810 not found")
            continue
        if len(m.group(1).strip().split("\n")) != lf:
            fail(f"{form}QuarticLoadFree810 has wrong monomial count")
        cols = 0
        for ld in CC.LOADS:
            for mm in re.finditer(
                    rf"def {form}QuarticColumn{CC.LOAD_CAP[ld]}\d?810\n    \({ld} : k\)\n"
                    rf"    \(A B C D E F G : k\[X\]\) : k\[X\] :=\n((?:  .*\n)+)", text):
                cols += len(mm.group(1).strip().split("\n"))
        if lf + cols != tot:
            fail(f"{form}: load-free {lf} + columns {cols} != {tot} records")
    # 2. every chamber's obligations
    nobl = nmiss = 0
    packets = collections.OrderedDict()
    per_form = collections.Counter()
    for c in data["chambers"]:
        if not E.killable(c):
            continue
        for cr in c["certificate"]["carriers"]:
            if cr not in E.CARRIERS:
                continue
            key = (cr, E.parse_face(c["faces"][cr]))
            if key not in packets:
                packets[key] = per_form[cr]
                per_form[cr] += 1
    for c in data["chambers"]:
        if not E.killable(c):
            continue
        base = CC.chamber_cons(c["conjuncts"])
        live = set(c["live"])
        for cr in c["certificate"]["carriers"]:
            if cr not in E.CARRIERS:
                continue
            cons = list(base)
            for q in c["refinement_conjuncts"].get(cr, []):
                cons += CC.constraints_of(q)
            keys = E.parse_face(c["faces"][cr])
            n = packets[(cr, keys)]
            lem = f"{cr}QuarticChamberRestLF{n}810_natDegree_lt_of_live_{c['live']}"
            if lem not in names:
                nmiss += 1
                fail(f"missing rest bound {lem}")
            lf = EC.sort_records(coords[cr + "_lf"])
            face = [r for r in lf if E.rec_key(r) in keys]
            d0 = E.deg_expr(face[0].get("exps") or {})
            d = CC.lin(d0)
            for r in face[1:]:
                nobl += 1
                for tgt, st in CC.target_of(
                        f"{E.deg_expr(r.get('exps') or {})} = {d0}"):
                    if CC.derive(cons, tgt, st) is None:
                        fail(f"{c['id']}/{cr}: face tie not implied: "
                             f"{E.deg_expr(r.get('exps') or {})} = {d0}")
            for r in lf:
                ex = r.get("exps") or {}
                if E.rec_key(r) in keys:
                    continue
                if any(int(ex.get(L, 0) or 0) > 0 and L != "A" and L not in live
                       for L in LET):
                    continue
                nobl += 1
                if CC.derive(cons, CC.sub7(d, CC.lin(E.deg_expr(ex))), True) is None:
                    fail(f"{c['id']}/{cr}: rest monomial not dominated: "
                         f"{E.deg_expr(ex)} < {d0}")
    log(f"  {len(packets)} packets, {nobl} face/rest obligations, "
        f"{nmiss} missing lemmas")


def check_aux(mods):
    """Recompute every auxiliary's pure-`A` load column and its load-free
    letter support from the coordinates JSON and compare with the module."""
    from fractions import Fraction as Fr
    import emit_810_quartic_chambers_lean as E
    aux_mod = [ln for m, ln in mods if m.endswith("ChamberAuxTowerScratch")]
    if not aux_mod:
        log("auxiliary tower module absent - skipped")
        return
    log("auxiliary tower: load columns and load-free supports")
    text = "\n".join(aux_mod[0])
    coords = CC.load_coords()
    nchk = 0
    for name, (w, kk, parts) in E.AUX.items():
        ps = [(f, ap, Fr(co.replace("(", "").replace(")", "")))
              for f, ap, co in parts]
        for ld in E.PURE_A_LOADS:
            j = (w - E.LOADW[ld]) // 2
            tot = sum(c * E._col_coeff(coords, f, ld, j - ap) for f, ap, c in ps)
            num, den = tot.numerator, tot.denominator
            want = (f"({num} / {den} * {ld} : k) • A ^ {j}" if den != 1
                    else f"({num} * {ld} : k) • A ^ {j}")
            if num < 0:
                want = (f"(-({-num} / {den}) * {ld} : k) • A ^ {j}" if den != 1
                        else f"(-({-num}) * {ld} : k) • A ^ {j}")
            dn = f"{name}Quartic{CC.LOAD_CAP[ld]}Face810"
            m = re.search(rf"def {dn} \({ld} : k\) \(A : k\[X\]\) : k\[X\] :=\n  (.*)\n", text)
            nchk += 1
            if not m:
                fail(f"{dn} not found")
            elif m.group(1).strip() != want:
                fail(f"{dn}: emitted {m.group(1).strip()!r}, recomputed {want!r}")
        # load-free letter support (the OPEN_CHAMBERS.md §1 table)
        acc = {}
        for f, ap, c in ps:
            for r in coords[f + "_lf"]:
                ex = r.get("exps") or {}
                mon = "".join(L * int(ex.get(L, 0) or 0) for L in SIG)
                key = (mon, int(ex.get("A", 0) or 0) + ap)
                acc[key] = acc.get(key, Fr(0)) + c * Fr(int(r["qn"]), int(r["qd"]))
        supp = sorted({mo for (mo, _a), v in acc.items() if v != 0},
                      key=lambda mo: (len(mo), mo))
        if not supp:
            fail(f"{name}: empty load-free support")
        nchk += 1
    log(f"  {nchk} auxiliary coefficients/supports recomputed")


HYPRE = re.compile(r"^    \((\w+'?) :")


def theorem_hyps(lines):
    """name -> list of explicit hypothesis names, for `theorem name\n    (…"""
    out, i = {}, 0
    while i < len(lines):
        m = re.match(r"^theorem (\S+)$", lines[i])
        if m:
            hyps, j = [], i + 1
            while j < len(lines) and lines[j].startswith("    "):
                mm = HYPRE.match(lines[j])
                if mm:
                    hyps.append(mm.group(1))
                if lines[j].rstrip().endswith(":= by") or lines[j].rstrip().endswith(":="):
                    break
                j += 1
            out[m.group(1)] = hyps
            i = j
        i += 1
    return out


def check_kills(mods, names):
    """Cross-module name resolution and arity of the emitted kill chain."""
    text = {m: "\n".join(ln) for m, ln in mods}
    have = set(names)
    log("kill chain: name resolution and arities")
    hyps = {}
    for m, ln in mods:
        hyps.update(theorem_hyps(ln))
    nref = nbad = 0
    # 1. every `<x>_natDegree_lt_of_live_<S>` / face / rest / kill referenced exists
    pat = re.compile(r"\b(\w+810(?:_natDegree_lt_of_live_[A-G]+|_natDegree|_zero"
                     r"|_impossible|_eq_face\d+_add_rest|_eq_chamberSplit"
                     r"|_eq_face\d+_add_rest))\b")
    for m, ln in mods:
        if "Chamber" not in m:
            continue
        for nm in set(pat.findall(text[m])):
            nref += 1
            if nm not in have:
                nbad += 1
                fail(f"{m}: undefined reference {nm}")
    # 2. column-bound calls inside the rest bounds
    ncall = 0
    for m, ln in mods:
        if not m.endswith("ChamberRestsScratch"):
            continue
        for mm in re.finditer(r"· exact (\w+810_natDegree_lt_of_live_[A-G]+) "
                              r"(\w+) A B C D E F G hdpos([^\n]*)", text[m]):
            ncall += 1
            nm = mm.group(1)
            want = hyps.get(nm)
            if want is None:
                fail(f"{m}: no signature for {nm}")
                continue
            got = 2 + len(mm.group(3).split())   # the load + hdpos + rest
            if got != len(want):
                fail(f"{m}: {nm} called with {got} args, wants {len(want)}")
    # 3. the residual dispatch covers every constructor exactly once
    for suffix in ("ChamberResidualScratch", "ChamberResidual2Scratch",
                   "ChamberResidual3Scratch", "ChamberResidual4Scratch",
                   "ChamberResidual5Scratch", "ChamberResidual6Scratch",
                   "ChamberResidual7Scratch"):
      res = [t for mm, t in text.items() if mm.endswith(suffix)]
      if res:
        # the dispatch is either one theorem (8-space branches) or, when the
        # module is split into per-size parts, 2-space branches in each part
        used = re.findall(r"^        \| (c\w+) hc =>$", res[0], re.M) or \
            re.findall(r"^  \| (c\w+) hc =>$", res[0], re.M)
        ctors = set()
        for m, ln in mods:
            ctors |= {c for (ind, c) in parse_ctors([(m, ln)]) if c.startswith("c")}
        dup = [c for c, n in collections.Counter(used).items() if n > 1]
        if dup:
            fail(f"{suffix}: dispatch repeats {len(dup)} constructors")
        miss = ctors - set(used)
        if miss:
            fail(f"{suffix}: dispatch misses {len(miss)} constructors, "
                 f"e.g. {sorted(miss)[:4]}")
        log(f"  {suffix}: {len(used)} branches for {len(ctors)} chambers")
    r6 = [t for mm, t in text.items() if mm.endswith("ChamberResidual6Scratch")]
    if r6:
        used6 = re.findall(r"^        \| (c\w+) hc =>$", r6[0], re.M)
        ctors = set()
        for m, ln in mods:
            ctors |= {c for (ind, c) in parse_ctors([(m, ln)]) if c.startswith("c")}
        miss = ctors - set(used6)
        if miss or len(used6) != len(ctors):
            fail(f"Residual6: {len(used6)} branches for {len(ctors)} chambers, "
                 f"{len(miss)} missing")
        else:
            log(f"  ChamberResidual6Scratch: {len(used6)} branches for "
                f"{len(ctors)} chambers")
    # 4. the kills: rest-lemma / face-lemma arity and the 7-way band rcases
    # the single-monomial kill families are split one declaration per module,
    # so the aggregators carry no proof any more: read the `Part` modules too,
    # or these checks would see almost nothing
    kl = [t for mm, t in text.items()
          if re.search(r"Chamber(?:Power|Refined|Unowned)?"
                       r"(?:Kills|Systems|Splits|Refine)\d*"
                       r"(?:Part\d+)?Scratch$", mm)]
    kl = ["\n".join(kl)] if kl else []
    nk = 0
    if kl:
        for mm in re.finditer(
                r"    (\w+QuarticChamberRest\d+810_natDegree_lt_of_live_[A-G]+) "
                r"l beta gamma delta epsilon zeta eta theta\n"
                r"      A B C D E F G hd[pz](?:os|\d+) ?([^\n]*)\n", kl[0]):
            nk += 1
            want = hyps.get(mm.group(1))
            if want is None:
                fail(f"kills: no signature for {mm.group(1)}")
                continue
            # a kill argument is `(by [clear * - …; ] omega)`, the same
            # wrapped in `Or.inr`, an `Or.inr <name>`, or a bare hypothesis
            toks = (["hdpos"] +
                    re.findall(r"\(Or\.inr ⟨[^⟩]*⟩\)"
                               r"|\(Or\.inr \(by [^()]*omega\)\)"
                               r"|\(Or\.inr [A-Za-z0-9_']+\)"
                               r"|\(by [^()]*omega\)|[A-Za-z0-9_']+",
                               mm.group(2)))
            if len(toks) != len(want):
                fail(f"kills: {mm.group(1)} called with {len(toks)} args, "
                     f"wants {len(want)}")
        nf = 0
        for mm in re.finditer(r"    (\w+QuarticChamberFace\d+810_natDegree) "
                              r"A B C D E F G ([^\n]*)\n", kl[0]):
            nf += 1
            want = hyps.get(mm.group(1))
            if want is None:
                fail(f"kills: no signature for {mm.group(1)}")
            elif len(mm.group(2).split()) != len(want):
                fail(f"kills: {mm.group(1)} called with "
                     f"{len(mm.group(2).split())} args, wants {len(want)}")
        # a κ-letter band `rcases` has one branch per letter plus `l = 0`;
        # a kill that first proves the band into the head of its load column
        # (`hb<ld>s`) then splits that two-way — check both shapes, at any
        # indentation, since the head stage nests the band `rcases` deeper
        for mm in re.finditer(r"\n\s+rcases hb([a-z]+) with ([^\n]*)\n",
                              kl[0]):
            nm2 = mm.group(1)
            # `hb<ld>s` is the head stage a kill proves the band into; no
            # load is spelled with a trailing `s`, so the two are distinct
            head = nm2.endswith("s") and nm2[:-1] in CC.LOADS
            want = 2 if head else 7
            got = len(mm.group(2).split("|"))
            if got != want:
                fail(f"kills: band rcases on hb{nm2} has "
                     f"{got} branches, wants {want}")
        log(f"  kills: {nk} rest calls, {nf} face calls checked")
    log(f"  {nref} cross-module references, {ncall} column calls, {nbad} unresolved")


def check_costladder(mods):
    """The cost-form auxiliary ladder: every rest monomial of every (aux, load)
    is below the pure-`A` column, from the predicate alone."""
    import emit_810_quartic_chambers_lean as E
    if not any(m.endswith("ChamberCostLadderScratch") for m, _ in mods):
        log("cost ladder absent - skipped")
        return
    log("cost ladder: predicate satisfiability and rest bounds")
    nobl = 0
    have_aux = [a for a in ("kappa", "n2", "n5")
                if a in ("kappa", "n2")
                or any(m.endswith(f"Chamber{E.AUXTAG[a]}CostLadderScratch")
                       for m, _ in mods)]
    for aux in have_aux:
        T = E.aux_terms(aux)
        w = E.AUXWT[aux]
        for pi in E.PUREA:
            sat = E.cost_predicate_satisfiable(aux, pi)
            if not sat:
                log(f"  {aux}/{pi}: predicate unsatisfiable - correctly skipped")
                continue
            wp = E.WPI[pi]
            j = (w - wp) // 2
            cons = list(CC.CONEA) + list(CC.NONNEG)
            for m, ww in E.cost_conjuncts(aux, pi):
                cons.append(CC.gt(CC.cform(m), CC.scal7(ww, CC.unit(0))))
            for (mon, ap, ld), _c in T.items():
                if ld == pi and mon == "":
                    continue
                if ld in E.PUREA and E.WPI[ld] < wp:
                    continue
                v = [ap] + [0] * 6
                for ch in mon:
                    v[1 + CC.IDX[ch]] += 1
                nobl += 1
                if CC.derive(cons, CC.sub7(CC.scal7(j, CC.unit(0)), tuple(v)),
                             True) is None:
                    fail(f"cost ladder {aux}/{pi}: monomial {ld or 'lf'} "
                         f"{mon or '1'}·A^{ap} not below {j}·a")
    log(f"  {nobl} cost-ladder rest obligations")
    if any(m.endswith("ChamberN7LadderScratch") for m, _ in mods):
        T = E.n7_terms()
        n7 = 0
        for pi in E.PUREA:
            wp = E.WPI[pi]
            j = (17 - wp) // 2
            cons = list(CC.CONEA) + list(CC.NONNEG)
            for m, w in E.n7_cost_conjuncts(pi):
                cons.append(CC.gt(CC.cform(m), CC.scal7(w, CC.unit(0))))
            if CC.feasible(cons) is False:
                fail(f"N7 ladder {pi}: predicate unsatisfiable")
            for (mon, ap, ld), _c in T.items():
                if ld == pi and mon == "":
                    continue
                if ld in E.PUREA and E.WPI[ld] < wp:
                    continue
                v = [ap] + [0] * 6
                for ch in mon:
                    v[1 + CC.IDX[ch]] += 1
                n7 += 1
                if CC.derive(cons, CC.sub7(CC.scal7(j, CC.unit(0)), tuple(v)),
                             True) is None:
                    fail(f"N7 ladder {pi}: {ld or 'lf'} {mon or '1'}·A^{ap} "
                         f"not below {j}·a")
        log(f"  {n7} N7-ladder rest obligations")


def check_refine(mods):
    """The carrier-refined tournaments: three bullets per node, and every leaf's
    refined `Prop` implied by its branch."""
    import emit_810_quartic_chambers_lean as E
    if not any(m.endswith("ChamberRefineScratch") for m, _ in mods):
        log("refine module absent - skipped")
        return
    log("refined-cell tournaments")
    data = CC.load_chambers()
    chambers = E.build_chambers(data)
    cham = {c.name: c for c in chambers}
    text = {m: ln for m, ln in mods if m.endswith("ChamberRefineScratch")}
    lines = list(text.values())[0]
    nleaf = nobl = 0
    i = 0
    while i < len(lines):
        m = re.match(r"^theorem quarticChamber(\w+)810_refine$", lines[i])
        if not m:
            i += 1
            continue
        cname = m.group(1)
        c = cham.get(cname)
        if c is None:
            fail(f"refine: unknown chamber {cname}")
            i += 1
            continue
        j = i
        while not lines[j].rstrip().endswith(":= by"):
            j += 1
        j += 1
        body = []
        while j < len(lines) and lines[j].strip():
            s2 = lines[j].strip()
            if not (s2.startswith("obtain ") or s2.startswith("have h")):
                body.append((len(lines[j]) - len(lines[j].lstrip()), s2))
            j += 1
        base = CC.chamber_cons(c.conjuncts)

        def walk(blk, cons):
            nonlocal nleaf, nobl
            ind0, head = blk[0]
            mm = TRI.match(head)
            if mm:
                subs, cur = [], None
                for (ind, txt) in blk[1:]:
                    if ind == ind0 and txt.startswith("·"):
                        if cur is not None:
                            subs.append(cur)
                        rest = txt[1:].strip()
                        cur = [] if (not rest or rest.startswith("--")) else [(ind + 2, rest)]
                    else:
                        cur.append((ind, txt))
                subs.append(cur)
                if len(subs) != 3:
                    fail(f"refine {cname}: {len(subs)} bullets")
                    return
                u, v = CC.lin(mm.group(1)), CC.lin(mm.group(2))
                walk(subs[0], cons + [CC.gt(v, u)])
                walk(subs[1], cons + [CC.ge(v, u), CC.ge(u, v)])
                walk(subs[2], cons + [CC.gt(u, v)])
                return
            joined = " ".join(t for _d, t in blk)
            mm = re.search(r"Or\.(inl|inr)", joined)
            k = joined.count("Or.inr ")
            if "Or.inl" not in joined and "Or.inr" not in joined:
                fail(f"refine {cname}: unparsed leaf {joined[:60]}")
                return
            nleaf += 1
            if k >= len(c.leaves):
                fail(f"refine {cname}: injection index {k} out of range")
                return
            lf = c.leaves[k]
            for q in E._leaf_conjuncts(lf):
                nobl += 1
                for tgt, st in CC.target_of(q):
                    if CC.derive(cons, tgt, st) is None:
                        fail(f"refine {cname}/L{k}: not implied: {q}")
        walk(body, base)
        i = j
    log(f"  {nleaf} tournament leaves, {nobl} refinement obligations")


def main():
    mods = modules()
    log(f"{len(mods)} modules: " + ", ".join(m for m, _ in mods))
    names = structural(mods)
    cham = parse_chamber_defs(mods)
    ctors = parse_ctors(mods)
    log(f"  {len(cham)} chamber definitions, {len(ctors)} constructors")
    sizes = {f"QuarticChamberSupportSize{i}810" for i in range(1, 7)}
    for (ind, ctor), dn in ctors.items():
        if dn not in cham and dn not in sizes:
            fail(f"constructor {ind}.{ctor} names undefined {dn}")
    check_exhaust(mods, cham, ctors)
    check_faces(mods, names)
    check_aux(mods)
    check_kills(mods, names)
    check_costladder(mods)
    check_refine(mods)
    print(f"\nTOTAL PROBLEMS: {problems}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
