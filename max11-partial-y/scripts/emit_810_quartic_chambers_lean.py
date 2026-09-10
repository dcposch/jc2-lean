#!/usr/bin/env python3
"""Emit Files B/C of the (8,10) scale-zero σ-ladder from the corrected
cost-argmin chamber taxonomy.

    python3 scripts/emit_810_quartic_chambers_lean.py [--only defs,exhaust,...]

Reads
    scripts/out_810_scale_zero_quartic_chambers.json      (1163 leaf chambers)
    scripts/out_810_scale_zero_quartic_coordinates.json   (the seven integrals)
Writes a chain of untracked Lean modules `Grok810ScaleZeroQuarticChamber*.lean`
plus `~/lean/tools/sigma810/FILES_BC_MANIFEST.md`.

Design (see the manifest for the full story)
--------------------------------------------
* A **chamber** is one cost-argmin cell `(S, T)`: `S` the live-letter set,
  `T ⊆ M_S` the argmin monomial set.  There are 1115 of them (the JSON's 1163
  leaves refine 11 of these cells further, per carrier; those 11 are carried to
  the residual, see `REFINED`).
* The **exhaust** follows the closed form
  `c₀ = min(2·μ₂, β + r, 2·β + ω)` of `CHAMBERS.md` §1: a linear tournament
  inside `{B,C}`, `{D,E}`, `{F,G}`, then `μ₂ = min(q,r)`, `ω = min(β,q)`, then
  the three cost types against each other.  Every branch that no chamber
  matches is ℚ-infeasible (checked by exact Farkas certificates) and is closed
  by `omega`.
* **Faces and rests** are cut per *packet* `(carrier, T)`, not per chamber: the
  face is load-free, so the eight load columns of an integral are shared by
  every packet of that integral.  `Φ = Φ_lf + Σ_π Φ_π` is one module identity
  per integral; `Φ_lf = face + restLF` is one per packet.
"""
from __future__ import annotations

import argparse
import collections
import itertools
import os
import re
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _810_chamber_common as CC  # noqa: E402

ROOT = CC.ROOT
SIG = CC.SIG
LET = CC.LET
started = time.monotonic()


def log(*a):
    print(f"[{time.monotonic() - started:7.1f}s]", *a, flush=True)


# --------------------------------------------------------------- Lean preamble
LINTERS = """set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false"""


def _flatten_imports(x, acc=None):
    if acc is None:
        acc = []
    if isinstance(x, str):
        if x not in acc:
            acc.append(x)
        return acc
    for y in x:
        _flatten_imports(y, acc)
    return acc


WRITTEN = set()


def _import_exists(i):
    """A `Grok810…Scratch` import is real only if the module got emitted.

    Some emitters skip a module when it has nothing new to say, yet its name
    stays on the accumulated module list; importing it is `unknown module
    prefix` at the gate."""
    if not i.startswith("Grok810"):
        return True
    return i + ".lean" in WRITTEN or (ROOT / (i + ".lean")).exists()


def header(imp, doc):
    imps = _flatten_imports(imp)
    assert all(isinstance(i, str) for i in imps), imps
    imps = [i for i in imps if _import_exists(i)]
    return (
        "".join(f"import {i}\n" for i in imps) + "\n"
        f"/-! {doc}\n-/\n\n"
        "open scoped Polynomial.Bivariate\n\n"
        "noncomputable section\n\n"
        "open Polynomial\n\n"
        "namespace Max11DegreeRoutes\n\n"
        f"{LINTERS}\n\n"
        "set_option maxRecDepth 1000000\n\n"
        "variable {k : Type*} [Field k] [CharZero k]\n\n"
    )


FOOTER = "\nend Max11DegreeRoutes\n"


_RECEIPTS = None
GREEN_SKIPPED = []


def green_receipts():
    """Every `(sha256, file)` pair the gate has issued a receipt for."""
    global _RECEIPTS
    if _RECEIPTS is None:
        _RECEIPTS = set()
        d = ROOT / ".max11-lanes" / "gates"
        if d.is_dir():
            for r in d.glob("*.receipt"):
                try:
                    t = r.read_text()
                except OSError:
                    continue
                for m in re.finditer(
                        r"^VERIFIED_SHA256=([0-9a-f]+) FILE=(\S+)$", t, re.M):
                    _RECEIPTS.add((m.group(1), m.group(2)))
    return _RECEIPTS


def is_green(name):
    """Does the file on disk, as it stands, carry a green receipt?  Such a
    module is frozen: its text must never change, or the receipt is void."""
    import hashlib
    p = ROOT / name
    if not p.exists():
        return False
    return (hashlib.sha256(p.read_bytes()).hexdigest(), name) in green_receipts()


_DECL_RE = re.compile(
    r"^(?:theorem|lemma|def|abbrev|inductive|structure)\s+([^\s(:{]+)")
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_NAME_OWNERS = None
_IMPORTS_OF = {}


def _module_imports(mod):
    """The `Grok810…` modules `mod` imports, read off disk (cached)."""
    if mod not in _IMPORTS_OF:
        q = ROOT / (mod + ".lean")
        got = []
        if q.exists():
            for ln in q.read_text().split("\n"):
                if ln.startswith("import Grok810"):
                    got.append(ln.split()[1])
                elif ln and not ln.startswith("import "):
                    break
        _IMPORTS_OF[mod] = got
    return _IMPORTS_OF[mod]


def _import_closure(mods):
    seen, stack = set(), list(mods)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(_module_imports(m))
    return seen


def name_owners():
    """`declaration name -> {modules declaring it}`, over every emitted file."""
    global _NAME_OWNERS
    if _NAME_OWNERS is None:
        _NAME_OWNERS = {}
        for q in sorted(ROOT.glob("Grok810*.lean")):
            for ln in q.read_text().split("\n"):
                mm = _DECL_RE.match(ln)
                if mm:
                    _NAME_OWNERS.setdefault(mm.group(1), set()).add(q.stem)
    return _NAME_OWNERS


def _register(mod, body):
    own = name_owners()
    for ln in body.split("\n"):
        mm = _DECL_RE.match(ln)
        if mm:
            own.setdefault(mm.group(1), set()).add(mod)
    _IMPORTS_OF.pop(mod, None)


def _strip_comments(text):
    """Lean code with `/- … -/` (nested) and `--` comments blanked out."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


# --------------------------------------------- arithmetic-context pruning
# A chamber kill carries every band disjunction, every rest bound and every
# top-coefficient equation of its chamber in one local context.  `omega` and
# `linarith` preprocess the *whole* context, so each of the hundreds of
# arithmetic leaves in a kill pays for all of it; that, not any single goal,
# is what drives a kill to tens of GiB.  Every one of those leaves is a pure
# ℕ-degree statement, so `clear * - …` in front of it, keeping only the
# ℕ-degree facts in scope, is enough - and it is a context restriction, so it
# can only make a proof harder, never admit a false one.

# the ℕ-degree facts every kill shape has: the refined-leaf conjuncts, the
# `A`-degree comparisons, the dead letters' degrees, the `natDegree_le`
# bound, and the names a local `by_contra` / `rcases` binds.
COMMON_KEEP = (r"hx\d+|hApos|hA[B-G]|h[B-G]n|hle|hcon|h"
               # the `0 < d` fact every kill contradicts at the end,
               # and the two `by_contra` witnesses the kills bind
               r"|hdpos|hzero|hz0")
# the chamber kills: the chamber's own conjuncts (renamed `hcq…` so the
# per-carrier `hq…` coefficient facts cannot shadow them) and the
# per-carrier degree positivity facts.
KILL_KEEP = COMMON_KEEP + r"|hcq\d+|hdp\d+|hdz\d+"
# the refinement trees: the chamber conjuncts keep their `hq…` names, and the
# accumulated trichotomy path values are what the deeper branches need.
TREE_KEEP = COMMON_KEEP + r"|hq\d+|hpv\d+"
# the five single-monomial kill emitters: they name the `0 < d` fact `hdpos`,
# the `by_contra` of the `hnc` step `hzero` and the `A ≠ 0` witness `hz0`.
SINGLE_KEEP = KILL_KEEP + r"|hdpos|hzero|hz0|hrf\d+"

# ------------------------------------- exact Farkas supports for `clear * -`
# `omega` is complete for linear integer arithmetic, so an exact rational
# Farkas certificate for an obligation names a *sufficient* set of
# hypotheses; handing `omega` only those is a context restriction and can
# never admit a false proof.  `scripts/_810_chamber_common.py` carries the
# exact-rational LP these certificates come from.
CONE_CONS = ([("hApos", CC.unit(0), True)]
             + [(f"hA{X}", CC.sform(X), True) for X in SIG])
NONNEG_CONS = [(None, CC.unit(i), False) for i in range(7)]


def chamber_cons_named(nums, tag="hcq"):
    """The chamber's ℕ conjuncts as `(name, vec, strict)`, in the order the
    kill's `obtain` binds them (an equality contributes both directions
    under one name)."""
    out = []
    for i, f in enumerate(nums):
        try:
            cs = CC.constraints_of(f)
        except AssertionError:          # not a ℕ-degree comparison
            continue
        for v, st in cs:
            out.append((f"{tag}{i}", v, st))
    return out


def dead_cons(live, letters=SIG):
    """`h<X>n : X.natDegree = 0` for every dead letter."""
    out = []
    for X in letters:
        if X not in live:
            for v, st in CC.constraints_of(f"{X}.natDegree = 0"):
                out.append((f"h{X}n", v, st))
    return out


def farkas_keep(cons, goals):
    """The hypothesis names an exact Farkas proof of every goal uses, or
    `None` when some goal is not derivable over ℚ from `cons`."""
    plain = [(v, st) for _n, v, st in cons]
    need = set()
    for tgt, strict in goals:
        lam = CC.derive(plain, tgt, strict)
        if lam is None:
            return None
        for l, (n, _v, _s) in zip(lam, cons):
            if l != 0 and n is not None:
                need.add(n)
    return need


def keep_str(cons, goals, always=()):
    """`clear * - …` keep-list for an `omega` discharging `goals`, or `None`
    when no certificate exists (the caller then keeps the whole context)."""
    need = farkas_keep(cons, goals)
    if need is None:
        return None
    need |= set(always)
    # `clear * -` wants at least one name, and `hApos` is in every kill
    need = need or {"hApos"}
    return " ".join(sorted(need, key=lambda s: (s != "h", len(s), s)))


def cover_head(cons, goals):
    """A small subset `S` of `goals` with `cons + S ⊢ every goal`.

    The load column of a band is ordered so that its pure-`A` head dominates
    the rest over the chamber's own conjuncts, so `S` is normally a single
    conjunct: the kill can then turn the 7-way band `rcases` into that one
    conjunct and expand it into the full ∧-chain once instead of six times.
    Returns `None` when no proper subset works."""
    if len(goals) < 2:
        return None
    def implies(S):
        c = list(cons) + [(f"hS{j}", goals[j][0], goals[j][1]) for j in S]
        plain = [(v, st) for _n, v, st in c]
        return [CC.derive(plain, t, s) is not None for t, s in goals]
    for j in range(len(goals)):          # the head is normally conjunct 0
        if all(implies([j])):
            return [j]
    S, rest = [], list(range(len(goals)))
    while not all(implies(S)):
        best, bestn = None, -1
        for j in rest:
            n = sum(implies(S + [j]))
            if n > bestn:
                bestn, best = n, j
        if best is None:
            return None
        S.append(best)
        rest.remove(best)
        if len(S) >= len(goals) - 1:
            return None
    return S

_PR_OBTAIN = re.compile(r"^\s*obtain ⟨([^⟩]*)⟩")
_PR_HAVE = re.compile(r"^\s*have (\w+)")
_PR_RCASES = re.compile(r"^\s*rcases .* with (\w+(?: \| \w+)*)\s*$")
_PR_BYCONTRA = re.compile(r"^\s*by_contra (\w+)")
_PR_HANE = re.compile(r"^(\s*)have hAne : A ≠ 0 := by$")
_PR_OMEGA = re.compile(r"(?<![A-Za-z_'])omega(?![A-Za-z_'])")


def prune_arith(body, names=None):
    """Put `clear * - <ℕ-degree hypotheses in scope>` in front of every
    `omega` of one emitted declaration.

    Scope is read off the indentation: a name bound at column `c` is live
    exactly while the following lines stay at column `c` or deeper, and a
    `have` binds its name only after its own proof, never inside it."""
    keep = re.compile("^(?:" + (names or KILL_KEEP) + ")$")
    lines = body.split("\n")
    out, scope, pend = [], [], []
    # a hypothesis a `rw … at h` targets may be a *binder of the theorem*, so
    # it never enters `scope`; the closing `omega` of a kill contradicts
    # exactly that hypothesis.  Keep it, scoped like everything else: at the
    # indentation of the `rw` it belongs to, so a sibling branch of a tree kill
    # does not inherit a `have` of the branch before it.
    atn, sind = [], 0
    i = 0
    while i < len(lines):
        ln = lines[i]
        if ln.startswith(("theorem ", "private theorem ", "set_option")):
            atn = []
        mat = re.match(r"^ *(?:\] )?at (\w+)$", ln)
        if mat:
            if mat.group(1) not in [a for a, _s in atn]:
                atn.append((mat.group(1), sind))
        elif ln.strip() and not ln.lstrip().startswith(("natDegree_add",
                                                        "at ", "] at ")):
            sind = len(ln) - len(ln.lstrip(" "))
        if not ln.strip():
            out.append(ln)
            i += 1
            continue
        ind = len(ln) - len(ln.lstrip(" "))
        for n, d in pend:
            if d >= ind:
                scope = [x for x in scope if x[0] != n]
                scope.append((n, d))
        pend = [x for x in pend if x[1] < ind]
        scope = [x for x in scope if x[1] <= ind]
        atn = [x for x in atn if x[1] <= ind]
        m = _PR_HANE.match(ln)
        if m:
            # `A ≠ 0` is closed by `0 < A.natDegree` against `A.natDegree = 0`
            out += [ln, lines[i + 1], lines[i + 2],
                    m.group(1) + "  clear * - hApos hz0; omega"]
            i += 4
            continue
        new = []
        mm = _PR_OBTAIN.match(ln)
        if mm:
            new = [x.strip() for x in mm.group(1).split(",")]
        elif _PR_BYCONTRA.match(ln):
            new = [_PR_BYCONTRA.match(ln).group(1)]
        elif _PR_RCASES.match(ln):
            for x in _PR_RCASES.match(ln).group(1).split(" | "):
                if x not in new:
                    new.append(x)
        else:
            mm = _PR_HAVE.match(ln)
            if mm:
                new = [mm.group(1)]
        if ("omega" in ln and "clear * -" not in ln
                and "all_goals" not in ln):
            # the hypothesis a `rw … at h` has already targeted is a binder of
            # the theorem (or a `have` of this proof) that `scope` may not
            # carry, and it is the one the closing `omega` contradicts
            live = [n for n, _d in scope]
            for a, _s in atn:
                if a not in live:
                    live.append(a)
            pre = "clear * - " + " ".join(live) + "; "
            ln = _PR_OMEGA.sub(pre + "omega", ln)
        out.append(ln)
        for n in new:
            if keep.match(n):
                pend.append((n, ind))
        i += 1
    return "\n".join(out)


def name_chamber_facts(body):
    """Rename the chamber conjuncts `hq…` the chamber structure binds to
    `hcq…`, so the per-carrier `hq…` coefficient facts a kill introduces
    later cannot shadow them out of the pruned arithmetic context."""
    return re.sub(r"obtain ⟨hA,[^⟩]*⟩ := h(?:ch|cell)",
                  lambda m: m.group(0).replace("hq", "hcq"), body)


def name_path_values(body):
    """Give the trichotomy fact of each tree depth its own name `hpv<d>`.

    The tree emits one `hpv` per node; nested nodes shadow it, so a pruned
    context at a leaf could only ever see the innermost comparison.  The
    statements are unchanged - only the local binder names are."""
    out, stack = [], []
    for l in body.split("\n"):
        m = re.match(r"^(\s*)rcases lt_trichotomy .* with hpv \| hpv \| hpv$",
                     l)
        if m:
            ind = len(m.group(1))
            while stack and stack[-1] >= ind:
                stack.pop()
            stack.append(ind)
            d = len(stack) - 1
            l = l.replace("with hpv | hpv | hpv",
                          f"with hpv{d} | hpv{d} | hpv{d}")
        else:
            ind = len(l) - len(l.lstrip(" "))
            if l.strip():
                while stack and stack[-1] > ind:
                    stack.pop()
            if stack:
                l = re.sub(r"(?<![A-Za-z_0-9])hpv(?![A-Za-z_0-9])",
                           f"hpv{len(stack) - 1}", l)
        out.append(l)
    return "\n".join(out)


def sparse_tree_rows(body, certs):
    """Derive only the carrier rows a plan-tree certificate actually combines.

    The Singular lift is sparse - `quarticUnownedTree8810_cert` combines three
    of its ten rows - but the kill derived all of them, and every derived row
    adds a rest bound, a band disjunction per load and a top-coefficient
    rewrite to every later arithmetic context.  Keep the rows the combination
    names, keep the band cascades the survivors share, and apply the same
    scalar identity in place.  `certs` is the emitted certificate section; the
    certificate lemmas themselves are untouched and still checked."""
    lines = body.split("\n")
    ei = [i for i, l in enumerate(lines)
          if re.match(r"^  exact quarticUnownedTree\d+810_cert ", l)]
    if len(ei) != 1:
        return body                      # trichotomy trees: several leaves
    ei = ei[0]
    call = lines[ei].split()
    cert, hsy = call[1], [x for x in call if x.startswith("hsy")]
    i = certs.index(f"theorem {cert}\n")
    j = certs.find("\nset_option maxHeartbeats", i)
    cb = certs[i:j if j > 0 else len(certs)]
    lc = re.search(r"^    linear_combination (.*)$", cb, re.M).group(1)
    tgt = re.search(r"^  have ht : (.*) = 0 := by$", cb, re.M).group(1)
    ne = re.search(r"^  exact (.*) ht$", cb, re.M).group(1)
    up = lambda s: re.sub(r"(?<![A-Za-z_0-9])([a-g])(?![A-Za-z_0-9])",
                          lambda m: f"{m.group(1).upper()}.leadingCoeff", s)
    used = sorted({int(m) for m in re.findall(r"\* hr(\d+)", lc)})
    keep = {hsy[i2] for i2 in used}
    comb = re.sub(r"\* hr(\d+)", lambda m: "* " + hsy[int(m.group(1))], up(lc))
    starts = [i2 for i2, l in enumerate(lines)
              if re.match(r"^  have hdp\d+ :", l)]
    out = lines[:starts[0]]
    for n, s in enumerate(starts):
        e = starts[n + 1] if n + 1 < len(starts) else ei
        blk = lines[s:e]
        if any(re.match(r"^  have (%s) :" % "|".join(keep), l) for l in blk):
            out += blk
            continue
        # a band cascade is shared: it must survive its own row being dropped
        i2 = 0
        while i2 < len(blk):
            if blk[i2].startswith("  obtain ⟨"):
                out.append(blk[i2])
                i2 += 1
                while i2 < len(blk) and blk[i2].startswith("    "):
                    out.append(blk[i2])
                    i2 += 1
            else:
                i2 += 1
    out += [f"  have ht : {up(tgt)} = 0 := by",
            f"    linear_combination {comb}",
            f"  exact {ne} ht"] + lines[ei + 1:]
    return "\n".join(out)


def split_carrier_rows(block, stem):
    """`(wrapper, [(module, lemma)])`: each carrier row of a tower chamber
    kill lifted into a private lemma of its own module.

    The tower's own scalar `quarticCostChamber<tag>810_impossible` needs every
    face row, so the sparse selection above does not apply; what does is that
    the rows are independent, so deriving each in a module of its own keeps
    the peak at one row's cost instead of the sum.  The public statement, its
    binders and the final call are unchanged."""
    lines = block.split("\n")
    ti = next(i for i, l in enumerate(lines) if l.startswith("theorem "))
    name = lines[ti].split()[1]
    bi = next(i for i, l in enumerate(lines) if l.strip() == "False := by")
    binders = lines[ti + 1:bi]
    args = " ".join(x for l in binders
                    for m in [re.match(r"^    \((.*?) :", l)] if m
                    for x in m.group(1).split())
    starts = [i for i, l in enumerate(lines) if re.match(r"^  have hdp\d+ :", l)]
    tail = next(i for i, l in enumerate(lines) if re.match(r"^  have hAc :", l))
    pre = lines[bi + 1:starts[0]]
    cut = next(i for i, l in enumerate(pre)
               if l.startswith("  obtain ⟨h") and i > 1)
    wrap_pre = [l.replace(":= hch", ":= id hch") for l in pre[:cut]]
    lemmas, calls, opens = [], [], []
    for i in range(len(starts)):
        blk = lines[starts[i]:(starts[i + 1] if i + 1 < len(starts) else tail)]

        def own(l, i=i):
            def fix(m):
                keep = [x for x in m.group(1).split()
                        if not re.fullmatch(r"(hdp|hdz)(\d+)", x)
                        or int(x[3:]) == i]
                return "clear * - " + " ".join(keep) + ";"
            return re.sub(r"clear \* - ([^;]*);", fix, l)
        blk = [own(l) if "clear * - " in l else l for l in blk]
        h = next(j for j, l in enumerate(blk)
                 if re.match(r"^  have hin%d :" % i, l))
        goal = [blk[h][len(f"  have hin{i} : "):]]
        j = h
        while not blk[j].rstrip().endswith(":= by"):
            j += 1
            goal.append(blk[j])
        goal[-1] = goal[-1][:-len(" := by")]
        mod = f"{stem}Row{i}Scratch"
        lemmas.append((mod, "\n".join(
            ["set_option maxHeartbeats 64000000 in",
             f"/-- Carrier row {i} of `{name}`. -/",
             f"private theorem {name}_row{i}"] + binders
            + ["    " + goal[0]] + goal[1:] + ["    := by"] + pre + blk
            + [f"  exact hin{i}", ""]) + "\n"))
        calls.append(f"  have hin{i} := {name}_row{i} {args}")
        opens.append(f"open private {name}_row{i} from {mod} in")
    wrap = "\n".join(opens + lines[:bi + 1] + wrap_pre + calls + lines[tail:])
    return wrap, lemmas


def close_imports(name, body):
    """Import every module that declares a name this module only references.

    Dedup (`have`) suppresses a declaration whenever some earlier module of
    the family already made it, of any kind - a column bound, a chamber face
    `_natDegree`, a rest bound, a kill.  The suppressing emitter does not
    always put that module on the import list, and the gate then reports
    `unknown identifier`.  This closes the gap once, for every emitter: the
    written text is the ground truth for what it references."""
    mod = name[:-5]
    lines = body.split("\n")
    last = -1
    for i, ln in enumerate(lines):
        if ln.startswith("import "):
            last = i
        elif ln.strip() and last >= 0:
            break
    if last < 0:
        return body
    have = set(_import_closure([l.split()[1] for l in lines[:last + 1]
                                if l.startswith("import Grok810")]))
    have.add(mod)
    local = {mm.group(1) for mm in
             (_DECL_RE.match(l) for l in lines) if mm}
    owners = name_owners()
    add = []
    for tok in set(_IDENT_RE.findall(_strip_comments(body))):
        if tok in local:
            continue
        cand = owners.get(tok)
        if not cand or cand & have:
            continue
        pick = sorted(m for m in cand if mod not in _import_closure([m]))
        if not pick:
            log(f"{name}: `{tok}` lives in {sorted(cand)}, which would cycle "
                "- left alone")
            continue
        m = pick[0]
        add.append(m)
        have |= _import_closure([m])
    if (REFL_NS + "." in _strip_comments(body)
            and f"import {REFL_LIB}\n" not in body):
        add.append(REFL_LIB)
    if not add:
        return body
    add = sorted(set(add))
    log(f"{name}: import closure added {len(add)} module(s): "
        + ", ".join(a.replace("Grok810ScaleZeroQuartic", "…") for a in add))
    lines[last + 1:last + 1] = [f"import {a}" for a in add]
    return "\n".join(lines)


# Lean does not release a declaration's elaboration memory when the
# declaration ends, so a module's peak grows with the number of declarations
# in it: the single-monomial kill families ran 51-95 declarations to a module
# and peaked at 13.6-19.8 GiB.  Cut them to at most this many declarations.
SPLIT_GROUP = 12
SPLIT_PARTS = {"Grok810ScaleZeroQuarticChamberKillsScratch",
               "Grok810ScaleZeroQuarticChamberKills2Scratch"}


def write_split(name, section, doc, body, prev):
    """Write `body` as part modules of at most `SPLIT_GROUP` declarations each
    and keep `name` itself as the aggregator that imports them, so every
    module downstream can go on importing the one name it always imported.

    Only the face-degree lemmas at the head of the body are used by the kills
    below, so they all go to part 1 and every later part imports part 1 and
    nothing else of the family - the parts then build in parallel rather than
    in a chain."""
    if name not in SPLIT_PARTS or not os.environ.get("SPLIT_KILLS"):
        out = (header(prev, doc) + f"section {section}\n\n" + body
               + f"\nend {section}\n" + FOOTER)
        return write(name + ".lean", out), [name]
    blocks = decl_blocks(body)
    face = [i for i, b in enumerate(blocks)
            if re.search(r"^theorem (\S+_natDegree)$", b, re.M)]
    k = max(face) + 1 if face else 0
    groups = [blocks[:k]] + [blocks[i:i + SPLIT_GROUP]
                             for i in range(k, len(blocks), SPLIT_GROUP)]
    stem = name[:-len("Scratch")]
    first = f"{stem}Part1Scratch"
    names = []
    for i, g in enumerate(groups, start=1):
        pn = f"{stem}Part{i}Scratch"
        out = (header(_flatten_imports(prev) + ([] if i == 1 else [first]), doc)
               + f"section {section}\n\n" + "".join(g).rstrip("\n") + "\n"
               + f"\nend {section}\n" + FOOTER)
        write(pn + ".lean", out)
        names.append(pn)
    agg = (header(_flatten_imports(prev) + names, doc)
           + f"section {section}\n\n" + f"end {section}\n" + FOOTER)
    ln = write(name + ".lean", agg)
    log(f"{name}: split into {len(groups)} parts of at most {SPLIT_GROUP} "
        f"declarations; aggregator {ln}L")
    return ln, names + [name]


def decl_blocks(body):
    """A concatenated emitted body cut back into one string per declaration.

    Every declaration this file emits is introduced by its own
    `set_option maxHeartbeats … in` guard, so that guard is the cut point.
    The section comment that heads the body is repeated on every piece, so
    each one still reads as the section it came from."""
    parts = body.split("\nset_option maxHeartbeats")
    if len(parts) == 1:
        return [body] if body.strip() else []
    lead = parts[0] + "\n" if parts[0].strip() else ""
    return [lead + "set_option maxHeartbeats" + x for x in parts[1:]]


EXHAUST_SPLIT = {"3", "4"}
# tower chamber kills whose five carrier rows do not fit a 16 GiB runner in
# one declaration; each row goes to a private lemma of its own module
TOWER_ROW_SPLIT = ("quarticChamberBCDEFG58810_impossible",
                   "quarticChamberBCDEFG15810_impossible",
                   # measured at 10.09 GiB with the Farkas keep-lists in place
                   "quarticChamberBCDEFG83810_impossible",
                   "quarticChamberBCDEFG11810_impossible")


def split_decls(name, section, doc, blocks, prev, tail="", base=0):
    """Write one declaration per module and keep `name` as the aggregator.

    A module's elaboration peak is the peak of its largest declaration, and
    `lake` runs four modules at once, so a single 20 GiB chamber kill sitting
    beside its siblings is what puts a 16 GiB runner over.  One declaration
    per module keeps each peak on its own; each part starts from `Mathlib`
    alone and lets `close_imports` add exactly the providers it names."""
    stem = name[:-len("Scratch")]
    names = []
    for i, b in enumerate(blocks, start=base):
        pn = f"{stem}Part{i}Scratch"
        out = (header(["Mathlib"], doc) + f"section {section}\n\n"
               + b.rstrip("\n") + "\n"
               + f"\nend {section}\n" + FOOTER)
        write(pn + ".lean", out)
        names.append(pn)
    agg = (header(_flatten_imports(prev) + names, doc)
           + f"section {section}\n\n" + f"end {section}\n" + tail + FOOTER)
    ln = write(name + ".lean", agg)
    log(f"{name}: {len(names)} one-declaration parts, aggregator {ln}L")
    return names


def write(name, body):
    body = refl_localize(name[:-5], body)
    body = close_imports(name, body)
    _register(name[:-5], body)
    n = body.count("\n")
    p = ROOT / name
    dump = os.environ.get("EMIT_DUMP")
    if dump:
        # regenerate the whole family into a directory and touch nothing, so
        # a change can be diffed against the receipted tree before it lands
        d = Path(dump)
        d.mkdir(parents=True, exist_ok=True)
        (d / name).write_text(body)
        return n
    only = os.environ.get("EMIT_ONLY")
    if only and name[:-5] not in only.split(","):
        return n
    if p.exists() and name not in GATED and name not in FORCE and is_green(name):
        if p.read_text() != body:
            REGEN.mkdir(parents=True, exist_ok=True)
            (REGEN / name).write_text(body)
            GREEN_SKIPPED.append(name)
            log(f"GREEN {name}: receipt on disk, left alone; the new text is "
                "in tools/sigma810/regen/")
        return n
    if name in GATED and p.exists():
        REGEN.mkdir(parents=True, exist_ok=True)
        q = REGEN / name
        q.write_text(body)
        same = q.read_text() == p.read_text()
        REGEN_VERDICT.append((name, same))
        log(f"gated {name}: regenerated into tools/sigma810/regen/, "
            f"{'byte-identical' if same else '*** DIFFERS ***'}")
        return n
    try:
        p.write_text(body)
        WRITTEN.add(name)
    except PermissionError:
        REGEN.mkdir(parents=True, exist_ok=True)
        q = REGEN / name
        q.write_text(body)
        same = q.read_text() == p.read_text()
        REGEN_VERDICT.append((name, same))
        log(f"FROZEN {name}: not writable, regenerated into "
            f"tools/sigma810/regen/, "
            f"{'byte-identical' if same else '*** DIFFERS ***'}")
        return n
    log(f"wrote {name}: {n} lines")
    return n


# ------------------------------------------------------------------ chambers
class Chamber:
    __slots__ = ("live", "argmin", "conjuncts", "leaves", "idx", "name")

    def __init__(self, live, argmin, conjuncts, leaves, idx):
        self.live = live
        self.argmin = argmin
        self.conjuncts = conjuncts
        self.leaves = leaves          # the JSON leaf chambers of this cell
        self.idx = idx
        self.name = f"{live}{idx}"

    @property
    def defname(self):
        return f"QuarticChamber{self.name}810"

    @property
    def ctor(self):
        return f"c{self.name}"

    @property
    def refined(self):
        return len(self.leaves) > 1

    @property
    def leaf(self):
        return self.leaves[0]

    def letters(self):
        return {ch: (ch in self.live) for ch in SIG}

    def nums(self):
        return [CC.strip(c) for c in self.conjuncts
                if not c.startswith("QuarticRatioConeA810")
                and not re.fullmatch(r"[A-G] [≠=] 0", CC.strip(c))]

    def cons(self):
        return CC.chamber_cons(self.conjuncts)


def build_chambers(data):
    cells = collections.OrderedDict()
    for c in data["chambers"]:
        cells.setdefault((c["live"], tuple(c["argmin"])), []).append(c)
    per_live = collections.Counter()
    chambers = []
    for (live, argmin), leaves in cells.items():
        base = leaves[0]["conjuncts"]
        for lf in leaves[1:]:
            assert lf["conjuncts"] == base, (live, argmin)
        idx = per_live[live]
        per_live[live] += 1
        chambers.append(Chamber(live, argmin, base, leaves, idx))
    return chambers


# ------------------------------------------------------------- the case tree
def mons1(mu2):
    return {"".join(sorted(p))
            for p in itertools.combinations_with_replacement(sorted(mu2), 2)}


def mons2(bc, fg):
    return {"".join(sorted(x + y)) for x in bc for y in fg}


def mons3(bc, om):
    out = set()
    for pair in itertools.combinations_with_replacement(sorted(bc), 2):
        for z in om:
            out.add("".join(sorted(pair + (z,))))
    return out


class Tree:
    """('node', lhsvec, rhsvec, [lt, eq, gt]) | ('leaf', key) | ('dead',)"""

    def __init__(self, index):
        self.index = index        # (live, argmin tuple) -> Chamber
        self.dead = 0
        self.live = 0

    def build(self, S):
        Sset = set(S)
        base = list(CC.CONEA) + list(CC.NONNEG) + [
            (CC.scal7(-1, CC.unit(LET.index(x))), False)
            for x in SIG if x not in Sset]
        bc = [c for c in "BC" if c in Sset]
        de = [c for c in "DE" if c in Sset]
        fg = [c for c in "FG" if c in Sset]

        def stage(g, cons, cont):
            if len(g) < 2:
                return cont(frozenset(g), cons)
            return self._tri(CC.sform(g[0]), CC.sform(g[1]), cons,
                             [frozenset([g[0]]), frozenset(g), frozenset([g[1]])],
                             cont)

        def after_bc(bcam, c1):
            def after_de(deam, c2):
                def after_fg(fgam, c3):
                    return self._mu(S, bcam, deam, fgam, c3)
                return stage(fg, c2, after_fg)
            return stage(de, c1, after_de)
        return stage(bc, base, after_bc)

    def _tri(self, u, v, cons, vals, cont):
        cs = [cons + [CC.gt(v, u)],
              cons + [CC.ge(v, u), CC.ge(u, v)],
              cons + [CC.gt(u, v)]]
        return ("node", u, v, [cont(vals[i], cs[i]) for i in range(3)])

    def _mu(self, S, bcam, deam, fgam, cons):
        def after(mu2, c):
            return self._omega(S, bcam, deam, fgam, mu2, c)
        if deam and fgam:
            return self._tri(CC.sform(sorted(deam)[0]), CC.sform(sorted(fgam)[0]),
                             cons, [deam, deam | fgam, fgam], after)
        return after(deam | fgam, cons)

    def _omega(self, S, bcam, deam, fgam, mu2, cons):
        def after(om, c):
            return self._cands(S, bcam, deam, fgam, mu2, om, c)
        if bcam and deam:
            return self._tri(CC.sform(sorted(bcam)[0]), CC.sform(sorted(deam)[0]),
                             cons, [bcam, bcam | deam, deam], after)
        return after(bcam if bcam else deam, cons)

    def _cands(self, S, bcam, deam, fgam, mu2, om, cons):
        cands = []
        if mu2:
            cands.append((CC.scal7(2, CC.sform(sorted(mu2)[0])), mons1(mu2)))
        if bcam and fgam:
            cands.append((CC.add7(CC.sform(sorted(bcam)[0]),
                                  CC.sform(sorted(fgam)[0])), mons2(bcam, fgam)))
        if bcam and om:
            cands.append((CC.add7(CC.scal7(2, CC.sform(sorted(bcam)[0])),
                                  CC.sform(sorted(om)[0])), mons3(bcam, om)))
        return self._compare(cands, cons, S)

    def _compare(self, cands, cons, S):
        if len(cands) == 1:
            return self._leaf(cands[0][1], cons, S)
        a, b = cands[0], cands[1]
        rest = cands[2:]
        outs = []
        for kind, extra, win in (
                ("lt", [CC.gt(b[0], a[0])], [a]),
                ("eq", [CC.ge(b[0], a[0]), CC.ge(a[0], b[0])],
                 [(a[0], a[1] | b[1])]),
                ("gt", [CC.gt(a[0], b[0])], [b])):
            outs.append(self._compare(win + rest, cons + extra, S))
        return ("node", a[0], b[0], outs)

    def _leaf(self, mons, cons, S):
        key = (S, tuple(sorted(mons, key=lambda m: (len(m), m))))
        cham = self.index.get(key)
        if cham is None:
            assert not CC.feasible(cons), f"unlisted but feasible chamber {key}"
            self.dead += 1
            return ("dead",)
        self.live += 1
        return ("leaf", cham, cons)


def prune(t):
    """Collapse subtrees all of whose leaves are dead."""
    if t[0] != "node":
        return t
    kids = [prune(x) for x in t[3]]
    if all(x[0] == "dead" for x in kids):
        return ("dead",)
    return ("node", t[1], t[2], kids)


# ------------------------------------------------------------------ emitters
CONE_A_DESTRUCT = """  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
"""


# Chamber definitions the gate lane had to guard individually (elaboration
# budget); reproduced here so a regeneration stays byte-identical to the gated
# module.
DEF_HEARTBEAT_FIXUPS = {"QuarticChamberBCDEFG134810"}


def chamber_def(c):
    out = []
    if c.defname in DEF_HEARTBEAT_FIXUPS:
        out.append("set_option maxHeartbeats 64000000 in")
    out += [f"/-- Cost-argmin chamber `{c.live}` / `{'·'.join(c.argmin)}`"
           f" (leaf{'s' if c.refined else ''} "
           f"{', '.join(l['id'] for l in c.leaves)}). -/"]
    out.append(f"def {c.defname} (A B C D E F G : k[X]) : Prop :=")
    fields = [CC.strip(x) for x in c.conjuncts]
    body = "  " + fields[0]
    for f in fields[1:]:
        body += " ∧\n    " + f
    out.append(body)
    return "\n".join(out) + "\n\n"


SIZE_IND = "QuarticChamberSupportSize{}810"


def support_defs(chambers):
    out = []
    for s in range(1, 7):
        grp = [c for c in chambers if len(c.live) == s]
        out.append("set_option maxHeartbeats 64000000 in")
        out.append(f"/-- The {len(grp)} cost-argmin chambers with |S| = {s}. -/")
        out.append(f"inductive {SIZE_IND.format(s)} (A B C D E F G : k[X]) : Prop")
        for c in grp:
            out.append(f"  | {c.ctor} : {c.defname} A B C D E F G →")
            out.append(f"      {SIZE_IND.format(s)} A B C D E F G")
        out.append("")
    out.append("set_option maxHeartbeats 64000000 in")
    out.append("/-- The full cost-argmin taxonomy of cone `A`: 1115 chambers. -/")
    out.append("inductive QuarticChamberSupport810 (A B C D E F G : k[X]) : Prop")
    for s in range(1, 7):
        out.append(f"  | size{s} : {SIZE_IND.format(s)} A B C D E F G →")
        out.append("      QuarticChamberSupport810 A B C D E F G")
    out.append("")
    return "\n".join(out) + "\n"


def inject(c):
    s = len(c.live)
    return (f"QuarticChamberSupport810.size{s} ({SIZE_IND.format(s)}.{c.ctor}", ")")


def leaf_term(c):
    pre, post = inject(c)
    parts = []
    for f in c.conjuncts:
        f = CC.strip(f)
        if f.startswith("QuarticRatioConeA810"):
            parts.append("hA")
            continue
        m = re.fullmatch(r"([A-G]) ≠ 0", f)
        if m:
            parts.append(f"h{m.group(1)}ne")
            continue
        m = re.fullmatch(r"([A-G]) = 0", f)
        if m:
            parts.append(f"h{m.group(1)}z")
            continue
        break
    if c.nums():
        parts.append("by omega")
    return f"exact {pre} ⟨{', '.join(parts)}⟩{post}"


def render_tree(t, indent, depth):
    ind = " " * indent
    if t[0] == "dead":
        return [f"{ind}exact (by omega : False).elim"]
    if t[0] == "leaf":
        return [f"{ind}{leaf_term(t[1])}"]
    L, R = CC.sides7(CC.sub7(t[1], t[2]))
    h = f"ht{depth}"
    out = [f"{ind}rcases lt_trichotomy ({L}) ({R}) with {h}a | {h}b | {h}c"]
    tags = ("<", "=", ">")
    for tag, kid in zip(tags, t[3]):
        sub = render_tree(kid, indent + 2, depth + 1)
        if len(sub) == 1:
            out.append(f"{ind}· {sub[0].strip()}")
        else:
            out.append(f"{ind}· -- {L} {tag} {R}")
            out += sub
    return out


# live sets whose whole case tree does not fit a 16 GiB runner in one
# declaration: lift every subtree at this depth into a private lemma of its
# own module.  The tree is unchanged - splicing the lemma bodies back in
# reproduces the original proof line for line.
SUBTREE_SPLIT = {"BCDEFG": 3}


def subtree_lemmas(S, tree):
    """`(wrapper theorem, [(lemma name, lemma text)])` for a live set whose
    tree is cut at `SUBTREE_SPLIT[S]`, or `(None, [])` when it is not cut."""
    depth = SUBTREE_SPLIT.get(S)
    if depth is None:
        return None, []
    hyps = []
    for ch in SIG:
        hyps.append(f"({'h' + ch + 'ne'} : {ch} ≠ 0)" if ch in S
                    else f"({'h' + ch + 'z'} : {ch} = 0)")
    zeros = [f"  have h{ch}n : {ch}.natDegree = 0 := by simp [h{ch}z]"
             for ch in SIG if ch not in S]
    lemmas = []

    def cut(t, path, conds):
        """Render `t` at `path`, lifting it out once `path` is deep enough."""
        if len(path) == depth:
            nm = f"chamberExhaust{S}Path{''.join(path)}"
            out = ["set_option maxHeartbeats 64000000 in",
                   f"/-- Cost-argmin subtree on the three comparison branches "
                   f"`{''.join(path)}`. -/",
                   f"private theorem {nm}",
                   "    (A B C D E F G : k[X])",
                   "    (hA : QuarticRatioConeA810 A B C D E F G)",
                   "    " + " ".join(hyps)]
            for h, c in conds:
                out.append(f"    ({h} : {c})")
            out[-1] += " :"
            out.append("    QuarticChamberSupport810 A B C D E F G := by")
            out.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
            out += zeros
            out += render_tree(t, 2, len(path))
            out.append("")
            lemmas.append((nm, "\n".join(out) + "\n"))
            args = (" A B C D E F G hA "
                    + " ".join(("h" + ch + "ne") if ch in S else ("h" + ch + "z")
                               for ch in SIG)
                    + " " + " ".join(h for h, _c in conds))
            return [f"exact {nm}{args}"]
        L, R = CC.sides7(CC.sub7(t[1], t[2]))
        h = f"ht{len(path)}"
        out = [f"rcases lt_trichotomy ({L}) ({R}) with {h}a | {h}b | {h}c"]
        for tag, suf, kid in zip(("<", "=", ">"), "abc", t[3]):
            sub = cut(kid, path + [str("abc".index(suf))],
                      conds + [(h + suf, f"({L}) {tag} ({R})"
                                if suf != "b" else f"({L}) = ({R})")])
            out.append(f"· -- {L} {tag} {R}")
            out += ["  " + x for x in sub]
        return out

    body = cut(tree, [], [])
    wrap = ["set_option maxHeartbeats 64000000 in",
            f"/-- Exhaust of the cost-argmin taxonomy on the live set `{S}`. -/",
            f"theorem quarticChamberSupport810_of_live_{S}",
            "    (A B C D E F G : k[X])",
            "    (hA : QuarticRatioConeA810 A B C D E F G)",
            "    " + " ".join(hyps) + " :",
            "    QuarticChamberSupport810 A B C D E F G := by",
            "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA"]
    wrap += zeros
    wrap += ["  " + x for x in body]
    wrap.append("")
    return "\n".join(wrap) + "\n", lemmas


def exhaust_theorem(S, tree):
    hyps = []
    for ch in SIG:
        hyps.append(f"({'h' + ch + 'ne'} : {ch} ≠ 0)" if ch in S
                    else f"({'h' + ch + 'z'} : {ch} = 0)")
    out = ["set_option maxHeartbeats 64000000 in",
           f"/-- Exhaust of the cost-argmin taxonomy on the live set `{S}`. -/",
           f"theorem quarticChamberSupport810_of_live_{S}",
           "    (A B C D E F G : k[X])",
           "    (hA : QuarticRatioConeA810 A B C D E F G)",
           "    " + " ".join(hyps) + " :",
           "    QuarticChamberSupport810 A B C D E F G := by",
           "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA"]
    for ch in SIG:
        if ch not in S:
            out.append(f"  have h{ch}n : {ch}.natDegree = 0 := by simp [h{ch}z]")
    out += render_tree(tree, 2, 0)
    out.append("")
    return "\n".join(out) + "\n"


def top_exhaust():
    """The 64-way vanishing split, mirroring `quarticSigmaSupportCone810_of`."""
    out = ["set_option maxHeartbeats 64000000 in",
           "/-- Every point of cone `A` with a live letter sits in exactly one",
           "cost-argmin chamber. -/",
           "theorem quarticChamberSupport810_of",
           "    {j t : k}",
           "    (l beta gamma delta epsilon zeta eta theta : k)",
           "    (A B C D E F G : k[X])",
           "    (hA : QuarticRatioConeA810 A B C D E F G)",
           "    (hjdiv : j / t ≠ 0)",
           "    (hder : derivative",
           "        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta",
           "          eta theta A B C D E F G) =",
           "        Polynomial.C (j / t)) :",
           "    QuarticChamberSupport810 A B C D E F G := by"]

    def rec(i, live, indent):
        ind = " " * indent
        if i == len(SIG):
            if not live:
                out.append(
                    f"{ind}exact (quarticSigmaSupportCone810_of_allZero A B C D E F G hA"
                    " l beta gamma delta epsilon zeta eta theta hjdiv hder"
                    " hBz hCz hDz hEz hFz hGz).elim")
            else:
                S = "".join(live)
                args = " ".join(
                    f"h{ch}{'ne' if ch in live else 'z'}" for ch in SIG)
                out.append(
                    f"{ind}exact quarticChamberSupport810_of_live_{S}"
                    f" A B C D E F G hA {args}")
            return
        ch = SIG[i]
        out.append(f"{ind}by_cases h{ch}z : {ch} = 0")
        out.append(f"{ind}· -- {ch} vanishes")
        rec(i + 1, live, indent + 2)
        out.append(f"{ind}· -- {ch} lives")
        out.append(f"{ind}  have h{ch}ne : {ch} ≠ 0 := h{ch}z")
        rec(i + 1, live + [ch], indent + 2)

    rec(0, [], 2)
    out.append("")
    return "\n".join(out) + "\n"


# --------------------------------------------------------------------- driver
BASE_IMPORT = "Grok810ScaleZeroQuarticSigmaLadderScratch"
MANIFEST = Path.home() / "lean/tools/sigma810/FILES_BC_MANIFEST.md"
REGEN = Path.home() / "lean/tools/sigma810/regen"
MODULES = []          # (filename, lines, description)

# Modules 1-9 are under coordinator gating: a rewrite changes their content key
# and invalidates the gate, so the emitter never touches them in place.  A
# re-run drops the regenerated text in `~/lean/tools/sigma810/regen/` and
# reports whether it is byte-identical to the gated file.
GATED = {
    "Grok810ScaleZeroQuarticChamberDefs1Scratch.lean",
    "Grok810ScaleZeroQuarticChamberDefs2Scratch.lean",
    "Grok810ScaleZeroQuarticChamberDefs3Scratch.lean",
    "Grok810ScaleZeroQuarticChamberDefs4Scratch.lean",
    "Grok810ScaleZeroQuarticChamberExhaust1Scratch.lean",
    "Grok810ScaleZeroQuarticChamberExhaust2Scratch.lean",
    "Grok810ScaleZeroQuarticChamberExhaust3Scratch.lean",
    "Grok810ScaleZeroQuarticChamberExhaust4Scratch.lean",
    "Grok810ScaleZeroQuarticChamberFacesScratch.lean",
    "Grok810ScaleZeroQuarticChamberN7BandsScratch.lean",
    "Grok810ScaleZeroQuarticChamberAuxTowerScratch.lean",
    "Grok810ScaleZeroQuarticChamberBandsScratch.lean",
    "Grok810ScaleZeroQuarticChamberCostLadderScratch.lean",
    "Grok810ScaleZeroQuarticAssemblyCoreScratch.lean",
    "Grok810ScaleZeroQuarticAssemblyScratch.lean",
}
GATED |= {f"Grok810ScaleZeroQuarticChamberFacesPart{_i}Scratch.lean"
          for _i in range(0, 20)}
GATED |= {f"Grok810ScaleZeroQuarticChamberInfra{_c}Scratch.lean"
          for _c in ("N2", "N3", "N4", "N5", "N6", "N7", "Omicron",
                     "Primitive")}
GATED |= {f"Grok810ScaleZeroQuarticChamber{_k}{_i}Scratch.lean"
          for _k in ("Columns", "Rests", "Kills", "Residual")
          for _i in ("", "2", "3", "4", "5", "6")}
# the tail of the chain is not receipted yet: those must land in the repo
GATED -= {"Grok810ScaleZeroQuarticChamberKills4Scratch.lean",
          "Grok810ScaleZeroQuarticChamberResidual4Scratch.lean",
          "Grok810ScaleZeroQuarticChamberColumns5Scratch.lean",
          "Grok810ScaleZeroQuarticChamberRests5Scratch.lean",
          "Grok810ScaleZeroQuarticChamberResidual5Scratch.lean",
          "Grok810ScaleZeroQuarticChamberRests6Scratch.lean",
          "Grok810ScaleZeroQuarticChamberResidual6Scratch.lean"}
GATED |= {"Grok810ScaleZeroQuarticChamberN7LadderScratch.lean",
          "Grok810ScaleZeroQuarticChamberNuFacesScratch.lean",
                }
GATED |= {x for x in os.environ.get("EMIT_GATED", "").split(",") if x}
GATED -= {x for x in os.environ.get("EMIT_UNGATED", "").split(",") if x}
# modules whose green receipt is deliberately being replaced
FORCE = {x for x in os.environ.get("EMIT_FORCE", "").split(",") if x}
# the hypotheses a chamber kill can reach for, in the order the helpers and
# their call sites bind them ({L} is the eight load letters)
RESID7_HYPS = {
    "hjdiv": "hjdiv : j / t ≠ 0",
    "hder": ("hder : derivative\n"
             "        (degreeZeroPrimitiveQuartic810 {L}\n"
             "          A B C D E F G) =\n"
             "      Polynomial.C (j / t)"),
    "hprimdeg": ("hprimdeg : (degreeZeroPrimitiveQuartic810 {L}\n"
                 "        A B C D E F G).natDegree = 1"),
    "hxiDeg": ("hxiDeg : (degreeZeroXiQuartic810 {L}\n"
               "        A B C D E F G).natDegree = 0"),
    "hmuDeg": ("hmuDeg : (degreeZeroMuQuartic810 {L}\n"
               "        A B C D E F G).natDegree = 0"),
    "homiDeg": ("homiDeg : (degreeZeroOmicronQuartic810 {L}\n"
                "        A B C D E F G).natDegree = 0"),
    "hkapDeg": ("hkapDeg : (degreeZeroKappaQuartic810 {L}\n"
                "        A B C D E F G).natDegree = 0"),
    "hnuDeg": ("hnuDeg : (degreeZeroNuQuartic810 {L}\n"
               "        A B C D E F G).natDegree = 0"),
    "hpiDeg": ("hpiDeg : (degreeZeroPiQuartic810 {L}\n"
               "        A B C D E F G).natDegree = 0"),
    "hconeA": "hconeA : QuarticRatioConeA810 A B C D E F G",
    "hnc": ("hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧\n"
            "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0)"),
}


REGEN_VERDICT = []


def emit_defs(chambers):
    groups = [("1", [1, 2, 3]), ("2", [4]), ("3", [5]), ("4", [6])]
    prev = BASE_IMPORT
    for tag, sizes in groups:
        grp = [c for c in chambers if len(c.live) in sizes]
        name = f"Grok810ScaleZeroQuarticChamberDefs{tag}Scratch"
        doc = (
            f"# Cost-argmin chamber definitions ({tag}/4), `(8,10)` scale zero\n\n"
            f"The {len(grp)} chambers whose live-letter set `S` has "
            f"|S| ∈ {{{', '.join(map(str, sizes))}}}, machine-generated from\n"
            "`scripts/out_810_scale_zero_quartic_chambers.json` by\n"
            "`scripts/emit_810_quartic_chambers_lean.py`.  A chamber is one\n"
            "argmin cell of `cost(m) = Σ m_X s_X`, `s_X = w_X·a − 2·natDegree X`,\n"
            "on cone `A`; the conjuncts are the cross-multiplied ℕ cost ties and\n"
            "strict comparisons of `~/lean/tools/sigma810/CHAMBERS.md` §1.\n"
            "Definitions only — no proofs.  Untracked working note."
        )
        body = header(prev, doc)
        for c in grp:
            body += chamber_def(c)
        if tag == "4":
            body += "/-! ## The taxonomy -/\n\n"
            body += support_defs(chambers)
        body += FOOTER
        n = write(name + ".lean", body)
        MODULES.append((name, n,
                        f"{len(grp)} chamber `Prop`s (|S| ∈ "
                        f"{{{', '.join(map(str, sizes))}}})"
                        + (", the six size-graded `inductive`s and "
                           "`QuarticChamberSupport810`" if tag == "4" else "")))
        prev = name
    return prev


def emit_exhaust(chambers, prev):
    index = {(c.live, c.argmin): c for c in chambers}
    tb = Tree(index)
    trees = {}
    for r in range(1, 7):
        for combo in itertools.combinations(SIG, r):
            S = "".join(combo)
            trees[S] = prune(tb.build(S))
    log(f"tree: {tb.live} live leaves, {tb.dead} infeasible leaves "
        f"(all Farkas-checked)")
    groups = [("1", [1, 2, 3]), ("2", [4]), ("3", [5]), ("4", [6])]
    for tag, sizes in groups:
        sets = [S for S in trees if len(S) in sizes]
        name = f"Grok810ScaleZeroQuarticChamberExhaust{tag}Scratch"
        doc = (
            f"# Cost-argmin chamber exhaust ({tag}/4), `(8,10)` scale zero\n\n"
            f"The {len(sets)} live-letter sets with |S| ∈ "
            f"{{{', '.join(map(str, sizes))}}}.  Each theorem runs the case tree\n"
            "of `CHAMBERS.md` §1: a linear tournament for `β = min s|_{B,C}`,\n"
            "`q = min s|_{D,E}`, `r = min s|_{F,G}`, then `μ₂ = min(q,r)`,\n"
            "`ω = min(β,q)`, then the three cost types `2μ₂`, `β+r`, `2β+ω`\n"
            "against each other.  Branches no chamber matches are ℚ-infeasible\n"
            "(exact Farkas certificates in\n"
            "`scripts/check_810_quartic_chambers_lean.py`) and close by `omega`.\n"
            "Untracked working note."
        )
        decls, subs, wired = [], [], []
        for S in sorted(sets, key=lambda s: (len(s), s)):
            wrap, lem = subtree_lemmas(S, trees[S])
            if wrap is None:
                decls.append(exhaust_theorem(S, trees[S]))
            else:
                decls.append(wrap)
                wired.append((len(decls) - 1, [nm for nm, _x in lem],
                              len(subs)))
                subs += [x for _nm, x in lem]
        if tag == "4":
            decls.append(top_exhaust())
        # the subtree lemmas are private in modules of their own, so the
        # wrapper has to open them by name from the module they landed in;
        # `split_decls` puts them right after the public declarations.
        stem = name[:-len("Scratch")]
        for di, nms, off in wired:
            opens = [f"open private {nm} from "
                     f"{stem}Part{len(decls) + off + i}Scratch in"
                     for i, nm in enumerate(nms)]
            decls[di] = "\n".join(opens) + "\n" + decls[di]
        if wired:
            prev = _flatten_imports(prev) + ["Batteries.Tactic.OpenPrivate"]
        if tag in EXHAUST_SPLIT:
            # `|S| = 5` and `|S| = 6` are the two exhausts whose single
            # largest live set does not fit a 16 GiB runner beside its
            # siblings; give each live set its own module.
            split_decls(name, "QuarticChamberExhaust810", doc, decls + subs,
                        prev,
                        tail=("\n#print axioms quarticChamberSupport810_of\n"
                              if tag == "4" else ""))
            n = sum(b.count("\n") for b in decls + subs)
        else:
            body = header(prev, doc)
            body += "section QuarticChamberExhaust810\n\n" + "".join(decls)
            body += "\nend QuarticChamberExhaust810\n"
            if tag == "4":
                body += "\n#print axioms quarticChamberSupport810_of\n"
            body += FOOTER
            n = write(name + ".lean", body)
        MODULES.append((name, n, f"exhaust for the {len(sets)} live sets with "
                                 f"|S| ∈ {{{', '.join(map(str, sizes))}}}"
                        + (" plus the 64-way vanishing split "
                           "`quarticChamberSupport810_of`" if tag == "4" else "")))
        prev = name
    return prev, trees




# ---------------------------------------------------------- faces and rests
import _810_quartic_emit_common as EC  # noqa: E402

CARRIERS = ["kappa", "mu", "xi", "pi"]
LOADS = CC.LOADS
CHUNK = 20


def rec_key(rec):
    return tuple(int((rec.get("exps") or {}).get(L, 0) or 0) for L in LET)


def deg_expr(exps):
    parts = []
    for L in LET:
        e = int(exps.get(L, 0) or 0)
        if e == 1:
            parts.append(f"{L}.natDegree")
        elif e > 1:
            parts.append(f"{e} * {L}.natDegree")
    return " + ".join(parts) if parts else "0"


def face_records(coords, form, argmin, chambers_faces):
    """The load-free records of `form` whose monomial lies in the face."""
    keys = chambers_faces[(form, argmin)]
    return [r for r in EC.sort_records(coords[form + "_lf"]) if rec_key(r) in keys]


def poly_def(name, params, recs, letters=LET):
    head = f"def {name}\n"
    if params:
        head += f"    ({params} : k)\n"
    head += "    (A B C D E F G : k[X]) : k[X] :=\n"
    refl_register(name, params, recs)
    return head + EC.records_to_lean(recs) + "\n\n"


def split_chunks(recs, size=CHUNK):
    return [recs[i:i + size] for i in range(0, len(recs), size)] or [[]]


# ------------------------------------------------------- reflective degree
# `compute_degree` closes `natDegree p < d` by decomposing `p` structurally
# and `norm_num`-normalising the resulting `max` tree.  On these machine-
# emitted rests -- tens of monomials in seven symbolic atoms over an abstract
# `[Field k]` -- that last step is what the chamber taxonomy spends its CPU
# on: 5-35 s per call, and there are thousands of calls.
#
# `Max11SpeedReflectDegLibScratch` reflects the polynomial instead: the
# emitter writes out the coefficient list and the exponent vectors, the
# library proves `natDegree (polyOf as cs es) <= bnd (as.map natDegree) es`
# once by induction, and the residual goal is linear arithmetic in the atom
# degrees that `omega` closes.  One `module` per *definition* then replaces
# one `compute_degree` per *(definition, live set)* bound, and each module
# carries its own private copy of the bridges it uses, so nothing is added to
# any module's public interface.
REFL_NS = "Max11ReflectDeg"
REFL_LIB = "Max11SpeedReflectDegLibScratch"
REFL_PREFIX = "refl810PolyOf_"
REFL_DATA = {}            # polynomial def name -> (scalar params, records)
_REFL_USE_RE = re.compile(REFL_PREFIX + r"([A-Za-z0-9_]+)")


def refl_coeff(rec):
    """The record's scalar as a `k`-typed coefficient of `polyOf`."""
    qn, qd = int(rec["qn"]), int(rec["qd"])
    loads = rec.get("loads") or {}
    facs = []
    for n in EC.LOAD_NAMES:
        e = int(loads.get(n, 0) or 0)
        if e == 1:
            facs.append(n)
        elif e > 1:
            raise RuntimeError(f"load power {n}^{e}")
    core = f"{abs(qn)}" if qd == 1 else f"{abs(qn)} / {qd}"
    if facs:
        core = core + " * " + " * ".join(facs)
    return f"(-({core}) : k)" if qn < 0 else f"({core} : k)"


def refl_exps(rec, letters=LET):
    ex = rec.get("exps") or {}
    return [int(ex.get(L, 0) or 0) for L in letters]


def _refl_wrap(items, per, ind="      "):
    return "\n".join(
        ind + ", ".join(items[i:i + per]) + ("," if i + per < len(items) else "")
        for i in range(0, len(items), per))


def refl_register(name, params, recs):
    """Record a monomial definition so its bridge can be reconstructed."""
    if recs:
        REFL_DATA[name] = (params, list(recs))


def refl_ok(name):
    return name in REFL_DATA


def refl_bridge_text(name, letters=LET):
    """`name … = polyOf [A…G] cs es`, private to whichever module uses it."""
    params, recs = REFL_DATA[name]
    args = params.split() if params else []
    cs = [refl_coeff(r) for r in recs]
    es = ["[" + ", ".join(str(x) for x in refl_exps(r, letters)) + "]"
          for r in recs]
    o = ["set_option maxHeartbeats 64000000 in",
         f"/-- Reflected monomial data for `{name}` ({len(recs)} monomials).",
         "The reflective degree checker of `Max11SpeedReflectDegLibScratch`",
         "replaces `compute_degree` on every bound of this polynomial. -/",
         f"private theorem {REFL_PREFIX}{name}"]
    if params:
        o.append(f"    ({params} : k)")
    o.append("    (A B C D E F G : k[X]) :")
    o.append("    " + " ".join([name] + args + list(letters)) + " =")
    o.append(f"      {REFL_NS}.polyOf [" + ", ".join(letters) + "]")
    o.append("      [")
    o.append(_refl_wrap(cs, 3))
    o.append("      ]")
    o.append("      [")
    o.append(_refl_wrap(es, 4))
    o.append("      ] := by")
    o.append(f"  simp only [{name}, {REFL_NS}.polyOf_cons,")
    o.append(f"    {REFL_NS}.polyOf_nil_right, {REFL_NS}.mono_cons,")
    o.append(f"    {REFL_NS}.mono_nil_left, {REFL_NS}.mono_nil_right,")
    o.append("    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]")
    o.append("  all_goals module")
    o.append("")
    return "\n".join(o) + "\n"


def refl_bnd_proof(name, ind="  "):
    """`(name …).natDegree < d` from one hypothesis per monomial."""
    return [f"{ind}rw [{REFL_PREFIX}{name}]",
            f"{ind}apply {REFL_NS}.natDegree_lt_of_bnd_lt",
            f"{ind}simp only [{REFL_NS}.bnd_cons, {REFL_NS}.bnd_nil,",
            f"{ind}  {REFL_NS}.mdeg_cons, {REFL_NS}.mdeg_nil_left,",
            f"{ind}  {REFL_NS}.mdeg_nil_right, List.map_cons, List.map_nil,",
            f"{ind}  Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,",
            f"{ind}  max_lt_iff]",
            f"{ind}repeat' apply And.intro",
            f"{ind}all_goals omega"]


def refl_degok_proof(name, ind="  ", pos="hdpos"):
    """`(name …).natDegree < d` once the dead letters have been `subst`-ed.

    `bnd` is blind to a monomial that died because one of its atoms was set to
    zero, so the branch-aware `degOk` checker is used instead: the `simp only`
    turns every dead monomial's side condition into `True` and normalises
    every surviving one into a linear form in the atom degrees, and `omega`
    finishes from the bound's own hypotheses."""
    return [f"{ind}rw [{REFL_PREFIX}{name}]",
            f"{ind}refine {REFL_NS}.natDegree_polyOf_lt_of_degOk {pos} ?_",
            f"{ind}simp only [{REFL_NS}.degOk_cons, {REFL_NS}.degOk_nil_left,",
            f"{ind}  {REFL_NS}.degOk_nil_right, {REFL_NS}.mono_cons,",
            f"{ind}  {REFL_NS}.mono_nil_left, {REFL_NS}.mono_nil_right,",
            f"{ind}  {REFL_NS}.mdeg_cons, {REFL_NS}.mdeg_nil_left,",
            f"{ind}  {REFL_NS}.mdeg_nil_right, List.map_cons, List.map_nil,",
            f"{ind}  {POWNAMES},",
            f"{ind}  natDegree_zero, pow_zero, pow_one, one_mul, mul_one,",
            f"{ind}  zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,",
            f"{ind}  true_or, or_true, true_and, and_true]",
            f"{ind}repeat' apply And.intro",
            f"{ind}all_goals exact Or.inr (Or.inr (by omega))"]


def refl_tag(mod):
    t = mod
    for pre in ("Grok810ScaleZeroQuartic", "Astra810ScaleZeroQuartic",
                "Fable810ScaleZeroQuartic"):
        if t.startswith(pre):
            t = t[len(pre):]
            break
    if t.endswith("Scratch"):
        t = t[:-len("Scratch")]
    return "".join(ch for ch in t if ch.isalnum()) or "X"


_REFL_ANCHOR = "variable {k : Type*} [Field k] [CharZero k]\n\n"


_REFL_BLOCK_START = ("set_option", "theorem", "def", "private", "/--", "/-!",
                     "noncomputable", "@[")


def _refl_block_start(body, pos):
    """The start of the top-level declaration block containing `pos`.

    Emitted declarations are blank-line separated blocks of column-0 text, so
    the previous blank line is the block boundary."""
    j = body.rfind("\n\n", 0, pos)
    while j >= 0:
        k = j + 2
        if body[k:].startswith(_REFL_BLOCK_START):
            return k
        j = body.rfind("\n\n", 0, j)
    return None


def refl_localize(mod, body):
    """Give `mod` its own private copy of every reflection bridge it uses.

    The bridges are private, so two modules may both carry the bridge of the
    same definition; the name is tagged with the module anyway so that the
    structural checker's global no-duplicate-declaration rule still holds.
    Each bridge is spliced in front of the declaration that first uses it,
    which puts it after the definition whenever that definition is emitted by
    this same module."""
    used = list(dict.fromkeys(_REFL_USE_RE.findall(body)))
    if not used:
        return body
    fallback = body.index(_REFL_ANCHOR) + len(_REFL_ANCHOR)
    m = re.match(r"section \S+\n\n", body[fallback:])
    if m:
        fallback += m.end()
    spots = []
    for n in used:
        pos = body.index(REFL_PREFIX + n)
        at = _refl_block_start(body, pos)
        spots.append((fallback if at is None else at, n))
    for at, n in sorted(spots, key=lambda x: -x[0]):
        body = body[:at] + refl_bridge_text(n) + "\n" + body[at:]
    return body.replace(REFL_PREFIX, f"{REFL_PREFIX}{refl_tag(mod)}_")


def bound_lemma_split(name, params, recs):
    """`bound_lemma` with the `compute_degree` split so that no piece ever sees
    more than `CD_MAX` monomials.  The outer lemma keeps its name, its binders
    and its statement; the pieces are new declarations."""
    hyps, seen = [], {}
    for r in recs:
        e = deg_expr(r.get("exps") or {})
        if e not in seen:
            seen[e] = f"hd{len(seen)}"
            hyps.append((seen[e], e))
    if len(recs) <= CD_MAX:
        return bound_lemma(name, params, recs)
    args = params.split() if params else []
    parts = split_chunks(recs, CD_MAX)
    body = ""
    for pi, chunk in enumerate(parts):
        pn = f"{name}s{pi + 1}"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Piece {pi + 1}/{len(parts)} of `{name}` "
                 f"({len(chunk)} monomials): a `compute_degree` over more than "
                 "six\nmonomials with seven symbolic degrees times out. -/\n")
        body += poly_def(pn, params, chunk)
        ph, pseen = [], {}
        for r in chunk:
            e = deg_expr(r.get("exps") or {})
            if e not in pseen:
                pseen[e] = f"hd{len(pseen)}"
                ph.append((pseen[e], e))
        o = ["set_option maxHeartbeats 64000000 in",
             f"theorem {pn}_natDegree_lt", "    {d : \u2115}"]
        if params:
            o.append(f"    ({params} : k)")
        o.append("    (A B C D E F G : k[X])")
        for h, e in ph:
            o.append(f"    ({h} : {e} < d)")
        o[-1] += " :"
        o.append("    (" + " ".join([pn] + args + list("ABCDEFG"))
                 + ").natDegree < d := by")
        if refl_ok(pn):
            o += refl_bnd_proof(pn)
        else:
            o.append(f"  simp only [{pn}]")
            o.append("  compute_degree")
            o.append("  omega")
        o.append("")
        body += "\n".join(o) + "\n"
    o = ["set_option maxHeartbeats 64000000 in", f"theorem {name}_split"]
    if params:
        o.append(f"    ({params} : k)")
    o.append("    (A B C D E F G : k[X]) :")
    o.append("    " + " ".join([name] + args + list("ABCDEFG")) + " =")
    o.append("      " + " +\n        ".join(
        " ".join([f"{name}s{pi + 1}"] + args + list("ABCDEFG"))
        for pi in range(len(parts))) + " := by")
    o.append(f"  simp only [{name}, "
             + ", ".join(f"{name}s{pi + 1}" for pi in range(len(parts))) + "]")
    o.append("  all_goals module")
    o.append("")
    body += "\n".join(o) + "\n"
    o = ["set_option maxHeartbeats 64000000 in",
         f"theorem {name}_natDegree_lt", "    {d : \u2115}"]
    if params:
        o.append(f"    ({params} : k)")
    o.append("    (A B C D E F G : k[X])")
    for h, e in hyps:
        o.append(f"    ({h} : {e} < d)")
    o[-1] += " :"
    o.append("    (" + " ".join([name] + args + list("ABCDEFG"))
             + ").natDegree < d := by")
    o.append("  rw [" + " ".join([f"{name}_split"] + args + list("ABCDEFG"))
             + "]")
    accs = []
    for pi, chunk in enumerate(parts):
        aa, ps = [], []
        for r in chunk:
            e = deg_expr(r.get("exps") or {})
            if e not in ps:
                ps.append(e)
                aa.append(seen[e])
        accs.append("(" + " ".join([f"{name}s{pi + 1}_natDegree_lt"] + args
                                   + list("ABCDEFG") + aa) + ")")
    acc = accs[0]
    for a in accs[1:]:
        acc = f"(natDegree_add_lt810 {acc} {a})"
    o.append(f"  exact {acc}")
    o.append("")
    body += "\n".join(o) + "\n"
    return body, [e for _, e in hyps]


def bound_lemma(name, params, recs, extra_hyps=()):
    """`natDegree < d` from one hypothesis per monomial."""
    hyps = []
    seen = {}
    for r in recs:
        e = deg_expr(r.get("exps") or {})
        if e not in seen:
            seen[e] = f"hd{len(seen)}"
            hyps.append((seen[e], e))
    out = ["set_option maxHeartbeats 64000000 in",
           f"theorem {name}_natDegree_lt",
           "    {d : ℕ}"]
    if params:
        out.append(f"    ({params} : k)")
    out.append("    (A B C D E F G : k[X])")
    for h, e in hyps:
        out.append(f"    ({h} : {e} < d)")
    for h in extra_hyps:
        out.append(f"    ({h})")
    args = (params.split() if params else [])
    out[-1] = out[-1] + " :"
    call = " ".join([name] + args + ["A", "B", "C", "D", "E", "F", "G"])
    out.append(f"    ({call}).natDegree < d := by")
    if refl_ok(name):
        out += refl_bnd_proof(name)
    else:
        out.append(f"  simp only [{name}]")
        out.append("  compute_degree")
        out.append("  omega")
    out.append("")
    return "\n".join(out) + "\n", [e for _, e in hyps]


PI_GROUP_DEFS = ["piBaseGroupQuartic810", "piBetaGroupQuartic810",
                 "piGammaGroupQuartic810", "piDeltaGroupQuartic810",
                 "piEpsilonGroupQuartic810", "piZetaGroupQuartic810",
                 "piEtaGroupQuartic810", "piThetaGroupQuartic810"]


ZERO_SIMP = ("zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, "
             "sub_zero, zero_sub, neg_zero, natDegree_zero")


def parse_face(s):
    """A `faces` entry of the chamber JSON -> the set of monomial keys."""
    keys = set()
    for term in s.split(" + "):
        m = re.match(r"^\((-?\d+(?:/\d+)?)\)\s*\*\s*(.*)$", term.strip())
        if not m:
            continue
        exps = [0] * 7
        for fct in m.group(2).split("*"):
            mm = re.fullmatch(r"([a-g])(?:\^(\d+))?", fct.strip())
            assert mm, fct
            exps[LET.index(mm.group(1).upper())] += int(mm.group(2) or 1)
        keys.add(tuple(exps))
    return frozenset(keys)


def killable(c):
    return (c["certificate"]["kind"] in ("single_monomial", "power_target")
            and not c["weak_bands"])


def emit_faces(data, coords, chambers, prev):
    """Face packets are keyed by (carrier, face monomial set) — the face of a
    carrier depends on the live set as well as on the argmin, so two chambers
    with the same argmin but different `S` are different packets."""
    packets = collections.OrderedDict()      # (form, faceset) -> id
    uses = collections.defaultdict(set)      # (form, faceset) -> {live}
    names = collections.defaultdict(set)     # (form, faceset) -> {argmin}
    for c in data["chambers"]:
        if not killable(c):
            continue
        for cr in c["certificate"]["carriers"]:
            if cr not in CARRIERS:
                continue
            key = (cr, parse_face(c["faces"][cr]))
            if key not in packets:
                packets[key] = None
            uses[key].add(c["live"])
            names[key].add("·".join(c["argmin"]))
    per_form = collections.Counter()
    for key in packets:
        packets[key] = per_form[key[0]]
        per_form[key[0]] += 1
    log(f"{len(packets)} face packets, "
        f"{sum(len(v) for v in uses.values())} (packet, live set) rest bounds")

    body = ""
    for form in CARRIERS:
        lf = EC.sort_records(coords[form + "_lf"])
        body += (f"/-! ## `{CC.GREEK[form]}`: load-free part and the eight "
                 "load columns -/\n\n")
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- The load-free part of `{CC.FORM_LEAN[form]}` "
                 f"({len(lf)} monomials). -/\n")
        body += poly_def(f"{form}QuarticLoadFree810", "", lf)
        cols = {}
        for ld in LOADS:
            recs = EC.sort_records([r for r in coords[form]
                                    if (r.get("loads") or {}).get(ld)])
            chunks = split_chunks(recs)
            nms = []
            for i, chunk in enumerate(chunks):
                nm = (f"{form}QuarticColumn{CC.LOAD_CAP[ld]}810" if len(chunks) == 1
                      else f"{form}QuarticColumn{CC.LOAD_CAP[ld]}{i + 1}810")
                nms.append(nm)
                body += "set_option maxHeartbeats 64000000 in\n"
                body += (f"/-- The `{ld}` column of `{CC.FORM_LEAN[form]}`"
                         + (f", chunk {i + 1}/{len(chunks)}" if len(chunks) > 1 else "")
                         + f" ({len(chunk)} monomials). -/\n")
                body += poly_def(nm, ld, chunk)
                lem, _ = bound_lemma(nm, ld, chunk)
                body += lem
                body += (f"theorem {nm}_zero (A B C D E F G : k[X]) :\n"
                         f"    {nm} 0 A B C D E F G = 0 := by\n"
                         f"  simp [{nm}]\n\n")
            cols[ld] = nms
        simpset = [CC.FORM_LEAN[form], f"{form}QuarticLoadFree810"] + \
            [n for ns in cols.values() for n in ns]
        if form == "pi":
            simpset += PI_GROUP_DEFS
        rhs = f"{form}QuarticLoadFree810 A B C D E F G"
        for ld in LOADS:
            for nm in cols[ld]:
                rhs += f" +\n      {nm} {ld} A B C D E F G"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Cone-free split of `{CC.FORM_LEAN[form]}` into its "
                 "load-free part and its eight load columns. -/\n")
        body += (f"theorem {CC.FORM_LEAN[form]}_eq_chamberSplit\n"
                 "    (l beta gamma delta epsilon zeta eta theta : k)\n"
                 "    (A B C D E F G : k[X]) :\n"
                 f"    {CC.FORM_LEAN[form]} l beta gamma delta epsilon zeta eta theta\n"
                 "        A B C D E F G =\n"
                 f"      {rhs} := by\n"
                 f"  simp only [{', '.join(simpset)}]\n"
                 "  all_goals module\n\n")

    infra = body
    body = ""
    packets_body = ""
    bounds = []
    for (form, faceset), n in packets.items():
        lf = EC.sort_records(coords[form + "_lf"])
        face = [r for r in lf if rec_key(r) in faceset]
        rest = [r for r in lf if rec_key(r) not in faceset]
        assert len(face) == len(faceset)
        fname = f"{form}QuarticChamberFace{n}810"
        rname = f"{form}QuarticChamberRestLF{n}810"
        d = deg_expr(face[0].get("exps") or {})
        argmins = ", ".join(sorted(names[(form, faceset)])[:4])
        packets_body += "set_option maxHeartbeats 64000000 in\n"
        packets_body += (f"/-- Face of `{CC.GREEK[form]}` on the argmin packet(s) "
                         f"`{argmins}` ({len(face)} monomial"
                         f"{'s' if len(face) > 1 else ''}, top degree `{d}`). -/\n")
        packets_body += poly_def(fname, "", face)
        packets_body += "set_option maxHeartbeats 64000000 in\n"
        packets_body += (f"/-- Load-free rest of `{CC.GREEK[form]}` off packet "
                         f"{n} ({len(rest)} monomials). -/\n")
        packets_body += poly_def(rname, "", rest)
        packets_body += "set_option maxHeartbeats 64000000 in\n"
        packets_body += (f"theorem {form}QuarticLoadFree810_eq_face{n}_add_rest\n"
                         "    (A B C D E F G : k[X]) :\n"
                         f"    {form}QuarticLoadFree810 A B C D E F G =\n"
                         f"      {fname} A B C D E F G + {rname} A B C D E F G := by\n"
                         f"  simp only [{form}QuarticLoadFree810, {fname}, {rname}]\n"
                         "  all_goals module\n\n")
        for S in sorted(uses[(form, faceset)], key=lambda s: (len(s), s)):
            live = set(S)
            surv, hyps, seen = [], [], {}
            for r in rest:
                ex = r.get("exps") or {}
                if any(int(ex.get(L, 0) or 0) > 0 and L != "A" and L not in live
                       for L in LET):
                    continue
                e = deg_expr(ex)
                if e not in seen:
                    seen[e] = f"hd{len(seen)}"
                    hyps.append((seen[e], e))
                surv.append(r)
            dead = [ch for ch in SIG if ch not in live]
            out = ["set_option maxHeartbeats 64000000 in",
                   f"theorem {rname}_natDegree_lt_of_live_{S}",
                   "    {d : ℕ}",
                   "    (A B C D E F G : k[X])",
                   "    (hdpos : 0 < d)"]
            for ch in dead:
                out.append(f"    (h{ch}z : {ch} = 0)")
            for h, e in hyps:
                out.append(f"    ({h} : {e} < d)")
            out[-1] += " :"
            out.append(f"    ({rname} A B C D E F G).natDegree < d := by")
            for ch in dead:
                out.append(f"  subst h{ch}z")
            for e in range(2, 9):
                out.append(f"  have hpow{e} : (0 : k[X]) ^ {e} = 0 := "
                           f"zero_pow (by decide)")
            pows = ", ".join(f"hpow{e}" for e in range(2, 9))
            if surv and refl_ok(rname):
                out += refl_degok_proof(rname)
            else:
                out.append(f"  simp only [{rname}, {pows}, {ZERO_SIMP}]")
                out.append("  omega")
            out.append("")
            bounds.append("\n".join(out) + "\n")

    parts = []
    p0 = "Grok810ScaleZeroQuarticChamberFacesPart0Scratch"
    doc0 = (
        "# Cost-argmin faces and rests, part 0: the carriers, `(8,10)` scale zero\n\n"
        "For each carrier `κ, μ, ξ, π`: the load-free part, the eight load\n"
        f"columns (chunked at {CHUNK} monomials) with their `natDegree` bounds and\n"
        "`_zero` lemmas, and the cone-free module identity splitting the integral\n"
        "into them.  Imported by every other `…FacesPart*` module.  Untracked note."
    )
    out0 = header(prev, doc0) + "section QuarticChamberFaces810\n\n" + infra
    out0 += "\nend QuarticChamberFaces810\n" + FOOTER
    parts.append((p0, write(p0 + ".lean", out0)))

    p1 = "Grok810ScaleZeroQuarticChamberFacesPart1Scratch"
    doc1 = (
        "# Cost-argmin faces and rests, part 1: the packets, `(8,10)` scale zero\n\n"
        f"The {len(packets)} face packets — a packet is a *(carrier, face monomial\n"
        "set)* pair, since the face depends on the live set as well as on the\n"
        "argmin — each with its face, its load-free rest and the cone-free packet\n"
        "split identity.  Definitions and identities only; the rest *bounds* are\n"
        "in the sibling `…FacesPart2..PartN` modules, which are mutually\n"
        "independent.  Untracked working note."
    )
    out1 = header(p0, doc1) + "section QuarticChamberFaces810\n\n" + packets_body
    out1 += "\nend QuarticChamberFaces810\n" + FOOTER
    parts.append((p1, write(p1 + ".lean", out1)))

    PER = 80
    groups = [bounds[i:i + PER] for i in range(0, len(bounds), PER)]
    for gi, grp in enumerate(groups):
        pn = f"Grok810ScaleZeroQuarticChamberFacesPart{gi + 2}Scratch"
        docn = (
            f"# Cost-argmin rest bounds, part {gi + 2}/{len(groups) + 1}, "
            "`(8,10)` scale zero\n\n"
            f"{len(grp)} of the {len(bounds)} load-free rest bounds, one per\n"
            "(packet, live-letter set): the dead letters are `subst`-ed away and\n"
            "each surviving monomial is below the face degree `d`, so the\n"
            "chamber's ℕ conjuncts enter later by `omega`.  Depends only on\n"
            f"`{p1}`; the sibling `…Part*` modules are independent of each other,\n"
            "so they gate in parallel.  Untracked working note."
        )
        outn = header(p1, docn) + "section QuarticChamberFaces810\n\n" + "".join(grp)
        outn += "\nend QuarticChamberFaces810\n" + FOOTER
        parts.append((pn, write(pn + ".lean", outn)))
    for nm, ln in parts:
        MODULES.append((nm, ln, "faces: "
                        + ("carrier load-free/column split" if nm.endswith("Part0Scratch")
                           else "packet faces, rests and split identities"
                           if nm.endswith("Part1Scratch")
                           else "load-free rest bounds")))

    name = "Grok810ScaleZeroQuarticChamberFacesScratch"
    doc = (
        "# Cost-argmin faces and rests, `(8,10)` scale zero — aggregator\n\n"
        "The single 19,969-line module this replaces was correct but hit the\n"
        "six-hour compile ceiling, and every later module waits on it.  The\n"
        "content now lives in\n"
        f"`…FacesPart0Scratch` (the four carriers' load-free part, their eight\n"
        f"load columns and the split identities), `…FacesPart1Scratch` (the\n"
        f"{len(packets)} packet faces, rests and packet split identities) and\n"
        f"`…FacesPart2..Part{len(parts) - 1}Scratch` "
        f"({sum(len(v) for v in uses.values())} load-free rest bounds, ≤ 80\n"
        "`compute_degree` calls each).  Part 0 → Part 1 is the only dependency\n"
        "between parts; the bound parts are mutually independent and gate in\n"
        "parallel.  This module only re-exports them, so modules 10-40 need no\n"
        "change.  Untracked working note."
    )
    out = ("".join(f"import {nm}\n" for nm, _ln in parts) + "\n"
           + f"/-! {doc}\n-/\n")
    nlines = write(name + ".lean", out)
    MODULES.append((name, nlines,
                    f"aggregator: re-exports the {len(parts)} `…FacesPart*` "
                    "modules"))
    return name, packets


# ------------------------------------------------- the odd A-power auxiliaries
# `~/lean/tools/sigma810/OPEN_CHAMBERS.md` §1.  Weight is preserved by
# multiplication by `A` (weight 2), so the odd integrals span, at weight 17,
# the 4-dimensional space ⟨A³κ, A²ν, Aο, Π⟩; these are the chamber-independent
# combinations whose load-free support drops one cost level at a time.
# name -> (weight, natDegree bound as a multiple of `a`, [(form, A power, coeff)])
AUX = {
    "n4": (17, 1, [("primitive", 0, "1"), ("omicron", 1, "-1")]),
    "n5": (15, 2, [("omicron", 0, "1"), ("nu", 1, "1 / 8"), ("kappa", 2, "3 / 128")]),
    "n6": (17, 2, [("primitive", 0, "1"), ("omicron", 1, "-(2 / 3)"),
                   ("nu", 2, "-(1 / 48)")]),
    "n7": (17, 3, [("primitive", 0, "1"), ("omicron", 1, "1"),
                   ("nu", 2, "3 / 16"), ("kappa", 3, "5 / 128")]),
}
AUX_GREEK = {"n4": "N₄", "n5": "N₅", "n6": "N₆", "n7": "N₇"}
AUX_LEAN = {n: f"degreeZero{n.upper()}Quartic810" for n in AUX}
PURE_A_LOADS = ["l", "beta", "delta", "zeta", "theta"]
LOADW = {"l": 1, "beta": 3, "delta": 5, "zeta": 7, "theta": 9}
LOADSIG = "l beta gamma delta epsilon zeta eta theta"


def _col_coeff(coords, form, ld, apow):
    from fractions import Fraction as Fr
    for r in coords[form]:
        if (r.get("loads") or {}).get(ld) != 1:
            continue
        ex = r.get("exps") or {}
        if all(int(ex.get(L, 0) or 0) == 0 for L in SIG) and int(ex.get("A", 0) or 0) == apow:
            return Fr(int(r["qn"]), int(r["qd"]))
    return Fr(0)


def _call(form):
    return f"{CC.FORM_LEAN[form]} {LOADSIG} A B C D E F G"


def emit_aux_tower(coords, prev):
    from fractions import Fraction as Fr
    body = ("/-! ## The odd `A`-power auxiliaries `N₄, N₅, N₆, N₇`\n\n"
            "`N₂ = ν + (1/8)·A·κ` is already in File A.  Each auxiliary cancels one\n"
            "more level of the odd tower `⟨A³κ, A²ν, Aο, Π⟩`; `N₇` is the deepest\n"
            "possible member.  `natDegree N ≤ k·a` costs the face equation `2·deg > …`\n"
            "slack `w − 2k` instead of `w`. -/\n\n")
    for name, (w, kk, parts) in AUX.items():
        needs_prim = any(f == "primitive" for f, _, _ in parts)
        terms = []
        for f, ap, co in parts:
            if ap == 0:
                terms.append(_call(f))
            elif ap == 1:
                terms.append(f"({co} : k) • (A * {_call(f)})")
            else:
                terms.append(f"({co} : k) • (A ^ {ap} * {_call(f)})")
        rhs = terms[0]
        for t in terms[1:]:
            rhs += " +\n    " + t
        pieces = []
        for f, ap, co in parts:
            apart = "" if ap == 0 else ("A·" if ap == 1 else f"A{chr(0x00B2 + ap - 2)}·")
            neg = co.startswith("-")
            mag = co.lstrip("-").strip("()")
            scal = "" if mag == "1" else f"({mag})·"
            pieces.append(("− " if neg else ("+ " if pieces else "")) +
                          f"{scal}{apart}{CC.GREEK[f]}")
        defn = " ".join(pieces)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- `{AUX_GREEK[name]} = {defn}` (weight {w}, "
                 f"`natDegree ≤ {kk}·a`, face slack `{w - 2 * kk}·a > c₀`). -/\n")
        body += (f"def {AUX_LEAN[name]}\n"
                 f"    ({LOADSIG} : k)\n"
                 "    (A B C D E F G : k[X]) : k[X] :=\n"
                 f"  {rhs}\n\n")
        # natDegree bound
        bound = "A.natDegree" if kk == 1 else f"{kk} * A.natDegree"
        hyp_of = {"primitive": ("hprim", "= 1"), "omicron": ("homi", "= 0"),
                  "nu": ("hnu", "= 0"), "kappa": ("hkap", "= 0")}
        out = ["set_option maxHeartbeats 64000000 in",
               f"theorem {AUX_LEAN[name]}_natDegree_le",
               f"    ({LOADSIG} : k)",
               "    (A B C D E F G : k[X])",
               "    (hApos : 0 < A.natDegree)"]
        for f, _ap, _co in parts:
            h, rel = hyp_of[f]
            out.append(f"    ({h} : ({_call(f)}).natDegree {rel})")
        out[-1] += " :"
        out.append(f"    ({AUX_LEAN[name]} {LOADSIG} A B C D E F G).natDegree ≤")
        out.append(f"      {bound} := by")
        hs = []
        for idx, (f, ap, co) in enumerate(parts):
            h, _rel = hyp_of[f]
            hn = f"hb{idx}"
            hs.append(hn)
            if ap == 0:
                out.append(f"  have {hn} : ({_call(f)}).natDegree ≤ {bound} := by")
                out.append(f"    rw [{h}]")
                out.append("    omega")
                continue
            tm = (f"({co} : k) • (A * {_call(f)})" if ap == 1
                  else f"({co} : k) • (A ^ {ap} * {_call(f)})")
            inner = (f"A * {_call(f)}" if ap == 1 else f"A ^ {ap} * {_call(f)}")
            lhs = "A.natDegree" if ap == 1 else f"(A ^ {ap}).natDegree"
            out.append(f"  have {hn} : ({tm}).natDegree ≤ {bound} := by")
            out.append("    refine (natDegree_smul_le810 _ _).trans ?_")
            out.append(f"    have hmul : ({inner}).natDegree ≤")
            out.append(f"        {lhs} + ({_call(f)}).natDegree := natDegree_mul_le")
            if ap == 1:
                out.append(f"    rw [{h}, add_zero] at hmul")
            else:
                out.append(f"    rw [{h}, add_zero, natDegree_pow] at hmul")
            out.append("    omega")
        out.append(f"  simp only [{AUX_LEAN[name]}]")
        acc = hs[0]
        for h in hs[1:]:
            acc = f"natDegree_add_le810 ({acc}) {h}" if acc.startswith("natDegree") \
                else f"natDegree_add_le810 {acc} {h}"
        out.append(f"  exact {acc}")
        out.append("")
        body += "\n".join(out) + "\n"
        # the five pure-`A` load columns
        for ld in PURE_A_LOADS:
            j = (w - LOADW[ld]) // 2
            tot = Fr(0)
            for f, ap, co in parts:
                c = Fr(co.replace("(", "").replace(")", "")) if "/" not in co else None
                tot += Fr(_col_coeff(coords, f, ld, j - ap)) * Fr(
                    co.replace("(", "").replace(")", ""))
            num, den = tot.numerator, tot.denominator
            coeff = (f"{num} / {den}" if den != 1 else f"{num}")
            if num < 0:
                coeff = f"-({-num} / {den})" if den != 1 else f"-({-num})"
            body += (f"/-- The pure-`A` `{ld}` column of `{AUX_GREEK[name]}`. -/\n"
                     f"def {name}Quartic{CC.LOAD_CAP[ld]}Face810 ({ld} : k) (A : k[X]) : k[X] :=\n"
                     f"  ({coeff} * {ld} : k) • A ^ {j}\n\n")

    name = "Grok810ScaleZeroQuarticChamberAuxTowerScratch"
    doc = (
        "# The odd `A`-power auxiliary tower, `(8,10)` scale zero\n\n"
        "`N₄ = Π − A·ο`, `N₅ = ο + (1/8)A·ν + (3/128)A²·κ`,\n"
        "`N₆ = Π − (2/3)A·ο − (1/48)A²·ν`,\n"
        "`N₇ = Π + A·ο + (3/16)A²·ν + (5/128)A³·κ`, with their `natDegree`\n"
        "bounds `a, 2a, 2a, 3a` and their five pure-`A` load columns.  `N₂` is\n"
        "already in File A.  Data and shapes: `~/lean/tools/sigma810/OPEN_CHAMBERS.md`\n"
        "§1 and `scripts/derive_810_scale_zero_quartic_open_aux.py`; every column\n"
        "coefficient here was recomputed from\n"
        "`scripts/out_810_scale_zero_quartic_coordinates.json`.  Consumed by File D\n"
        "(the two open chambers, the 19 deep-rescue chambers and the 405 weak-band\n"
        "walls); nothing in Files B/C depends on it.  Untracked working note."
    )
    out = header(prev, doc) + "section QuarticAuxTower810\n\n" + body
    out += "\nend QuarticAuxTower810\n" + FOOTER
    n = write(name + ".lean", out)
    MODULES.append((name, n, "`N₄, N₅, N₆, N₇`, their `natDegree ≤ k·a` bounds "
                             "and their pure-`A` load columns (for File D)"))
    return name


TRANCHE = {"single": 0, "system": 0, "sysdrop": 0, "split": 0,
           "splitdrop": 0, "surv": 0, "survref": 0, "wall": 0}


def emit_manifest(data, chambers, packets):
    ch = data["chambers"]
    cnt = collections.Counter(c["certificate"]["kind"] for c in ch)
    weak = [c for c in ch if c["weak_bands"]]
    refined = [c for c in chambers if c.refined]
    side = 25
    nsurv = 1115 - 550
    nrefined = len(refined)
    rows = "\n".join(
        f"| {i + 1} | `{m}.lean` | {n} | {d} |"
        for i, (m, n, d) in enumerate(MODULES))
    txt = f"""# Files B/C of the (8,10) scale-zero σ-ladder — module manifest

Machine-generated by `scripts/emit_810_quartic_chambers_lean.py` from
`scripts/out_810_scale_zero_quartic_chambers.json`
(`~/lean/tools/sigma810/CHAMBERS.md`), checked by
`scripts/check_810_quartic_chambers_lean.py`.  All modules are untracked
working notes in `~/lean/src/jc2-lean/max11-partial-y`, namespace
`Max11DegreeRoutes`, Tier-1 preamble (nine `linter.*` off,
`maxRecDepth 1000000`, `set_option maxHeartbeats 64000000 in` **before** every
doc comment of a large declaration).

## Gating order

| # | module | lines | contents |
|---|---|---|---|
{rows}

Module *i* imports module *i−1*; module 1 imports the tracked, green
`Grok810ScaleZeroQuarticSigmaLadderScratch` (File A, commit b32bd96).
Module 10 (the auxiliary tower) is a **leaf**: nothing in Files B/C depends on
it, File D does.

### Gating discipline

`Defs1-4` and `Exhaust1-4` are under coordinator gating, so
`emit_810_quartic_chambers_lean.py` never rewrites them in place: a re-run drops
the regenerated text into `~/lean/tools/sigma810/regen/` and reports, per
module, whether it is byte-identical to the gated file.  The emitter is
idempotent — all eight regenerate byte-identically, including the gate lane's
own `set_option maxHeartbeats 64000000 in` in front of
`QuarticChamberBCDEFG134810` (`…Defs4Scratch`, the 30-conjunct `BCDEFG`/`GG`
chamber), reproduced from `DEF_HEARTBEAT_FIXUPS`.  Add any further hand fixes to
that set so regeneration stays byte-stable.

### The `…ChamberFaces` split

The original single `Grok810ScaleZeroQuarticChamberFacesScratch.lean` (19,969
lines, 655 rest bounds) was correct but hit the six-hour compile ceiling with
zero errors, and every later module waited on it.  It is now

* `…FacesPart0Scratch` — the four carriers' load-free parts, their eight load
  columns with `natDegree` bounds and `_zero` lemmas, and the four split
  identities (33 `compute_degree`, 4 `module`);
* `…FacesPart1Scratch` — the 79 packet faces, load-free rests and packet split
  identities (0 `compute_degree`, 79 small `module` calls), importing Part0;
* `…FacesPart2Scratch` … `…FacesPart10Scratch` — the 655 rest bounds in nine
  groups of ≤ 80 `compute_degree` calls, each importing **only** Part1, so they
  are mutually independent and gate in parallel;
* `…ChamberFacesScratch` — a 26-line aggregator that only re-exports the eleven
  parts, so modules 10-40 need no change.

The split is content-preserving: the checker counts the same 5646 declarations
before and after, re-verifies all 7060 face/rest obligations against the
concatenated parts, and resolves all 12,923 cross-module references.

## What a chamber is

`cost(m) = Σ_X m_X·s_X`, `s_X = w_X·a − 2·natDegree X`, `w_{{B..G}} = 3..8`.
A chamber is one argmin cell `(S, T)` of `cost` on cone `A`: `S` the live
letters, `T ⊆ M_S` the argmin monomials.  There are **1115** cells
(the JSON's {len(ch)} leaves refine {nrefined} of them further, per carrier).
Definitions are the cross-multiplied ℕ ties and strict comparisons; the
`Prop` is `QuarticChamber<S><n>810`, the taxonomy is the six size-graded
`inductive`s `QuarticChamberSupportSize{{1..6}}810` collected by
`QuarticChamberSupport810`.

## The exhaust

`quarticChamberSupport810_of` runs File A's 64-way vanishing split (all-zero
leaf → `quarticSigmaSupportCone810_of_allZero`), then one theorem per live
set, each a case tree on the closed form `c₀ = min(2·μ₂, β + r, 2·β + ω)`:
`lt_trichotomy` for `min s|_{{B,C}}`, `min s|_{{D,E}}`, `min s|_{{F,G}}`, then
`μ₂ = min(q,r)`, `ω = min(β,q)`, then the three cost types against each other.
Every leaf either names a chamber (5515 leaves) or is ℚ-infeasible and closed
by `omega` (5150 leaves).  **Verified without Lean**: 78611 arithmetic
obligations, each with an exact rational Farkas certificate; all 1115
chambers reached.

## Faces and rests

A *packet* is a `(carrier, face monomial set)` pair — the face of an integral
depends on the live set as well as on the argmin, so packets are **not** the
135 argmin sets.  There are {len(packets)} packets over the four carriers
`κ, μ, ξ, π` (`ο` and `Π` are never used: they have 102 and 160 monomials).
Per carrier: the load-free part, the eight load columns (each ≤ 20 monomials
after chunking) and the cone-free module identity
`degreeZero<Φ>Quartic810 = Φ_lf + Σ_π Φ_π`.  Per packet: `Φ_lf = face + restLF`
(again cone-free) and one rest bound per live set, with the dead letters
`subst`-ed away and one `natDegree` hypothesis per surviving monomial.

## Certificate census ({len(ch)} JSON leaves)

* `single_monomial` {cnt['single_monomial']}, `power_target` {cnt['power_target']},
  `no_monomial_target` {cnt['no_monomial_target']}, `deep_rescue` {cnt['deep_rescue']},
  `OPEN` {cnt['OPEN']}, `BUDGET` {cnt['BUDGET']}
* weak-band leaves (κ/ν/ο band neither dominated nor strict): {len(weak)}
* killable at level 0 with a usable certificate: 1068 leaves / 1049 cells

## The kill plan

`scripts/derive_810_quartic_chamber_killplan.py` decides, leaf by leaf and with
exact rational Farkas certificates, whether the level-0 certificate is usable
with the load bands Lean actually has, and writes
`scripts/out_810_quartic_chamber_killplan.json`.  For a carrier and a load the
column must sit strictly below the face: it is `empty` (every column monomial
carries a dead letter), `dominated` (forced by the chamber's own conjuncts) or
covered by the kappa `band`; otherwise the leaf is blocked.

* killable leaves with a usable certificate: **1068**
* of those, **598** clear every column; **550** of them are `single_monomial`
  and are killed in `…ChamberKillsScratch`, the other 48 are `power_target`
  and still need a `_coeff_top` extraction
* blocked: **470** leaves — 376 by an unusable kappa band alone, 60 by corner
  `H` alone, 34 by both

Column census over the 1315 (leaf, carrier) pairs: `l` 733 band / 28 dominated /
29 empty / 525 blocked; `beta` 587/173/30/525; `delta` 330/435/30/520;
`zeta` 3/940/63/309; `theta` 0/874/249/192; `gamma` 0/1184/56/75;
`epsilon` 0/1118/163/34; `eta` 0/1066/241/8.

### Why the 470 are blocked, and what unblocks them

1. **`zeta`/`theta` with `B` (or `C`) live.**  `QuarticKappaLoadTopZeta810`
   contains a hard `B = 0` and `…Theta810` a hard `B = 0 and C = 0`, so on a
   chamber where those letters live the band degenerates to `B ≠ 0` and says
   nothing.  This is exactly what the auxiliary tower is for: `N2/N5/N7` shift
   the pure-`A` column up by one `A` each, so they kill a load `kappa` cannot
   (`OPEN_CHAMBERS.md` §1, §4.2).  Module 10 already defines `N4…N7` with their
   `natDegree <= k*a` bounds; an `N`-tower load ladder is the next lane.
2. **The `l`/`beta`/`delta` band is weaker than the taxonomy assumed.**
   `QuarticKappaLoadTop<P>810` asks `2*s_X > w*a` for *every* letter, which
   implies but is not equivalent to `c0(kappa) > w*a`; `band_report` in
   `emit_810_quartic_chambers.py` computed its `kappa_strict` flags against the
   latter.  Re-running the plan with the cost-form band
   `OR over m in min kappa|_S of (cost m <= w*a)` drops the blocked
   (leaf, carrier) pairs from 319 to 131 — but only 12 more leaves become
   killable, so a cost-form `QuarticKappaLoadTop<P>'810` is worth doing only
   together with 1.
3. **Corner `H` (`gamma/epsilon/eta`).**  With the corrected arena these
   columns are dominated almost everywhere (gamma 1184 of 1315, epsilon 1118,
   eta 1066); only 75 + 34 + 8 pairs need a band, and there is no kappa kill for
   them.  That is a much smaller corner than `CHAMBERS.md` §4 suggests, because
   `always_dominated` there was computed without `n_X >= 0` and `0 < n_A`.

## Not killed here (the residual)

`QuarticChamberResidual810` is a {nsurv}-constructor inductive over the chambers
Files B/C do not close, and `normalized810ScaleZero_quarticChamberResidual`
exports

```
cone A and ( (l = beta = delta = zeta = 0 and every letter constant)
             or QuarticChamberResidual810 A B C D E F G )
   or  QuarticRatioConeABCDEFG810 A B C D E F G
```

built on `normalized810ScaleZero_quarticLoadLadderResidual`.  The all-constant
corner is File A's, unchanged.  The residual chambers are

1. the 2 genuinely open leaves, the 19 deep-rescue leaves and the 64 weak-band
   leaves — all closed **mathematically** by the parallel open-chamber lane
   (`~/lean/tools/sigma810/OPEN_CHAMBERS.md`: 19- and 72-term certificates over
   `{{kappa,mu,pi,N5}}` / `{{kappa,mu,xi,pi,N2,N6}}`; 3-70 cofactor terms with every
   degree side condition forced; 405 walls = 101 empty + 202 killed by `N7` +
   102 `p`-augmented splits), consumed by File D together with module 10's
   auxiliary tower;
2. the 12 `no_monomial_target` leaves — the scalar identities are green in
   `Grok810ScaleZeroQuarticChamberCertificatesScratch`, they only need the
   `_coeff_top` extraction wired up;
3. the 48 `power_target` leaves that clear every column — same missing piece;
4. the 470 leaves blocked by a load band (see above);
5. the {nrefined} carrier-refined cells (59 JSON leaves): their extra conjuncts
   live in `refinement_conjuncts` and are *not* implied by the cell's own
   conjuncts (131 of 2260 fail the Farkas test), so the exhaust cannot split
   them without a further per-carrier tournament.

## The cost-form ladder (modules 16-20)

`QuarticKappaLoadTop<P>810` of File A asks `2*s_X > w*a` for *every* letter,
which implies but is not equivalent to `c0(kappa) > w*a` — and the taxonomy's
band-strictness flags were computed against the latter.  Module 16 states the
kill in **cost form**: one inequality per *minimal* load-free monomial of the
auxiliary, plus one per minimal monomial of each lighter load column with no
pure-`A` monomial.  It proves the five kills, bands and the cascade for `kappa`
and for `N2 = nu + (1/8)*A*kappa`, whose pure-`A` column sits one `A` higher and
so reaches loads `kappa` cannot.  `kappa`/`theta` is **skipped**: its predicate
is unsatisfiable (`cost B^3 = 9a - 6b > 9a` is impossible over N), which is
exactly why File A's `theta` predicate has to force `B = 0` as a polynomial.

`scripts/derive_810_quartic_chamber_killplan2.py` re-decides every blocked
column against the three band sources now in Lean — `kappa-letter` (File A),
`kappa-cost`, `n2-cost` — and writes
`scripts/out_810_quartic_chamber_killplan2.json`:

* killable leaves rise from **598 to 959** of 1068 (823 `single_monomial`,
  136 `power_target`);
* blocked columns fall from 2570 to 109, and **all but 6+17+18+17+6 = 64 of
  those are corner `H`** (`gamma` 75, `epsilon` 34, `eta` 8 — loads with no
  pure-`A` column in any auxiliary, so no column kill exists);
* by source: `l` 733 letter / 224 cost-kappa / 295 cost-N2; `beta`
  587/222/286; `delta` 330/217/285; `zeta` 3/5/287; `theta` 0/-/186.

Modules 17-19 emit the extra column bounds, rest bounds and **265 further
single-monomial kills** (total 815); module 20 re-dispatches the 1115-chamber
exhaust through both kill sets and exports
`normalized810ScaleZero_quarticChamber2Residual` over
`QuarticChamberResidual2810`, now **300** chambers (was 565).

`N5` would add 9 more leaves and `N7` none, so the tower stops at `N2` here;
module 10 still defines `N4, N5, N6, N7` with their bounds for File D.

## The carrier change and the multi-carrier kills (modules 21-30)

**Carrier change** (`scripts/derive_810_quartic_chamber_killplan3.py`).  The
certificate carrier is not sacred: *any* integral whose face on the chamber is a
single monomial kills it once its eight load columns clear.  `π` and `ξ` have
`γ`/`ε` columns of letter count ≥ 2 (plan §2.4), which is what corner `H` needs.
Over the 300 chambers module 20 left, 51 fall this way — `π` 34, `ξ` 9, `κ` 4,
`ν` 4 — and `ν` needed its own load-free/column infrastructure (module 21),
which `…ChamberFacesScratch` does not emit.

**Multi-carrier kills** (`scripts/derive_810_quartic_chamber_killplan4.py`).
44 further chambers die on a *system* of faces: each face's top coefficient is
extracted by a `_coeff_top` bridge `(face).coeff d = inner(A.leadingCoeff, …)`
and the isobaric membership identity then forces a product of non-zero leading
coefficients to vanish.  37 come from six `power_target` systems whose cofactors
the taxonomy recorded (re-verified by `sympy`: `expand(Σ h_Φ·face_Φ − target) = 0`);
7 are `no_monomial_target` leaves that reuse the green scalar identities of the
tracked `Grok810ScaleZeroQuarticChamberCertificatesScratch`, matched to my face
packets coefficient-for-coefficient.

Kills now total **910** of the 1115 chambers; `QuarticChamberResidual4810`
carries **205**.

## The unowned tranche: two emitter bugs, and the carrier infrastructure

`~/lean/tools/sigma810/UNOWNED_CHAMBERS.md` re-ledgers `QuarticChamberResidual6810`
as 21 tower-owned + 151 unowned, and closes 144 of the 151.  It found two bugs
in this pipeline, both now fixed:

1. **Faces were read out of the taxonomy, which records them only for the
   carrier its own refinement happened to reach** — so `killplan3/5/6` never
   tried most carriers.  `_810_chamber_common.carrier_face` now computes the
   face of *any* integral on *any* chamber straight from the coordinates: the
   cost-minimal load-free monomials whose letters are all live, with each
   minimality decided by an exact Farkas certificate.  On the very first
   chamber it recovers `μ`, `ξ` and `π` faces the taxonomy never recorded.
   `killplan3` now uses it.
2. **The face-degree side-condition test ignored an `A` factor**, so faces like
   `a·f²` were rejected as possibly degree-zero.  A face monomial carrying `A`
   is positive from `0 < A.natDegree` alone; `killplan3` and `killplan6` now
   test the side condition only when the `A` exponent is zero.

### Carrier infrastructure (seven sibling modules)

`…ChamberFacesPart0Scratch` does the load-free/column split for `κ, μ, ξ, π`
only.  The unowned plan needs the same for `ο`, `Π` and the auxiliaries, so
`…ChamberInfra{{N2,N3,N5,N6,N7,Omicron,Primitive}}Scratch` each emit that
carrier's load-free part, its eight load columns (chunked at 20, with
`natDegree` bounds and `_zero` lemmas) and the cone-free split identity.  They
share one base import and are independent of each other, so they gate in
parallel; none exceeds 540 lines or 10 `compute_degree` calls.
`…ChamberInfraN3Scratch` also **defines the new auxiliary**
`N₃ = ο − (1/16)·A·ν` (weight 15) and proves `natDegree N₃ ≤ a`.

Monomial counts after cancellation: `N₂` 56, `N₃` 97, `N₅` 89, `N₆` 148,
`N₇` 136, `ο` 102, `Π` 160.

### The two new band sources

* `…ChamberN5CostLadderScratch` — the full cost-form `N₅` ladder (predicates,
  pure-`A` splits, rest bounds, kills, bands, cascade).  All five predicates
  are satisfiable and all 255 rest monomials Farkas-bounded.  370 system rows
  and 49 single columns use it.
* `…ChamberN7BandsScratch` — only the five band disjunctions and the cascade;
  the `N₇` predicates, splits, rest bounds, kills and monotonicity are already
  in `…ChamberN7LadderScratch` (which bridges to the tower lane's column
  lemmas).  103 single columns use it.

### Still to emit for the unowned tranche

The plan's 144 closures break down as 85 `single`, 48 `system`, 7
`trichotomy`, 4 `split`.  The 85 singles need 18 face packets over
`κ, μ, ξ, π, N₂, N₃, N₅, N₆` and 75 (packet, live-set) rest bounds; their
column census is 333 `dominated`, 152 `band-hnc`, 123 `band`, 65 `empty`,
7 `dominated-hnc`.  The 48 systems carry Singular cofactors (3-12 terms) over
`κ, μ, ν, ξ, ο, π, Π, N₂, N₃, N₄` with their top-coefficient rows already in
the JSON.  Those, the 11 `split`/`trichotomy` kills and `Residual7` are the
remaining emission; the infrastructure above is their prerequisite and gates
first.

## The wall wiring (module 40) — the `N₇` split the tower lane left open

`Grok810ScaleZeroQuarticTowerScratch` (tracked, green, SHA 9b534891) proves the
five `quarticSigma_<load>_eq_zero_of_N7_column` shapes with the module identity
`N₇ = face + rest` and the rest bound as **hypotheses** — its docstring says the
identity "unfolds `Π` and lives in the residual assembly".  Module 40
(`…ChamberN7LadderScratch`) supplies exactly those, in the shape of module 16's
`κ`/`N₂` cost ladder:

* `n7QuarticNoPureA{{1..7}}810` — `N₇` off its five pure-`A` load columns
  (`N₇` has 136 monomials after cancellation; the rest is 131, chunked at 20);
* `degreeZeroN7TowerQuartic810_eq_pureA_add_rest` — the one heavy split identity,
  unfolding `Π` through the eight `rho` groups (356 raw monomials) with the
  `RatFunc` embedding trick File A uses for `N₂`.  **This is the one declaration
  in the whole chain whose elaboration cost I cannot estimate**; if it times out,
  split it into the four per-form pure-`A` splits (`Π`, `ο`, `ν`, `κ`) and
  re-assemble — the arithmetic is identical;
* `QuarticN7CostTop<Π>810` for the five pure-`A` loads (20-37 cost conjuncts
  each, all satisfiable), the per-load rests, their bounds, and
  `quarticSigmaN7Cost_<π>_eq_zero`, which discharges the tower lemma's three
  hypotheses.  Every one of the 402 rest-monomial obligations is Farkas-checked.

That unblocks the **202 `N₇`-killed walls**.  Still to wire for the remaining
203 walls, once the unowned-chamber plan lands:

* the **101 empty walls** — the tower has 80 `quarticWallEmpty_*` lemmas
  (`chamber → wall equation → False`); 21 walls have no lemma and 3 are recorded
  as `omega`-resistant, so those need either a new lemma or a residual conjunct;
* the **102 `p`-augmented split walls** — the tower supplies the pivot `Prop`s
  and their trichotomies but no sub-cell kills, so the 3-13 sub-cells per wall
  and their scalar identities are still open;
* the per-(chamber, carrier, load) dispatch `by_cases hw : w_π·a = c₀(Φ)` that
  routes a weak-band leaf to the wall lemmas on the wall and to the ordinary
  band off it.

## The power-target kills and the refined leaves (modules 33-39)

`Grok810ScaleZeroQuarticPowerCertificatesScratch` (tracked, green, SHA 102939dc)
supplies 37 Singular-lifted scalar systems `quarticPowerInnerS<NN>810_identity`
/ `_false`.  `scripts/derive_810_quartic_chamber_killplan5.py` re-decides the 78
power-target chambers it targets: **59 clear every load column** (blocked: 8 on
`κ/l`, 9 on `ξ/ε`, 1 on `μ/γ`, 1 on `ξ/γ`).  Module 35
(`…ChamberPowerKillsScratch`) emits the `_coeff_top` bridges from my face
packets to the lane's inner scalars and the 59 kills; the carriers used are only
`κ, μ, ξ, π`, so no `ο` infrastructure was needed.

`scripts/derive_810_quartic_chamber_killplan6.py` then does the same for the 59
leaves of the 11 carrier-refined cells, now separated by module 30's tournament
and using each leaf's *full* conjunct set: **25 of 59 die** — 8 on a
single-monomial face of some carrier, 17 on the lane's systems `S24`-`S34`
(`S24`, the CEG `g^4`, is absent from the lane's Lean module because its `μ/γ`
column does not clear, so its 3 leaves stay).  Module 38
(`…ChamberResidual6Scratch`) dispatches the exhaust through every kill set,
splitting the 11 refined cells with `quarticChamber<cell>810_refine` first.

Kills now total **994** chamber-level kills plus 22 refined-leaf kills.

### Residual census — `QuarticChamberResidual6810`, 172 entries

**135 whole chambers**

| certificate kind | count | why it is still open |
|---|---|---|
| `single_monomial` | 94 | corner `H` (`γ/ε/η` columns) or a κ/N₂ band that is still too weak |
| `power_target` | 25 | the load columns do not clear, so no certificate applies |
| `deep_rescue` | 13 | tower lane |
| `no_monomial_target` | 2 | columns do not clear |
| `BUDGET` | 1 | tower lane |

**37 refined leaves**: `power_target` 19, `single_monomial` 8,
`no_monomial_target` 3, `deep_rescue` 6, `OPEN` 1.

The tower lane's own families account for exactly **21** of the 172 (13 + 1
whole, 6 + 1 refined = the 2 open and 19 deep-rescue leaves); **45** of the whole
chambers carry a weak-band leaf.  The remaining ~106 are corner `H` and
unclear-column cases, not tower work.  `~/lean/tools/sigma810/RESIDUAL6_CHAMBERS.md`
lists every constructor with its chamber `Prop`, live set, argmin, JSON leaf ids
and certificate kinds.

## The refined-cell tournament and the final assembly (modules 30-32)

**Module 30** (`…ChamberRefineScratch`) splits each of the 11 carrier-refined
cells into its leaves.  Each leaf gets a `Prop`
`QuarticRefined<cell>L<i>810 = QuarticChamber<cell>810 ∧ <its refinement
conjuncts>`, and `quarticChamber<cell>810_refine` is a decision tree on those
conjuncts: one `lt_trichotomy` per node, and at each of the 65 leaves exactly
one refined `Prop` whose conjuncts the branch implies (995 obligations, all
Farkas-checked; no dead and no unresolved branch).  The refined leaves' *kills*
are not here: measured against plan v2, **no cell is fully killable**, so the
tournament converts 11 residual chambers into ≈ 59 of which ≈ 22 die once the
power-certificate lane lands.

**Module 31** (`…AssemblyCoreScratch`) is the whole cone-`A` route reduced to
three named obligations, and is gate-able now:

```
theorem normalized810ScaleZero_impossible_of_residualKills
    (hresid …) (hcorner …) (habcdefg …)
    (hsource : Normalized810LeadingCoreSource P Q H 0) : False
```

**Module 32** (`Grok810ScaleZeroQuarticAssemblyScratch`, the name the tracked
route glue expects) derives `normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed`
(`planeKeller810ScaleZeroExclusion_of_impossible`,
`Grok810ScaleZeroConeEliminationScratch.lean:2266`).  **It gates only once the
three externals land.**

### External lemma names the assembly assumes

| name | what it must kill | signature |
|---|---|---|
| `quarticChamberResidual4810_impossible` | every constructor of the 205-chamber inductive `QuarticChamberResidual4810` — the tower lane's 2 open / 19 deep-rescue / 405-wall families and the power lane's `power_target` systems | the `hresid` binder of `…AssemblyCoreScratch` |
| `quarticAllConstantCorner810_impossible` | the all-constant corner with `l = β = δ = ζ = 0` (the `θ`/`B³` tie on `A⁴`; File A already kills the four cases where one of those loads is non-zero) | the `hcorner` binder |
| `quarticConeABCDEFG810_impossible` | the sibling cone `QuarticRatioConeABCDEFG810`; `Grok810ScaleZeroQuarticFullConeFinalScratch` is at `quarticConeABCDEFG810_residual9` | the `habcdefg` binder |

`~/lean/tools/sigma810/RESIDUAL4_CHAMBERS.md` maps all 205 constructors to their
chamber `Prop`, live set, argmin, JSON leaf ids and certificate kinds, so the
tower lane's `quarticCostChamber<S><n>810` numbering can be reconciled with
mine.

## Still open after module 30

1. **78 chambers whose `power_target` certificate has no cofactors** in
   `out_810_scale_zero_quartic_chambers.json` (37 distinct systems, e.g.
   `e^6` over `{{κ,μ,π,ξ}}`, `c^7` over `{{κ,μ,π}}`).  Everything else about them
   is ready — every load column clears and the `_coeff_top` machinery is
   generic.  They need one CAS run: an isobaric ansatz (`h_Φ` isobaric of weight
   `w(target) − w_Φ` in the live letters) solved by linear algebra, or Singular
   `lift`, exactly as `derive_810_scale_zero_quartic_notarget_certs.py` did for
   the twelve.
2. **The 11 carrier-refined cells (59 leaves).**  Measured: **no cell is fully
   killable** — each has at least one `deep_rescue`/`OPEN`/no-cofactor leaf — so
   a per-carrier tournament would split 11 residual chambers into ≈ 59 and kill
   ≈ 22 of them, leaving ≈ 37.  Worth doing after 1.
3. **Corner `H` residue**: after the carrier change, the leaves where *no*
   carrier has both a single-monomial face and clear `γ`/`ε`/`η` columns.
4. The 2 open, 19 deep-rescue and 64 weak-band leaves, closed mathematically in
   `~/lean/tools/sigma810/OPEN_CHAMBERS.md` and transcribed by the parallel
   `Grok810ScaleZeroQuarticTowerScratch` lane — never duplicated here.

## The unowned tranche, `Residual7` and the re-pointed assembly

`~/lean/tools/sigma810/UNOWNED_CHAMBERS.md` re-ledgers the 172 entries of
`QuarticChamberResidual6810` as **21 tower-owned + 151 unowned**.  The unowned
part is emitted here, each remedy in its own independent module family, and
every load column carries an exact rational Farkas verdict produced by
`_810_chamber_common.derive` and re-checked by `verify` before it is used:

| family | modules | what |
|---|---|---|
| single-carrier kills | `…ChamberUnownedPacketsScratch`, `…ChamberUnownedColumns1-4Scratch`, `…ChamberUnownedRests1-6Scratch`, `…ChamberUnownedKills1-7Scratch` | {{SINGLE}} chambers/leaves that die on a single-monomial face of one carrier after the carrier change (over `κ, μ, ξ, π, N₂, N₃, N₅, N₆`), with the `n5-cost`/`n7-cost` bands and the `hnc` column bounds |
| multi-carrier systems | `…ChamberUnownedSystemPacketsScratch`, `…ChamberUnownedSystemColumns1-5Scratch`, `…ChamberUnownedSystemRests1-10Scratch`, `…ChamberUnownedSystemBridgesScratch`, `…ChamberUnownedSystems1-8Scratch` | {{SYSTEM}} of the 48 Singular-lifted top-coefficient systems: one `_coeff_top` bridge per face packet, one scalar certificate (`linear_combination` with the JSON cofactors) per chamber, one chamber kill joining them |
| letter splits and load trichotomies | `…ChamberUnownedSplitPacketsScratch`, `…ChamberUnownedSplitColumns1Scratch`, `…ChamberUnownedSplitRests1-2Scratch`, `…ChamberUnownedSplitsScratch` | {{SPLIT}} chambers that need a `by_cases` on `n_X = 0` or an `lt_trichotomy` against a load column, with a single-carrier kill on every branch |
| carrier infrastructure | `…ChamberInfraN2/N3/N4/N5/N6/N7/Omicron/PrimitiveScratch` | the load-free/column split, the packet split identity and the `natDegree` bound of every carrier the tranche uses; `InfraN3` also defines `degreeZeroN3Quartic810 = ο − (1/16)·A·ν` |
| the load bands | `…ChamberN5CostLadderScratch`, `…ChamberN7BandsScratch` | the `n5-cost` and `n7-cost` cost-form bands, same recipe as module 16's `κ`/`N₂` ladder |
| refinement trees | `…ChamberUnownedRefinePacketsScratch`, `…ChamberUnownedRefineColumns1Scratch`, `…ChamberUnownedRefineRests1Scratch`, `…ChamberUnownedRefineScratch` | the §11 recursive trees: nested `lt_trichotomy` pivots with a single-carrier kill or a Farkas-infeasibility on every leaf.  The pivots come from the plan; **the tree, each leaf's carrier and face and every column verdict are re-derived here**, so no branch is emitted on the plan's word |
| the residual | `…ChamberResidual7Scratch` | `QuarticChamberResidual7810` — {{SURV}} whole chambers + {{SURVREF}} refined leaves, dispatched from the 1115-chamber exhaust exactly as `Residual6` |
| the assembly | `…AssemblyCore2Scratch`, `…Assembly2Scratch` | the same three named obligations, now against `QuarticChamberResidual7810` (`normalized810ScaleZero_impossible_of_residual7Kills`, `normalized810ScaleZero_impossible7`, `planeKeller810ScaleZeroExclusion_closed7`).  Modules 31/32 are left frozen and untouched. |

**Every verdict is re-certified.**  `certify_plan` re-decides every load
column of every entry with the exact Farkas engine — including the *band
disjuncts*, which are linear and therefore checkable: a band on load `p` with
source `s` is accepted only when **every** disjunct of `s` implies
`deg(column monomial) < deg(face)` on the chamber (a `hard` disjunct on a dead
letter is refuted by `hXz`, on a live letter it carries no information and the
column must be dominated outright).  This rejected 6 of the 85 single kills and
is why 10 of the 48 systems are dropped: on those rows the recorded band source
leaves two disjuncts under which the column is *not* dominated, so the kill
would not compile.  The failing rows are listed in the report.

**What is *not* emitted, and why.**

* {{SYSDROP}} of the 48 systems have a load column that is neither dominated,
  `hnc`-dominated nor covered by the band the plan records — the emitter drops
  the entry rather than emit a `by omega` it cannot certify.  All of them are
  refined leaves of the weak-band cells `BCDEG30`, `BCDFG7`, `BCDFG54`,
  `BCEFG7`, `CDEFG28`, `BCDEFG7`, `BCDEFG102`; the blocked loads are the
  pure-`A` ones `δ`, `ζ`, `θ` and (twice) `γ`, `ε`.  Closing them needs the
  wall trichotomy of `UNOWNED_CHAMBERS.md` §4.2 *with the band disjuncts
  modelled in the Farkas engine*, which this pass does not do.
* {{SPLITDROP}} of the 11 splits/trichotomies have a branch of kind `loadkill`
  (`FG1`, `CFG3`) or `system` (`DEG0`, `DFG0`, `DEFG8`), each of which needs
  its own proof shape.
* the 3 `refinement`-mode entries (`BCFG7`, `DEFG0`, `DEFG4`, and the two
  `BCDEFG108` leaves) are the recursive §11 refinement — not attempted.
* the 2 entries `UNOWNED_CHAMBERS.md` §7 reports open (`EFG0`, `CEFG3`).
* the 21 tower-owned entries.  `Grok810ScaleZeroQuarticTowerScratch`'s
  `quarticOpenChamberI/II810_impossible` and its 19
  `quarticCostChamber<S><n>810_impossible` are **scalar** lemmas (face
  coefficients vanish → `False`), so wiring them needs the same `_coeff_top` +
  rest-bound pass this file does for the systems, against *their* face
  definitions.  That work is left to the tower lane and is the single largest
  remaining block of `Residual7`.

**The wall lane.**  `Grok810ScaleZeroQuarticWallSplitsScratch` supplies 64
`quarticWeakBandLeaf…_wall_impossible` theorems; 49 of them take only the
chamber `Prop` and the wall equation, the other 15 take per-sub-cell `hrows`
row-vanishing hypotheses or the `N₇` split identity.  A wall theorem closes the
*on-wall* case only, so on its own it cannot retire a residual entry; what it
can do is sharpen one.  `Residual7` therefore routes every surviving entry
whose cell has such a theorem through
`by_cases hw : <wall>` and carries `¬ <wall>` as an extra constructor argument:
{{WALL}} of its constructors are now off-wall only.  Wiring the remaining 15
(and closing the 7 sharpened entries outright) needs the off-wall column pass
described above.

## The `degree_ok` bug of `CHAMBERS.md` §6

`emit_810_quartic_chambers.py` builds its `(n_A, n_B…n_G)` arena with
`cons7 = to7cons(cons)`, which drops `n_X >= 0` and `0 < n_A`; that is why
almost every `degree_ok` in `CHAMBERS.md` §6 reads `false`, and why
`always_dominated` is `false` for `gamma/epsilon/eta` nearly everywhere.
**No module here reads either field.**  Everything emitted and checked uses
`_810_chamber_common.chamber_cons`: cone `A` (`0 < n_A`, `sigma_X > 0` for the
*live* letters), `n_X >= 0` for all seven letters and `n_X <= 0` for the dead
ones — the correct arena, and **not** `ch.base7(S)`, which would wrongly demand
`sigma_X > 0` for dead letters too.

Re-deciding the 19 auxiliary degree conditions of the deep rescue in that arena:
**13 of 19 are forced by the chamber's own conjuncts** (on `BCDEF`,
`4(E + F - A) = A + 14*B` modulo the cost ties, with `0 < A` and `B >= 0`); the
other 6 are exactly the cases where `OPEN_CHAMBERS.md` §3 switches `N2` to
`N4 = Pi - A*omicron`, whose condition is trivial.  The face-degree side
conditions the kills need are computed without that arena; 1117 of 1142 are
discharged from `not (all six letters constant)`, which is why every kill takes
`hnc` and proves `0 < d` by `by_contra`.

**A soundness bug of my own, found while re-deciding these.**  The first Farkas
engine forced one strict multiplier to `>= 1`, which is not scale-invariant (the
`BCDEF` certificate needs `lambda = 1/4` on `0 < A`), and read solutions off
tableaux that could still carry basic artificials — so it could both miss
certificates and return invalid ones.  `_810_chamber_common.derive` is now a
full two-phase exact-rational LP that *maximises* the strict weight, drops
degenerate artificial rows, and re-verifies every certificate before returning
it.  All counts here are from the fixed engine; the 78611 exhaust obligations
and the 7060 face/rest obligations were re-checked with it.

## Call-telescope and import invariants the generator enforces

* `header()` drops any `Grok810…Scratch` import whose module was never
  emitted - some emitters skip a module that has nothing new to say, yet its
  name stays on the accumulated module list, and the gate then reports
  `unknown module prefix`.
* `close_imports()` runs on every body before it is written: it reads the
  identifiers the text actually references (comments stripped) and imports the
  module declaring any name this module neither declares itself nor already
  reaches through its transitive import closure.  That covers every kind of
  `have`-suppressed declaration - column bounds, chamber face `_natDegree`
  lemmas deduplicated across the parts of one family, rest bounds, kills - and
  a candidate that would close a cycle is logged instead of imported.
* `aux_le_argstr()` reads the real binder list of `<carrier>_natDegree_le`
  off the tree rather than guessing it from the degree bound, so `hApos` is
  passed only where the lemma binds it (N3-N7 do, N2 does not).
* Every `…_natDegree_lt_of_live_<S>` call passes a hypothesis of the shape
  `0 < d`, which is what the rest lemmas bind as `hdpos`.  The k-side fact
  `k * A.natDegree < d` that the kill also derives is strictly stronger but is
  not that statement; the emitters state it as `hdp…` and then derive
  `hdz… : 0 < d` from it by `omega`.
"""
    for kk, vv in TRANCHE.items():
        txt = txt.replace("{" + kk.upper() + "}", str(vv))
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(txt)
    log(f"wrote {MANIFEST}")




# ------------------------------------------------- modules 10-12: the kills
LADDER = ["l", "beta", "delta", "zeta", "theta"]
LOADSIG8 = "l beta gamma delta epsilon zeta eta theta"
# `QuarticKappaLoadTop<Load>810`: letter -> "hard" (a bare `X = 0` conjunct)
# or (p, q) for the conjunct `(X = 0 ∨ q * X.natDegree < p * A.natDegree)`.
TOP = {
    "l":     {"B": (5, 4), "C": (7, 4), "D": (9, 4), "E": (11, 4), "F": (13, 4), "G": (15, 4)},
    "beta":  {"B": (3, 4), "C": (5, 4), "D": (7, 4), "E": (9, 4), "F": (11, 4), "G": (13, 4)},
    "delta": {"B": (1, 4), "C": (3, 4), "D": (5, 4), "E": (7, 4), "F": (9, 4), "G": (11, 4)},
    "zeta":  {"B": "hard", "C": (1, 4), "D": (3, 4), "E": (5, 4), "F": (7, 4), "G": (9, 4)},
    "theta": {"B": "hard", "C": "hard", "D": (1, 4), "E": (3, 4), "F": (1, 1), "G": (7, 4)},
}
TOPNAME = {ld: f"QuarticKappaLoadTop{CC.LOAD_CAP[ld]}810" for ld in LADDER}
KILLNAME = {ld: f"quarticSigma_{ld}_eq_zero" for ld in LADDER}
BANDNAME = {"l": "quarticSigma_l_band_disjunction",
            "beta": "quarticSigma_beta_band_disjunction",
            "delta": "quarticSigma_delta_band_disjunction",
            "zeta": "quarticSigma_zeta_band_disjunction810'",
            "theta": "quarticSigma_theta_band_disjunction"}


def ineq_of(X, spec):
    """The band disjunct: the negation of the `Top` conjunct on letter `X`."""
    if spec == "hard":
        return f"{X} ≠ 0"
    p, q = spec
    lhs = "A.natDegree" if p == 1 else f"{p} * A.natDegree"
    rhs = f"{X}.natDegree" if q == 1 else f"{q} * {X}.natDegree"
    return f"{lhs} ≤ {rhs}"


def band_statement(ld, var):
    parts = [f"{var} = 0"] + [ineq_of(X, TOP[ld][X]) for X in SIG]
    return " ∨\n      ".join(parts)


def emit_bands(prev):
    """Module 10a: the κ-ladder cascade, once, as five band disjunctions."""
    body = "/-! ## Monotonicity of the κ kill predicates -/\n\n"
    chain = [("beta", "l"), ("delta", "beta"), ("zeta", "delta"), ("theta", "zeta")]
    for hi, lo in chain:
        nm = f"quarticKappaLoadTop{CC.LOAD_CAP[hi]}810_imp_{CC.LOAD_CAP[lo]}810"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- The `{hi}` column tops `κ` only if the cheaper `{lo}` column does. -/\n"
                 f"theorem {nm}\n"
                 "    {A B C D E F G : k[X]}\n"
                 f"    (h : {TOPNAME[hi]} A B C D E F G) :\n"
                 f"    {TOPNAME[lo]} A B C D E F G := by\n")
        names = []
        for X in SIG:
            names.append(f"h{X}")
        body += f"  obtain ⟨hA, {', '.join(names)}⟩ := h\n"
        body += "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA\n"
        body += "  refine ⟨hA, " + ", ".join("?_" for _ in SIG) + "⟩\n"
        for X in SIG:
            hs, ls = TOP[hi][X], TOP[lo][X]
            if ls == "hard":
                body += f"  · exact h{X}\n"
            elif hs == "hard":
                body += f"  · exact Or.inl h{X}\n"
            else:
                body += (f"  · rcases h{X} with h0 | hlt\n"
                         f"    · exact Or.inl h0\n"
                         f"    · exact Or.inr (by omega)\n")
        body += "\n"

    # the `zeta` band in usable shape (File A's has a vacuous `0 ≤ …` disjunct)
    body += "/-! ## The `zeta` band in usable shape -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += ("/-- File A's `quarticSigma_zeta_band_disjunction` renders the hard\n"
             "`B = 0` conjunct of `QuarticKappaLoadTopZeta810` as the vacuous\n"
             "`0 ≤ A.natDegree + 4 * B.natDegree`; this is the same disjunction with\n"
             "that summand as `B ≠ 0`. -/\n")
    body += (f"theorem {BANDNAME['zeta']}\n"
             "    {zeta : k} (A B C D E F G : k[X])\n"
             "    (hA : QuarticRatioConeA810 A B C D E F G)\n"
             f"    (hkill : {TOPNAME['zeta']} A B C D E F G → zeta = 0) :\n"
             f"    {band_statement('zeta', 'zeta')} := by\n")
    def inj(pos, total):
        if pos == total - 1:
            return "Or.inr (" * pos + "?_" + ")" * pos
        return "Or.inr (" * pos + "Or.inl ?_" + ")" * pos

    live = [X for X in SIG if TOP["zeta"][X] != "hard"]

    def zeta_tree(j, ind):
        if j == len(live):
            return [f"{ind}exact Or.inl (hkill ⟨hA, hB, "
                    + ", ".join(f"Or.inr h{X}" for X in live) + "⟩)"]
        X = live[j]
        pp, qq = TOP["zeta"][X]
        lhs = f"{qq} * {X}.natDegree" if qq != 1 else f"{X}.natDegree"
        rhs = f"{pp} * A.natDegree" if pp != 1 else "A.natDegree"
        out = [f"{ind}by_cases h{X} : {lhs} < {rhs}"]
        sub = zeta_tree(j + 1, ind + "  ")
        out.append(f"{ind}· {sub[0].strip()}")
        out += sub[1:]
        out.append(f"{ind}· refine {inj(2 + j, 7)}")
        out.append(f"{ind}  omega")
        return out

    body += "  by_cases hB : B = 0\n"
    sub = zeta_tree(0, "    ")
    body += f"  · {sub[0].strip()}\n" + "\n".join(sub[1:]) + "\n"
    body += "  · exact Or.inr (Or.inl hB)\n\n"

    # the cascade
    body += "/-! ## The five κ bands, from the ladder -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += ("/-- The `l → β → δ → ζ → θ` κ-column ladder, packaged as the five\n"
             "band disjunctions the chamber kills consume.  In each branch the\n"
             "first `QuarticKappaLoadTop` that fails kills nothing, but by\n"
             "monotonicity every later one fails too, so its band holds vacuously. -/\n")
    body += (f"theorem quarticSigma_kappaLoadBands810\n"
             f"    ({LOADSIG8} : k)\n"
             "    (A B C D E F G : k[X])\n"
             "    (hA : QuarticRatioConeA810 A B C D E F G)\n"
             "    (hkap : (degreeZeroKappaQuartic810 " + LOADSIG8 + "\n"
             "          A B C D E F G).natDegree = 0) :\n")
    stmts = [f"    ({band_statement(ld, ld)})" for ld in LADDER]
    body += " ∧\n".join(stmts) + " := by\n"

    def mono(hi, lo):
        """`Top<hi> → Top<lo>` as a term."""
        i, j = LADDER.index(hi), LADDER.index(lo)
        term = "htop"
        for t in range(i, j, -1):
            term = (f"quarticKappaLoadTop{CC.LOAD_CAP[LADDER[t]]}810_imp_"
                    f"{CC.LOAD_CAP[LADDER[t - 1]]}810 ({term})")
        return term

    def emit_branch(pos, ind):
        """`pos` loads already killed; case on the next `Top`."""
        out = []
        if pos == len(LADDER):
            comps = [f"Or.inl h{ld}0" for ld in LADDER]
            out.append(f"{ind}exact ⟨{', '.join(comps)}⟩")
            return out
        ld = LADDER[pos]
        out.append(f"{ind}by_cases hT{ld} : {TOPNAME[ld]} A B C D E F G")
        args = " ".join(f"h{p}0" for p in LADDER[:pos])
        out.append(f"{ind}· have h{ld}0 : {ld} = 0 :=")
        out.append(f"{ind}    {KILLNAME[ld]} {LOADSIG8}")
        out.append(f"{ind}      A B C D E F G hT{ld}" + (f" {args}" if args else "")
                   + " hkap")
        out += emit_branch(pos + 1, ind + "  ")
        # this Top fails: everything from `pos` on gets a vacuous band
        comps = [f"Or.inl h{p}0" for p in LADDER[:pos]]
        for q in LADDER[pos:]:
            comps.append(f"{BANDNAME[q]} (A := A) (B := B) (C := C) (D := D)\n"
                         f"{ind}      (E := E) (F := F) (G := G) ({q} := {q}) hA\n"
                         f"{ind}      (fun htop => absurd ({mono(q, ld)}) hT{ld})")
        out.append(f"{ind}· exact ⟨" + (",\n" + ind + "    ").join(comps) + "⟩")
        return out

    body += "\n".join(emit_branch(0, "  ")) + "\n\n"

    name = "Grok810ScaleZeroQuarticChamberBandsScratch"
    doc = (
        "# The κ load bands of the chamber kills, `(8,10)` scale zero\n\n"
        "One cascade over the `l → β → δ → ζ → θ` κ-column ladder of\n"
        "`Grok810ScaleZeroQuarticLoadLadderScratch`, packaged as the five band\n"
        "disjunctions `π = 0 ∨ ¬ QuarticKappaLoadTop<Π>810` the chamber kills\n"
        "consume.  Monotonicity `Topθ → Topζ → Topδ → Topβ → Topl` makes the\n"
        "cascade linear: in the branch where the first predicate fails, every\n"
        "later one fails too and its band is vacuous.  `γ, ε, η` have no pure-`A`\n"
        "column in `κ` and therefore no band here — that is corner `H`; the\n"
        "chambers that need one are named in the residual.  Untracked working note."
    )
    out = header([prev, "Grok810ScaleZeroQuarticLoadLadderScratch"], doc) \
        + "section QuarticChamberBands810\n\n" + body
    out += "\nend QuarticChamberBands810\n" + FOOTER
    n = write(name + ".lean", out)
    MODULES.append((name, n, "κ-kill monotonicity, the usable `zeta` band and "
                             "`quarticSigma_kappaLoadBands810`"))
    return name




# --------------------------------------------- modules 10b/10c: columns, rests
def load_plan():
    import json
    return json.loads((ROOT / "scripts" /
                       "out_810_quartic_chamber_killplan.json").read_text())


def col_chunks(coords, form, ld):
    """The emitted chunk names of the `ld` column of `form`, with records."""
    recs = EC.sort_records([r for r in coords[form]
                            if (r.get("loads") or {}).get(ld)])
    chunks = split_chunks(recs)
    out = []
    for i, ch in enumerate(chunks):
        nm = (f"{form}QuarticColumn{CC.LOAD_CAP[ld]}810" if len(chunks) == 1
              else f"{form}QuarticColumn{CC.LOAD_CAP[ld]}{i + 1}810")
        out.append((nm, ch))
    return out


def surviving(recs, live):
    return [r for r in recs
            if all(int((r.get("exps") or {}).get(L, 0) or 0) == 0
                   for L in SIG if L not in live)]


POWS = "\n".join(f"  have hpow{e} : (0 : k[X]) ^ {e} = 0 := zero_pow (by decide)"
                 for e in range(2, 9))
POWNAMES = ", ".join(f"hpow{e}" for e in range(2, 9))


def subst_block(live, ind="  "):
    return "".join(f"{ind}subst h{X}z\n" for X in SIG if X not in live)


def emit_columns(coords, plan, prev):
    """Module 10b: one column bound per (carrier, load, chunk, live set)."""
    want = collections.OrderedDict()
    for e in plan["leaves"]:
        if not e["killable"]:
            continue
        for r in e["carriers"]:
            for ld, v in r["loads"].items():
                if v["status"] in ("dominated", "band"):
                    want[(r["carrier"], ld, e["live"])] = True
    body = ""
    n = 0
    for (form, ld, S) in want:
        live = set(S)
        for nm, recs in col_chunks(coords, form, ld):
            surv = surviving(recs, live)
            hyps, seen = [], {}
            for r in surv:
                g = deg_expr(r.get("exps") or {})
                if g not in seen:
                    seen[g] = f"hd{len(seen)}"
                    hyps.append((seen[g], g))
            out = ["set_option maxHeartbeats 64000000 in",
                   f"theorem {nm}_natDegree_lt_of_live_{S}",
                   "    {d : ℕ}",
                   f"    ({ld} : k)",
                   "    (A B C D E F G : k[X])",
                   "    (hdpos : 0 < d)"]
            for X in SIG:
                if X not in live:
                    out.append(f"    (h{X}z : {X} = 0)")
            for h, g in hyps:
                out.append(f"    ({h} : {g} < d)")
            out[-1] += " :"
            out.append(f"    ({nm} {ld} A B C D E F G).natDegree < d := by")
            out.append(subst_block(live).rstrip("\n"))
            out.append(POWS)
            if surv and refl_ok(nm):
                out += refl_degok_proof(nm)
            else:
                out.append(f"  simp only [{nm}, {POWNAMES}, {ZERO_SIMP}]")
                out.append("  omega")
            out.append("")
            body += "\n".join(x for x in out if x != "") + "\n\n"
            n += 1
    name = "Grok810ScaleZeroQuarticChamberColumnsScratch"
    doc = (
        "# Load-column bounds per live-letter set, `(8,10)` scale zero\n\n"
        f"{n} bounds: for each carrier `κ, μ, ξ, π`, each of the eight load\n"
        "columns (chunked at 20 monomials in `…ChamberFacesScratch`) and each\n"
        "live-letter set the chamber kills need, the column's `natDegree` is\n"
        "below the face degree `d` once the dead letters are substituted away\n"
        "and each surviving monomial is below `d`.  Machine-generated; every\n"
        "hypothesis list is exactly the surviving monomial set, and every\n"
        "instantiation is Farkas-checked in\n"
        "`scripts/derive_810_quartic_chamber_killplan.py`.  Untracked working note."
    )
    out = header(prev, doc) + "section QuarticChamberColumns810\n\n" + body
    out += "\nend QuarticChamberColumns810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{n} load-column `natDegree` bounds per "
                              "(carrier, load, live set)"))
    return name


def packet_face_records(coords, form, facekeys):
    lf = EC.sort_records(coords[form + "_lf"])
    face = [r for r in lf if rec_key(r) in set(map(tuple, facekeys))]
    rest = [r for r in lf if rec_key(r) not in set(map(tuple, facekeys))]
    return face, rest


def emit_rests(coords, plan, prev):
    """Module 10c: the combined rest per packet and its bound per live set."""
    pk = {(p["carrier"], p["id"]): [tuple(x) for x in p["face"]]
          for p in plan["packets"]}
    used_pk = collections.OrderedDict()
    used_pl = collections.OrderedDict()
    for e in plan["leaves"]:
        if not e["killable"]:
            continue
        for r in e["carriers"]:
            used_pk[(r["carrier"], r["packet"])] = True
            used_pl[(r["carrier"], r["packet"], e["live"])] = r
    body = "/-! ## The combined rest of each packet, and the split identity -/\n\n"
    for (form, p) in used_pk:
        rname = f"{form}QuarticChamberRest{p}810"
        cols = []
        for ld in LOADS:
            for nm, _ in col_chunks(coords, form, ld):
                cols.append(f"{nm} {ld} A B C D E F G")
        rhs = f"{form}QuarticChamberRestLF{p}810 A B C D E F G"
        for c in cols:
            rhs += " +\n    " + c
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Everything of `{CC.GREEK[form]}` off the face of packet "
                 f"{p}: the load-free rest and the eight load columns. -/\n")
        body += (f"def {rname}\n    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) : k[X] :=\n"
                 f"  {rhs}\n\n")
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem degreeZero{CC.FORM_CAP[form]}Quartic810_eq_face{p}_add_rest\n"
                 f"    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) :\n"
                 f"    {CC.FORM_LEAN[form]} {LOADSIG8} A B C D E F G =\n"
                 f"      {form}QuarticChamberFace{p}810 A B C D E F G +\n"
                 f"        {rname} {LOADSIG8} A B C D E F G := by\n"
                 f"  rw [{CC.FORM_LEAN[form]}_eq_chamberSplit,\n"
                 f"    {form}QuarticLoadFree810_eq_face{p}_add_rest]\n"
                 f"  simp only [{rname}]\n"
                 "  ring\n\n")

    body += "/-! ## The rest bound, one per (packet, live-letter set) -/\n\n"
    nb = 0
    for (form, p, S), rec in used_pl.items():
        live = set(S)
        face, rest = packet_face_records(coords, form, pk[(form, p)])
        rname = f"{form}QuarticChamberRest{p}810"
        surv_lf = surviving(rest, live)
        lfh, seen = [], {}
        for r in surv_lf:
            g = deg_expr(r.get("exps") or {})
            if g not in seen:
                seen[g] = f"hl{len(seen)}"
                lfh.append((seen[g], g))
        out = ["set_option maxHeartbeats 64000000 in",
               f"theorem {rname}_natDegree_lt_of_live_{S}",
               "    {d : ℕ}",
               f"    ({LOADSIG8} : k)",
               "    (A B C D E F G : k[X])",
               "    (hdpos : 0 < d)"]
        for X in SIG:
            if X not in live:
                out.append(f"    (h{X}z : {X} = 0)")
        for h, g in lfh:
            out.append(f"    ({h} : {g} < d)")
        loadhyp = {}
        for ld in LOADS:
            recs = [r for c in col_chunks(coords, form, ld) for r in c[1]]
            surv = surviving(recs, live)
            if not surv:
                continue
            degs, sn = [], {}
            for r in surv:
                g = deg_expr(r.get("exps") or {})
                if g not in sn:
                    sn[g] = True
                    degs.append(g)
            loadhyp[ld] = degs
            conj = " ∧ ".join(f"{g} < d" for g in degs)
            out.append(f"    (hb{ld} : {ld} = 0 ∨ ({conj}))")
        out[-1] += " :"
        out.append(f"    ({rname} {LOADSIG8} A B C D E F G).natDegree < d := by")
        zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
        largs = " ".join(h for h, _ in lfh)
        out.append(f"  have hr0 :=")
        out.append(f"    {form}QuarticChamberRestLF{p}810_natDegree_lt_of_live_{S}")
        out.append(f"      A B C D E F G hdpos" + (f" {zargs}" if zargs else "")
                   + (f" {largs}" if largs else ""))
        pieces = ["hr0"]
        ci = 0
        for ld in LOADS:
            for nm, recs in col_chunks(coords, form, ld):
                surv = surviving(recs, live)
                hn = f"hc{ci}"
                ci += 1
                pieces.append(hn)
                if not surv:
                    out.append(f"  have {hn} : ({nm} {ld} A B C D E F G).natDegree < d := by")
                    for X in SIG:
                        if X not in live:
                            out.append(f"    subst h{X}z")
                    for e in range(2, 9):
                        out.append(f"    have hpow{e} : (0 : k[X]) ^ {e} = 0 := "
                                   "zero_pow (by decide)")
                    out.append(f"    simp only [{nm}, {POWNAMES}, {ZERO_SIMP}]")
                    out.append("    omega")
                    continue
                degs = [deg_expr(r.get("exps") or {}) for r in surv]
                idx = [loadhyp[ld].index(g) for g in degs]
                nh = len(loadhyp[ld])
                pat = ("g0" if nh == 1 else
                       "⟨" + ", ".join(f"g{t}" for t in range(nh)) + "⟩")
                args = " ".join(f"g{t}" for t in idx)
                out.append(f"  have {hn} : ({nm} {ld} A B C D E F G).natDegree < d := by")
                out.append(f"    rcases hb{ld} with rfl | {pat}")
                out.append(f"    · rw [{nm}_zero]")
                out.append("      simpa using hdpos")
                out.append(f"    · exact {nm}_natDegree_lt_of_live_{S} {ld} A B C D E F G hdpos"
                           + (f" {zargs}" if zargs else "") + (f" {args}" if args else ""))
        out.append(f"  simp only [{rname}]")
        acc = pieces[0]
        for h in pieces[1:]:
            acc = f"natDegree_add_lt810 ({acc}) {h}" if " " in acc else \
                f"natDegree_add_lt810 {acc} {h}"
        out.append(f"  exact {acc}")
        out.append("")
        body += "\n".join(out) + "\n"
        nb += 1
    name = "Grok810ScaleZeroQuarticChamberRestsScratch"
    doc = (
        "# Chamber rests and their bounds, `(8,10)` scale zero\n\n"
        f"For each of the {len(used_pk)} face packets the chamber kills use: the\n"
        "combined rest `Φ_lf-off-face + Σ_π Φ_π` and the cone-free identity\n"
        "`Φ = face + rest` (a re-association of the packet split of\n"
        "`…ChamberFacesScratch` and the eight-column split), and then\n"
        f"{nb} rest bounds, one per (packet, live-letter set), each chaining\n"
        "`natDegree_add_lt810` over the load-free piece and the load columns.\n"
        "The load hypotheses have the uniform shape `π = 0 ∨ (every column\n"
        "monomial is below the face degree)`, so a caller discharges a\n"
        "*dominated* column by `omega` and a *banded* one by `rcases` on\n"
        "`quarticSigma_kappaLoadBands810`.  Untracked working note."
    )
    out = header(prev, doc) + "section QuarticChamberRests810\n\n" + body
    out += "\nend QuarticChamberRests810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{len(used_pk)} packet rests with their split "
                              f"identities and {nb} rest bounds"))
    return name




# ------------------------------------------------------ module 11: the kills
def mono_ne(exps):
    """(rw chain, needed `≠ 0` letters) for `natDegree` of a single monomial."""
    fac = [(L, int(exps.get(L, 0) or 0)) for L in LET
           if int(exps.get(L, 0) or 0) > 0]
    need = [L for L, _ in fac]

    def ne(i):
        L, e = fac[i]
        return f"h{L}ne" if e == 1 else f"(pow_ne_zero {e} h{L}ne)"

    def pre(i):
        return ne(0) if i == 0 else f"(mul_ne_zero {pre(i - 1)} {ne(i)})"

    chain = [f"natDegree_mul {pre(i - 1)} {ne(i)}"
             for i in range(len(fac) - 1, 0, -1)]
    haspow = any(e >= 2 for _, e in fac)
    return chain, need, haspow


def emit_kills(data, coords, chambers, plan, prev):
    cham = {(c.live, c.argmin): c for c in chambers}
    pk = {(p["carrier"], p["id"]): [tuple(x) for x in p["face"]]
          for p in plan["packets"]}
    leaves = [e for e in plan["leaves"]
              if e["killable"] and e["kind"] == "single_monomial"]
    # face-degree lemmas for the packets these leaves use
    used = collections.OrderedDict()
    for e in leaves:
        r = e["carriers"][0]
        used[(r["carrier"], r["packet"])] = True
    body = "/-! ## Face degrees -/\n\n"
    facedeg = {}
    for (form, p) in used:
        face, _rest = packet_face_records(coords, form, pk[(form, p)])
        assert len(face) == 1, (form, p, len(face))
        rec = face[0]
        exps = rec.get("exps") or {}
        d = deg_expr(exps)
        qn, qd = int(rec["qn"]), int(rec["qd"])
        coef = (f"({qn} / {qd} : k)" if qd != 1 else f"({qn} : k)")
        if qn < 0:
            coef = (f"(-({-qn} / {qd} : k))" if qd != 1 else f"(-({-qn} : k))")
        chain, need, haspow = mono_ne(exps)
        nm = f"{form}QuarticChamberFace{p}810_natDegree"
        facedeg[(form, p)] = (nm, need, d)
        out = ["set_option maxHeartbeats 64000000 in",
               f"theorem {nm}",
               "    (A B C D E F G : k[X])"]
        for L in need:
            out.append(f"    (h{L}ne : {L} ≠ 0)")
        out[-1] += " :"
        out.append(f"    ({form}QuarticChamberFace{p}810 A B C D E F G).natDegree =")
        out.append(f"      {d} := by")
        out.append(f"  have hc : {coef} ≠ 0 := by norm_num")
        out.append(f"  simp only [{form}QuarticChamberFace{p}810]")
        out.append("  rw [natDegree_smul _ hc"
                   + ("".join(f", {c}" for c in chain)) + "]")
        if haspow:
            out.append("  simp only [natDegree_pow]")
        out.append("  all_goals omega")
        out.append("")
        body += "\n".join(out) + "\n"

    body += "/-! ## The chamber kills -/\n\n"
    nk = 0
    for e in leaves:
        c = cham[(e["live"], tuple(e["argmin"]))]
        r = e["carriers"][0]
        form, p, S = r["carrier"], r["packet"], e["live"]
        live = set(S)
        nm, need, d = facedeg[(form, p)]
        assert d == r["d"], (c.name, d, r["d"])
        _face, rest = packet_face_records(coords, form, pk[(form, p)])
        surv_lf = surviving(rest, live)
        deg_hyp = CC.DEG_HYP[form]
        out = ["set_option maxHeartbeats 64000000 in",
               f"/-- Chamber `{S}` / `{'·'.join(e['argmin'])}` dies on the "
               f"`{CC.GREEK[form]}` face `{d}`. -/",
               f"theorem quarticChamber{c.name}810_impossible",
               f"    ({LOADSIG8} : k)",
               "    (A B C D E F G : k[X])",
               f"    (hch : {c.defname} A B C D E F G)",
               "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
               "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))",
               f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}",
               "          A B C D E F G).natDegree = 0)"]
        if form != "kappa":
            out.append(f"    ({deg_hyp} : ({CC.FORM_LEAN[form]} {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        out[-1] += " :"
        out.append("    False := by")
        names = ["hA"]
        for X in SIG:
            names.append(f"h{X}ne" if X in live else f"h{X}z")
        nums = c.nums()
        names += [f"hq{i}" for i in range(len(nums))]
        out.append(f"  obtain ⟨{', '.join(names)}⟩ := hch")
        out.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                out.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        if "A" in need:
            out.append("  have hAne : A ≠ 0 := by")
            out.append("    intro h0")
            out.append("    have hz0 : A.natDegree = 0 := by simp [h0]")
            out.append("    clear * - hApos hz0; omega")
        # the exact-LP context every arithmetic leaf of this kill is decided
        # over: the chamber's own conjuncts, cone `A`, the dead letters and
        # (after its own `have`) `0 < d`
        base = (chamber_cons_named(nums) + CONE_CONS + dead_cons(live)
                + NONNEG_CONS)
        dvec = CC.lin(d)
        withd = base + [("hdpos", dvec, True)]
        out.append(f"  have hdpos : 0 < {d} := by")
        out.append("    by_contra hzero")
        knc = keep_str(base + [("hzero", tuple(-x for x in dvec), False)],
                       [g for X in SIG
                        for g in CC.target_of(f"{X}.natDegree = 0")])
        out.append("    exact hnc (by "
                   + (f"clear * - {knc}; " if knc else "") + "omega)")
        out.append("  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=")
        out.append(f"    quarticSigma_kappaLoadBands810 {LOADSIG8}")
        out.append("      A B C D E F G hA hkap")
        args = []
        for ld in LOADS:
            st = r["loads"][ld]["status"]
            if st == "empty":
                continue
            # exactly the order `emit_rests` uses for the hypothesis conjunction
            recs = [x for cnk in col_chunks(coords, form, ld) for x in cnk[1]]
            uniq = []
            for x in surviving(recs, live):
                g = deg_expr(x.get("exps") or {})
                if g not in uniq:
                    uniq.append(g)
            goals = [CC.target_of(f"{g} < {d}")[0] for g in uniq]
            if st == "dominated":
                kd = keep_str(withd, goals)
                args.append("(Or.inr (by "
                            + (f"clear * - {kd}; " if kd else "") + "omega))")
                continue
            hn = f"hb{ld}'"
            args.append(hn)
            out += band_block(hn, ld, f"hb{ld}",
                              band_disjuncts("kappa-letter", ld), uniq, d,
                              base, withd, live)
        zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
        seenlf = []
        for x in surv_lf:
            g = deg_expr(x.get("exps") or {})
            if g not in seenlf:
                seenlf.append(g)
        lfa = []
        for g in seenlf:
            kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]])
            lfa.append("(by " + (f"clear * - {kg}; " if kg else "") + "omega)")
        lfargs = " ".join(lfa)
        rname = f"{form}QuarticChamberRest{p}810"
        out.append(f"  have hrest : ({rname} {LOADSIG8}")
        out.append(f"      A B C D E F G).natDegree < {d} :=")
        out.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
        out.append(f"      A B C D E F G hdpos" + (f" {zargs}" if zargs else "")
                   + (f" {lfargs}" if lfargs else "") + " " + " ".join(args))
        out.append(f"  have hlead : ({form}QuarticChamberFace{p}810 "
                   "A B C D E F G).natDegree =")
        out.append(f"      {d} :=")
        out.append(f"    {nm} A B C D E F G " + " ".join(f"h{L}ne" for L in need))
        out.append(f"  rw [degreeZero{CC.FORM_CAP[form]}Quartic810_eq_face{p}_add_rest,")
        out.append("    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]")
        hy = deg_hyp if form != "kappa" else "hkap"
        out.append(f"    at {hy}")
        out.append(f"  clear * - hdpos {hy}; omega")
        out.append("")
        body += "\n".join(out) + "\n"
        nk += 1
    name = "Grok810ScaleZeroQuarticChamberKillsScratch"
    doc = (
        "# Single-monomial chamber kills, `(8,10)` scale zero\n\n"
        f"{len(used)} face-degree lemmas and {nk} chamber kills: every leaf whose\n"
        "level-0 certificate is a single monomial *and* whose eight load columns\n"
        "are either empty, dominated by the chamber's own ℕ conjuncts, or covered\n"
        "by the κ band of `…ChamberBandsScratch`.  Which leaves those are is\n"
        "decided, with exact rational Farkas certificates, by\n"
        "`scripts/derive_810_quartic_chamber_killplan.py`; the rest are named in\n"
        "the residual.  Untracked working note."
    )
    ln, _names = write_split(name, "QuarticChamberKills810", doc,
                             prune_arith(name_chamber_facts(body),
                                         SINGLE_KEEP), prev)
    MODULES.append((name, ln, f"{len(used)} face-degree lemmas and {nk} "
                              "single-monomial chamber kills"))
    return name, {(e["live"], tuple(e["argmin"])) for e in leaves}




# --------------------------------------------------- module 12: the residual
def emit_residual(data, chambers, plan, killed, prev):
    kills = {}
    for e in plan["leaves"]:
        if e["killable"] and e["kind"] == "single_monomial":
            kills[(e["live"], tuple(e["argmin"]))] = e["carriers"][0]["carrier"]
    surv = [c for c in chambers if (c.live, c.argmin) not in kills]
    body = "/-! ## What the chamber ladder leaves -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- The {len(surv)} cost-argmin chambers Files B/C do not close: the\n"
             "two genuinely open leaves, the 19 deep-rescue leaves, the 64\n"
             "weak-band leaves, the 12 `no_monomial_target` leaves, the\n"
             "`power_target` leaves (whose kill needs a `_coeff_top` extraction),\n"
             "and every leaf whose κ band is unusable (`ζ`/`θ` with `B` or `C`\n"
             "live) or which needs a `γ/ε/η` band (corner `H`). -/\n")
    body += "inductive QuarticChamberResidual810 (A B C D E F G : k[X]) : Prop\n"
    for c in surv:
        body += (f"  | r{c.name} : {c.defname} A B C D E F G →\n"
                 f"      QuarticChamberResidual810 A B C D E F G\n")
    body += "\n"

    # the exhaust -> kill/residual dispatch
    lines = []
    for s in range(1, 7):
        grp = [c for c in chambers if len(c.live) == s]
        lines.append(f"      | size{s} h =>")
        lines.append("        cases h with")
        for c in grp:
            key = (c.live, c.argmin)
            if key in kills:
                form = kills[key]
                resid_hyp = {"kappa": "hkapDeg", "mu": "hmuDeg",
                             "xi": "hxiDeg", "pi": "hpiDeg",
                             "nu": "hnuDeg", "omicron": "homiDeg"}
                extra = "" if form == "kappa" else f" {resid_hyp[form]}"
                lines.append(f"        | {c.ctor} hc =>")
                lines.append(f"          exact (quarticChamber{c.name}810_impossible")
                lines.append(f"            {LOADSIG8}")
                lines.append(f"            A B C D E F G hc hnc hkapDeg{extra}).elim")
            else:
                lines.append(f"        | {c.ctor} hc =>")
                lines.append(f"          exact QuarticChamberResidual810.r{c.name} hc")
    dispatch = "\n".join(lines)

    body += "set_option maxHeartbeats 64000000 in\n"
    body += ("/-- Honest leftover after Files B/C of the σ-defect ladder.\n\n"
             "Closed relative to `normalized810ScaleZero_quarticLoadLadderResidual`:\n"
             f"the 1115-chamber cost-argmin exhaust and the {len(kills)} chambers whose\n"
             "level-0 certificate is a single monomial and whose eight load\n"
             "columns are empty, dominated, or covered by the κ ladder's band.\n"
             f"Remaining: the all-constant corner (`l = β = δ = ζ = 0`) and the\n"
             f"{len(surv)} chambers of `QuarticChamberResidual810`.  Next unused row:\n"
             "the `power_target` and `no_monomial_target` kills (`_coeff_top` plus\n"
             "the certificates of `Grok810ScaleZeroQuarticChamberCertificatesScratch`),\n"
             "then the `N₂/N₅/N₇` load ladder of\n"
             "`Grok810ScaleZeroQuarticChamberAuxTowerScratch` for the `ζ`/`θ`\n"
             "columns κ cannot reach, then corner `H` (`γ/ε/η`).\n"
             "No `sorry`, no new axioms, no finite-root shortcut. -/\n")
    body += """theorem normalized810ScaleZero_quarticChamberResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧
              B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
              E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0) ∨
            QuarticChamberResidual810 A B C D E F G)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticLoadLadderResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · obtain ⟨hconeA, hexh, hlK, hbK, hdK, hzK, htK, hconst, hevenC, hevenE⟩ := hA
    refine Or.inl ⟨hconeA, ?_⟩
    by_cases hnc : B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
    · rcases hconst with ⟨hl0, hb0, hd0, hz0⟩ | hn
      · exact Or.inl ⟨hl0, hb0, hd0, hz0, hnc.1, hnc.2.1, hnc.2.2.1,
          hnc.2.2.2.1, hnc.2.2.2.2.1, hnc.2.2.2.2.2⟩
      · exact absurd hnc hn
    · refine Or.inr ?_
      have hsupp := quarticChamberSupport810_of (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G hconeA
        hjdiv hder
      cases hsupp with
"""
    body += dispatch + "\n"
    body += "  · exact Or.inr hABCDEFG\n\n"
    body += "#print axioms normalized810ScaleZero_quarticChamberResidual\n"

    name = "Grok810ScaleZeroQuarticChamberResidualScratch"
    doc = (
        "# Residual after Files B/C, `(8,10)` scale zero\n\n"
        f"`QuarticChamberResidual810`, the {len(surv)}-constructor inductive of the\n"
        "cost-argmin chambers the level-0 kills do not reach, and\n"
        "`normalized810ScaleZero_quarticChamberResidual`, which routes the\n"
        f"1115-chamber exhaust through the {len(kills)} single-monomial kills.\n"
        "Untracked working note."
    )
    out = (header(prev, doc) + "section QuarticChamberResidual810\n\n"
           + "variable [IsAlgClosed k]\n\n"
           + body)
    out += "\nend QuarticChamberResidual810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"`QuarticChamberResidual810` ({len(surv)} chambers) "
                              "and `normalized810ScaleZero_quarticChamberResidual`"))
    return name, surv, kills




# ------------------------------- module 16: the cost-form auxiliary ladder
from fractions import Fraction as _Fr  # noqa: E402

AUXPARTS = {"kappa": [("kappa", 0, _Fr(1))],
            "n2": [("nu", 0, _Fr(1)), ("kappa", 1, _Fr(1, 8))],
            "n5": [("omicron", 0, _Fr(1)), ("nu", 1, _Fr(1, 8)),
                   ("kappa", 2, _Fr(3, 128))],
            "n7": [("primitive", 0, _Fr(1)), ("omicron", 1, _Fr(1)),
                   ("nu", 2, _Fr(3, 16)), ("kappa", 3, _Fr(5, 128))]}
AUXWT = {"kappa": 11, "n2": 13, "n5": 15, "n7": 17}
AUXNDEG = {"kappa": 0, "n2": 1, "n5": 2, "n7": 3}
AUXFACE = {"kappa": "kappaQuartic{}Face810", "n2": "n2Quartic{}Face810",
           "n5": "n5Quartic{}Face810", "n7": "n7Quartic{}Face810"}
AUXNEEDS = {"kappa": ["kappa"], "n2": ["nu", "kappa"],
            "n3": ["omicron", "nu"],
            "n4": ["primitive", "omicron"],
            "n5": ["omicron", "nu", "kappa"],
            "n6": ["primitive", "omicron", "nu"],
            "n7": ["primitive", "omicron", "nu", "kappa"]}
AUXTAG = {"kappa": "Kappa", "n2": "N2", "n3": "N3", "n4": "N4",
          "n5": "N5", "n6": "N6", "n7": "N7"}
AUXHYP = {"primitive": ("hprim", "= 1"), "omicron": ("homi", "= 0"),
          "nu": ("hnu", "= 0"), "kappa": ("hkap", "= 0")}
PUREA = ["l", "beta", "delta", "zeta", "theta"]
NOPUREA = ["gamma", "epsilon", "eta"]
WPI = CC.LOADW


def aux_terms(aux):
    """(letter monomial, A power, load) -> rational coefficient."""
    coords = CC.load_coords()
    acc = {}
    for f, ap, co in AUXPARTS[aux]:
        for r in coords[f]:
            ex = r.get("exps") or {}
            mon = "".join(L * int(ex.get(L, 0) or 0) for L in SIG)
            ld = (list(r["loads"]) or [None])[0]
            key = (mon, int(ex.get("A", 0) or 0) + ap, ld)
            acc[key] = acc.get(key, _Fr(0)) + co * _Fr(int(r["qn"]), int(r["qd"]))
    return {k: v for k, v in acc.items() if v != 0}


def _divides(a, b):
    ca, cb = collections.Counter(a), collections.Counter(b)
    return all(ca[x] <= cb[x] for x in ca)


def _minimal(ms):
    ms = set(ms)
    return sorted({m for m in ms if not any(n != m and _divides(n, m) for n in ms)},
                  key=lambda m: (len(m), m))


def as_record(key, coef):
    mon, ap, ld = key
    exps = {"A": ap} if ap else {}
    for ch in mon:
        exps[ch] = exps.get(ch, 0) + 1
    return {"exps": exps, "loads": ({ld: 1} if ld else {}),
            "qn": coef.numerator, "qd": coef.denominator}


def cost_gt(m, w):
    """`w * A.natDegree < cost m`, cross-multiplied over ℕ."""
    return CC.render7(CC.sub7(CC.scal7(w, CC.unit(0)), CC.cform(m)), True)


def cost_le(m, w):
    """`cost m ≤ w * A.natDegree` — the negation, for the band."""
    return CC.render7(CC.sub7(CC.cform(m), CC.scal7(w, CC.unit(0))), False)


def cost_conjuncts(aux, pi):
    """The predicate's cost conjuncts, as (monomial, weight) pairs."""
    T = aux_terms(aux)
    wp = WPI[pi]
    out = [(m, wp) for m in _minimal([m for (m, _a, ld) in T if ld is None])]
    for p2 in NOPUREA:
        if WPI[p2] >= wp:
            continue
        for m in _minimal([m for (m, _a, ld) in T if ld == p2]):
            out.append((m, wp - WPI[p2]))
    return out


CONE_HYPS = [("hApos", "0 < A.natDegree"),
             ("hAB", "2 * B.natDegree < 3 * A.natDegree"),
             ("hAC", "C.natDegree < 2 * A.natDegree"),
             ("hAD", "2 * D.natDegree < 5 * A.natDegree"),
             ("hAE", "E.natDegree < 3 * A.natDegree"),
             ("hAF", "2 * F.natDegree < 7 * A.natDegree"),
             ("hAG", "G.natDegree < 4 * A.natDegree")]


def cost_predicate_satisfiable(aux, pi):
    """Is the cost-form `Top` predicate realisable at all?  For `κ` and `theta`,
    `cost B³ = 9a − 6b > 9a` is impossible over ℕ, so that kill would be vacuous
    and its band trivially true."""
    cons = list(CC.CONEA) + list(CC.NONNEG)
    for m, w in cost_conjuncts(aux, pi):
        cons.append(CC.gt(CC.cform(m), CC.scal7(w, CC.unit(0))))
    return CC.feasible(cons)


def emit_cost_kills(aux, entries):
    """The five cost-form kills, their bands and the cascade, for one auxiliary."""
    T = aux_terms(aux)
    w = AUXWT[aux]
    tag = AUXTAG[aux]
    gk = GREEK_ALL[aux]
    lhs = CARRIER_LEAN[aux]
    body = f"/-! ### `{gk}` cost-form monotonicity, kills and bands -/\n\n"
    byload = {pi: e for e in entries for pi in [e[0]]}
    # monotonicity along the ladder
    have = [e[0] for e in entries]
    for hi, lo in zip(have[1:], have[:-1]):
        chi, clo = CC.LOAD_CAP[hi], CC.LOAD_CAP[lo]
        hyp_hi = byload[hi][2]
        hyp_lo = byload[lo][2]
        nm = f"quartic{tag}CostTop{chi}810_imp_{clo}810"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- The `{hi}` column of `{gk}` tops it only if the cheaper `{lo}`\n"
                 "column does. -/\n"
                 f"theorem {nm}\n"
                 "    {A B C D E F G : k[X]}\n"
                 f"    (h : Quartic{tag}CostTop{chi}810 A B C D E F G) :\n"
                 f"    Quartic{tag}CostTop{clo}810 A B C D E F G := by\n"
                 f"  obtain ⟨hA, {', '.join(h for h, _ in hyp_hi)}⟩ := h\n"
                 "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA\n"
                 "  exact ⟨hA, " + ", ".join("by omega" for _ in hyp_lo) + "⟩\n\n")
    # kills
    for (pi, pname, hyp, j, rname, zeroed, cap) in entries:
        coef = T[("", j, pi)]
        cstr = (f"{coef.numerator} / {coef.denominator}" if coef.denominator != 1
                else f"{coef.numerator}")
        lighter = [p for p in PUREA if WPI[p] < WPI[pi]]
        face = AUXFACE[aux].format(cap)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Cost-form kill: if the pure-`A` `{pi}` column tops `{gk}` then\n"
                 f"`{pi} = 0`, because `natDegree {gk} ≤ {AUXNDEG[aux]}·a < {j}·a`. -/\n"
                 f"theorem quarticSigma{tag}Cost_{pi}_eq_zero\n"
                 f"    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X])\n"
                 f"    (htop : {pname} A B C D E F G)\n")
        for p in lighter:
            body += f"    (h{p}0 : {p} = 0)\n"
        for f in AUXNEEDS[aux]:
            if f == "kappa":
                continue
            h, rel = AUXHYP[f]
            body += (f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}\n"
                     f"          A B C D E F G).natDegree {rel})\n")
        body += (f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}\n"
                 "          A B C D E F G).natDegree = 0) :\n"
                 f"    {pi} = 0 := by\n"
                 "  by_contra hne\n"
                 f"  obtain ⟨hA, {', '.join(h for h, _ in hyp)}⟩ := htop\n"
                 "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA\n"
                 f"  have hc : ({cstr} * {pi} : k) ≠ 0 :=\n"
                 "    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne\n"
                 f"  have hlead : ({face} {pi} A).natDegree = {j} * A.natDegree := by\n"
                 f"    simp only [{face}]\n"
                 + (f"    rw [natDegree_smul _ hc, natDegree_pow]\n" if j > 1 else
                    f"    rw [natDegree_smul _ hc]\n    omega\n")
                 + f"  have hrest := {rname}_natDegree_lt {LOADSIG8}\n"
                 + "    " + " ".join(h for h, _ in CONE_HYPS + hyp) + "\n")
        for p in lighter:
            body += f"  subst h{p}0\n"
        if aux != "kappa":
            hargs = " ".join(AUXHYP[f][0] for f in AUXNEEDS[aux])
            pre = "hApos " if aux in ("n5", "n7") else ""
            body += (f"  have hle := {CARRIER_LEAN[aux]}_natDegree_le {zeroed}\n"
                     f"    A B C D E F G {pre}{hargs}\n")
            tgt = "hle"
        else:
            tgt = "hkap"
        # the substituted loads stay as binders in the split lemma, so they
        # must be given by name or `rw` leaves them as metavariables
        named = "".join(f" ({p} := 0)" for p in lighter)
        body += (f"  rw [{lhs}_eq_{pi}CostColumn_add_rest{named},\n"
                 "    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]\n"
                 f"    at {tgt}\n"
                 "  omega\n\n")
    # bands
    for (pi, pname, hyp, j, rname, zeroed, cap) in entries:
        cc = cost_conjuncts(aux, pi)
        n = len(cc)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem quarticSigma{tag}Cost_{pi}_band\n"
                 f"    {{{pi} : k}} (A B C D E F G : k[X])\n"
                 "    (hA : QuarticRatioConeA810 A B C D E F G)\n"
                 f"    (hkill : {pname} A B C D E F G → {pi} = 0) :\n"
                 f"    {pi} = 0 ∨\n      "
                 + " ∨\n      ".join(cost_le(m, ww) for m, ww in cc) + " := by\n")

        def tree(t, ind):
            if t == n:
                return [f"{ind}exact Or.inl (hkill ⟨hA, "
                        + ", ".join(f"hb{u}" for u in range(n)) + "⟩)"]
            out = [f"{ind}by_cases hb{t} : {hyp[t][1]}"]
            sub = tree(t + 1, ind + "  ")
            out.append(f"{ind}· {sub[0].strip()}")
            out += sub[1:]
            pos = 1 + t
            inj = ("Or.inr (" * pos + "?_" + ")" * pos if pos == n
                   else "Or.inr (" * pos + "Or.inl ?_" + ")" * pos)
            out.append(f"{ind}· refine {inj}")
            out.append(f"{ind}  omega")
            return out
        body += "\n".join(tree(0, "  ")) + "\n\n"
    # the cascade
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- The cost-form `{gk}` ladder as five band disjunctions. -/\n"
             f"theorem quarticSigma{tag}CostBands810\n"
             f"    ({LOADSIG8} : k)\n"
             "    (A B C D E F G : k[X])\n"
             "    (hA : QuarticRatioConeA810 A B C D E F G)\n")
    for f in AUXNEEDS[aux]:
        if f == "kappa":
            continue
        h, rel = AUXHYP[f]
        body += (f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}\n"
                 f"          A B C D E F G).natDegree {rel})\n")
    body += (f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}\n"
             "          A B C D E F G).natDegree = 0) :\n")
    stmts = []
    for (pi, _pn, _h, _j, _r, _z, _c) in entries:
        cc = cost_conjuncts(aux, pi)
        stmts.append(f"    ({pi} = 0 ∨\n      "
                     + " ∨\n      ".join(cost_le(m, ww) for m, ww in cc) + ")")
    body += " ∧\n".join(stmts) + " := by\n"

    def mono(hi, lo):
        i, jj = have.index(hi), have.index(lo)
        term = "htop"
        for t in range(i, jj, -1):
            term = (f"quartic{tag}CostTop{CC.LOAD_CAP[have[t]]}810_imp_"
                    f"{CC.LOAD_CAP[have[t - 1]]}810 ({term})")
        return term

    def branch(pos, ind):
        out = []
        if pos == len(have):
            out.append(f"{ind}exact ⟨" + ", ".join(f"Or.inl h{p}0" for p in have) + "⟩")
            return out
        pi = have[pos]
        pname = byload[pi][1]
        out.append(f"{ind}by_cases hT{pi} : {pname} A B C D E F G")
        args = "".join(f" h{p}0" for p in have[:pos])
        extra = ("".join(" " + AUXHYP[f][0] for f in AUXNEEDS[aux])
                 if aux != "kappa" else " hkap")
        out.append(f"{ind}· have h{pi}0 : {pi} = 0 :=")
        out.append(f"{ind}    quarticSigma{tag}Cost_{pi}_eq_zero {LOADSIG8}")
        out.append(f"{ind}      A B C D E F G hT{pi}{args}{extra}")
        out += branch(pos + 1, ind + "  ")
        comps = [f"Or.inl h{p}0" for p in have[:pos]]
        for q in have[pos:]:
            comps.append(f"quarticSigma{tag}Cost_{q}_band ({q} := {q}) A B C D E F G hA\n"
                         f"{ind}      (fun htop => absurd ({mono(q, pi)}) hT{pi})")
        out.append(f"{ind}· exact ⟨" + (",\n" + ind + "    ").join(comps) + "⟩")
        return out
    body += "\n".join(branch(0, "  ")) + "\n\n"
    return body


def emit_cost_ladder(prev, auxes=("kappa", "n2"), name=None, doc=None,
                     split=False):
    body = ""
    casc = {}
    for aux in auxes:
        T = aux_terms(aux)
        w, kdeg = AUXWT[aux], AUXNDEG[aux]
        gk = GREEK_ALL[aux]
        body += (f"/-! ## `{gk}` in cost form: `c₀({gk}) > w_π·a` instead of "
                 "`2·s_X > w_π·a` -/\n\n")
        for pi in PUREA:
            wp = WPI[pi]
            j = (w - wp) // 2
            cap = CC.LOAD_CAP[pi]
            if not cost_predicate_satisfiable(aux, pi):
                continue          # `κ`/`theta`: `cost B³ > 9a` is impossible
            zeroed = " ".join("0" if (p in PUREA and WPI[p] < wp) else p
                              for p in CC.LOADS)
            recs = EC.sort_records(
                [as_record(k, c) for k, c in T.items()
                 if not (k[2] == pi and k[0] == "" )
                 and not (k[2] in PUREA and WPI[k[2]] < wp)])
            rname = f"{aux}QuarticCostRest{cap}810"
            chunks = split_chunks(recs)
            cnames = []
            for i, ch in enumerate(chunks):
                nm = rname if len(chunks) == 1 else f"{rname}c{i + 1}"
                cnames.append((nm, ch))
                body += "set_option maxHeartbeats 64000000 in\n"
                body += (f"/-- `{gk}` off its pure-`A` `{pi}` column, with the lighter\n"
                         f"pure-`A` loads set to zero"
                         + (f" (chunk {i + 1}/{len(chunks)})" if len(chunks) > 1 else "")
                         + f": {len(ch)} monomials. -/\n")
                body += poly_def(nm, LOADSIG8, ch)
            if len(chunks) > 1:
                body += "set_option maxHeartbeats 64000000 in\n"
                body += (f"def {rname}\n    ({LOADSIG8} : k)\n"
                         "    (A B C D E F G : k[X]) : k[X] :=\n  "
                         + " +\n    ".join(f"{nm} {LOADSIG8} A B C D E F G"
                                           for nm, _ in cnames) + "\n\n")
            # the split identity
            simpset = [CARRIER_LEAN[aux]]
            if aux != "kappa":
                simpset += [CC.FORM_LEAN[f] for f in AUXNEEDS[aux]]
                if "primitive" in AUXNEEDS[aux]:
                    simpset += RHO_GROUPS
            simpset += [AUXFACE[aux].format(cap), rname] + [nm for nm, _ in cnames
                                                            if nm != rname]
            lhs = CARRIER_LEAN[aux]
            body += "set_option maxHeartbeats 64000000 in\n"
            body += (f"/-- Cone-free: with the lighter pure-`A` loads zero, `{gk}` splits\n"
                     f"into its pure-`A` `{pi}` column `c·{pi}·A^{j}` and the rest. -/\n")
            body += (f"theorem {lhs}_eq_{pi}CostColumn_add_rest\n"
                     f"    ({LOADSIG8} : k)\n"
                     "    (A B C D E F G : k[X]) :\n"
                     f"    {lhs} {zeroed} A B C D E F G =\n"
                     f"      {AUXFACE[aux].format(cap)} {pi} A +\n"
                     f"        {rname} {zeroed} A B C D E F G := by\n"
                     f"  simp only [{', '.join(dict.fromkeys(simpset))},\n"
                     "    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,\n"
                     "    zero_add, sub_zero, neg_zero, pow_one]\n")
            if aux == "kappa":
                body += "  all_goals module\n\n"
            else:
                body += ("  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))\n"
                         "  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,\n"
                         "    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,\n"
                         "    map_div₀, map_ofNat, map_natCast, map_one]\n"
                         "  ring\n\n")
            # the rest bounds
            cc = cost_conjuncts(aux, pi)
            hyp = [(f"hp{t}", cost_gt(m, ww)) for t, (m, ww) in enumerate(cc)]
            for nm, ch in cnames:
                subs = (split_chunks(ch, CD_MAX) if len(ch) > CD_MAX else [])
                for t2, sch in enumerate(subs):
                    sn = f"{nm}s{t2 + 1}"
                    body += "set_option maxHeartbeats 64000000 in\n"
                    body += (f"/-- Sub-chunk {t2 + 1}/{len(subs)} of `{nm}`\n"
                             f"({len(sch)} monomials): a `compute_degree` over "
                             "more than six\nmonomials with seven symbolic "
                             "degrees times out. -/\n")
                    body += poly_def(sn, LOADSIG8, sch)
                    body += "set_option maxHeartbeats 64000000 in\n"
                    body += (f"theorem {sn}_natDegree_lt\n"
                             f"    ({LOADSIG8} : k)\n"
                             "    {A B C D E F G : k[X]}\n")
                    for h, s2 in CONE_HYPS + hyp:
                        body += f"    ({h} : {s2})\n"
                    body = body[:-1] + " :\n"
                    body += (f"    ({sn} {zeroed} A B C D E F G).natDegree <\n"
                             f"      {j} * A.natDegree := by\n")
                    if refl_ok(sn):
                        body += "\n".join(refl_bnd_proof(sn)) + "\n\n"
                    else:
                        body += (f"  simp only [{sn}, zero_mul, mul_zero, "
                                 "zero_smul,\n"
                                 "    smul_zero, add_zero, zero_add, sub_zero, "
                                 "neg_zero]\n"
                                 "  compute_degree\n  omega\n\n")
                if subs:
                    body += "set_option maxHeartbeats 64000000 in\n"
                    body += (f"theorem {nm}_split\n"
                             f"    ({LOADSIG8} : k)\n"
                             "    (A B C D E F G : k[X]) :\n"
                             f"    {nm} {LOADSIG8} A B C D E F G =\n      "
                             + " +\n        ".join(
                                 f"{nm}s{t2 + 1} {LOADSIG8} A B C D E F G"
                                 for t2 in range(len(subs)))
                             + " := by\n"
                             + f"  simp only [{nm}, "
                             + ", ".join(f"{nm}s{t2 + 1}"
                                         for t2 in range(len(subs))) + "]\n"
                             "  all_goals module\n\n")
                body += "set_option maxHeartbeats 64000000 in\n"
                body += (f"theorem {nm}_natDegree_lt\n"
                         f"    ({LOADSIG8} : k)\n"
                         "    {A B C D E F G : k[X]}\n")
                for h, s2 in CONE_HYPS + hyp:
                    body += f"    ({h} : {s2})\n"
                body = body[:-1] + " :\n"
                body += (f"    ({nm} {zeroed} A B C D E F G).natDegree <\n"
                         f"      {j} * A.natDegree := by\n")
                if subs:
                    aa = " ".join(h for h, _ in CONE_HYPS + hyp)
                    body += f"  rw [{nm}_split {zeroed} A B C D E F G]\n"
                    tt = [f"{nm}s{t2 + 1}_natDegree_lt {LOADSIG8} {aa}"
                          for t2 in range(len(subs))]
                    acc2 = f"({tt[0]})"
                    for t3 in tt[1:]:
                        acc2 = f"(natDegree_add_lt810 {acc2} ({t3}))"
                    body += f"  exact {acc2}\n\n"
                elif refl_ok(nm):
                    body += "\n".join(refl_bnd_proof(nm)) + "\n\n"
                else:
                    body += (f"  simp only [{nm}, zero_mul, mul_zero, "
                             "zero_smul,\n"
                             "    smul_zero, add_zero, zero_add, sub_zero, "
                             "neg_zero]\n"
                             "  compute_degree\n  omega\n\n")
            if len(chunks) > 1:
                args = " ".join(h for h, _ in CONE_HYPS + hyp)
                body += "set_option maxHeartbeats 64000000 in\n"
                body += (f"theorem {rname}_natDegree_lt\n"
                         f"    ({LOADSIG8} : k)\n"
                         "    {A B C D E F G : k[X]}\n")
                for h, s in CONE_HYPS + hyp:
                    body += f"    ({h} : {s})\n"
                body = body[:-1] + " :\n"
                body += (f"    ({rname} {zeroed} A B C D E F G).natDegree <\n"
                         f"      {j} * A.natDegree := by\n"
                         f"  simp only [{rname}]\n")
                terms_ = [f"{nm}_natDegree_lt {LOADSIG8} {args}" for nm, _ in cnames]
                acc = f"({terms_[0]})"
                for t in terms_[1:]:
                    acc = f"(natDegree_add_lt810 {acc} ({t}))"
                body += f"  exact {acc}\n\n"
            # the predicate, the kill and the band
            pname = f"Quartic{AUXTAG[aux]}CostTop{cap}810"
            body += "set_option maxHeartbeats 64000000 in\n"
            body += (f"/-- The pure-`A` `{pi}` column of `{gk}` is its unique top: every\n"
                     f"load-free monomial costs more than `{wp}·a`, and every monomial of a\n"
                     "lighter load column without a pure-`A` monomial costs more than the\n"
                     "weight gap. -/\n")
            body += (f"def {pname} (A B C D E F G : k[X]) : Prop :=\n"
                     "  QuarticRatioConeA810 A B C D E F G ∧\n    "
                     + " ∧\n    ".join(s for _h, s in hyp) + "\n\n")
            casc.setdefault(aux, []).append((pi, pname, hyp, j, rname, zeroed, cap))
        kills_body = emit_cost_kills(aux, casc[aux])
        if not split:
            body += kills_body
    name = name or "Grok810ScaleZeroQuarticChamberCostLadderScratch"
    doc = doc or (
        "# The cost-form `κ`/`N₂` load ladder, `(8,10)` scale zero\n\n"
        "`QuarticKappaLoadTop<P>810` of File A asks `2·s_X > w·a` for *every*\n"
        "letter, which implies but is not equivalent to `c₀(κ) > w·a`; the\n"
        "chamber taxonomy's band-strictness flags were computed against the\n"
        "latter, so File A's band is too weak on 525 (leaf, carrier) pairs.\n"
        "This module states the kill in cost form — one inequality per *minimal*\n"
        "load-free monomial of the auxiliary, plus one per minimal monomial of\n"
        "each lighter load column that has no pure-`A` monomial — and proves the\n"
        "same five kills for `κ` and for `N₂ = ν + (1/8)·A·κ`, whose pure-`A`\n"
        "column sits one `A` higher and therefore reaches loads `κ` cannot\n"
        "(`~/lean/tools/sigma810/OPEN_CHAMBERS.md` §1).  Untracked working note."
    )
    sec = ("QuarticCostLadder810" if auxes == ("kappa", "n2")
           else f"QuarticCostLadder{AUXTAG[auxes[0]]}810")
    out = header([prev, "Grok810ScaleZeroQuarticLoadLadderScratch"], doc)
    out += f"section {sec}\n\n" + body
    out += f"\nend {sec}\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, "cost-form kill predicates, rest bounds"
                              + ("" if split else ", kills, bands and cascades")))
    if not split:
        return name
    name2 = name.replace("LadderScratch", "KillsScratch")
    doc2 = (f"# The cost-form `{GREEK_ALL[auxes[0]]}` kills and bands, "
            "`(8,10)` scale zero\n\nThe monotonicity chain, the five kills, "
            "their band disjunctions and the cascade, split off\n"
            f"`{name}` to stay under the compile budget.  "
            "Untracked working note.")
    out2 = (header([name, "Grok810ScaleZeroQuarticLoadLadderScratch"], doc2)
            + f"section {sec}Kills\n\n" + kills_body
            + f"\nend {sec}Kills\n" + FOOTER)
    ln2 = write(name2 + ".lean", out2)
    MODULES.append((name2, ln2, "cost-form kills, bands and the cascade"))
    return name2




# --------------------------- modules 17-20: the cost-ladder kills and residual
BANDVAR = {"kappa-letter": "hb{}", "kappa-cost": "hkb{}", "n2-cost": "hnb{}"}
BANDCASC = {"kappa-letter": ("quarticSigma_kappaLoadBands810", LADDER, False),
            "kappa-cost": ("quarticSigmaKappaCostBands810",
                           ["l", "beta", "delta", "zeta"], False),
            "n2-cost": ("quarticSigmaN2CostBands810", LADDER, True)}


def band_disjuncts(source, ld):
    if source == "kappa-letter":
        return [(X, ineq_of(X, TOP[ld][X])) for X in SIG]
    aux = "kappa" if source == "kappa-cost" else "n2"
    return [(None, cost_le(m, w)) for m, w in cost_conjuncts(aux, ld)]


def band_block(hn, ld, hv, dis, uniq, d, base, withd, live, ind="  ",
               always=()):
    """The band-to-∧-chain conversion of one load column of a kill.

    `dis` is `band_disjuncts(source, ld)`.  The ∧-chain the rest lemma wants
    is normally implied, over the chamber's own conjuncts, by a *single* one
    of its own conjuncts (the head of the load column), so the 7- resp.
    21-way band `rcases` is proved into that one conjunct and expanded into
    the full chain once instead of once per branch.  Every `omega` gets the
    `clear * -` keep-list of an exact rational Farkas certificate; where no
    certificate exists the whole context is kept, so the shape can only get
    slower, never unsound.  The statement of `hn` is unchanged."""
    goals = [CC.target_of(f"{g} < {d}")[0] for g in uniq]
    out = [f"{ind}have {hn} : {ld} = 0 ∨ ("
           + " ∧ ".join(f"{g} < {d}" for g in uniq) + ") := by"]
    head = cover_head(withd, goals)
    i2, tgt = ind + "  ", goals
    if head is not None:
        out.append(f"{i2}have hb{ld}s : {ld} = 0 ∨ ("
                   + " ∧ ".join(f"{uniq[j]} < {d}" for j in head) + ") := by")
        i2, tgt = ind + "    ", [goals[j] for j in head]
    out.append(f"{i2}rcases {hv} with h | " + " | ".join("h" for _ in dis))
    out.append(f"{i2}· exact Or.inl h")
    for X, txt in dis:
        if X is not None and TOP[ld][X] == "hard":
            out.append(f"{i2}· exact absurd h{X}z h")
            continue
        hc = CC.constraints_of(txt)[0]
        kn = (keep_str(base, [(CC.scal7(-1, hc[0]), True)], always)
              if X is not None and X not in live else None)
        if kn is not None:
            out.append(f"{i2}· exact absurd h (by clear * - {kn}; omega)")
            continue
        kb = keep_str(withd + [("h", hc[0], hc[1])], tgt, always)
        out.append(f"{i2}· exact Or.inr (by "
                   + (f"clear * - {kb}; " if kb else "") + "omega)")
    if head is not None:
        kh = keep_str(withd + [("h", goals[j][0], goals[j][1]) for j in head],
                      goals, always)
        out.append(f"{ind}  rcases hb{ld}s with h | h")
        out.append(f"{ind}  · exact Or.inl h")
        out.append(f"{ind}  · exact Or.inr (by "
                   + (f"clear * - {kh}; " if kh else "") + "omega)")
    return out


FACES_PARTS = ["Grok810ScaleZeroQuarticChamberFacesPart0Scratch",
               "Grok810ScaleZeroQuarticChamberFacesPart1Scratch"] + \
    [f"Grok810ScaleZeroQuarticChamberFacesPart{i}Scratch" for i in range(2, 20)]


def declared_names(modules):
    modules = [m for m in modules
               if m != "Grok810ScaleZeroQuarticChamberFacesScratch"] + \
        ([n for n in FACES_PARTS
          if "Grok810ScaleZeroQuarticChamberFacesScratch" in modules] or [])
    """Declaration names already emitted, so modules 17-20 never re-declare."""
    out = set()
    files = []
    for m in modules:
        files.append(ROOT / (m + ".lean"))
        # an aggregator holds no declarations; they are in its parts
        files += sorted(ROOT.glob(m[:-7] + "Part*Scratch.lean"))
    for p in files:
        if not p.exists():
            continue
        for ln in p.read_text().split("\n"):
            mm = re.match(r"^(?:theorem|lemma|def|abbrev|inductive)\s+([^\s(:{]+)", ln)
            if mm:
                out.add(mm.group(1))
    return out


def load_plan2():
    import json
    return json.loads((ROOT / "scripts" /
                       "out_810_quartic_chamber_killplan2.json").read_text())


def emit_columns2(coords, plan2, have, prev, tag="2", doc=None,
                  kinds=("single_monomial",)):
    want = collections.OrderedDict()
    for e in plan2["leaves"]:
        if not e["killable"] or e["kind"] not in kinds:
            continue
        for r in e["carriers"]:
            for ld, v in r["loads"].items():
                if v["status"] in ("dominated", "band"):
                    want[(r["carrier"], ld, e["live"])] = True
    body, n = "", 0
    for (form, ld, S) in want:
        live = set(S)
        for nm, recs in col_chunks(coords, form, ld):
            if f"{nm}_natDegree_lt_of_live_{S}" in have:
                continue
            surv = surviving(recs, live)
            hyps, seen = [], {}
            for r in surv:
                g = deg_expr(r.get("exps") or {})
                if g not in seen:
                    seen[g] = f"hd{len(seen)}"
                    hyps.append((seen[g], g))
            out = ["set_option maxHeartbeats 64000000 in",
                   f"theorem {nm}_natDegree_lt_of_live_{S}",
                   "    {d : ℕ}", f"    ({ld} : k)",
                   "    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
            for X in SIG:
                if X not in live:
                    out.append(f"    (h{X}z : {X} = 0)")
            for h, g in hyps:
                out.append(f"    ({h} : {g} < d)")
            out[-1] += " :"
            out.append(f"    ({nm} {ld} A B C D E F G).natDegree < d := by")
            for X in SIG:
                if X not in live:
                    out.append(f"  subst h{X}z")
            for e2 in range(2, 9):
                out.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                           "zero_pow (by decide)")
            if surv and refl_ok(nm):
                out += refl_degok_proof(nm)
            else:
                out.append(f"  simp only [{nm}, {POWNAMES}, {ZERO_SIMP}]")
                out.append("  omega")
            out.append("")
            body += "\n".join(out) + "\n"
            n += 1
    if n == 0:
        log(f"columns{tag}: nothing new - module skipped")
        return prev
    name = f"Grok810ScaleZeroQuarticChamberColumns{tag}Scratch"
    doc = doc or ("# Load-column bounds for the cost-ladder kills, `(8,10)` scale zero\n\n"
                  f"The {n} (carrier, load, live-set) column bounds the chambers\n"
                  "unblocked by `…ChamberCostLadderScratch` need and\n"
                  "`…ChamberColumnsScratch` does not already have.  Untracked note.")
    out = header(prev, doc) + f"section QuarticChamberColumns{tag}810\n\n" + body
    out += f"\nend QuarticChamberColumns{tag}810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{n} further load-column bounds"))
    return name


def emit_rests2(coords, plan2, have, prev, tag="2", doc=None,
                kinds=("single_monomial",)):
    pk = {(p["carrier"], p["id"]): [tuple(x) for x in p["face"]]
          for p in plan2["packets"]}
    used_pk, used_pl = collections.OrderedDict(), collections.OrderedDict()
    for e in plan2["leaves"]:
        if not e["killable"] or e["kind"] not in kinds:
            continue
        for r in e["carriers"]:
            used_pk[(r["carrier"], r["packet"])] = True
            used_pl[(r["carrier"], r["packet"], e["live"])] = r
    body, npk, nb = "", 0, 0
    for (form, p) in used_pk:
        rname = f"{form}QuarticChamberRest{p}810"
        if rname in have:
            continue
        cols = [f"{nm} {ld} A B C D E F G" for ld in LOADS
                for nm, _ in col_chunks(coords, form, ld)]
        rhs = f"{form}QuarticChamberRestLF{p}810 A B C D E F G"
        for c in cols:
            rhs += " +\n    " + c
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"def {rname}\n    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) : k[X] :=\n"
                 f"  {rhs}\n\n")
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem degreeZero{CC.FORM_CAP[form]}Quartic810_eq_face{p}_add_rest\n"
                 f"    ({LOADSIG8} : k)\n    (A B C D E F G : k[X]) :\n"
                 f"    {CC.FORM_LEAN[form]} {LOADSIG8} A B C D E F G =\n"
                 f"      {form}QuarticChamberFace{p}810 A B C D E F G +\n"
                 f"        {rname} {LOADSIG8} A B C D E F G := by\n"
                 f"  rw [{CC.FORM_LEAN[form]}_eq_chamberSplit,\n"
                 f"    {form}QuarticLoadFree810_eq_face{p}_add_rest]\n"
                 f"  simp only [{rname}]\n  ring\n\n")
        npk += 1
    for (form, p, S), rec in used_pl.items():
        rname = f"{form}QuarticChamberRest{p}810"
        if f"{rname}_natDegree_lt_of_live_{S}" in have:
            continue
        live = set(S)
        _face, rest = packet_face_records(coords, form, pk[(form, p)])
        surv_lf = surviving(rest, live)
        lfh, seen = [], {}
        for r in surv_lf:
            g = deg_expr(r.get("exps") or {})
            if g not in seen:
                seen[g] = f"hl{len(seen)}"
                lfh.append((seen[g], g))
        out = ["set_option maxHeartbeats 64000000 in",
               f"theorem {rname}_natDegree_lt_of_live_{S}",
               "    {d : ℕ}", f"    ({LOADSIG8} : k)",
               "    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
        for X in SIG:
            if X not in live:
                out.append(f"    (h{X}z : {X} = 0)")
        for h, g in lfh:
            out.append(f"    ({h} : {g} < d)")
        loadhyp = {}
        for ld in LOADS:
            recs = [r for c in col_chunks(coords, form, ld) for r in c[1]]
            surv = surviving(recs, live)
            if not surv:
                continue
            degs = []
            for r in surv:
                g = deg_expr(r.get("exps") or {})
                if g not in degs:
                    degs.append(g)
            loadhyp[ld] = degs
            out.append(f"    (hb{ld} : {ld} = 0 ∨ ("
                       + " ∧ ".join(f"{g} < d" for g in degs) + "))")
        out[-1] += " :"
        out.append(f"    ({rname} {LOADSIG8} A B C D E F G).natDegree < d := by")
        zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
        largs = " ".join(h for h, _ in lfh)
        out.append("  have hr0 :=")
        out.append(f"    {form}QuarticChamberRestLF{p}810_natDegree_lt_of_live_{S}")
        out.append(f"      A B C D E F G hdpos" + (f" {zargs}" if zargs else "")
                   + (f" {largs}" if largs else ""))
        pieces, ci = ["hr0"], 0
        for ld in LOADS:
            for nm, recs in col_chunks(coords, form, ld):
                surv = surviving(recs, live)
                hn = f"hc{ci}"
                ci += 1
                pieces.append(hn)
                out.append(f"  have {hn} : ({nm} {ld} A B C D E F G).natDegree < d := by")
                if not surv:
                    for X in SIG:
                        if X not in live:
                            out.append(f"    subst h{X}z")
                    for e2 in range(2, 9):
                        out.append(f"    have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                                   "zero_pow (by decide)")
                    out.append(f"    simp only [{nm}, {POWNAMES}, {ZERO_SIMP}]")
                    out.append("    omega")
                    continue
                degs = [deg_expr(r.get("exps") or {}) for r in surv]
                idx = [loadhyp[ld].index(g) for g in degs]
                nh = len(loadhyp[ld])
                pat = ("g0" if nh == 1 else
                       "⟨" + ", ".join(f"g{t}" for t in range(nh)) + "⟩")
                out.append(f"    rcases hb{ld} with rfl | {pat}")
                out.append(f"    · rw [{nm}_zero]")
                out.append("      simpa using hdpos")
                out.append(f"    · exact {nm}_natDegree_lt_of_live_{S} {ld} "
                           "A B C D E F G hdpos"
                           + (f" {zargs}" if zargs else "")
                           + (" " + " ".join(f"g{t}" for t in idx) if idx else ""))
        out.append(f"  simp only [{rname}]")
        acc = pieces[0]
        for h in pieces[1:]:
            acc = (f"natDegree_add_lt810 ({acc}) {h}" if " " in acc
                   else f"natDegree_add_lt810 {acc} {h}")
        out.append(f"  exact {acc}")
        out.append("")
        body += "\n".join(out) + "\n"
        nb += 1
    if npk == 0 and nb == 0:
        log(f"rests{tag}: nothing new - module skipped")
        return prev
    name = f"Grok810ScaleZeroQuarticChamberRests{tag}Scratch"
    doc = doc or ("# Chamber rests for the cost-ladder kills, `(8,10)` scale zero\n\n"
                  f"{npk} further packet rests with their split identities and {nb}\n"
                  "further rest bounds.  Untracked working note.")
    out = header(prev, doc) + f"section QuarticChamberRests{tag}810\n\n" + body
    out += f"\nend QuarticChamberRests{tag}810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{npk} further packet rests and {nb} rest bounds"))
    return name


def emit_kills2(data, coords, chambers, plan2, have, killed1, prev,
                tag="2", doc=None):
    cham = {(c.live, c.argmin): c for c in chambers}
    pk = {(p["carrier"], p["id"]): [tuple(x) for x in p["face"]]
          for p in plan2["packets"]}
    # A carrier-refined cell has several JSON leaves with *different*
    # certificates but the *same* chamber `Prop`, so no single leaf's kill is
    # valid on the whole cell: those go to the residual (item 3 of the plan).
    refined = {(c.live, c.argmin) for c in chambers if c.refined}
    leaves, seen = [], set()
    for e in plan2["leaves"]:
        key = (e["live"], tuple(e["argmin"]))
        if (not e["killable"] or e["kind"] != "single_monomial"
                or key in killed1 or key in refined or key in seen):
            continue
        seen.add(key)
        leaves.append(e)
    used = collections.OrderedDict()
    for e in leaves:
        used[(e["carriers"][0]["carrier"], e["carriers"][0]["packet"])] = True
    body = "/-! ## Face degrees -/\n\n"
    facedeg = {}
    for (form, p) in used:
        nm = f"{form}QuarticChamberFace{p}810_natDegree"
        face, _r = packet_face_records(coords, form, pk[(form, p)])
        exps = face[0].get("exps") or {}
        d = deg_expr(exps)
        chain, need, haspow = mono_ne(exps)
        facedeg[(form, p)] = (nm, need, d)
        if nm in have:
            continue
        rec = face[0]
        qn, qd = int(rec["qn"]), int(rec["qd"])
        coef = (f"({qn} / {qd} : k)" if qd != 1 else f"({qn} : k)")
        if qn < 0:
            coef = (f"(-({-qn} / {qd} : k))" if qd != 1 else f"(-({-qn} : k))")
        out = ["set_option maxHeartbeats 64000000 in", f"theorem {nm}",
               "    (A B C D E F G : k[X])"]
        for L in need:
            out.append(f"    (h{L}ne : {L} ≠ 0)")
        out[-1] += " :"
        out.append(f"    ({form}QuarticChamberFace{p}810 A B C D E F G).natDegree =")
        out.append(f"      {d} := by")
        out.append(f"  have hc : {coef} ≠ 0 := by norm_num")
        out.append(f"  simp only [{form}QuarticChamberFace{p}810]")
        out.append("  rw [natDegree_smul _ hc" + "".join(f", {c}" for c in chain) + "]")
        if haspow:
            out.append("  simp only [natDegree_pow]")
        out.append("  all_goals omega")
        out.append("")
        body += "\n".join(out) + "\n"

    body += "/-! ## The chamber kills unblocked by the cost ladder -/\n\n"
    nk = 0
    for e in leaves:
        c = cham[(e["live"], tuple(e["argmin"]))]
        r = e["carriers"][0]
        form, p, S = r["carrier"], r["packet"], e["live"]
        live = set(S)
        nm, need, d = facedeg[(form, p)]
        _face, rest = packet_face_records(coords, form, pk[(form, p)])
        surv_lf = surviving(rest, live)
        deg_hyp = CC.DEG_HYP[form]
        srcs = {v.get("source") for v in r["loads"].values() if v["status"] == "band"}
        need_nu = ("n2-cost" in srcs) or form == "nu"
        out = ["set_option maxHeartbeats 64000000 in",
               f"/-- Chamber `{S}` / `{'·'.join(e['argmin'])}` dies on the "
               f"`{CC.GREEK[form]}` face `{d}`, using the "
               + ", ".join(sorted(srcs) or ["dominated"]) + " band(s). -/",
               f"theorem quarticChamber{c.name}810_impossible",
               f"    ({LOADSIG8} : k)", "    (A B C D E F G : k[X])",
               f"    (hch : {c.defname} A B C D E F G)",
               "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
               "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))",
               f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}",
               "          A B C D E F G).natDegree = 0)"]
        if need_nu:
            out.append(f"    (hnu : (degreeZeroNuQuartic810 {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        if form not in ("kappa", "nu"):
            out.append(f"    ({deg_hyp} : ({CC.FORM_LEAN[form]} {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        out[-1] += " :"
        out.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        out.append(f"  obtain ⟨{', '.join(names)}⟩ := hch")
        out.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                out.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        if "A" in need:
            out += ["  have hAne : A ≠ 0 := by", "    intro h0",
                    "    have hz0 : A.natDegree = 0 := by simp [h0]",
                    "    clear * - hApos hz0; omega"]
        base = (chamber_cons_named(c.nums()) + CONE_CONS + dead_cons(live)
                + NONNEG_CONS)
        dvec = CC.lin(d)
        withd = base + [("hdpos", dvec, True)]
        out.append(f"  have hdpos : 0 < {d} := by")
        out.append("    by_contra hzero")
        knc = keep_str(base + [("hzero", tuple(-x for x in dvec), False)],
                       [g for X in SIG
                        for g in CC.target_of(f"{X}.natDegree = 0")])
        out.append("    exact hnc (by "
                   + (f"clear * - {knc}; " if knc else "") + "omega)")
        for src in sorted(srcs):
            casc, loads, needsnu = BANDCASC[src]
            vs = ", ".join(BANDVAR[src].format(x) for x in loads)
            out.append(f"  obtain ⟨{vs}⟩ :=")
            out.append(f"    {casc} {LOADSIG8}")
            out.append("      A B C D E F G hA" + (" hnu hkap" if needsnu else " hkap"))
        args = []
        for ld in LOADS:
            v = r["loads"][ld]
            if v["status"] == "empty":
                continue
            recs = [x for cnk in col_chunks(coords, form, ld) for x in cnk[1]]
            uniq = []
            for x in surviving(recs, live):
                g = deg_expr(x.get("exps") or {})
                if g not in uniq:
                    uniq.append(g)
            if v["status"] == "dominated":
                kd = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]
                                      for g in uniq])
                args.append("(Or.inr (by "
                            + (f"clear * - {kd}; " if kd else "") + "omega))")
                continue
            src = v["source"]
            hn = f"hz{ld}"
            args.append(hn)
            out += band_block(hn, ld, BANDVAR[src].format(ld),
                              band_disjuncts(src, ld), uniq, d,
                              base, withd, live)
        zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
        seenlf = []
        for x in surv_lf:
            g = deg_expr(x.get("exps") or {})
            if g not in seenlf:
                seenlf.append(g)
        lfa = []
        for g in seenlf:
            kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]])
            lfa.append("(by " + (f"clear * - {kg}; " if kg else "") + "omega)")
        lfargs = " ".join(lfa)
        rname = f"{form}QuarticChamberRest{p}810"
        out.append(f"  have hrest : ({rname} {LOADSIG8}")
        out.append(f"      A B C D E F G).natDegree < {d} :=")
        out.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
        out.append(f"      A B C D E F G hdpos" + (f" {zargs}" if zargs else "")
                   + (f" {lfargs}" if lfargs else "") + " " + " ".join(args))
        out.append(f"  have hlead : ({form}QuarticChamberFace{p}810 "
                   "A B C D E F G).natDegree =")
        out.append(f"      {d} :=")
        out.append(f"    {nm} A B C D E F G " + " ".join(f"h{L}ne" for L in need))
        out.append(f"  rw [degreeZero{CC.FORM_CAP[form]}Quartic810_eq_face{p}_add_rest,")
        out.append("    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]")
        # the rewrite must land on the hypothesis of the *same* carrier as the
        # face identity: `ν`'s identity does not occur in `hkap`
        tgt = ("hkap" if form == "kappa"
               else "hnu" if form == "nu" else deg_hyp)
        out.append(f"    at {tgt}")
        out.append(f"  clear * - hdpos {tgt}; omega")
        out.append("")
        body += "\n".join(out) + "\n"
        nk += 1
    name = f"Grok810ScaleZeroQuarticChamberKills{tag}Scratch"
    doc = doc or ("# Cost-ladder chamber kills, `(8,10)` scale zero\n\n"
                  f"{nk} further single-monomial chamber kills.  Untracked note.")
    ln, _names = write_split(name, f"QuarticChamberKills{tag}810", doc,
                             prune_arith(name_chamber_facts(body),
                                         SINGLE_KEEP), prev)
    MODULES.append((name, ln, f"{nk} further single-monomial chamber kills"))
    return name, {(e["live"], tuple(e["argmin"])) for e in leaves}


def kill_extra_args(entry, resid_hyp):
    """The degree hypotheses a chamber kill takes after `hkapDeg`.  A
    multi-carrier kill takes one per carrier, so the kill map may carry the
    whole ordered list; a single-carrier entry falls back to its own."""
    form, nu = entry[0], entry[1]
    extras = entry[2] if len(entry) > 2 else None
    out = " hnuDeg" if (nu or form == "nu") else ""
    if extras is None:
        if form not in ("kappa", "nu"):
            out += f" {resid_hyp[form]}"
    else:
        for h in extras:
            out += f" {h}"
    return out


def emit_residual_gen(chambers, kills, prev, tag, doc, note):
    """Re-dispatch the 1115-chamber exhaust through a given kill set."""
    resid_hyp = {"kappa": "hkapDeg", "mu": "hmuDeg", "xi": "hxiDeg",
                 "pi": "hpiDeg", "nu": "hnuDeg", "omicron": "homiDeg"}
    surv = [c for c in chambers if (c.live, c.argmin) not in kills]
    ind_name = f"QuarticChamberResidual{tag}810"
    body = f"/-! ## What the chamber kills leave ({tag}) -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += f"/-- The {len(surv)} cost-argmin chambers still open. -/\n"
    body += f"inductive {ind_name} (A B C D E F G : k[X]) : Prop\n"
    for c in surv:
        body += (f"  | r{c.name} : {c.defname} A B C D E F G →\n"
                 f"      {ind_name} A B C D E F G\n")
    body += "\n"
    lines = []
    for sz in range(1, 7):
        grp = [c for c in chambers if len(c.live) == sz]
        lines.append(f"      | size{sz} h =>")
        lines.append("        cases h with")
        for c in grp:
            key = (c.live, c.argmin)
            lines.append(f"        | {c.ctor} hc =>")
            if key in kills:
                extra = kill_extra_args(kills[key], resid_hyp)
                lines.append(f"          exact (quarticChamber{c.name}810_impossible")
                lines.append(f"            {LOADSIG8}")
                lines.append(f"            A B C D E F G hc hnc hkapDeg{extra}).elim")
            else:
                lines.append(f"          exact {ind_name}.r{c.name} hc")
    thm = f"normalized810ScaleZero_quarticChamber{tag}Residual"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += f"/-- {note} -/\n"
    body += f"""theorem {thm}
    {{P Q : MvPolynomial (Fin 2) k}} {{H : k[X]}}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧
              B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
              E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0) ∨
            {ind_name} A B C D E F G)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticLoadLadderResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · obtain ⟨hconeA, hexh, hlK, hbK, hdK, hzK, htK, hconst, hevenC, hevenE⟩ := hA
    refine Or.inl ⟨hconeA, ?_⟩
    by_cases hnc : B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
    · rcases hconst with ⟨hl0, hb0, hd0, hz0⟩ | hn
      · exact Or.inl ⟨hl0, hb0, hd0, hz0, hnc.1, hnc.2.1, hnc.2.2.1,
          hnc.2.2.2.1, hnc.2.2.2.2.1, hnc.2.2.2.2.2⟩
      · exact absurd hnc hn
    · refine Or.inr ?_
      have hsupp := quarticChamberSupport810_of (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G hconeA
        hjdiv hder
      cases hsupp with
"""
    body += "\n".join(lines) + "\n"
    body += "  · exact Or.inr hABCDEFG\n\n"
    body += f"#print axioms {thm}\n"
    name = f"Grok810ScaleZeroQuarticChamberResidual{tag}Scratch"
    out = (header(prev, doc) + f"section QuarticChamberResidual{tag}810\n\n"
           + "variable [IsAlgClosed k]\n\n" + body)
    out += f"\nend QuarticChamberResidual{tag}810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"`{ind_name}` ({len(surv)} chambers) and "
                              f"`{thm}`"))
    return name, surv


def emit_residual2(data, chambers, plan, plan2, prev):
    """Module 20: re-dispatch the 1115-chamber exhaust through both kill sets."""
    resid_hyp = {"kappa": "hkapDeg", "mu": "hmuDeg", "xi": "hxiDeg",
                 "pi": "hpiDeg", "nu": "hnuDeg", "omicron": "homiDeg"}
    kills = {}
    for e in plan["leaves"]:
        if e["killable"] and e["kind"] == "single_monomial":
            kills[(e["live"], tuple(e["argmin"]))] = (e["carriers"][0]["carrier"], False)
    refined2 = {(c.live, c.argmin) for c in chambers if c.refined}
    for e in plan2["leaves"]:
        key = (e["live"], tuple(e["argmin"]))
        if (key in kills or not e["killable"] or e["kind"] != "single_monomial"
                or key in refined2):
            continue
        r = e["carriers"][0]
        srcs = {v.get("source") for v in r["loads"].values() if v["status"] == "band"}
        kills[key] = (r["carrier"], "n2-cost" in srcs)
    surv = [c for c in chambers if (c.live, c.argmin) not in kills]
    body = "/-! ## What the cost-ladder chamber kills leave -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- The {len(surv)} cost-argmin chambers still open after the\n"
             "cost-form `κ`/`N₂` ladder. -/\n")
    body += "inductive QuarticChamberResidual2810 (A B C D E F G : k[X]) : Prop\n"
    for c in surv:
        body += (f"  | r{c.name} : {c.defname} A B C D E F G →\n"
                 f"      QuarticChamberResidual2810 A B C D E F G\n")
    body += "\n"
    lines = []
    for s in range(1, 7):
        grp = [c for c in chambers if len(c.live) == s]
        lines.append(f"      | size{s} h =>")
        lines.append("        cases h with")
        for c in grp:
            key = (c.live, c.argmin)
            lines.append(f"        | {c.ctor} hc =>")
            if key in kills:
                extra = kill_extra_args(kills[key], resid_hyp)
                lines.append(f"          exact (quarticChamber{c.name}810_impossible")
                lines.append(f"            {LOADSIG8}")
                lines.append(f"            A B C D E F G hc hnc hkapDeg{extra}).elim")
            else:
                lines.append(f"          exact QuarticChamberResidual2810.r{c.name} hc")
    body += "set_option maxHeartbeats 64000000 in\n"
    body += ("/-- Honest leftover after the cost-form ladder.\n\n"
             f"Closed relative to `normalized810ScaleZero_quarticLoadLadderResidual`:\n"
             f"the 1115-chamber exhaust and {len(kills)} single-monomial chamber kills\n"
             "(the 550 of `…ChamberKillsScratch` plus the ones the cost-form `κ`/`N₂`\n"
             "bands unblock).  Remaining: the all-constant corner and the\n"
             f"{len(surv)} chambers of `QuarticChamberResidual2810` — the\n"
             "`power_target` and `no_monomial_target` leaves (which need the\n"
             "`_coeff_top` extraction), the carrier-refined cells, corner `H`\n"
             "(`γ/ε/η`), and the open/rescue/weak-band families of\n"
             "`~/lean/tools/sigma810/OPEN_CHAMBERS.md`.\n"
             "No `sorry`, no new axioms, no finite-root shortcut. -/\n")
    body += """theorem normalized810ScaleZero_quarticChamber2Residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧
              B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
              E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0) ∨
            QuarticChamberResidual2810 A B C D E F G)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticLoadLadderResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · obtain ⟨hconeA, hexh, hlK, hbK, hdK, hzK, htK, hconst, hevenC, hevenE⟩ := hA
    refine Or.inl ⟨hconeA, ?_⟩
    by_cases hnc : B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
    · rcases hconst with ⟨hl0, hb0, hd0, hz0⟩ | hn
      · exact Or.inl ⟨hl0, hb0, hd0, hz0, hnc.1, hnc.2.1, hnc.2.2.1,
          hnc.2.2.2.1, hnc.2.2.2.2.1, hnc.2.2.2.2.2⟩
      · exact absurd hnc hn
    · refine Or.inr ?_
      have hsupp := quarticChamberSupport810_of (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G hconeA
        hjdiv hder
      cases hsupp with
"""
    body += "\n".join(lines) + "\n"
    body += "  · exact Or.inr hABCDEFG\n\n"
    body += "#print axioms normalized810ScaleZero_quarticChamber2Residual\n"
    name = "Grok810ScaleZeroQuarticChamberResidual2Scratch"
    doc = ("# Residual after the cost-form ladder, `(8,10)` scale zero\n\n"
           f"`QuarticChamberResidual2810` ({len(surv)} chambers) and\n"
           "`normalized810ScaleZero_quarticChamber2Residual`, which routes the\n"
           f"1115-chamber exhaust through all {len(kills)} single-monomial kills.\n"
           "Untracked working note.")
    out = (header(prev, doc) + "section QuarticChamberResidual2810\n\n"
           + "variable [IsAlgClosed k]\n\n" + body)
    out += "\nend QuarticChamberResidual2810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"`QuarticChamberResidual2810` ({len(surv)} chambers) "
                              "and the second residual export"))
    return name, surv, kills




# --------------------------- modules 21-24: `ν`, carrier change, corner `H`
def load_plan3():
    import json
    return json.loads((ROOT / "scripts" /
                       "out_810_quartic_chamber_killplan3.json").read_text())


def packet_map_module9(data, coords):
    """(carrier, face key set) -> packet id, exactly as `emit_faces` numbers."""
    packets = collections.OrderedDict()
    per_form = collections.Counter()
    for c in data["chambers"]:
        if not killable(c):
            continue
        for cr in c["certificate"]["carriers"]:
            if cr not in CARRIERS:
                continue
            key = (cr, parse_face(c["faces"][cr]))
            if key not in packets:
                packets[key] = per_form[cr]
                per_form[cr] += 1
    return packets


def plan3_leaves(data, coords, chambers, plan3):
    """Plan v3 -> the leaf shape `emit_columns2`/`emit_rests2`/`emit_kills2` eat,
    with packet ids reused from module 9 where the face packet already exists and
    allocated from 1000 upwards otherwise."""
    pm = packet_map_module9(data, coords)
    nxt = collections.Counter()
    faces = {}
    for (cr, fk), i in pm.items():
        faces[(cr, i)] = fk
    leaves = []
    for e in plan3["chambers"]:
        if not e["killable"]:
            continue
        opt = e["options"][0]
        cr = opt["carrier"]
        fk = None
        for p in plan3["packets"]:
            if p["carrier"] == cr and p["id"] == opt["packet"]:
                fk = frozenset(tuple(x) for x in p["face"])
                break
        pid = pm.get((cr, fk))
        if pid is None:
            key = (cr, fk)
            if key not in pm:
                pm[key] = 1000 + nxt[cr]
                nxt[cr] += 1
                faces[(cr, pm[key])] = fk
            pid = pm[key]
        rec = dict(opt)
        rec["packet"] = pid
        rec["face"] = []
        leaves.append({"live": e["live"], "argmin": e["argmin"],
                       "kind": "single_monomial", "killable": True,
                       "carriers": [rec], "blocked": []})
    packets = [{"carrier": cr, "id": i, "face": [list(x) for x in fk]}
               for (cr, i), fk in faces.items()]
    return {"packets": packets, "leaves": leaves}


def emit_extra_faces(data, coords, plan3full, have, prev):
    """Module 21: the `ν` load-free/column split, plus the face packets and
    load-free rest bounds the carrier-change kills need and that
    `…ChamberFacesScratch` does not have."""
    body = ""
    if "nuQuarticLoadFree810" not in have:
        form = "nu"
        lf0 = EC.sort_records(coords[form + "_lf"])
        body += "/-! ## `ν`: load-free part and the eight load columns -/\n\n"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- The load-free part of `degreeZeroNuQuartic810` "
                 f"({len(lf0)} monomials). -/\n")
        body += poly_def("nuQuarticLoadFree810", "", lf0)
        cols = {}
        for ld in LOADS:
            recs = EC.sort_records([r for r in coords[form]
                                    if (r.get("loads") or {}).get(ld)])
            chunks = split_chunks(recs)
            nms = []
            for i2, chunk in enumerate(chunks):
                nm = (f"nuQuarticColumn{CC.LOAD_CAP[ld]}810" if len(chunks) == 1
                      else f"nuQuarticColumn{CC.LOAD_CAP[ld]}{i2 + 1}810")
                nms.append(nm)
                body += "set_option maxHeartbeats 64000000 in\n"
                body += (f"/-- The `{ld}` column of `degreeZeroNuQuartic810`"
                         + (f", chunk {i2 + 1}/{len(chunks)}" if len(chunks) > 1 else "")
                         + f" ({len(chunk)} monomials). -/\n")
                body += poly_def(nm, ld, chunk)
                lem, _ = bound_lemma(nm, ld, chunk)
                body += lem
                body += (f"theorem {nm}_zero (A B C D E F G : k[X]) :\n"
                         f"    {nm} 0 A B C D E F G = 0 := by\n  simp [{nm}]\n\n")
            cols[ld] = nms
        simpset = ["degreeZeroNuQuartic810", "nuQuarticLoadFree810"] + \
            [n for ns in cols.values() for n in ns]
        rhs = "nuQuarticLoadFree810 A B C D E F G"
        for ld in LOADS:
            for nm in cols[ld]:
                rhs += f" +\n      {nm} {ld} A B C D E F G"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += ("/-- Cone-free split of `degreeZeroNuQuartic810` into its load-free\n"
                 "part and its eight load columns. -/\n")
        body += ("theorem degreeZeroNuQuartic810_eq_chamberSplit\n"
                 f"    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) :\n"
                 f"    degreeZeroNuQuartic810 {LOADSIG8}\n"
                 "        A B C D E F G =\n"
                 f"      {rhs} := by\n"
                 f"  simp only [{', '.join(simpset)}]\n  module\n\n")
    body += "/-! ## Face / rest splits the carrier change needs -/\n\n"
    pk = {(p["carrier"], p["id"]): [tuple(x) for x in p["face"]]
          for p in plan3full["packets"]}
    used = collections.OrderedDict()
    for e in plan3full["leaves"]:
        for r in e["carriers"]:
            used[(r["carrier"], r["packet"], e["live"])] = r
    npk = nb = 0
    seen_pk = set()
    for (cr, p, S) in used:
        if (cr, p) in seen_pk:
            continue
        seen_pk.add((cr, p))
        fname = f"{cr}QuarticChamberFace{p}810"
        if fname in have:
            continue
        lf = EC.sort_records(coords[cr + "_lf"])
        keys = set(map(tuple, pk[(cr, p)]))
        face = [x for x in lf if rec_key(x) in keys]
        rest = [x for x in lf if rec_key(x) not in keys]
        rname = f"{cr}QuarticChamberRestLF{p}810"
        d = deg_expr(face[0].get("exps") or {})
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Face of `{CC.GREEK[cr]}` on packet {p} "
                 f"({len(face)} monomial, top degree `{d}`). -/\n")
        body += poly_def(fname, "", face)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Load-free rest of `{CC.GREEK[cr]}` off packet {p} "
                 f"({len(rest)} monomials). -/\n")
        body += poly_def(rname, "", rest)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem {cr}QuarticLoadFree810_eq_face{p}_add_rest\n"
                 "    (A B C D E F G : k[X]) :\n"
                 f"    {cr}QuarticLoadFree810 A B C D E F G =\n"
                 f"      {fname} A B C D E F G + {rname} A B C D E F G := by\n"
                 f"  simp only [{cr}QuarticLoadFree810, {fname}, {rname}]\n"
                 "  all_goals module\n\n")
        npk += 1
    for (cr, p, S), r in used.items():
        rname = f"{cr}QuarticChamberRestLF{p}810"
        if f"{rname}_natDegree_lt_of_live_{S}" in have:
            continue
        live = set(S)
        lf = EC.sort_records(coords[cr + "_lf"])
        keys = set(map(tuple, pk[(cr, p)]))
        rest = [x for x in lf if rec_key(x) not in keys]
        surv, hyps, seen = [], [], {}
        for x in rest:
            ex = x.get("exps") or {}
            if any(int(ex.get(L, 0) or 0) > 0 and L != "A" and L not in live
                   for L in LET):
                continue
            g = deg_expr(ex)
            if g not in seen:
                seen[g] = f"hd{len(seen)}"
                hyps.append((seen[g], g))
            surv.append(x)
        out = ["set_option maxHeartbeats 64000000 in",
               f"theorem {rname}_natDegree_lt_of_live_{S}",
               "    {d : ℕ}", "    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
        for X in SIG:
            if X not in live:
                out.append(f"    (h{X}z : {X} = 0)")
        for h, g in hyps:
            out.append(f"    ({h} : {g} < d)")
        out[-1] += " :"
        out.append(f"    ({rname} A B C D E F G).natDegree < d := by")
        for X in SIG:
            if X not in live:
                out.append(f"  subst h{X}z")
        for e2 in range(2, 9):
            out.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                       "zero_pow (by decide)")
        if surv and refl_ok(rname):
            out += refl_degok_proof(rname)
        else:
            out.append(f"  simp only [{rname}, {POWNAMES}, {ZERO_SIMP}]")
            if surv:
                out.append("  compute_degree")
            out.append("  omega")
        out.append("")
        body += "\n".join(out) + "\n"
        nb += 1
    name = "Grok810ScaleZeroQuarticChamberNuFacesScratch"
    doc = ("# `ν` faces and the carrier-change face packets, `(8,10)` scale zero\n\n"
           "`…ChamberFacesScratch` emits the load-free/column split for `κ, μ, ξ, π`\n"
           "only.  The carrier-change kills need the same infrastructure for `ν`\n"
           "(the two `no_monomial_target` leaves whose saturating set is `{κ, ν}`,\n"
           f"and 4 more), plus {npk} further face packets and {nb} further load-free\n"
           "rest bounds for the carriers the change picks — `π` and `ξ` have `γ`/`ε`\n"
           "columns of letter count ≥ 2, which is what corner `H` needs.\n"
           "Untracked working note.")
    out = header(prev, doc) + "section QuarticChamberNuFaces810\n\n" + body
    out += "\nend QuarticChamberNuFaces810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"`ν` load-free/column split, {npk} further face "
                              f"packets and {nb} further rest bounds"))
    return name




# --------------------- modules 26-28: `_coeff_top` and the multi-carrier kills
LC = {L: f"{L}.leadingCoeff" for L in LET}


def load_plan4():
    import json
    return json.loads((ROOT / "scripts" /
                       "out_810_quartic_chamber_killplan4.json").read_text())


def scalar_lean(qn, qd):
    if qd == 1:
        return f"({qn} : k)" if qn >= 0 else f"(-({-qn}) : k)"
    return f"({qn} / {qd} : k)" if qn >= 0 else f"(-({-qn} / {qd}) : k)"


def mon_lower(exps, names):
    out = []
    for L in LET:
        e = int(exps.get(L, 0) or 0)
        if e == 1:
            out.append(names[L])
        elif e > 1:
            out.append(f"{names[L]} ^ {e}")
    return " * ".join(out) if out else "1"


def inner_body(recs, names):
    parts = []
    for r in recs:
        s = scalar_lean(int(r["qn"]), int(r["qd"]))
        m = mon_lower(r.get("exps") or {}, names)
        parts.append(f"{s} * {m}" if m != "1" else s)
    return " +\n    ".join(parts)


def poly_to_lean(expr, names):
    """A sympy polynomial in a..g -> a Lean scalar expression."""
    import sympy as sp
    expr = sp.expand(expr)
    terms = []
    syms = {s.name: s for s in sp.symbols("a b c d e f g")}
    for term in sp.Add.make_args(expr):
        c, rest = term.as_coeff_Mul()
        r = sp.Rational(c)
        s = scalar_lean(r.numerator, r.denominator)
        pieces = []
        d = rest.as_powers_dict() if rest != 1 else {}
        for L in LET:
            sym = syms[L.lower()]
            e = int(d.get(sym, 0))
            if e == 1:
                pieces.append(names[L])
            elif e > 1:
                pieces.append(f"{names[L]} ^ {e}")
        terms.append(" * ".join([s] + pieces) if pieces else s)
    return " +\n      ".join(terms) if terms else "(0 : k)"


def coeff_top_named(ne):
    """`(X := X)` for every polynomial binder the `≠ 0` hypotheses leave
    unconstrained: the bridge binds `A..G` implicitly and they occur only in
    its conclusion, so `have h := bridge …` cannot synthesise them."""
    return "".join(f" ({L} := {L})" for L in LET if L not in ne)


def coeff_top_lemma(form, p, face, d, name, inner_call, unfold=()):
    """`(face).coeff d = inner(leadingCoeffs)` — the 610 `_coeff_top` shape."""
    letters = sorted({L for r in face for L in LET
                      if int((r.get("exps") or {}).get(L, 0) or 0) > 0},
                     key=LET.index)
    out = ["set_option maxHeartbeats 64000000 in", f"theorem {name}",
           "    {A B C D E F G : k[X]}"]
    for L in letters:
        out.append(f"    (h{L}ne : {L} ≠ 0)")
    ties = []
    for i, r in enumerate(face[1:], start=1):
        ties.append((f"ht{i}", f"{deg_expr(r.get('exps') or {})} = {d}"))
    for h, s in ties:
        out.append(f"    ({h} : {s})")
    out[-1] += " :"
    out.append(f"    ({form}QuarticChamberFace{p}810 A B C D E F G).coeff")
    out.append(f"        ({d}) =")
    out.append(f"      {inner_call} := by")
    out.append(f"  simp only [{form}QuarticChamberFace{p}810, coeff_add, coeff_sub,")
    out.append("    coeff_smul, smul_eq_mul]")
    rw = []
    for i, r in enumerate(face):
        exps = r.get("exps") or {}
        chain, _need, haspow = mono_ne(exps)
        mon = EC.monomial_lean(exps)
        out.append(f"  have hd{i} : ({mon}).natDegree = {d} := by")
        if chain:
            out.append("    rw [" + ", ".join(chain) + "]")
        if haspow:
            out.append("    simp only [natDegree_pow]")
        # `simp only` can close the goal outright, and then `omega` errors
        out.append("    all_goals omega")
        lc = " * ".join(
            (LC[L] if int(exps.get(L, 0) or 0) == 1
             else f"{LC[L]} ^ {int(exps.get(L, 0) or 0)}")
            for L in LET if int(exps.get(L, 0) or 0) > 0)
        out.append(f"  have hc{i} : ({mon}).coeff ({d}) = {lc} := by")
        out.append(f"    rw [← hd{i}, coeff_natDegree]")
        # a `rw` can close the goal outright; guard every trailing tactic
        out.append("    all_goals simp only [leadingCoeff_mul, "
                   "leadingCoeff_pow]")
        rw.append(f"hc{i}")
    out.append("  rw [" + ", ".join(rw) + "]")
    if unfold:
        out.append("  all_goals simp only [" + ", ".join(unfold) + "]")
    out.append("  all_goals ring")
    out.append("")
    return "\n".join(out) + "\n"


def target_lean(target, var=None):
    """`c^5` / `(a*b*c*e*g)^1` -> the Lean product `c ^ 5` / `a * b * c * e * g`.

    `var` names the Lean term that plays the letter `X`; the default is the
    certificate's own scalar variable `x`."""
    import sympy as sp
    var = var or (lambda L: L.lower())
    syms = {x.name: x for x in sp.symbols("a b c d e f g")}
    d = sp.sympify(target.replace("^", "**"), locals=syms).as_powers_dict()
    out = []
    for L in LET:
        e = int(d.get(syms[L.lower()], 0))
        if e == 1:
            out.append(var(L))
        elif e > 1:
            out.append(f"{var(L)} ^ {e}")
    return " * ".join(out)


def elim_target(target, names, hz):
    """Tactic block deriving `False` from `<target> = 0` and the `≠ 0` letters."""
    import sympy as sp
    syms = {s.name: s for s in sp.symbols("a b c d e f g")}
    d = sp.sympify(target.replace("^", "**"), locals=syms).as_powers_dict()
    fac = []
    for L in LET:
        e = int(d.get(syms[L.lower()], 0))
        if e:
            fac.append((L, e))
    out = []

    def rec(i, h, ind):
        L, e = fac[i]
        if i == len(fac) - 1:
            if e == 1:
                out.append(f"{ind}exact h{L}c {h}")
            else:
                out.append(f"{ind}exact h{L}c ((pow_eq_zero_iff "
                           f"(by decide : ({e} : ℕ) ≠ 0)).mp {h})")
            return
        out.append(f"{ind}rcases (mul_eq_zero.mp {h}) with h' | h'")
        out.append(f"{ind}· " + ("exact h" + fac[i][0] + "c h'" if False else ""))
        out.pop()
        out.append(f"{ind}· " + ("")); out.pop()
        out.append(f"{ind}· -- the first factor")
        rec2(i, "h'", ind + "  ")
        out.append(f"{ind}· -- the rest")
        rec(i + 1, "h'", ind + "  ")

    def rec2(i, h, ind):
        L, e = fac[i]
        if e == 1:
            out.append(f"{ind}exact h{L}c {h}")
        else:
            out.append(f"{ind}exact h{L}c ((pow_eq_zero_iff "
                       f"(by decide : ({e} : ℕ) ≠ 0)).mp {h})")

    if len(fac) == 1:
        rec(0, hz, "  ")
    else:
        # the product is left-associated: (((x1 * x2) * x3) * x4)
        def peel(i, h, ind):
            if i == 0:
                rec2(0, h, ind)
                return
            out.append(f"{ind}rcases (mul_eq_zero.mp {h}) with h{i} | h{i}")
            out.append(f"{ind}· -- the left factor")
            peel(i - 1, f"h{i}", ind + "  ")
            out.append(f"{ind}· -- the right factor")
            rec2(i, f"h{i}", ind + "  ")
        peel(len(fac) - 1, hz, "  ")
    return "\n".join(out), [L for L, _e in fac]


def plan4_leaves(data, coords, plan4):
    """Plan v4 -> the leaf shape, with module-9 packet ids."""
    pm = packet_map_module9(data, coords)
    faces = {}
    for (cr, fk), i in pm.items():
        faces[(cr, i)] = fk
    nxt = collections.Counter()
    leaves = []
    for e in plan4["chambers"]:
        recs = []
        for r in e["carriers"]:
            fk = frozenset(tuple(x) for x in r["face"])
            key = (r["carrier"], fk)
            if key not in pm:
                pm[key] = 2000 + nxt[r["carrier"]]
                nxt[r["carrier"]] += 1
                faces[(r["carrier"], pm[key])] = fk
            rr = dict(r)
            rr["packet"] = pm[key]
            recs.append(rr)
        leaves.append({"live": e["live"], "argmin": e["argmin"],
                       "kind": "multi", "killable": True,
                       "carriers": recs, "blocked": [],
                       "target": e["target"], "cofactors": e["cofactors"],
                       "certkind": e["kind"], "name": e["name"]})
    packets = [{"carrier": cr, "id": i, "face": [list(x) for x in fk]}
               for (cr, i), fk in faces.items()]
    return {"packets": packets, "leaves": leaves}


def notarget_inner_map(coords):
    """(carrier, frozenset of face keys) -> the certificates module's inner name
    and its argument letters, matched coefficient-for-coefficient."""
    import re as _re
    p = ROOT / "Grok810ScaleZeroQuarticChamberCertificatesScratch.lean"
    if not p.exists():
        return {}, {}
    txt = p.read_text()
    out, sysof = {}, {}
    for m in _re.finditer(r"def (\w+)QuarticNoTargetInner(\w+)810 \(([a-g ]+) : k\) : k :=\n"
                          r"((?:  .*\n)+)", txt):
        form, sysname, args, body = m.group(1), m.group(2), m.group(3), m.group(4)
        keys = set()
        for term in _re.finditer(r"\(?(-?\d+)\s*/\s*(\d+)\s*:\s*k\)?", body):
            pass
        # parse `(<q> : k) * a * b ^ 2 + …`
        for term in body.replace("\n", " ").split(" + "):
            t = term.strip()
            mm = _re.match(r"\((-?\d+)\s*/\s*(\d+)\s*:\s*k\)((?:\s*\*\s*[a-g](?:\s*\^\s*\d+)?)*)", t)
            if not mm:
                continue
            exps = [0] * 7
            for f in _re.finditer(r"([a-g])(?:\s*\^\s*(\d+))?", mm.group(3)):
                exps[LET.index(f.group(1).upper())] += int(f.group(2) or 1)
            keys.add(tuple(exps))
        out[(form, frozenset(keys))] = (
            f"{form}QuarticNoTargetInner{sysname}810", args.split())
        sysof[sysname] = f"quarticNoTargetInner_{sysname}_zero_impossible"
    return out, sysof


def emit_inner(data, coords, plan4full, have, prev):
    """Module: inner scalars, ideal identities and `_coeff_top` extractions."""
    import sympy as sp
    ntmap, ntsys = notarget_inner_map(coords)
    pk = {(p["carrier"], p["id"]): frozenset(tuple(x) for x in p["face"])
          for p in plan4full["packets"]}
    body = "/-! ## Inner scalars and the ideal identities -/\n\n"
    innername = {}
    emitted = set()
    # 1. inner defs for the `power_target` packets.  A packet shared by a
    # `no_monomial_target` leaf and a `power_target` one must take the tracked
    # `NoTargetInner` name, or the no-target `False` lemma will not accept the
    # bridge: decide those first.
    _lv = ([e for e in plan4full["leaves"]
            if e["certkind"] == "no_monomial_target"]
           + [e for e in plan4full["leaves"]
              if e["certkind"] != "no_monomial_target"])
    for e in _lv:
        for r in e["carriers"]:
            cr, p = r["carrier"], r["packet"]
            fk = pk[(cr, p)]
            if (cr, p) in emitted:
                continue
            emitted.add((cr, p))
            lf = EC.sort_records(coords[cr + "_lf"])
            face = [x for x in lf if rec_key(x) in fk]
            names = {L: L.lower() for L in LET}
            if e["certkind"] == "no_monomial_target" and (cr, fk) in ntmap:
                nm, args = ntmap[(cr, fk)]
                innername[(cr, p)] = (nm, args, face)
                continue
            nm = f"{cr}QuarticChamberInner{p}810"
            innername[(cr, p)] = (nm, [L.lower() for L in LET], face)
            if nm in have:
                continue
            body += (f"/-- The face of `{CC.GREEK[cr]}` on packet {p}, at the "
                     "leading coefficients. -/\n")
            body += (f"def {nm} (a b c d e f g : k) : k :=\n  "
                     + inner_body(face, names) + "\n\n")
    # 2. the identities and the `False` lemmas, one per system
    systems = collections.OrderedDict()
    for e in plan4full["leaves"]:
        key = (e["certkind"], e["target"],
               tuple((r["carrier"], r["packet"]) for r in e["carriers"]))
        systems.setdefault(key, e)
    sysname = {}
    for si, (key, e) in enumerate(systems.items()):
        kind, target, crs = key
        if kind == "no_monomial_target":
            nm = None
            for cr, p in crs:
                inm, _a, _f = innername[(cr, p)]
                mm = inm.split("QuarticNoTargetInner")
                if len(mm) == 2:
                    nm = ntsys.get(mm[1][:-3])
            sysname[key] = (nm, None)
            continue
        terms = []
        for cr, p in crs:
            inm, args, _f = innername[(cr, p)]
            cof = sp.sympify(e["cofactors"][cr].replace("^", "**"))
            terms.append((poly_to_lean(cof, {L: L.lower() for L in LET}),
                          f"{inm} " + " ".join(args)))
        idn = f"quarticChamberInnerSystem{si}810_identity"
        zn = f"quarticChamberInnerSystem{si}810_zero_impossible"
        sysname[key] = (zn, [c for c, _p in crs])
        tgt = target_lean(target)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Isobaric membership `{target} ∈ ⟨faces⟩` for the packet "
                 f"system {si}. -/\n")
        body += (f"theorem {idn} (a b c d e f g : k) :\n    "
                 + " +\n      ".join(f"({c}) *\n        ({p})" for c, p in terms)
                 + f" =\n      {tgt} := by\n")
        body += ("  simp only ["
                 + ", ".join(dict.fromkeys(innername[(cr, p)][0] for cr, p in crs))
                 + "]\n  ring\n\n")
        elim, need = elim_target(target, None, "hz")
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem {zn} (a b c d e f g : k)\n")
        for i, (cr, p) in enumerate(crs):
            inm, args, _f = innername[(cr, p)]
            body += f"    (hf{i} : {inm} " + " ".join(args) + " = 0)\n"
        for L in need:
            body += f"    (h{L}c : {L.lower()} ≠ 0)\n"
        body = body[:-1] + " :\n    False := by\n"
        body += f"  have hid := {idn} a b c d e f g\n"
        body += f"  have hz : {tgt} = 0 := by\n"
        body += ("    rw [" + ", ".join(f"hf{i}" for i in range(len(crs)))
                 + "] at hid\n")
        body += "    simpa using hid.symm\n"
        body += elim + "\n\n"
    # 3. the `_coeff_top` lemmas
    body += "/-! ## Top-coefficient extraction -/\n\n"
    ctname = {}
    for (cr, p), (inm, args, face) in innername.items():
        d = deg_expr(face[0].get("exps") or {})
        nm = f"{cr}QuarticChamberFace{p}810_coeff_top"
        ctname[(cr, p)] = (nm, d, face)
        if nm in have:
            continue
        call = f"{inm} " + " ".join(LC[a.upper()] for a in args)
        body += coeff_top_lemma(cr, p, face, d, nm, call,
                                unfold=(inm,))
    name = "Grok810ScaleZeroQuarticChamberInnerScratch"
    doc = ("# Inner scalars, ideal identities and top-coefficient extraction\n\n"
           f"{len(systems)} certificate systems over "
           f"{len(innername)} (carrier, packet) faces: the face evaluated at the\n"
           "leading coefficients, the isobaric membership identity with the\n"
           "cofactors of `scripts/out_810_scale_zero_quartic_chambers.json`\n"
           "(re-verified by `sympy` in\n"
           "`scripts/derive_810_quartic_chamber_killplan4.py`), the `False` lemma,\n"
           "and the `_coeff_top` bridge `(face).coeff d = inner(A.leadingCoeff, …)`.\n"
           "The `no_monomial_target` systems reuse the green scalar identities of\n"
           "`Grok810ScaleZeroQuarticChamberCertificatesScratch`.\n"
           "Untracked working note.")
    out = (header([prev,
                   "Grok810ScaleZeroQuarticChamberCertificatesScratch"], doc)
           + "section QuarticChamberInner810\n\n" + body)
    out += "\nend QuarticChamberInner810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{len(systems)} certificate systems and "
                              f"{len(ctname)} `_coeff_top` lemmas"))
    return name, innername, sysname, ctname, systems


def emit_kills4(data, coords, chambers, plan4full, innername, sysname, ctname,
                have, prev):
    cham = {(c.live, c.argmin): c for c in chambers}
    pk = {(p["carrier"], p["id"]): frozenset(tuple(x) for x in p["face"])
          for p in plan4full["packets"]}
    body = "/-! ## Multi-carrier chamber kills -/\n\n"
    nk = 0
    for e in plan4full["leaves"]:
        c = cham[(e["live"], tuple(e["argmin"]))]
        S = e["live"]
        live = set(S)
        key = (e["certkind"], e["target"],
               tuple((r["carrier"], r["packet"]) for r in e["carriers"]))
        zn, _crs = sysname[key]
        if zn is None:
            continue
        srcs = set()
        for r in e["carriers"]:
            srcs |= {v.get("source") for v in r["loads"].values()
                     if v["status"] == "band"}
        forms = [r["carrier"] for r in e["carriers"]]
        need_nu = ("n2-cost" in srcs) or ("nu" in forms)
        out = ["set_option maxHeartbeats 64000000 in",
               f"/-- Chamber `{S}` / `{'·'.join(e['argmin'])}`: the faces of "
               + ", ".join(CC.GREEK[f] for f in forms)
               + " vanish, and the isobaric certificate then kills it. -/",
               f"theorem quarticChamber{c.name}810_impossible",
               f"    ({LOADSIG8} : k)", "    (A B C D E F G : k[X])",
               f"    (hch : {c.defname} A B C D E F G)",
               "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
               "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))",
               f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}",
               "          A B C D E F G).natDegree = 0)"]
        if need_nu:
            out.append(f"    (hnu : (degreeZeroNuQuartic810 {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        for f in forms:
            if f in ("kappa", "nu"):
                continue
            out.append(f"    ({CC.DEG_HYP[f]} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        out[-1] += " :"
        out.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        out.append(f"  obtain ⟨{', '.join(names)}⟩ := hch")
        out.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                out.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        out += ["  have hAne : A ≠ 0 := by", "    intro h0",
                "    have hz0 : A.natDegree = 0 := by simp [h0]",
                "    clear * - hApos hz0; omega"]
        base = (chamber_cons_named(c.nums()) + CONE_CONS + dead_cons(live)
                + NONNEG_CONS)
        for src in sorted(srcs):
            casc, loads, needsnu = BANDCASC[src]
            vs = ", ".join(BANDVAR[src].format(x) for x in loads)
            out.append(f"  obtain ⟨{vs}⟩ :=")
            out.append(f"    {casc} {LOADSIG8}")
            out.append("      A B C D E F G hA" + (" hnu hkap" if needsnu else " hkap"))
        innerhyp = []
        for ci, r in enumerate(e["carriers"]):
            form, p = r["carrier"], r["packet"]
            d = r["d"]
            inm, args, face = innername[(form, p)]
            ctn = ctname[(form, p)][0]
            lf = EC.sort_records(coords[form + "_lf"])
            rest = [x for x in lf if rec_key(x) not in pk[(form, p)]]
            surv_lf = surviving(rest, live)
            dvec = CC.lin(d)
            withd = base + [(f"hdp{ci}", dvec, True)]
            out.append(f"  have hdp{ci} : 0 < {d} := by")
            out.append("    by_contra hzero")
            knc = keep_str(base + [("hzero", tuple(-x for x in dvec), False)],
                           [g for X in SIG
                            for g in CC.target_of(f"{X}.natDegree = 0")])
            out.append("    exact hnc (by "
                       + (f"clear * - {knc}; " if knc else "") + "omega)")
            args_r = []
            for ld in LOADS:
                v = r["loads"][ld]
                if v["status"] == "empty":
                    continue
                recs = [x for cnk in col_chunks(coords, form, ld) for x in cnk[1]]
                uniq = []
                for x in surviving(recs, live):
                    g = deg_expr(x.get("exps") or {})
                    if g not in uniq:
                        uniq.append(g)
                if v["status"] == "dominated":
                    kd = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]
                                          for g in uniq])
                    args_r.append("(Or.inr (by "
                                  + (f"clear * - {kd}; " if kd else "")
                                  + "omega))")
                    continue
                hn = f"hz{ci}{ld}"
                args_r.append(hn)
                out += band_block(hn, ld, BANDVAR[v["source"]].format(ld),
                                  band_disjuncts(v["source"], ld), uniq, d,
                                  base, withd, live)
            zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
            seenlf = []
            for x in surv_lf:
                g = deg_expr(x.get("exps") or {})
                if g not in seenlf:
                    seenlf.append(g)
            lfa = []
            for g in seenlf:
                kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]])
                lfa.append("(by " + (f"clear * - {kg}; " if kg else "")
                           + "omega)")
            lfargs = " ".join(lfa)
            rname = f"{form}QuarticChamberRest{p}810"
            out.append(f"  have hr{ci} : ({rname} {LOADSIG8}")
            out.append(f"      A B C D E F G).natDegree < {d} :=")
            out.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
            out.append(f"      A B C D E F G hdp{ci}" + (f" {zargs}" if zargs else "")
                       + (f" {lfargs}" if lfargs else "") + " " + " ".join(args_r))
            ne = sorted({L for x in face for L in LET
                         if int((x.get("exps") or {}).get(L, 0) or 0) > 0},
                        key=LET.index)
            tie = " ".join("(by omega)" for _ in face[1:])
            out.append(f"  have hct{ci} := {ctn} "
                       + " ".join(f"h{L}ne" for L in ne)
                       + coeff_top_named(ne) + (f" {tie}" if tie else ""))
            dh = CC.DEG_HYP[form] if form not in ("kappa", "nu") else \
                ("hkap" if form == "kappa" else "hnu")
            out.append(f"  have hq{ci} : ({CC.FORM_LEAN[form]} {LOADSIG8}")
            out.append(f"      A B C D E F G).coeff ({d}) = 0 := by")
            out.append("    apply coeff_eq_zero_of_natDegree_lt")
            out.append(f"    rw [{dh}]")
            out.append("    omega")
            out.append(f"  rw [degreeZero{CC.FORM_CAP[form]}Quartic810_eq_face{p}_add_rest,")
            out.append(f"    coeff_add, coeff_eq_zero_of_natDegree_lt hr{ci},")
            out.append(f"    add_zero] at hq{ci}")
            out.append(f"  have hin{ci} : {inm} "
                       + " ".join(LC[a.upper()] for a in args) + " = 0 :=")
            out.append(f"    hct{ci}.symm.trans hq{ci}")
            innerhyp.append(f"hin{ci}")
        _elim, need = elim_target(e["target"], None, "hz") if e["target"] else ("", [])
        if not e["target"]:
            need = sorted({L for r in e["carriers"]
                           for a in innername[(r["carrier"], r["packet"])][1]
                           for L in [a.upper()]}, key=LET.index)
        # the tracked `no_target` lemmas take only their own letters, both as
        # scalars and as `≠ 0` hypotheses; my own system lemmas take all seven
        mnt = re.fullmatch(r"quarticNoTargetInner_([A-G]+)_zero_impossible", zn)
        lets = list(mnt.group(1)) if mnt else LET
        if mnt:
            need = list(mnt.group(1))
        for L in need:
            src = f"h{L}ne" if L != "A" else "hAne"
            out.append(f"  have h{L}c : {L}.leadingCoeff ≠ 0 := "
                       f"leadingCoeff_ne_zero.mpr {src}")
        out.append(f"  exact {zn} " + " ".join(LC[L] for L in lets) + " "
                   + " ".join(innerhyp) + " " + " ".join(f"h{L}c" for L in need))
        out.append("")
        body += "\n".join(out) + "\n"
        nk += 1
    name = "Grok810ScaleZeroQuarticChamberKills4Scratch"
    doc = ("# Multi-carrier chamber kills, `(8,10)` scale zero\n\n"
           f"{nk} chambers whose certificate needs several faces: each face's top\n"
           "coefficient is extracted with `…ChamberInnerScratch`'s `_coeff_top`\n"
           "bridge, and the isobaric identity then contradicts a product of\n"
           "non-zero leading coefficients.  Untracked working note.")
    split_decls(name, "QuarticChamberKills4810", doc,
                decl_blocks(prune_arith(name_chamber_facts(body), SINGLE_KEEP)),
                prev)
    MODULES.append((name, body.count("\n"),
                    f"{nk} multi-carrier chamber kills"))
    return name, {(e["live"], tuple(e["argmin"])) for e in plan4full["leaves"]
                  if sysname[(e["certkind"], e["target"],
                              tuple((r["carrier"], r["packet"])
                                    for r in e["carriers"]))][0] is not None}




# ------------------ module 30: the per-carrier tournament on refined cells
def _leaf_conjuncts(lf):
    out = []
    for cr, lst in sorted(lf["refinement_conjuncts"].items()):
        for q in lst:
            q = CC.strip(q)
            if q not in out:
                out.append(q)
    return out


def _cmp_of(q):
    m = re.match(r"^(.*?) (<|=) (.*)$", q)
    return CC.lin(m.group(1)), m.group(2), CC.lin(m.group(3))


def _decided(cons, q):
    L, op, R = _cmp_of(q)
    if op == "<":
        return CC.derive(cons, CC.sub7(R, L), True) is not None
    return (CC.derive(cons, CC.sub7(L, R), False) is not None
            and CC.derive(cons, CC.sub7(R, L), False) is not None)


def _refuted(cons, q):
    L, op, R = _cmp_of(q)
    if op == "<":
        return not CC.feasible(cons + [CC.gt(R, L)])
    return not CC.feasible(cons + [CC.ge(L, R), CC.ge(R, L)])


def refine_tree(cell_cons, leaves, cands, depth=0, cap=14):
    cands = [i for i in cands if CC.feasible(cell_cons + sum(
        (CC.constraints_of(q) for q in _leaf_conjuncts(leaves[i])), []))]
    if not cands:
        return ("dead",)
    for i in cands:
        if all(_decided(cell_cons, q) for q in _leaf_conjuncts(leaves[i])):
            return ("leaf", i)
    if depth >= cap:
        return ("giveup", cands)
    pick = None
    for i in cands:
        for q in _leaf_conjuncts(leaves[i]):
            if _decided(cell_cons, q) or _refuted(cell_cons, q):
                continue
            pick = _cmp_of(q)[0], _cmp_of(q)[2]
            break
        if pick:
            break
    if pick is None:
        return ("giveup", cands)
    L, R = pick
    kids = [refine_tree(cell_cons + ex, leaves, cands, depth + 1, cap)
            for ex in ([CC.gt(R, L)], [CC.ge(R, L), CC.ge(L, R)], [CC.gt(L, R)])]
    return ("node", L, R, kids)


def emit_refine(data, chambers, prev):
    refined = [c for c in chambers if c.refined]
    body = ""
    inj = {}
    for c in refined:
        n = len(c.leaves)
        for i, lf in enumerate(c.leaves):
            nm = f"QuarticRefined{c.name}L{i}810"
            inj[(c.name, i)] = nm
            body += "set_option maxHeartbeats 64000000 in\n"
            body += (f"/-- Carrier-refined leaf {i} of chamber `{c.live}` / "
                     f"`{'·'.join(c.argmin)}` (JSON `{lf['id']}`, certificate "
                     f"`{lf['certificate']['kind']}`, carriers "
                     f"{', '.join(lf['certificate'].get('carriers', []))}). -/\n")
            fields = [c.defname + " A B C D E F G"] + _leaf_conjuncts(lf)
            body += (f"def {nm} (A B C D E F G : k[X]) : Prop :=\n  "
                     + " ∧\n    ".join(fields) + "\n\n")
    ndead = ngive = nleaf = 0
    for c in refined:
        cons = CC.chamber_cons(c.conjuncts)
        t = refine_tree(cons, c.leaves, list(range(len(c.leaves))))
        n = len(c.leaves)

        def orinj(i):
            if i == n - 1:
                return "Or.inr (" * i + "?_" + ")" * i
            return "Or.inr (" * i + "Or.inl ?_" + ")" * i

        def render(t, ind, depth):
            nonlocal ndead, ngive, nleaf
            if t[0] == "dead":
                ndead += 1
                return [f"{ind}exact (by omega : False).elim"]
            if t[0] == "giveup":
                ngive += 1
                return [f"{ind}exact (by omega : False).elim  -- UNRESOLVED"]
            if t[0] == "leaf":
                nleaf += 1
                i = t[1]
                pre = "Or.inr (" * i + ("Or.inl " if i < n - 1 else "")
                post = ")" * i
                lf = c.leaves[i]
                parts = ["hch"] + ["by omega" for _ in _leaf_conjuncts(lf)]
                return [f"{ind}exact {pre}⟨{', '.join(parts)}⟩{post}"]
            L, R = CC.sides7(CC.sub7(t[1], t[2]))
            h = f"hr{depth}"
            out = [f"{ind}rcases lt_trichotomy ({L}) ({R}) with {h}a | {h}b | {h}c"]
            for tag, kid in zip(("<", "=", ">"), t[3]):
                sub = render(kid, ind + "  ", depth + 1)
                if len(sub) == 1:
                    out.append(f"{ind}· {sub[0].strip()}")
                else:
                    out.append(f"{ind}· -- {L} {tag} {R}")
                    out += sub
            return out
        disj = " ∨\n      ".join(f"{inj[(c.name, i)]} A B C D E F G" for i in range(n))
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- The {n} carrier-refined leaves cover chamber "
                 f"`{c.live}` / `{'·'.join(c.argmin)}`. -/\n"
                 f"theorem quarticChamber{c.name}810_refine\n"
                 "    (A B C D E F G : k[X])\n"
                 f"    (hch : {c.defname} A B C D E F G) :\n"
                 f"    {disj} := by\n")
        names = ["hA"] + [f"h{X}ne" if X in c.live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        body += f"  obtain ⟨{', '.join(names)}⟩ := id hch\n"
        body += "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA\n"
        for X in SIG:
            if X not in c.live:
                body += f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]\n"
        body += "\n".join(render(t, "  ", 0)) + "\n\n"
    name = "Grok810ScaleZeroQuarticChamberRefineScratch"
    doc = (
        "# The per-carrier tournament on the 11 refined cells, `(8,10)` scale zero\n\n"
        f"{sum(len(c.leaves) for c in refined)} refined leaves over {len(refined)}\n"
        "chambers whose leaves share one chamber `Prop` but carry *different*\n"
        "certificates (the level-0 refinement reached a carrier's own argmin at\n"
        "different cells).  Each `quarticChamber<name>810_refine` is a decision\n"
        "tree on the leaves' own refinement conjuncts: at every node one\n"
        "`lt_trichotomy`, at every leaf exactly one refined `Prop` whose conjuncts\n"
        "the branch implies (exact rational Farkas certificates in\n"
        "`scripts/check_810_quartic_chambers_lean.py`).  The refined leaves'\n"
        "*kills* are not here — they wait on the power-certificate and tower\n"
        "lanes; the manifest lists which certificate each leaf needs.\n"
        "Untracked working note."
    )
    out = header(prev, doc) + "section QuarticChamberRefine810\n\n" + body
    out += "\nend QuarticChamberRefine810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{sum(len(c.leaves) for c in refined)} refined-leaf "
                              f"`Prop`s and {len(refined)} tournaments"))
    log(f"refine trees: {nleaf} live leaves, {ndead} dead, {ngive} unresolved")
    return name, refined, inj


# ------------------------------------ modules 31-32: the final assembly
EXTERNALS = []


HC_OLD = """
      ∀ (j t gamma epsilon eta theta : k) (A B C D E F G : k[X]),
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
              A B C D E F G) =
          Polynomial.C (j / t) →
        QuarticRatioConeA810 A B C D E F G →
        B.natDegree = 0 → C.natDegree = 0 → D.natDegree = 0 →
        E.natDegree = 0 → F.natDegree = 0 → G.natDegree = 0 →
        False"""

HC_NEW = """
      ∀ {j t : k} (gamma epsilon eta theta : k) (A B C D E F G : k[X]),
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
              A B C D E F G) =
          Polynomial.C (j / t) →
        (degreeZeroXiQuartic810 0 0 gamma 0 epsilon 0 eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroMuQuartic810 0 0 gamma 0 epsilon 0 eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroOmicronQuartic810 0 0 gamma 0 epsilon 0 eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroKappaQuartic810 0 0 gamma 0 epsilon 0 eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroNuQuartic810 0 0 gamma 0 epsilon 0 eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroPiQuartic810 0 0 gamma 0 epsilon 0 eta theta
            A B C D E F G).natDegree = 0 →
        QuarticRatioConeA810 A B C D E F G →
        B.natDegree = 0 → C.natDegree = 0 → D.natDegree = 0 →
        E.natDegree = 0 → F.natDegree = 0 → G.natDegree = 0 →
        False"""

CUSE_OLD = """exact hcorner j t gamma epsilon eta theta A B C D E F G hjdiv hder
        hconeA hBn hCn hDn hEn hFn hGn"""

CUSE_NEW = """exact hcorner gamma epsilon eta theta A B C D E F G hjdiv hder
        hxiDeg hmuDeg homiDeg hkapDeg hnuDeg hpiDeg
        hconeA hBn hCn hDn hEn hFn hGn"""

HAB_OLD = """
      ∀ (j t l beta gamma delta epsilon zeta eta theta : k)
        (A B C D E F G : k[X]),
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
              eta theta A B C D E F G) =
          Polynomial.C (j / t) →
        (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        QuarticRatioConeABCDEFG810 A B C D E F G →
        False"""

HAB_NEW = """
      ∀ {j t : k} (l beta gamma delta epsilon zeta eta theta : k)
        (A B C D E F G : k[X]),
        QuarticRatioConeABCDEFG810 A B C D E F G →
        (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
            theta A B C D E F G).natDegree = 0 →
        (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
            theta A B C D E F G).natDegree = 0 →
        (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
              eta theta A B C D E F G) =
          Polynomial.C (j / t) →
        False"""

USE_OLD = """exact habcdefg j t l beta gamma delta epsilon zeta eta theta
      A B C D E F G hjdiv hder hkapDeg habc"""

USE_NEW = """exact habcdefg l beta gamma delta epsilon zeta eta theta
      A B C D E F G habc hxiDeg hmuDeg homiDeg hkapDeg hnuDeg hpiDeg
      hjdiv hder"""


def emit_assembly(chambers, surv4, prev, tag="4", names=None):
    """Module 31: the assembly core, complete modulo three named obligations;
    module 32: the tracked-name glue that discharges them."""
    body = ""
    body += ("/-! ## The three obligations the chamber ladder does not discharge\n\n"
             "Everything else on cone `A` is closed by modules 1-30.  These are\n"
             "exactly the inputs the parallel lanes owe. -/\n\n")
    body += """set_option maxHeartbeats 64000000 in
/-- Assembly core: `Normalized810LeadingCoreSource P Q H 0` is impossible once

* `hresid` kills every chamber of `QuarticChamberResidual4810` (the tower lane's
  2 open / 19 deep-rescue / 405-wall families and the power-certificate lane's
  `power_target` systems);
* `hcorner` kills the all-constant corner `l = β = δ = ζ = 0` with every letter
  constant (File A's `quarticADominant_constantLetters_impossible_of_*` handle
  the four cases where one of those loads is non-zero; this is the remaining
  `θ`/`B³` tie on `A⁴`);
* `habcdefg` kills the sibling cone `QuarticRatioConeABCDEFG810`.

No `sorry`, no new axioms, no finite-root shortcut. -/
theorem normalized810ScaleZero_impossible_of_residual{TAG}Kills
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hresid :
      ∀ (j t l beta gamma delta epsilon zeta eta theta : k)
        (A B C D E F G : k[X]),
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
              eta theta A B C D E F G) =
          Polynomial.C (j / t) →
        (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        QuarticRatioConeA810 A B C D E F G →
        QuarticChamberResidual{TAG}810 A B C D E F G →
        False)
    (hcorner :{HCORNER})
    (habcdefg :{HABCDEFG})
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    False := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticChamber{TAG}Residual hsource
  rcases hdisj with ⟨hconeA, hcase⟩ | habc
  · rcases hcase with ⟨hl0, hb0, hd0, hz0, hBn, hCn, hDn, hEn, hFn, hGn⟩ | hres
    · subst hl0; subst hb0; subst hd0; subst hz0
      {HCORNERUSE}
    · exact hresid j t l beta gamma delta epsilon zeta eta theta
        A B C D E F G hjdiv hder hxiDeg hmuDeg homiDeg hkapDeg hnuDeg hpiDeg
        hconeA hres
  · {HABCUSE}

"""
    body = body.replace("{TAG}", tag)
    body = body.replace("{HABCDEFG}", HAB_NEW if names else HAB_OLD)
    body = body.replace("{HCORNER}", HC_NEW if names else HC_OLD)
    body = body.replace("{HCORNERUSE}", CUSE_NEW if names else CUSE_OLD)
    body = body.replace("{HABCUSE}", USE_NEW if names else USE_OLD)
    name = (names[0] if names else
            "Grok810ScaleZeroQuarticAssemblyCoreScratch")
    doc = (
        "# Assembly core, `(8,10)` scale zero\n\n"
        "`normalized810ScaleZero_impossible_of_residual<tag>Kills`: the whole cone-`A`\n"
        "route of modules 1-30, reduced to three named obligations — the\n"
        f"{len(surv4)} chambers of `QuarticChamberResidual4810`, the all-constant\n"
        "corner, and the sibling cone `ABCDEFG`.  Gate-able now; the tracked-name\n"
        "glue is `Grok810ScaleZeroQuarticAssemblyScratch`.  Untracked working note."
    )
    out = (header(prev, doc) + "section QuarticAssemblyCore810\n\n"
           + "variable [IsAlgClosed k]\n\n" + body)
    out += "\nend QuarticAssemblyCore810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln,
                    "`normalized810ScaleZero_impossible_of_residual<tag>Kills` — the "
                    "cone-`A` route modulo three named obligations"))

    # ---- module 32: the tracked-name glue
    ext = [f"quarticChamberResidual{tag}810_impossible",
           "quarticAllConstantCorner810_impossible",
           "quarticConeABCDEFG810_impossible"]
    EXTERNALS.extend(ext)
    body2 = """set_option maxHeartbeats 64000000 in
/-- The `(8,10)` scale-zero leaf: no normalised leading-core source exists. -/
theorem normalized810ScaleZero_impossible{SFX}
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    False :=
  normalized810ScaleZero_impossible_of_residual{TAG}Kills
    quarticChamberResidual{TAG}810_impossible
    quarticAllConstantCorner810_impossible
    quarticConeABCDEFG810_impossible
    hsource

set_option maxHeartbeats 64000000 in
/-- Identity glue to the tracked exclusion
(`Grok810ScaleZeroConeEliminationScratch.lean:2266`). -/
theorem planeKeller810ScaleZeroExclusion_closed{SFX} :
    PlaneKeller810ScaleZeroExclusion (K := k) :=
  planeKeller810ScaleZeroExclusion_of_impossible
    (fun P Q H hsource => normalized810ScaleZero_impossible{SFX} hsource)

#print axioms normalized810ScaleZero_impossible{SFX}
#print axioms planeKeller810ScaleZeroExclusion_closed{SFX}
"""
    name2 = (names[1] if names else
             "Grok810ScaleZeroQuarticAssemblyScratch")
    doc2 = (
        "# Final assembly, `(8,10)` scale zero\n\n"
        "`normalized810ScaleZero_impossible` and\n"
        "`planeKeller810ScaleZeroExclusion_closed`, the two names the tracked\n"
        "route glue expects.  **This module gates only once the three external\n"
        "lemmas land**; it assumes exactly\n\n"
        "* `quarticChamberResidual{tag}810_impossible` — the aggregate kill of the\n"
        f"  {len(surv4)}-constructor inductive `QuarticChamberResidual{tag}810`\n"
        "  (tower lane: the 2 open, 19 deep-rescue and 405-wall families; power\n"
        "  lane: the `power_target` systems whose cofactors the taxonomy never\n"
        "  recorded), with the signature of `hresid` in\n"
        "  `…AssemblyCoreScratch`;\n"
        "* `quarticAllConstantCorner810_impossible` — the all-constant corner with\n"
        "  `l = β = δ = ζ = 0`, with the signature of `hcorner`;\n"
        "* `quarticConeABCDEFG810_impossible` — the sibling cone, expected from\n"
        "  `Grok810ScaleZeroQuarticFullConeFinalScratch` (whose latest is\n"
        "  `quarticConeABCDEFG810_residual9`), with the signature of `habcdefg`.\n\n"
        "Untracked working note."
    )
    body2 = body2.replace("{TAG}", tag)
    body2 = body2.replace("{SFX}", "7" if names else "")
    imp2 = ([name, "Grok810ScaleZeroQuarticFullConeD6F6Scratch",
             "Grok810ScaleZeroQuarticConstantCornerScratch"] if names
            else name)
    out2 = (header(imp2, doc2) + "section QuarticAssembly810\n\n"
            + "variable [IsAlgClosed k]\n\n" + body2)
    out2 += "\nend QuarticAssembly810\n" + FOOTER
    ln2 = write(name2 + ".lean", out2)
    MODULES.append((name2, ln2, "`normalized810ScaleZero_impossible` and "
                                "`planeKeller810ScaleZeroExclusion_closed` "
                                "(needs the three external lemmas)"))
    # the reconciliation table for the two lanes
    rows = []
    for c in surv4:
        rows.append(f"| `r{c.name}` | `{c.defname}` | `{c.live}` | "
                    f"`{'·'.join(c.argmin)}` | "
                    + ", ".join(f"`{lf['id']}`" for lf in c.leaves) + " | "
                    + ", ".join(sorted({lf["certificate"]["kind"]
                                        for lf in c.leaves})) + " |")
    tbl = (
        f"# `QuarticChamberResidual{tag}810` — the {len(surv4)} chambers the "
        "tower lane owes\n\n"
        "Constructor of the inductive in\n"
        f"`Grok810ScaleZeroQuarticChamberResidual{tag}Scratch.lean`, the chamber "
        "`Prop`\n"
        "it carries, its live-letter set and argmin, the JSON leaf ids of\n"
        "`scripts/out_810_scale_zero_quartic_chambers.json` it covers, and the\n"
        "certificate kinds of those leaves.  A chamber with several leaf ids is\n"
        "one of the 11 carrier-refined cells: use\n"
        "`quarticChamber<name>810_refine` of\n"
        "`Grok810ScaleZeroQuarticChamberRefineScratch.lean` to split it into the\n"
        "`QuarticRefined<name>L<i>810` leaves first.\n\n"
        "| constructor | chamber `Prop` | live | argmin | JSON leaves | kinds |\n"
        "|---|---|---|---|---|---|\n" + "\n".join(rows) + "\n")
    (Path.home() / f"lean/tools/sigma810/RESIDUAL{tag}_CHAMBERS.md").write_text(tbl)
    log(f"wrote ~/lean/tools/sigma810/RESIDUAL{tag}_CHAMBERS.md")
    return name2




# ------------- modules 33-36: the power-target bridges, kills and residual 5
def load_plan5():
    import json
    return json.loads((ROOT / "scripts" /
                       "out_810_quartic_chamber_killplan5.json").read_text())


def power_cert_signatures():
    """system -> (false lemma, [(carrier, inner name)], [letters]) parsed from
    the tracked `Grok810ScaleZeroQuarticPowerCertificatesScratch`."""
    p = ROOT / "Grok810ScaleZeroQuarticPowerCertificatesScratch.lean"
    txt = p.read_text()
    out = {}
    for m in re.finditer(r"theorem (quarticPowerInnerS(\d+)810_false) "
                         r"\(a b c d e f g : k\)\n((?:    \(.*\)\n)+)", txt):
        sysname = "S" + m.group(2)
        crs, lets = [], []
        for ln in m.group(3).strip().split("\n"):
            mm = re.match(r"\s*\((\w+) : (\w+)QuarticPowerInner(\w+)810 "
                          r"a b c d e f g = 0\)", ln)
            if mm:
                crs.append((mm.group(2), f"{mm.group(2)}QuarticPowerInner{sysname}810"))
                continue
            mm = re.match(r"\s*\(\w+ : ([a-g]) ≠ 0\)", ln)
            if mm:
                lets.append(mm.group(1).upper())
        out[sysname] = (m.group(1), crs, lets)
    return out


def plan5_leaves(data, coords, plan5):
    pm = packet_map_module9(data, coords)
    faces = {}
    for (cr, fk), i in pm.items():
        faces[(cr, i)] = fk
    nxt = collections.Counter()
    leaves = []
    for e in plan5["chambers"]:
        recs = []
        for r in e["carriers"]:
            fk = frozenset(tuple(x) for x in r["face"])
            key = (r["carrier"], fk)
            if key not in pm:
                pm[key] = 3000 + nxt[r["carrier"]]
                nxt[r["carrier"]] += 1
                faces[(r["carrier"], pm[key])] = fk
            rr = dict(r)
            rr["packet"] = pm[key]
            recs.append(rr)
        leaves.append({"live": e["live"], "argmin": e["argmin"], "kind": "power",
                       "killable": True, "carriers": recs, "blocked": [],
                       "system": e["system"], "name": e["name"]})
    packets = [{"carrier": cr, "id": i, "face": [list(x) for x in fk]}
               for (cr, i), fk in faces.items()]
    return {"packets": packets, "leaves": leaves}


def emit_power_kills(data, coords, chambers, plan5full, have, prev):
    sigs = power_cert_signatures()
    plan5full = {"packets": plan5full["packets"],
                 "leaves": [e for e in plan5full["leaves"]
                            if e["system"] in sigs]}
    cham = {(c.live, c.argmin): c for c in chambers}
    pk = {(p["carrier"], p["id"]): frozenset(tuple(x) for x in p["face"])
          for p in plan5full["packets"]}
    body = "/-! ## Top-coefficient bridges to the power-target inner scalars -/\n\n"
    bridge = {}
    for e in plan5full["leaves"]:
        sysname = e["system"]
        _fname, crs, _lets = sigs[sysname]
        inner = dict(crs)
        for r in e["carriers"]:
            cr, p = r["carrier"], r["packet"]
            key = (cr, sysname)
            if key in bridge:
                continue
            lf = EC.sort_records(coords[cr + "_lf"])
            face = [x for x in lf if rec_key(x) in pk[(cr, p)]]
            d = deg_expr(face[0].get("exps") or {})
            nm = f"{cr}QuarticChamberFace{p}810_coeff_top_{sysname}"
            bridge[key] = (nm, d, face, p)
            if nm in have:
                continue
            call = f"{inner[cr]} " + " ".join(LC[L] for L in LET)
            body += coeff_top_lemma(cr, p, face, d, nm, call,
                                    unfold=(inner[cr],))
    body += "/-! ## The power-target chamber kills -/\n\n"
    nk = 0
    for e in plan5full["leaves"]:
        c = cham[(e["live"], tuple(e["argmin"]))]
        S = e["live"]
        live = set(S)
        sysname = e["system"]
        fname, crs, lets = sigs[sysname]
        srcs = set()
        for r in e["carriers"]:
            srcs |= {v.get("source") for v in r["loads"].values()
                     if v["status"] == "band"}
        forms = [r["carrier"] for r in e["carriers"]]
        need_nu = ("n2-cost" in srcs) or ("nu" in forms)
        out = ["set_option maxHeartbeats 64000000 in",
               f"/-- Chamber `{S}` / `{'·'.join(e['argmin'])}` dies on power system "
               f"`{sysname}` (carriers " + ", ".join(CC.GREEK[f] for f in forms)
               + "). -/",
               f"theorem quarticChamber{c.name}810_impossible",
               f"    ({LOADSIG8} : k)", "    (A B C D E F G : k[X])",
               f"    (hch : {c.defname} A B C D E F G)",
               "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
               "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))",
               f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}",
               "          A B C D E F G).natDegree = 0)"]
        if need_nu:
            out.append(f"    (hnu : (degreeZeroNuQuartic810 {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        for f in forms:
            if f in ("kappa", "nu"):
                continue
            out.append(f"    ({CC.DEG_HYP[f]} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        out[-1] += " :"
        out.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        out.append(f"  obtain ⟨{', '.join(names)}⟩ := hch")
        out.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                out.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        out += ["  have hAne : A ≠ 0 := by", "    intro h0",
                "    have hz0 : A.natDegree = 0 := by simp [h0]",
                "    clear * - hApos hz0; omega"]
        base = (chamber_cons_named(c.nums()) + CONE_CONS + dead_cons(live)
                + NONNEG_CONS)
        for src in sorted(srcs):
            casc, loads, needsnu = BANDCASC[src]
            vs = ", ".join(BANDVAR[src].format(x) for x in loads)
            out.append(f"  obtain ⟨{vs}⟩ :=")
            out.append(f"    {casc} {LOADSIG8}")
            out.append("      A B C D E F G hA" + (" hnu hkap" if needsnu else " hkap"))
        innerhyp = []
        for ci, r in enumerate(e["carriers"]):
            form, p = r["carrier"], r["packet"]
            d = r["d"]
            nm, _d2, face, _p2 = bridge[(form, sysname)]
            lf = EC.sort_records(coords[form + "_lf"])
            rest = [x for x in lf if rec_key(x) not in pk[(form, p)]]
            surv_lf = surviving(rest, live)
            dvec = CC.lin(d)
            withd = base + [(f"hdp{ci}", dvec, True)]
            out.append(f"  have hdp{ci} : 0 < {d} := by")
            out.append("    by_contra hzero")
            knc = keep_str(base + [("hzero", tuple(-x for x in dvec), False)],
                           [g for X in SIG
                            for g in CC.target_of(f"{X}.natDegree = 0")])
            out.append("    exact hnc (by "
                       + (f"clear * - {knc}; " if knc else "") + "omega)")
            args_r = []
            for ld in LOADS:
                v = r["loads"][ld]
                if v["status"] == "empty":
                    continue
                recs = [x for cnk in col_chunks(coords, form, ld) for x in cnk[1]]
                uniq = []
                for x in surviving(recs, live):
                    g = deg_expr(x.get("exps") or {})
                    if g not in uniq:
                        uniq.append(g)
                if v["status"] == "dominated":
                    kd = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]
                                          for g in uniq])
                    args_r.append("(Or.inr (by "
                                  + (f"clear * - {kd}; " if kd else "")
                                  + "omega))")
                    continue
                hn = f"hz{ci}{ld}"
                args_r.append(hn)
                out += band_block(hn, ld, BANDVAR[v["source"]].format(ld),
                                  band_disjuncts(v["source"], ld), uniq, d,
                                  base, withd, live)
            zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
            seenlf = []
            for x in surv_lf:
                g = deg_expr(x.get("exps") or {})
                if g not in seenlf:
                    seenlf.append(g)
            lfa = []
            for g in seenlf:
                kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]])
                lfa.append("(by " + (f"clear * - {kg}; " if kg else "")
                           + "omega)")
            lfargs = " ".join(lfa)
            rname = f"{form}QuarticChamberRest{p}810"
            out.append(f"  have hr{ci} : ({rname} {LOADSIG8}")
            out.append(f"      A B C D E F G).natDegree < {d} :=")
            out.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
            out.append(f"      A B C D E F G hdp{ci}" + (f" {zargs}" if zargs else "")
                       + (f" {lfargs}" if lfargs else "") + " " + " ".join(args_r))
            ne = sorted({L for x in face for L in LET
                         if int((x.get("exps") or {}).get(L, 0) or 0) > 0},
                        key=LET.index)
            tie = " ".join("(by omega)" for _ in face[1:])
            out.append(f"  have hct{ci} := {nm} "
                       + " ".join(f"h{L}ne" for L in ne)
                       + coeff_top_named(ne) + (f" {tie}" if tie else ""))
            dh = (CC.DEG_HYP[form] if form not in ("kappa", "nu")
                  else ("hkap" if form == "kappa" else "hnu"))
            out.append(f"  have hq{ci} : ({CC.FORM_LEAN[form]} {LOADSIG8}")
            out.append(f"      A B C D E F G).coeff ({d}) = 0 := by")
            out.append("    apply coeff_eq_zero_of_natDegree_lt")
            out.append(f"    rw [{dh}]")
            out.append("    omega")
            out.append(f"  rw [degreeZero{CC.FORM_CAP[form]}Quartic810_eq_face{p}_add_rest,")
            out.append(f"    coeff_add, coeff_eq_zero_of_natDegree_lt hr{ci},")
            out.append(f"    add_zero] at hq{ci}")
            out.append(f"  have hin{ci} : {dict(crs)[form]} "
                       + " ".join(LC[L] for L in LET) + " = 0 :=")
            out.append(f"    hct{ci}.symm.trans hq{ci}")
            innerhyp.append((form, f"hin{ci}"))
        for L in lets:
            src = f"h{L}ne" if L != "A" else "hAne"
            out.append(f"  have h{L}c : {L}.leadingCoeff ≠ 0 := "
                       f"leadingCoeff_ne_zero.mpr {src}")
        ordered = [dict(innerhyp)[cr] for cr, _inm in crs]
        out.append(f"  exact {fname} " + " ".join(LC[L] for L in LET) + " "
                   + " ".join(ordered) + " " + " ".join(f"h{L}c" for L in lets))
        out.append("")
        body += "\n".join(out) + "\n"
        nk += 1
    name = "Grok810ScaleZeroQuarticChamberPowerKillsScratch"
    doc = ("# Power-target chamber kills, `(8,10)` scale zero\n\n"
           f"{len(bridge)} top-coefficient bridges and {nk} chamber kills against the\n"
           "tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`\n"
           "(SHA 102939dc): each carrier's face top coefficient is extracted, and\n"
           "the Singular-lifted isobaric identity then forces a product of non-zero\n"
           "leading coefficients to vanish.  Which chambers qualify is decided by\n"
           "`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.")
    split_decls(name, "QuarticChamberPowerKills810", doc,
                decl_blocks(prune_arith(name_chamber_facts(body), SINGLE_KEEP)),
                [prev, "Grok810ScaleZeroQuarticPowerCertificatesScratch"],
                base=1)
    MODULES.append((name, body.count("\n"),
                    f"{len(bridge)} `_coeff_top` bridges and {nk} "
                    "power-target chamber kills"))
    killmap = {}
    for e in plan5full["leaves"]:
        srcs = {v.get("source") for r in e["carriers"]
                for v in r["loads"].values() if v["status"] == "band"}
        forms = [r["carrier"] for r in e["carriers"]]
        _rh = {"kappa": "hkapDeg", "mu": "hmuDeg", "xi": "hxiDeg",
               "pi": "hpiDeg", "nu": "hnuDeg", "omicron": "homiDeg"}
        killmap[(e["live"], tuple(e["argmin"]))] = (
            e["carriers"][0]["carrier"], ("n2-cost" in srcs) or ("nu" in forms),
            [_rh[f] for f in forms if f not in ("kappa", "nu")])
    return name, killmap




# ------------------- modules 36-38: the refined-leaf kills and residual 6
def load_plan6():
    import json
    return json.loads((ROOT / "scripts" /
                       "out_810_quartic_chamber_killplan6.json").read_text())


def plan6_leaves(data, coords, plan6):
    """Refined leaves in the leaf shape, with packet ids from 4000 upwards."""
    pm = packet_map_module9(data, coords)
    faces = {}
    for (cr, fk), i in pm.items():
        faces[(cr, i)] = fk
    nxt = collections.Counter()
    leaves = []
    for e in plan6["leaves"]:
        recs = []
        for r in e["carriers"]:
            fk = frozenset(tuple(x) for x in r["face"])
            key = (r["carrier"], fk)
            if key not in pm:
                pm[key] = 4000 + nxt[r["carrier"]]
                nxt[r["carrier"]] += 1
                faces[(r["carrier"], pm[key])] = fk
            rr = dict(r)
            rr["packet"] = pm[key]
            recs.append(rr)
        leaves.append({"live": e["live"], "argmin": e["argmin"], "kind": "refined",
                       "killable": True, "carriers": recs, "blocked": [],
                       "cell": e["cell"], "leaf": e["leaf"], "mode": e["mode"],
                       "system": e.get("system")})
    packets = [{"carrier": cr, "id": i, "face": [list(x) for x in fk]}
               for (cr, i), fk in faces.items()]
    return {"packets": packets, "leaves": leaves}


def emit_refined_kills(data, coords, chambers, plan6full, have, prev):
    sigs = power_cert_signatures()
    # the lane omitted one system (`S24`, the CEG `g^4`: its `μ/γ` column does
    # not clear), so its leaves stay in the residual.
    plan6full = {"packets": plan6full["packets"],
                 "leaves": [e for e in plan6full["leaves"]
                            if e["mode"] != "power" or e["system"] in sigs]}
    cham = {c.name: c for c in chambers}
    pk = {(p["carrier"], p["id"]): frozenset(tuple(x) for x in p["face"])
          for p in plan6full["packets"]}
    body = "/-! ## Top-coefficient bridges for the refined leaves -/\n\n"
    bridge, facedeg = {}, {}
    emitted = set()
    for e in plan6full["leaves"]:
        for r in e["carriers"]:
            cr, p = r["carrier"], r["packet"]
            lf = EC.sort_records(coords[cr + "_lf"])
            face = [x for x in lf if rec_key(x) in pk[(cr, p)]]
            d = deg_expr(face[0].get("exps") or {})
            if e["mode"] == "single":
                nm = f"{cr}QuarticChamberFace{p}810_natDegree"
                facedeg[(cr, p)] = (nm, face, d)
                if nm in have or nm in emitted:
                    continue
                emitted.add(nm)
                exps = face[0].get("exps") or {}
                chain, need, haspow = mono_ne(exps)
                qn, qd = int(face[0]["qn"]), int(face[0]["qd"])
                coef = (f"({qn} / {qd} : k)" if qd != 1 else f"({qn} : k)")
                if qn < 0:
                    coef = (f"(-({-qn} / {qd} : k))" if qd != 1
                            else f"(-({-qn} : k))")
                out = ["set_option maxHeartbeats 64000000 in", f"theorem {nm}",
                       "    (A B C D E F G : k[X])"]
                for L in need:
                    out.append(f"    (h{L}ne : {L} ≠ 0)")
                out[-1] += " :"
                out.append(f"    ({cr}QuarticChamberFace{p}810 A B C D E F G)"
                           ".natDegree =")
                out.append(f"      {d} := by")
                out.append(f"  have hc : {coef} ≠ 0 := by norm_num")
                out.append(f"  simp only [{cr}QuarticChamberFace{p}810]")
                out.append("  rw [natDegree_smul _ hc"
                           + "".join(f", {c}" for c in chain) + "]")
                if haspow:
                    out.append("  simp only [natDegree_pow]")
                out.append("  all_goals omega")
                out.append("")
                body += "\n".join(out) + "\n"
                continue
            sysname = e["system"]
            key = (cr, sysname)
            if key in bridge:
                continue
            inner = dict(sigs[sysname][1])
            nm = f"{cr}QuarticChamberFace{p}810_coeff_top_{sysname}"
            bridge[key] = (nm, d, face, p)
            if nm in have or nm in emitted:
                continue
            emitted.add(nm)
            body += coeff_top_lemma(
                cr, p, face, d, nm,
                f"{inner[cr]} " + " ".join(LC[L] for L in LET),
                unfold=(inner[cr],))
    body += "/-! ## The refined-leaf kills -/\n\n"
    nk = 0
    for e in plan6full["leaves"]:
        c = cham[e["cell"]]
        i = e["leaf"]
        S = e["live"]
        live = set(S)
        pnm = f"QuarticRefined{c.name}L{i}810"
        rconj = _leaf_conjuncts(c.leaves[i])
        srcs = set()
        for r in e["carriers"]:
            srcs |= {v.get("source") for v in r["loads"].values()
                     if v["status"] == "band"}
        forms = [r["carrier"] for r in e["carriers"]]
        need_nu = ("n2-cost" in srcs) or ("nu" in forms)
        out = ["set_option maxHeartbeats 64000000 in",
               f"/-- Refined leaf {i} of chamber `{S}` / "
               f"`{'·'.join(e['argmin'])}` dies "
               + (f"on power system `{e['system']}`" if e["mode"] == "power"
                  else f"on the single-monomial `{CC.GREEK[forms[0]]}` face")
               + ". -/",
               f"theorem quarticRefined{c.name}L{i}810_impossible",
               f"    ({LOADSIG8} : k)", "    (A B C D E F G : k[X])",
               f"    (hch : {pnm} A B C D E F G)",
               "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
               "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))",
               f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}",
               "          A B C D E F G).natDegree = 0)"]
        if need_nu:
            out.append(f"    (hnu : (degreeZeroNuQuartic810 {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        for f in forms:
            if f in ("kappa", "nu"):
                continue
            out.append(f"    ({CC.DEG_HYP[f]} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        out[-1] += " :"
        out.append("    False := by")
        out.append("  obtain ⟨hcell, "
                   + ", ".join(f"hrf{t}" for t in range(len(rconj))) + "⟩ := hch")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{t}" for t in range(len(c.nums()))]
        out.append(f"  obtain ⟨{', '.join(names)}⟩ := hcell")
        out.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                out.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        out += ["  have hAne : A ≠ 0 := by", "    intro h0",
                "    have hz0 : A.natDegree = 0 := by simp [h0]",
                "    clear * - hApos hz0; omega"]
        base = (chamber_cons_named(c.nums())
                + chamber_cons_named(rconj, tag="hrf")
                + CONE_CONS + dead_cons(live) + NONNEG_CONS)
        for src in sorted(srcs):
            casc, loads, needsnu = BANDCASC[src]
            vs = ", ".join(BANDVAR[src].format(x) for x in loads)
            out.append(f"  obtain ⟨{vs}⟩ :=")
            out.append(f"    {casc} {LOADSIG8}")
            out.append("      A B C D E F G hA" + (" hnu hkap" if needsnu else " hkap"))
        innerhyp = []
        for ci, r in enumerate(e["carriers"]):
            form, p = r["carrier"], r["packet"]
            d = r["d"]
            lf = EC.sort_records(coords[form + "_lf"])
            face = [x for x in lf if rec_key(x) in pk[(form, p)]]
            rest = [x for x in lf if rec_key(x) not in pk[(form, p)]]
            surv_lf = surviving(rest, live)
            dvec = CC.lin(d)
            withd = base + [(f"hdp{ci}", dvec, True)]
            out.append(f"  have hdp{ci} : 0 < {d} := by")
            out.append("    by_contra hzero")
            knc = keep_str(base + [("hzero", tuple(-x for x in dvec), False)],
                           [g for X in SIG
                            for g in CC.target_of(f"{X}.natDegree = 0")])
            out.append("    exact hnc (by "
                       + (f"clear * - {knc}; " if knc else "") + "omega)")
            args_r = []
            for ld in LOADS:
                v = r["loads"][ld]
                if v["status"] == "empty":
                    continue
                recs = [x for cnk in col_chunks(coords, form, ld) for x in cnk[1]]
                uniq = []
                for x in surviving(recs, live):
                    g = deg_expr(x.get("exps") or {})
                    if g not in uniq:
                        uniq.append(g)
                if v["status"] == "dominated":
                    kd = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]
                                          for g in uniq])
                    args_r.append("(Or.inr (by "
                                  + (f"clear * - {kd}; " if kd else "")
                                  + "omega))")
                    continue
                hn = f"hz{ci}{ld}"
                args_r.append(hn)
                out += band_block(hn, ld, BANDVAR[v["source"]].format(ld),
                                  band_disjuncts(v["source"], ld), uniq, d,
                                  base, withd, live)
            zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
            seenlf = []
            for x in surv_lf:
                g = deg_expr(x.get("exps") or {})
                if g not in seenlf:
                    seenlf.append(g)
            lfa = []
            for g in seenlf:
                kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]])
                lfa.append("(by " + (f"clear * - {kg}; " if kg else "")
                           + "omega)")
            lfargs = " ".join(lfa)
            rname = f"{form}QuarticChamberRest{p}810"
            out.append(f"  have hr{ci} : ({rname} {LOADSIG8}")
            out.append(f"      A B C D E F G).natDegree < {d} :=")
            out.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
            out.append(f"      A B C D E F G hdp{ci}" + (f" {zargs}" if zargs else "")
                       + (f" {lfargs}" if lfargs else "") + " " + " ".join(args_r))
            ne = sorted({L for x in face for L in LET
                         if int((x.get("exps") or {}).get(L, 0) or 0) > 0},
                        key=LET.index)
            dh = (CC.DEG_HYP[form] if form not in ("kappa", "nu")
                  else ("hkap" if form == "kappa" else "hnu"))
            if e["mode"] == "single":
                nm, _f, _d = facedeg[(form, p)]
                out.append(f"  have hlead : ({form}QuarticChamberFace{p}810 "
                           "A B C D E F G).natDegree =")
                out.append(f"      {d} :=")
                out.append(f"    {nm} A B C D E F G " + " ".join(f"h{L}ne" for L in ne))
                out.append(f"  rw [degreeZero{CC.FORM_CAP[form]}Quartic810_eq_face{p}"
                           "_add_rest,")
                out.append("    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),"
                           " hlead]")
                out.append(f"    at {dh}")
                out.append("  omega")
            else:
                sysname = e["system"]
                nm, _d2, _f2, _p2 = bridge[(form, sysname)]
                tie = " ".join("(by omega)" for _ in face[1:])
                out.append(f"  have hct{ci} := {nm} "
                           + " ".join(f"h{L}ne" for L in ne)
                           + coeff_top_named(ne)
                           + (f" {tie}" if tie else ""))
                out.append(f"  have hqq{ci} : ({CC.FORM_LEAN[form]} {LOADSIG8}")
                out.append(f"      A B C D E F G).coeff ({d}) = 0 := by")
                out.append("    apply coeff_eq_zero_of_natDegree_lt")
                out.append(f"    rw [{dh}]")
                out.append("    omega")
                out.append(f"  rw [degreeZero{CC.FORM_CAP[form]}Quartic810"
                           f"_eq_face{p}_add_rest,")
                out.append(f"    coeff_add, coeff_eq_zero_of_natDegree_lt hr{ci},")
                out.append(f"    add_zero] at hqq{ci}")
                out.append(f"  have hin{ci} : {dict(sigs[sysname][1])[form]} "
                           + " ".join(LC[L] for L in LET) + " = 0 :=")
                out.append(f"    hct{ci}.symm.trans hqq{ci}")
                innerhyp.append((form, f"hin{ci}"))
        if e["mode"] == "power":
            fname, crs, lets = sigs[e["system"]]
            for L in lets:
                src = f"h{L}ne" if L != "A" else "hAne"
                out.append(f"  have h{L}c : {L}.leadingCoeff ≠ 0 := "
                           f"leadingCoeff_ne_zero.mpr {src}")
            ordered = [dict(innerhyp)[cr] for cr, _inm in crs]
            out.append(f"  exact {fname} " + " ".join(LC[L] for L in LET) + " "
                       + " ".join(ordered) + " " + " ".join(f"h{L}c" for L in lets))
        out.append("")
        body += "\n".join(out) + "\n"
        nk += 1
    name = "Grok810ScaleZeroQuarticChamberRefinedKillsScratch"
    doc = ("# Refined-leaf kills, `(8,10)` scale zero\n\n"
           f"{nk} of the 59 leaves of the 11 carrier-refined cells: 8 on a\n"
           "single-monomial face of some carrier, 17 on the power systems\n"
           "`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`\n"
           "produced for exactly those cells.  The leaves come from the tournament\n"
           "of `…ChamberRefineScratch`; their load columns are decided against the\n"
           "leaf's *full* conjunct set (cell + refinement) in\n"
           "`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.")
    split_decls(name, "QuarticChamberRefinedKills810", doc,
                decl_blocks(prune_arith(name_chamber_facts(body), SINGLE_KEEP)),
                [prev, "Grok810ScaleZeroQuarticPowerCertificatesScratch"])
    MODULES.append((name, body.count("\n"), f"{nk} refined-leaf kills"))
    killed = {}
    for e in plan6full["leaves"]:
        srcs = {v.get("source") for r in e["carriers"]
                for v in r["loads"].values() if v["status"] == "band"}
        forms = [r["carrier"] for r in e["carriers"]]
        killed[(e["cell"], e["leaf"])] = (e["carriers"][0]["carrier"],
                                          ("n2-cost" in srcs) or ("nu" in forms),
                                          [(r["carrier"]) for r in e["carriers"]])
    return name, killed


def emit_residual6(chambers, kills, refkills, prev):
    """Module 38: the exhaust dispatched through every kill set, with the 11
    carrier-refined cells split by their tournament first."""
    resid_hyp = {"kappa": "hkapDeg", "mu": "hmuDeg", "xi": "hxiDeg",
                 "pi": "hpiDeg", "nu": "hnuDeg", "omicron": "homiDeg"}
    refined = {c.name: c for c in chambers if c.refined}
    surv, survref = [], []
    for c in chambers:
        if c.name in refined:
            for i in range(len(c.leaves)):
                if (c.name, i) not in refkills:
                    survref.append((c, i))
        elif (c.live, c.argmin) not in kills:
            surv.append(c)
    ind = "QuarticChamberResidual6810"
    body = "/-! ## The last chamber residual -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- The {len(surv)} whole chambers and {len(survref)} refined leaves\n"
             "no kill module reaches. -/\n")
    body += f"inductive {ind} (A B C D E F G : k[X]) : Prop\n"
    for c in surv:
        body += (f"  | r{c.name} : {c.defname} A B C D E F G →\n"
                 f"      {ind} A B C D E F G\n")
    for c, i in survref:
        body += (f"  | r{c.name}L{i} : QuarticRefined{c.name}L{i}810 A B C D E F G →\n"
                 f"      {ind} A B C D E F G\n")
    body += "\n"
    lines = []
    for s in range(1, 7):
        grp = [c for c in chambers if len(c.live) == s]
        lines.append(f"      | size{s} h =>")
        lines.append("        cases h with")
        for c in grp:
            lines.append(f"        | {c.ctor} hc =>")
            if c.name in refined:
                n = len(c.leaves)
                lines.append(f"          rcases quarticChamber{c.name}810_refine "
                             "A B C D E F G hc with")
                lines.append("            " + " | ".join(f"h{t}" for t in range(n)))
                for t in range(n):
                    if (c.name, t) in refkills:
                        _cr, nu, forms = refkills[(c.name, t)]
                        extra = " hnuDeg" if (nu or "nu" in forms) else ""
                        for f in forms:
                            if f not in ("kappa", "nu"):
                                extra += f" {resid_hyp[f]}"
                        lines.append(f"          · exact (quarticRefined{c.name}L{t}"
                                     "810_impossible")
                        lines.append(f"              {LOADSIG8}")
                        lines.append(f"              A B C D E F G h{t} hnc "
                                     f"hkapDeg{extra}).elim")
                    else:
                        lines.append(f"          · exact {ind}.r{c.name}L{t} h{t}")
                continue
            key = (c.live, c.argmin)
            if key in kills:
                extra = kill_extra_args(kills[key], resid_hyp)
                lines.append(f"          exact (quarticChamber{c.name}810_impossible")
                lines.append(f"            {LOADSIG8}")
                lines.append(f"            A B C D E F G hc hnc hkapDeg{extra}).elim")
            else:
                lines.append(f"          exact {ind}.r{c.name} hc")
    thm = "normalized810ScaleZero_quarticChamber6Residual"
    note = ("Honest leftover after every chamber kill of Files B/C.  Closed "
            "relative to `normalized810ScaleZero_quarticLoadLadderResidual`: the "
            "1115-chamber exhaust, the tournament on the 11 carrier-refined "
            "cells, and every kill of modules 14, 19, 23, 29, 35 and 37.  "
            "Remaining: the all-constant corner and "
            f"`{ind}` — {len(surv)} whole chambers and {len(survref)} refined "
            "leaves, i.e. the tower lane's open / deep-rescue / weak-band "
            "families, corner `H`, and the systems whose columns do not clear.  "
            "No `sorry`, no new axioms, no finite-root shortcut.")
    body += "set_option maxHeartbeats 64000000 in\n"
    body += f"/-- {note} -/\n"
    body += f"""theorem {thm}
    {{P Q : MvPolynomial (Fin 2) k}} {{H : k[X]}}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧
              B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
              E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0) ∨
            {ind} A B C D E F G)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticLoadLadderResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · obtain ⟨hconeA, hexh, hlK, hbK, hdK, hzK, htK, hconst, hevenC, hevenE⟩ := hA
    refine Or.inl ⟨hconeA, ?_⟩
    by_cases hnc : B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
    · rcases hconst with ⟨hl0, hb0, hd0, hz0⟩ | hn
      · exact Or.inl ⟨hl0, hb0, hd0, hz0, hnc.1, hnc.2.1, hnc.2.2.1,
          hnc.2.2.2.1, hnc.2.2.2.2.1, hnc.2.2.2.2.2⟩
      · exact absurd hnc hn
    · refine Or.inr ?_
      have hsupp := quarticChamberSupport810_of (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G hconeA
        hjdiv hder
      cases hsupp with
"""
    body += "\n".join(lines) + "\n"
    body += "  · exact Or.inr hABCDEFG\n\n"
    body += f"#print axioms {thm}\n"
    name = "Grok810ScaleZeroQuarticChamberResidual6Scratch"
    doc = ("# The last chamber residual, `(8,10)` scale zero\n\n"
           f"`{ind}` ({len(surv)} whole chambers + {len(survref)} refined leaves)\n"
           f"and `{thm}`.  Untracked working note.")
    out = (header(prev, doc) + "section QuarticChamberResidual6810\n\n"
           + "variable [IsAlgClosed k]\n\n" + body)
    out += "\nend QuarticChamberResidual6810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"`{ind}` ({len(surv)} chambers + {len(survref)} "
                              f"refined leaves) and `{thm}`"))
    return name, surv, survref




# ------------------- module 40: the `N₇` cost ladder for the 202 wall kills
RHO_GROUPS = ["rhoBaseGroupQuartic810", "rhoBetaGroupQuartic810",
              "rhoGammaGroupQuartic810", "rhoDeltaGroupQuartic810",
              "rhoEpsilonGroupQuartic810", "rhoZetaGroupQuartic810",
              "rhoEtaGroupQuartic810", "rhoThetaGroupQuartic810"]
N7PARTS = [("primitive", 0, _Fr(1)), ("omicron", 1, _Fr(1)),
           ("nu", 2, _Fr(3, 16)), ("kappa", 3, _Fr(5, 128))]
N7FACE = "n7Quartic{}TowerFace810"
N7LEAN = "degreeZeroN7TowerQuartic810"


def n7_terms():
    coords = CC.load_coords()
    acc = {}
    for f, ap, co in N7PARTS:
        for r in coords[f]:
            ex = r.get("exps") or {}
            mon = "".join(L * int(ex.get(L, 0) or 0) for L in SIG)
            ld = (list(r["loads"]) or [None])[0]
            key = (mon, int(ex.get("A", 0) or 0) + ap, ld)
            acc[key] = acc.get(key, _Fr(0)) + co * _Fr(int(r["qn"]), int(r["qd"]))
    return {k: v for k, v in acc.items() if v != 0}


def n7_cost_conjuncts(pi):
    T = n7_terms()
    wp = WPI[pi]
    out = [(m, wp) for m in _minimal([m for (m, _a, ld) in T if ld is None])]
    for p2 in NOPUREA:
        if WPI[p2] >= wp:
            continue
        for m in _minimal([m for (m, _a, ld) in T if ld == p2]):
            out.append((m, wp - WPI[p2]))
    return out


def emit_n7_ladder(prev):
    T = n7_terms()
    body = ""
    # 1. the no-pure-A part, chunked
    recs = EC.sort_records([as_record(k, c) for k, c in T.items()
                            if not (k[2] in PUREA and k[0] == "")])
    chunks = split_chunks(recs)
    cnames = []
    body += ("/-! ## `N₇` off its five pure-`A` load columns -/\n\n")
    for i, ch in enumerate(chunks):
        nm = f"n7QuarticNoPureA{i + 1}810"
        cnames.append((nm, ch))
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- `N₇` off its pure-`A` load columns, chunk {i + 1}/"
                 f"{len(chunks)}: {len(ch)} monomials. -/\n")
        body += poly_def(nm, LOADSIG8, ch)
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"def n7QuarticNoPureA810\n    ({LOADSIG8} : k)\n"
             "    (A B C D E F G : k[X]) : k[X] :=\n  "
             + " +\n    ".join(f"{nm} {LOADSIG8} A B C D E F G"
                               for nm, _ in cnames) + "\n\n")
    # 2. the one heavy split identity
    faces = " +\n        ".join(
        f"{N7FACE.format(CC.LOAD_CAP[pi])} {pi} A" for pi in PUREA)
    simpset = ([N7LEAN, "degreeZeroPrimitiveQuartic810"] + RHO_GROUPS
               + ["degreeZeroOmicronQuartic810", "degreeZeroNuQuartic810",
                  "degreeZeroKappaQuartic810", "n7QuarticNoPureA810"]
               + [nm for nm, _ in cnames]
               + [N7FACE.format(CC.LOAD_CAP[pi]) for pi in PUREA])
    body += "set_option maxHeartbeats 64000000 in\n"
    body += ("/-- Cone-free: `N₇` splits into its five pure-`A` load columns and\n"
             "the rest.  This is the module identity the tower lane's\n"
             "`quarticSigma_<load>_eq_zero_of_N7_column` takes as a hypothesis;\n"
             "it unfolds `Π` through the eight `rho` groups. -/\n")
    body += (f"theorem {N7LEAN}_eq_pureA_add_rest\n"
             f"    ({LOADSIG8} : k)\n"
             "    (A B C D E F G : k[X]) :\n"
             f"    {N7LEAN} {LOADSIG8} A B C D E F G =\n"
             f"      {faces} +\n"
             f"        n7QuarticNoPureA810 {LOADSIG8} A B C D E F G := by\n"
             f"  simp only [{', '.join(dict.fromkeys(simpset))}]\n"
             "  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))\n"
             "  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,\n"
             "    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,\n"
             "    map_div₀, map_ofNat, map_natCast, map_one]\n"
             "  ring\n\n")
    # 3. the generic chunk bounds
    body += "/-! ## Generic chunk bounds -/\n\n"
    npdegs = {}
    for nm, ch in cnames:
        lem, dg = bound_lemma(nm, LOADSIG8, ch)
        npdegs[nm] = len(dg)
        body += lem
    # 4. per load: the predicate, the rest, the identity corollary, the bound,
    #    the kill and the band
    entries = []
    for pi in PUREA:
        wp = WPI[pi]
        j = (17 - wp) // 2
        cap = CC.LOAD_CAP[pi]
        zeroed = " ".join("0" if (p in PUREA and WPI[p] < wp) else p
                          for p in LOADS)
        heavier = [p for p in PUREA if WPI[p] > wp]
        rname = f"n7QuarticCostRest{cap}810"
        rhs = " +\n    ".join(
            [f"{N7FACE.format(CC.LOAD_CAP[p])} {p} A" for p in heavier]
            + [f"n7QuarticNoPureA810 {zeroed} A B C D E F G"])
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Everything of `N₇` below its pure-`A` `{pi}` column, once the\n"
                 "lighter pure-`A` loads are zero. -/\n")
        body += (f"def {rname}\n    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) : k[X] :=\n"
                 f"  {rhs}\n\n")
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem {N7LEAN}_eq_{pi}Column_add_rest\n"
                 f"    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) :\n"
                 f"    {N7LEAN} {zeroed} A B C D E F G =\n"
                 f"      {N7FACE.format(cap)} {pi} A +\n"
                 f"        {rname} {zeroed} A B C D E F G := by\n"
                 f"  rw [{N7LEAN}_eq_pureA_add_rest]\n"
                 f"  simp only [{rname}, "
                 + ", ".join(N7FACE.format(CC.LOAD_CAP[p]) for p in PUREA)
                 + ", zero_mul, mul_zero, zero_smul, smul_zero, add_zero,\n"
                 "    zero_add]\n  ring\n\n")
        cc = n7_cost_conjuncts(pi)
        hyp = [(f"hp{t}", cost_gt(m, ww)) for t, (m, ww) in enumerate(cc)]
        pname = f"QuarticN7CostTop{cap}810"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- The pure-`A` `{pi}` column of `N₇` is its unique top. -/\n")
        body += (f"def {pname} (A B C D E F G : k[X]) : Prop :=\n"
                 "  QuarticRatioConeA810 A B C D E F G ∧\n    "
                 + " ∧\n    ".join(s for _h, s in hyp) + "\n\n")
        # the rest bound
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem {rname}_natDegree_lt\n"
                 f"    ({LOADSIG8} : k)\n"
                 "    {A B C D E F G : k[X]}\n")
        for h, s in CONE_HYPS + hyp:
            body += f"    ({h} : {s})\n"
        body = body[:-1] + " :\n"
        body += (f"    ({rname} {zeroed} A B C D E F G).natDegree <\n"
                 f"      {j} * A.natDegree := by\n"
                 f"  simp only [{rname}]\n")
        pieces = []
        for p in heavier:
            jj = (17 - WPI[p]) // 2
            body += (f"  have hf{p} : ({N7FACE.format(CC.LOAD_CAP[p])} {p} A)"
                     f".natDegree <\n      {j} * A.natDegree := by\n"
                     f"    simp only [{N7FACE.format(CC.LOAD_CAP[p])}]\n"
                     f"    refine natDegree_smul_lt810 _ ?_\n"
                     "    rw [natDegree_pow]\n"
                     "    omega\n")
            pieces.append(f"hf{p}")
        args = " ".join(h for h, _ in CONE_HYPS + hyp)
        # each chunk bound wants its own `deg < d` facts, which `omega` reads
        # off the cone bounds and the `hp` conjuncts; naming the steps keeps
        # the elaborator off one huge nested application
        for ci2, (nm, _ch) in enumerate(cnames):
            body += (f"  have hnp{ci2} : ({nm} {zeroed} A B C D E F G)"
                     f".natDegree <\n      {j} * A.natDegree := by\n"
                     f"    apply {nm}_natDegree_lt {zeroed} A B C D E F G "
                     "<;> omega\n")
        body += (f"  have hnp : (n7QuarticNoPureA810 {zeroed} A B C D E F G)"
                 f".natDegree <\n      {j} * A.natDegree := by\n"
                 "    simp only [n7QuarticNoPureA810]\n")
        acc = "hnp0"
        for t in range(1, len(cnames)):
            acc = f"(natDegree_add_lt810 {acc} hnp{t})"
        body += f"    exact {acc}\n"
        pieces.append("hnp")
        acc = pieces[0]
        for h in pieces[1:]:
            acc = (f"natDegree_add_lt810 ({acc}) {h}" if " " in acc
                   else f"natDegree_add_lt810 {acc} {h}")
        body += f"  exact {acc}\n\n"
        entries.append((pi, pname, hyp, j, rname, zeroed, cap))
    # 5. the kills, bands and the cascade
    body += "/-! ## The `N₇` kills, bands and cascade -/\n\n"
    byload = {e[0]: e for e in entries}
    for hi, lo in zip(PUREA[1:], PUREA[:-1]):
        chi, clo = CC.LOAD_CAP[hi], CC.LOAD_CAP[lo]
        nm = f"quarticN7CostTop{chi}810_imp_{clo}810"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem {nm}\n    {{A B C D E F G : k[X]}}\n"
                 f"    (h : QuarticN7CostTop{chi}810 A B C D E F G) :\n"
                 f"    QuarticN7CostTop{clo}810 A B C D E F G := by\n"
                 f"  obtain ⟨hA, {', '.join(h for h, _ in byload[hi][2])}⟩ := h\n"
                 "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA\n"
                 "  exact ⟨hA, "
                 + ", ".join("by omega" for _ in byload[lo][2]) + "⟩\n\n")
    for (pi, pname, hyp, j, rname, zeroed, cap) in entries:
        lighter = [p for p in PUREA if WPI[p] < WPI[pi]]
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- `N₇` kills `{pi}` in cost form, via the tower lane's\n"
                 f"`quarticSigma_{pi}_eq_zero_of_N7_column`. -/\n"
                 f"theorem quarticSigmaN7Cost_{pi}_eq_zero\n"
                 f"    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X])\n"
                 f"    (htop : {pname} A B C D E F G)\n")
        for p in lighter:
            body += f"    (h{p}0 : {p} = 0)\n"
        body += ("    (hprim : (degreeZeroPrimitiveQuartic810 " + LOADSIG8 + "\n"
                 "          A B C D E F G).natDegree = 1)\n"
                 "    (homi : (degreeZeroOmicronQuartic810 " + LOADSIG8 + "\n"
                 "          A B C D E F G).natDegree = 0)\n"
                 "    (hnu : (degreeZeroNuQuartic810 " + LOADSIG8 + "\n"
                 "          A B C D E F G).natDegree = 0)\n"
                 "    (hkap : (degreeZeroKappaQuartic810 " + LOADSIG8 + "\n"
                 "          A B C D E F G).natDegree = 0) :\n"
                 f"    {pi} = 0 := by\n"
                 f"  obtain ⟨hA, {', '.join(h for h, _ in hyp)}⟩ := id htop\n"
                 "  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA\n"
                 f"  have hrest := {rname}_natDegree_lt {LOADSIG8}\n"
                 "    " + " ".join(h for h, _ in CONE_HYPS + hyp) + "\n")
        for p in lighter:
            body += f"  subst h{p}0\n"
        body += (f"  have hle := {N7LEAN}_natDegree_le {zeroed}\n"
                 "    A B C D E F G hApos hprim homi hnu hkap\n"
                 f"  exact quarticSigma_{pi}_eq_zero_of_N7_column {zeroed}\n"
                 f"    A B C D E F G ({rname} {zeroed} A B C D E F G) hApos"
                 + "".join(" rfl" for _ in lighter) + "\n"
                 + f"    hrest hle ({N7LEAN}_eq_{pi}Column_add_rest {zeroed}\n"
                 "      A B C D E F G)\n\n")
    name = "Grok810ScaleZeroQuarticChamberN7LadderScratch"
    doc = (
        "# The `N₇` cost ladder — the split the 202 wall kills need\n\n"
        "`Grok810ScaleZeroQuarticTowerScratch` proves\n"
        "`quarticSigma_<load>_eq_zero_of_N7_column` with the module identity\n"
        "`N₇ = face + rest` and the rest bound as *hypotheses* (\"the module\n"
        "identity unfolds `Π` and lives in the residual assembly\").  This module\n"
        "supplies exactly those: `N₇` off its five pure-`A` load columns (chunked\n"
        "at 20 monomials), the one heavy split identity through the eight `rho`\n"
        "groups, the cost-form `Top` predicates (one inequality per minimal\n"
        "load-free monomial of `N₇`, plus one per minimal monomial of each lighter\n"
        "`γ/ε/η` column), the rest bounds, and the five kills.  Every rest\n"
        "monomial is Farkas-checked against its predicate in\n"
        "`scripts/check_810_quartic_chambers_lean.py`.  Untracked working note."
    )
    out = header([prev, "Grok810ScaleZeroQuarticTowerScratch"], doc)
    out += "section QuarticN7Ladder810\n\n" + body
    out += "\nend QuarticN7Ladder810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, "the `N₇` pure-`A` split, cost-form predicates, "
                              "rest bounds and the five `N₇` kills"))
    return name




# ---------------- modules 52+: carrier infrastructure for ο, Π and N₂..N₇
AUXDEFS = {
    "n2": (13, 1, [("nu", 0, "1"), ("kappa", 1, "1 / 8")],
           "degreeZeroN2Quartic810", False),
    "n3": (15, 1, [("omicron", 0, "1"), ("nu", 1, "-(1 / 16)")],
           "degreeZeroN3Quartic810", True),
    "n4": (17, 1, [("primitive", 0, "1"), ("omicron", 1, "-1")],
           "degreeZeroN4Quartic810", False),
    "n5": (15, 2, [("omicron", 0, "1"), ("nu", 1, "1 / 8"),
                   ("kappa", 2, "3 / 128")], "degreeZeroN5Quartic810", False),
    "n6": (17, 2, [("primitive", 0, "1"), ("omicron", 1, "-(2 / 3)"),
                   ("nu", 2, "-(1 / 48)")], "degreeZeroN6Quartic810", False),
    "n7": (17, 3, [("primitive", 0, "1"), ("omicron", 1, "1"),
                   ("nu", 2, "3 / 16"), ("kappa", 3, "5 / 128")],
           "degreeZeroN7Quartic810", False),
}
CARRIER_LEAN = dict(CC.FORM_LEAN)
for _n, (_w, _k, _p, _nm, _new) in AUXDEFS.items():
    CARRIER_LEAN[_n] = _nm
def _parse_le_binders(lean):
    """Binder names of `<lean>_natDegree_le` as actually declared on disk."""
    pat = re.compile(r"theorem\s+" + re.escape(lean) + r"_natDegree_le\b")
    for f in sorted(ROOT.glob("*.lean")):
        try:
            txt = f.read_text()
        except OSError:
            continue
        m = pat.search(txt)
        if not m:
            continue
        lines = txt[m.start():].split("\n")
        sig = []
        for ln in lines:
            sig.append(ln)
            if ln.rstrip().endswith(":"):
                break
        blob = "\n".join(sig)
        return [b for b in re.findall(r"\(\s*([A-Za-z][A-Za-z0-9']*)[^):]*:",
                                      blob) if b.startswith("h")]
    return None


AUX_LE_BINDERS = {}
for _n in list(AUXDEFS):
    AUX_LE_BINDERS[_n] = _parse_le_binders(CARRIER_LEAN[_n])


def aux_le_argstr(form):
    """Argument string after `A B C D E F G` for `<form>_natDegree_le`.

    Derived from the lemma's real binder list where it can be read off the
    tree (so `hApos` is passed only where the lemma actually binds it), and
    from the AUXNEEDS heuristic otherwise."""
    names = {"primitive": "hprim", "omicron": "homi", "nu": "hnu",
             "kappa": "hkap"}
    got = AUX_LE_BINDERS.get(form)
    if got:
        return " ".join(got)
    hargs = [names[f] for f in AUXNEEDS[form]]
    if AUXDEFS[form][1] >= 1:
        hargs.insert(0, "hApos")
    return " ".join(hargs)


GREEK_ALL = dict(CC.GREEK)
GREEK_ALL.update({"n3": "N₃", "n4": "N₄", "n5": "N₅", "n6": "N₆", "n7": "N₇"})


def carrier_terms(coords, form):
    """(letter monomial, A power, load) -> coefficient, for any carrier."""
    if form not in AUXDEFS:
        acc = {}
        for r in coords[form]:
            ex = r.get("exps") or {}
            mon = "".join(L * int(ex.get(L, 0) or 0) for L in SIG)
            ld = (list(r["loads"]) or [None])[0]
            acc[(mon, int(ex.get("A", 0) or 0), ld)] = _Fr(int(r["qn"]),
                                                           int(r["qd"]))
        return acc
    acc = {}
    for f, ap, co in AUXDEFS[form][2]:
        c = _Fr(co.replace("(", "").replace(")", ""))
        for r in coords[f]:
            ex = r.get("exps") or {}
            mon = "".join(L * int(ex.get(L, 0) or 0) for L in SIG)
            ld = (list(r["loads"]) or [None])[0]
            key = (mon, int(ex.get("A", 0) or 0) + ap, ld)
            acc[key] = acc.get(key, _Fr(0)) + c * _Fr(int(r["qn"]), int(r["qd"]))
    return {k: v for k, v in acc.items() if v != 0}


def emit_carrier_infra(coords, form, prev):
    """One module: the carrier's load-free part, eight load columns and the
    cone-free split identity."""
    T = carrier_terms(coords, form)
    gk = GREEK_ALL[form]
    lean = CARRIER_LEAN[form]
    body = ""
    if form in AUXDEFS and AUXDEFS[form][4]:
        w, kk, parts, _nm, _new = AUXDEFS[form]
        terms = []
        for f, ap, co in parts:
            if ap == 0:
                terms.append(f"{CC.FORM_LEAN[f]} {LOADSIG8} A B C D E F G")
            elif ap == 1:
                terms.append(f"({co} : k) • (A * {CC.FORM_LEAN[f]} {LOADSIG8} "
                             "A B C D E F G)")
            else:
                terms.append(f"({co} : k) • (A ^ {ap} * {CC.FORM_LEAN[f]} "
                             f"{LOADSIG8} A B C D E F G)")
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- `{gk} = ο − (1/16)·A·ν` (weight {w}, `natDegree ≤ {kk}·a`);\n"
                 "the auxiliary `UNOWNED_CHAMBERS.md` adds to the tower. -/\n")
        body += (f"def {lean}\n    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) : k[X] :=\n  "
                 + " +\n    ".join(terms) + "\n\n")
        hyp = {"omicron": ("homi", "= 0"), "nu": ("hnu", "= 0"),
               "kappa": ("hkap", "= 0"), "primitive": ("hprim", "= 1")}
        out = ["set_option maxHeartbeats 64000000 in",
               f"theorem {lean}_natDegree_le", f"    ({LOADSIG8} : k)",
               "    (A B C D E F G : k[X])", "    (hApos : 0 < A.natDegree)"]
        for f, _ap, _co in parts:
            h, rel = hyp[f]
            out.append(f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            out.append(f"          A B C D E F G).natDegree {rel})")
        out[-1] += " :"
        bound = "A.natDegree" if kk == 1 else f"{kk} * A.natDegree"
        out.append(f"    ({lean} {LOADSIG8} A B C D E F G).natDegree ≤")
        out.append(f"      {bound} := by")
        hs = []
        for idx, (f, ap, co) in enumerate(parts):
            h, _rel = hyp[f]
            hn = f"hb{idx}"
            hs.append(hn)
            call = f"{CC.FORM_LEAN[f]} {LOADSIG8} A B C D E F G"
            if ap == 0:
                out.append(f"  have {hn} : ({call}).natDegree ≤ {bound} := by")
                out.append(f"    rw [{h}]")
                out.append("    omega")
                continue
            inner = (f"A * {call}" if ap == 1 else f"A ^ {ap} * {call}")
            lhs = "A.natDegree" if ap == 1 else f"(A ^ {ap}).natDegree"
            out.append(f"  have {hn} : (({co} : k) • ({inner})).natDegree ≤ "
                       f"{bound} := by")
            out.append("    refine (natDegree_smul_le810 _ _).trans ?_")
            out.append(f"    have hmul : ({inner}).natDegree ≤")
            out.append(f"        {lhs} + ({call}).natDegree := natDegree_mul_le")
            out.append(f"    rw [{h}, add_zero"
                       + (", natDegree_pow" if ap > 1 else "") + "] at hmul")
            out.append("    omega")
        out.append(f"  simp only [{lean}]")
        acc = hs[0]
        for h in hs[1:]:
            acc = (f"natDegree_add_le810 ({acc}) {h}" if " " in acc
                   else f"natDegree_add_le810 {acc} {h}")
        out.append(f"  exact {acc}")
        out.append("")
        body += "\n".join(out) + "\n"
    lf = EC.sort_records([as_record(k, c) for k, c in T.items() if k[2] is None])
    body += f"/-! ## `{gk}`: load-free part and the eight load columns -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += f"/-- The load-free part of `{lean}` ({len(lf)} monomials). -/\n"
    body += poly_def(f"{form}QuarticLoadFree810", "", lf)
    cols = {}
    for ld in LOADS:
        recs = EC.sort_records([as_record(k, c) for k, c in T.items()
                                if k[2] == ld])
        chunks = split_chunks(recs)
        nms = []
        for i, chunk in enumerate(chunks):
            nm = (f"{form}QuarticColumn{CC.LOAD_CAP[ld]}810" if len(chunks) == 1
                  else f"{form}QuarticColumn{CC.LOAD_CAP[ld]}{i + 1}810")
            nms.append(nm)
            body += "set_option maxHeartbeats 64000000 in\n"
            body += (f"/-- The `{ld}` column of `{lean}`"
                     + (f", chunk {i + 1}/{len(chunks)}" if len(chunks) > 1 else "")
                     + f" ({len(chunk)} monomials). -/\n")
            body += poly_def(nm, ld, chunk)
            lem, _ = bound_lemma(nm, ld, chunk)
            body += lem
            body += (f"theorem {nm}_zero (A B C D E F G : k[X]) :\n"
                     f"    {nm} 0 A B C D E F G = 0 := by\n  simp [{nm}]\n\n")
        cols[ld] = nms
    simp = [lean, f"{form}QuarticLoadFree810"] + \
        [n for ns in cols.values() for n in ns]
    if form in AUXDEFS:
        simp += [CC.FORM_LEAN[f] for f, _a, _c in AUXDEFS[form][2]]
    if form == "primitive" or (form in AUXDEFS and
                               any(f == "primitive" for f, _a, _c in AUXDEFS[form][2])):
        simp += RHO_GROUPS
    rhs = f"{form}QuarticLoadFree810 A B C D E F G"
    for ld in LOADS:
        for nm in cols[ld]:
            rhs += f" +\n      {nm} {ld} A B C D E F G"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- Cone-free split of `{lean}` into its load-free part and its\n"
             "eight load columns. -/\n")
    body += (f"theorem {lean}_eq_chamberSplit\n"
             f"    ({LOADSIG8} : k)\n"
             "    (A B C D E F G : k[X]) :\n"
             f"    {lean} {LOADSIG8} A B C D E F G =\n"
             f"      {rhs} := by\n"
             f"  simp only [{', '.join(dict.fromkeys(simp))}]\n"
             "  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))\n"
             "  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,\n"
             "    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,\n"
             "    map_div₀, map_ofNat, map_natCast, map_one]\n"
             "  ring\n\n")
    name = f"Grok810ScaleZeroQuarticChamberInfra{form.capitalize()}Scratch"
    doc = (
        f"# `{gk}` load-free part, load columns and split, `(8,10)` scale zero\n\n"
        f"`{lean}` has {len(T)} monomials.  `…ChamberFacesPart0Scratch` does this\n"
        "for `κ, μ, ξ, π` only; `UNOWNED_CHAMBERS.md` needs the same for `ο`, `Π`\n"
        "and the auxiliaries `N₂…N₇`"
        + (f", and defines `{gk}` itself" if form in AUXDEFS and AUXDEFS[form][4]
           else "") + ".  Independent of the sibling\n"
        "`…ChamberInfra*` modules.  Untracked working note."
    )
    out = header(prev, doc) + f"section QuarticChamberInfra{form.capitalize()}810\n\n"
    out += body + f"\nend QuarticChamberInfra{form.capitalize()}810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"`{gk}` load-free part, eight load columns and "
                              "the split identity"))
    return name




def emit_n7_bands(prev):
    """`…ChamberN7LadderScratch` already has the `N₇` cost predicates, rests and
    kills (through the tower lane's column lemmas); this adds only the pieces
    `UNOWNED_CHAMBERS.md`'s `n7-cost` band source needs — monotonicity, the five
    band disjunctions and the cascade."""
    aux = "n7"
    body = ""
    hyps = {pi: [(f"hp{t}", cost_gt(m, w))
                 for t, (m, w) in enumerate(n7_cost_conjuncts(pi))]
            for pi in PUREA}
    body += "/-! ## The five `N₇` band disjunctions -/\n\n"
    for pi in PUREA:
        cc = n7_cost_conjuncts(pi)
        n = len(cc)
        cap = CC.LOAD_CAP[pi]
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem quarticSigmaN7Cost_{pi}_band\n"
                 f"    {{{pi} : k}} (A B C D E F G : k[X])\n"
                 "    (hA : QuarticRatioConeA810 A B C D E F G)\n"
                 f"    (hkill : QuarticN7CostTop{cap}810 A B C D E F G → {pi} = 0) :\n"
                 f"    {pi} = 0 ∨\n      "
                 + " ∨\n      ".join(cost_le(m, w) for m, w in cc) + " := by\n")

        def tree(t, ind):
            if t == n:
                return [f"{ind}exact Or.inl (hkill ⟨hA, "
                        + ", ".join(f"hb{u}" for u in range(n)) + "⟩)"]
            out = [f"{ind}by_cases hb{t} : {hyps[pi][t][1]}"]
            sub = tree(t + 1, ind + "  ")
            out.append(f"{ind}· {sub[0].strip()}")
            out += sub[1:]
            pos = 1 + t
            inj = ("Or.inr (" * pos + "?_" + ")" * pos if pos == n
                   else "Or.inr (" * pos + "Or.inl ?_" + ")" * pos)
            out.append(f"{ind}· refine {inj}")
            out.append(f"{ind}  omega")
            return out
        body += "\n".join(tree(0, "  ")) + "\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += ("/-- The cost-form `N₇` ladder as five band disjunctions, the\n"
             "`n7-cost` band source of `UNOWNED_CHAMBERS.md`. -/\n"
             "theorem quarticSigmaN7CostBands810\n"
             f"    ({LOADSIG8} : k)\n"
             "    (A B C D E F G : k[X])\n"
             "    (hA : QuarticRatioConeA810 A B C D E F G)\n"
             f"    (hprim : (degreeZeroPrimitiveQuartic810 {LOADSIG8}\n"
             "          A B C D E F G).natDegree = 1)\n"
             f"    (homi : (degreeZeroOmicronQuartic810 {LOADSIG8}\n"
             "          A B C D E F G).natDegree = 0)\n"
             f"    (hnu : (degreeZeroNuQuartic810 {LOADSIG8}\n"
             "          A B C D E F G).natDegree = 0)\n"
             f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}\n"
             "          A B C D E F G).natDegree = 0) :\n")
    stmts = []
    for pi in PUREA:
        cc = n7_cost_conjuncts(pi)
        stmts.append(f"    ({pi} = 0 ∨\n      "
                     + " ∨\n      ".join(cost_le(m, w) for m, w in cc) + ")")
    body += " ∧\n".join(stmts) + " := by\n"

    def mono(hi, lo):
        i, jj = PUREA.index(hi), PUREA.index(lo)
        term = "htop"
        for t in range(i, jj, -1):
            term = (f"quarticN7CostTop{CC.LOAD_CAP[PUREA[t]]}810_imp_"
                    f"{CC.LOAD_CAP[PUREA[t - 1]]}810 ({term})")
        return term

    def branch(pos, ind):
        out = []
        if pos == len(PUREA):
            out.append(f"{ind}exact ⟨" + ", ".join(f"Or.inl h{p}0" for p in PUREA)
                       + "⟩")
            return out
        pi = PUREA[pos]
        cap = CC.LOAD_CAP[pi]
        out.append(f"{ind}by_cases hT{pi} : QuarticN7CostTop{cap}810 A B C D E F G")
        args = "".join(f" h{p}0" for p in PUREA[:pos])
        out.append(f"{ind}· have h{pi}0 : {pi} = 0 :=")
        out.append(f"{ind}    quarticSigmaN7Cost_{pi}_eq_zero {LOADSIG8}")
        out.append(f"{ind}      A B C D E F G hT{pi}{args} hprim homi hnu hkap")
        out += branch(pos + 1, ind + "  ")
        comps = [f"Or.inl h{p}0" for p in PUREA[:pos]]
        for q in PUREA[pos:]:
            comps.append(f"quarticSigmaN7Cost_{q}_band ({q} := {q}) A B C D E F G hA\n"
                         f"{ind}      (fun htop => absurd ({mono(q, pi)}) hT{pi})")
        out.append(f"{ind}· exact ⟨" + (",\n" + ind + "    ").join(comps) + "⟩")
        return out
    body += "\n".join(branch(0, "  ")) + "\n\n"
    name = "Grok810ScaleZeroQuarticChamberN7BandsScratch"
    doc = (
        "# The `n7-cost` band source, `(8,10)` scale zero\n\n"
        "`…ChamberN7LadderScratch` already carries the cost-form `N₇` predicates,\n"
        "the pure-`A` split, the rest bounds and the five kills (which go through\n"
        "the tower lane's `quarticSigma_<load>_eq_zero_of_N7_column`).  This adds\n"
        "only what the `n7-cost` band source of `UNOWNED_CHAMBERS.md` needs: the\n"
        "five band disjunctions and the cascade (the monotonicity chain is\n"
        "already in `…ChamberN7LadderScratch`).  103 single-chamber columns use\n"
        "it.\n"
        "Untracked working note."
    )
    out = header(prev, doc) + "section QuarticN7Bands810\n\n" + body
    out += "\nend QuarticN7Bands810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, "`N₇` cost-form monotonicity, the five bands and "
                              "the cascade"))
    return name




# =================== modules 61+: the unowned tranche (UNOWNED_CHAMBERS.md)
def load_unowned():
    import json
    return json.loads((ROOT / "scripts" /
                       "out_810_scale_zero_quartic_unowned.json").read_text())


def carrier_lf_records(coords, form):
    T = carrier_terms(coords, form)
    return EC.sort_records([as_record(k, c) for k, c in T.items() if k[2] is None])


def carrier_col_chunks(coords, form, ld):
    """The emitted chunk names of the `ld` column of any carrier."""
    T = carrier_terms(coords, form)
    recs = EC.sort_records([as_record(k, c) for k, c in T.items() if k[2] == ld])
    chunks = split_chunks(recs)
    out = []
    for i, ch in enumerate(chunks):
        nm = (f"{form}QuarticColumn{CC.LOAD_CAP[ld]}810" if len(chunks) == 1
              else f"{form}QuarticColumn{CC.LOAD_CAP[ld]}{i + 1}810")
        out.append((nm, ch))
    return out


HNC_BLOCK = ["    by_contra hcon",
             "    exact hnc (by omega)"]
HNC_INLINE = "(by by_contra hcon; exact hnc (by omega))"


def unowned_face(coords, form, facekeys):
    lf = carrier_lf_records(coords, form)
    keys = set(map(tuple, facekeys))
    return [r for r in lf if rec_key(r) in keys], [r for r in lf
                                                   if rec_key(r) not in keys]


CD_MAX = 6
PACKET_SPLIT = 2100


def emit_unowned_packets(coords, plan, prev, tag="Unowned"):
    """The 18 face packets of the `single` mode: faces, load-free rests, the
    packet split identity, the combined rest and the carrier split identity."""
    used = collections.OrderedDict()
    for e in plan["chambers"] + plan["leaves"]:
        if e["mode"] != "single":
            continue
        for r in e["carriers"]:
            used.setdefault((r["carrier"], r["packet"]), r)
    body_blocks = []
    for (form, p), r in used.items():
        body = ""
        face, rest = unowned_face(coords, form, r["face"])
        fname = f"{form}QuarticChamberFace{p}810"
        rname = f"{form}QuarticChamberRestLF{p}810"
        d = r["d"]
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Face of `{GREEK_ALL[form]}` on unowned packet {p} "
                 f"({len(face)} monomial, top degree `{d}`). -/\n")
        body += poly_def(fname, "", face)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Load-free rest of `{GREEK_ALL[form]}` off packet {p} "
                 f"({len(rest)} monomials). -/\n")
        body += poly_def(rname, "", rest)
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem {form}QuarticLoadFree810_eq_face{p}_add_rest\n"
                 "    (A B C D E F G : k[X]) :\n"
                 f"    {form}QuarticLoadFree810 A B C D E F G =\n"
                 f"      {fname} A B C D E F G + {rname} A B C D E F G := by\n"
                 f"  simp only [{form}QuarticLoadFree810, {fname}, {rname}]\n"
                 "  all_goals module\n\n")
        crname = f"{form}QuarticChamberRest{p}810"
        cols = [f"{nm} {ld} A B C D E F G" for ld in LOADS
                for nm, _ in carrier_col_chunks(coords, form, ld)]
        rhs = f"{rname} A B C D E F G"
        for c in cols:
            rhs += " +\n    " + c
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"def {crname}\n    ({LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X]) : k[X] :=\n"
                 f"  {rhs}\n\n")
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"theorem {CARRIER_LEAN[form]}_eq_face{p}_add_rest\n"
                 f"    ({LOADSIG8} : k)\n    (A B C D E F G : k[X]) :\n"
                 f"    {CARRIER_LEAN[form]} {LOADSIG8} A B C D E F G =\n"
                 f"      {fname} A B C D E F G +\n"
                 f"        {crname} {LOADSIG8} A B C D E F G := by\n"
                 f"  rw [{CARRIER_LEAN[form]}_eq_chamberSplit,\n"
                 f"    {form}QuarticLoadFree810_eq_face{p}_add_rest]\n"
                 f"  simp only [{crname}]\n  ring\n\n")
        body_blocks.append(body)
    parts, cur, curl = [], [], 0
    for blk in body_blocks:
        n = blk.count("\n")
        if cur and curl + n > PACKET_SPLIT:
            parts.append(cur)
            cur, curl = [], 0
        cur.append(blk)
        curl += n
    if cur:
        parts.append(cur)
    names = []
    for gi, grp in enumerate(parts or [[]]):
        nm = (f"Grok810ScaleZeroQuarticChamber{tag}PacketsScratch" if len(parts) <= 1
              else f"Grok810ScaleZeroQuarticChamber{tag}Packets{gi + 1}Scratch")
        doc = (f"# {tag} face packets, part {gi + 1}/{max(len(parts), 1)}\n\n"
               f"Face, load-free rest, packet split identity, combined rest and\n"
               "carrier split identity for the packets the kills use.\n"
               "Untracked working note.")
        sec = (f"QuarticChamber{tag}Packets810" if len(parts) <= 1
               else f"QuarticChamber{tag}Packets{gi + 1}810")
        out = (header(prev, doc) + f"section {sec}\n\n" + "".join(grp)
               + f"\nend {sec}\n" + FOOTER)
        ln = write(nm + ".lean", out)
        MODULES.append((nm, ln, f"{len(grp)} {tag} face packets"))
        names.append(nm)
    return names, used


def emit_unowned_columns(coords, plan, have, prev, tag="Unowned"):
    want = collections.OrderedDict()
    for e in plan["chambers"] + plan["leaves"]:
        if e["mode"] != "single":
            continue
        for r in e["carriers"]:
            for ld, v in r["loads"].items():
                if v["status"] != "empty":
                    want[(r["carrier"], ld, e["live"])] = True
    blocks, n = [], 0
    for (form, ld, S) in want:
        live = set(S)
        for nm, recs in carrier_col_chunks(coords, form, ld):
            if f"{nm}_natDegree_lt_of_live_{S}" in have:
                continue
            surv = surviving(recs, live)
            hyps, seen = [], {}
            for r in surv:
                g = deg_expr(r.get("exps") or {})
                if g not in seen:
                    seen[g] = f"hd{len(seen)}"
                    hyps.append((seen[g], g))
            pre = ""
            parts = []
            if len(surv) > CD_MAX:
                # a compute_degree over more than six surviving monomials with
                # seven symbolic degrees times out unpredictably at 64M
                # heartbeats: split the column first
                parts = split_chunks(surv, CD_MAX)
                for pi, chunk in enumerate(parts):
                    pn = f"{nm}Part{S}{pi + 1}810"
                    pre += "set_option maxHeartbeats 64000000 in\n"
                    pre += (f"/-- Piece {pi + 1}/{len(parts)} of `{nm}` on the "
                            f"live set `{S}` ({len(chunk)} monomials). -/\n")
                    pre += poly_def(pn, ld, chunk)
                    ph, pseen = [], {}
                    for r in chunk:
                        g = deg_expr(r.get("exps") or {})
                        if g not in pseen:
                            pseen[g] = f"hd{len(pseen)}"
                            ph.append((pseen[g], g))
                    o = ["set_option maxHeartbeats 64000000 in",
                         f"theorem {pn}_natDegree_lt", "    {d : ℕ}",
                         f"    ({ld} : k)", "    (A B C D E F G : k[X])",
                         "    (hdpos : 0 < d)"]
                    for h, g in ph:
                        o.append(f"    ({h} : {g} < d)")
                    o[-1] += " :"
                    o.append(f"    ({pn} {ld} A B C D E F G).natDegree < d := by")
                    if refl_ok(pn):
                        o += refl_bnd_proof(pn)
                    else:
                        o.append(f"  simp only [{pn}]")
                        o.append("  compute_degree")
                        o.append("  omega")
                    o.append("")
                    pre += "\n".join(o) + "\n"
                o = ["set_option maxHeartbeats 64000000 in",
                     f"theorem {nm}_split_of_live_{S}", f"    ({ld} : k)",
                     "    (A B C D E F G : k[X])"]
                for X in SIG:
                    if X not in live:
                        o.append(f"    (h{X}z : {X} = 0)")
                o[-1] += " :"
                o.append(f"    {nm} {ld} A B C D E F G =")
                o.append("      " + " +\n        ".join(
                    f"{nm}Part{S}{pi + 1}810 {ld} A B C D E F G"
                    for pi in range(len(parts))) + " := by")
                for X in SIG:
                    if X not in live:
                        o.append(f"  subst h{X}z")
                for e2 in range(2, 9):
                    o.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                             "zero_pow (by decide)")
                o.append("  simp only [" + nm + ", "
                         + ", ".join(f"{nm}Part{S}{pi + 1}810"
                                     for pi in range(len(parts)))
                         + f", {POWNAMES}, {ZERO_SIMP}]")
                o.append("  all_goals module")
                o.append("")
                pre += "\n".join(o) + "\n"
            out = ["set_option maxHeartbeats 64000000 in",
                   f"theorem {nm}_natDegree_lt_of_live_{S}",
                   "    {d : ℕ}", f"    ({ld} : k)",
                   "    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
            for X in SIG:
                if X not in live:
                    out.append(f"    (h{X}z : {X} = 0)")
            for h, g in hyps:
                out.append(f"    ({h} : {g} < d)")
            out[-1] += " :"
            out.append(f"    ({nm} {ld} A B C D E F G).natDegree < d := by")
            if parts:
                zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
                out.append(f"  rw [{nm}_split_of_live_{S} {ld} A B C D E F G"
                           + (f" {zargs}" if zargs else "") + "]")
                accs = []
                for pi, chunk in enumerate(parts):
                    pn = f"{nm}Part{S}{pi + 1}810"
                    args, pseen = [], []
                    for r in chunk:
                        g = deg_expr(r.get("exps") or {})
                        if g not in pseen:
                            pseen.append(g)
                            args.append(seen[g])
                    accs.append(f"({pn}_natDegree_lt {ld} A B C D E F G hdpos"
                                + ("".join(f" {a}" for a in args)) + ")")
                acc = accs[0]
                for a in accs[1:]:
                    acc = f"(natDegree_add_lt810 {acc} {a})"
                out.append(f"  exact {acc}")
            else:
                for X in SIG:
                    if X not in live:
                        out.append(f"  subst h{X}z")
                for e2 in range(2, 9):
                    out.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                               "zero_pow (by decide)")
                if surv and refl_ok(nm):
                    out += refl_degok_proof(nm)
                else:
                    out.append(f"  simp only [{nm}, {POWNAMES}, {ZERO_SIMP}]")
                    if surv:
                        out.append("  compute_degree")
                    out.append("  omega")
            out.append("")
            blocks.append(pre + "\n".join(out) + "\n")
            n += 1
    names = []
    groups, cur, curl, curc = [], [], 0, 0
    for b in blocks:
        # a reflective bound costs a declaration too, so it counts the
        # same way towards the per-module declaration budget
        nl, nc = b.count("\n"), (b.count("  compute_degree\n")
                                 + b.count(REFL_NS + ".natDegree_"))
        if cur and (curl + nl > 2200 or curc + nc > 65):
            groups.append(cur)
            cur, curl, curc = [], 0, 0
        cur.append(b)
        curl += nl
        curc += nc
    if cur:
        groups.append(cur)
    groups = groups or [[]]
    for gi, grp in enumerate(groups):
        nm = (f"Grok810ScaleZeroQuarticChamber{tag}Columns{gi + 1}"
              "Scratch")
        doc = (f"# {tag} load-column bounds, part {gi + 1}/{len(groups)}\n\n"
               f"{len(grp)} of the {n} (carrier, load, live-set) column bounds the\n"
               "kills need, including the columns of `N₂, N₃, N₅, N₆`.  A column\n"
               "with more than twelve surviving monomials is split first, so no\n"
               "single `compute_degree` sees more than ten.  Independent of its\n"
               "siblings.  Untracked note.")
        sec = f"QuarticChamber{tag}Columns{gi + 1}810"
        out = header(prev, doc) + f"section {sec}\n\n"
        out += "".join(grp) + f"\nend {sec}\n" + FOOTER
        ln = write(nm + ".lean", out)
        MODULES.append((nm, ln, f"{len(grp)} {tag} load-column bounds"))
        names.append(nm)
    return names


def emit_unowned_rests(coords, plan, packets, have, prev, tag="Unowned"):
    used = collections.OrderedDict()
    for e in plan["chambers"] + plan["leaves"]:
        if e["mode"] != "single":
            continue
        for r in e["carriers"]:
            used[(r["carrier"], r["packet"], e["live"])] = r
    blocks, nb, nlf = [], 0, 0
    for (form, p, S), rec in used.items():
        lfname = f"{form}QuarticChamberRestLF{p}810"
        live = set(S)
        _face, rest = unowned_face(coords, form, packets[(form, p)]["face"])
        if f"{lfname}_natDegree_lt_of_live_{S}" not in have:
            surv = surviving(rest, live)
            hyps, seen = [], {}
            for r in surv:
                g = deg_expr(r.get("exps") or {})
                if g not in seen:
                    seen[g] = f"hd{len(seen)}"
                    hyps.append((seen[g], g))
            o = ["set_option maxHeartbeats 64000000 in",
                 f"theorem {lfname}_natDegree_lt_of_live_{S}",
                 "    {d : ℕ}", "    (A B C D E F G : k[X])",
                 "    (hdpos : 0 < d)"]
            for X in SIG:
                if X not in live:
                    o.append(f"    (h{X}z : {X} = 0)")
            for h, g in hyps:
                o.append(f"    ({h} : {g} < d)")
            o[-1] += " :"
            o.append(f"    ({lfname} A B C D E F G).natDegree < d := by")
            pre = ""
            if len(surv) > CD_MAX:
                parts = split_chunks(surv, CD_MAX)
                for pi, chunk in enumerate(parts):
                    pn = f"{lfname}Part{S}{pi + 1}810"
                    pre += "set_option maxHeartbeats 64000000 in\n"
                    pre += (f"/-- Piece {pi + 1}/{len(parts)} of "
                            f"`{lfname}` on the live set `{S}` "
                            f"({len(chunk)} monomials). -/\n")
                    pre += poly_def(pn, "", chunk)
                    ph, pseen = [], {}
                    for r in chunk:
                        g = deg_expr(r.get("exps") or {})
                        if g not in pseen:
                            pseen[g] = f"hd{len(pseen)}"
                            ph.append((pseen[g], g))
                    q = ["set_option maxHeartbeats 64000000 in",
                         f"theorem {pn}_natDegree_lt", "    {d : ℕ}",
                         "    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
                    for h, g in ph:
                        q.append(f"    ({h} : {g} < d)")
                    q[-1] += " :"
                    q.append(f"    ({pn} A B C D E F G).natDegree < d := by")
                    if refl_ok(pn):
                        q += refl_bnd_proof(pn)
                    else:
                        q.append(f"  simp only [{pn}]")
                        q.append("  compute_degree")
                        q.append("  omega")
                    q.append("")
                    pre += "\n".join(q) + "\n"
                q = ["set_option maxHeartbeats 64000000 in",
                     f"theorem {lfname}_split_of_live_{S}",
                     "    (A B C D E F G : k[X])"]
                for X in SIG:
                    if X not in live:
                        q.append(f"    (h{X}z : {X} = 0)")
                q[-1] += " :"
                q.append(f"    {lfname} A B C D E F G =")
                q.append("      " + " +\n        ".join(
                    f"{lfname}Part{S}{pi + 1}810 A B C D E F G"
                    for pi in range(len(parts))) + " := by")
                for X in SIG:
                    if X not in live:
                        q.append(f"  subst h{X}z")
                for e2 in range(2, 9):
                    q.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                             "zero_pow (by decide)")
                q.append("  simp only [" + lfname + ", "
                         + ", ".join(f"{lfname}Part{S}{pi + 1}810"
                                     for pi in range(len(parts)))
                         + f", {POWNAMES}, {ZERO_SIMP}]")
                q.append("  all_goals module")
                q.append("")
                pre += "\n".join(q) + "\n"
                zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
                o.append(f"  rw [{lfname}_split_of_live_{S} A B C D E F G"
                         + (f" {zargs}" if zargs else "") + "]")
                accs = []
                for pi, chunk in enumerate(parts):
                    pn = f"{lfname}Part{S}{pi + 1}810"
                    args, pseen = [], []
                    for r in chunk:
                        g = deg_expr(r.get("exps") or {})
                        if g not in pseen:
                            pseen.append(g)
                            args.append(seen[g])
                    accs.append(f"({pn}_natDegree_lt A B C D E F G hdpos"
                                + "".join(f" {a}" for a in args) + ")")
                acc = accs[0]
                for a in accs[1:]:
                    acc = f"(natDegree_add_lt810 {acc} {a})"
                o.append(f"  exact {acc}")
            else:
                for X in SIG:
                    if X not in live:
                        o.append(f"  subst h{X}z")
                for e2 in range(2, 9):
                    o.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                             "zero_pow (by decide)")
                if surv and refl_ok(lfname):
                    o += refl_degok_proof(lfname)
                else:
                    o.append(f"  simp only [{lfname}, {POWNAMES}, {ZERO_SIMP}]")
                    if surv:
                        o.append("  compute_degree")
                    o.append("  omega")
            o.append("")
            blocks.append(pre + "\n".join(o) + "\n")
            nlf += 1
        rname = f"{form}QuarticChamberRest{p}810"
        if f"{rname}_natDegree_lt_of_live_{S}" in have:
            continue
        surv_lf = surviving(rest, live)
        lfh, seen = [], {}
        for r in surv_lf:
            g = deg_expr(r.get("exps") or {})
            if g not in seen:
                seen[g] = f"hl{len(seen)}"
                lfh.append((seen[g], g))
        out = ["set_option maxHeartbeats 64000000 in",
               f"theorem {rname}_natDegree_lt_of_live_{S}",
               "    {d : ℕ}", f"    ({LOADSIG8} : k)",
               "    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
        for X in SIG:
            if X not in live:
                out.append(f"    (h{X}z : {X} = 0)")
        for h, g in lfh:
            out.append(f"    ({h} : {g} < d)")
        loadhyp = {}
        for ld in LOADS:
            recs = [r for c in carrier_col_chunks(coords, form, ld) for r in c[1]]
            surv = surviving(recs, live)
            if not surv:
                continue
            degs = []
            for r in surv:
                g = deg_expr(r.get("exps") or {})
                if g not in degs:
                    degs.append(g)
            loadhyp[ld] = degs
            out.append(f"    (hb{ld} : {ld} = 0 ∨ ("
                       + " ∧ ".join(f"{g} < d" for g in degs) + "))")
        out[-1] += " :"
        out.append(f"    ({rname} {LOADSIG8} A B C D E F G).natDegree < d := by")
        zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
        largs = " ".join(h for h, _ in lfh)
        out.append("  have hr0 :=")
        out.append(f"    {lfname}_natDegree_lt_of_live_{S}")
        out.append(f"      A B C D E F G hdpos" + (f" {zargs}" if zargs else "")
                   + (f" {largs}" if largs else ""))
        pieces, ci = ["hr0"], 0
        for ld in LOADS:
            for nm, recs in carrier_col_chunks(coords, form, ld):
                surv = surviving(recs, live)
                hn = f"hc{ci}"
                ci += 1
                pieces.append(hn)
                out.append(f"  have {hn} : ({nm} {ld} A B C D E F G).natDegree "
                           "< d := by")
                if not surv:
                    for X in SIG:
                        if X not in live:
                            out.append(f"    subst h{X}z")
                    for e2 in range(2, 9):
                        out.append(f"    have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                                   "zero_pow (by decide)")
                    out.append(f"    simp only [{nm}, {POWNAMES}, {ZERO_SIMP}]")
                    out.append("    omega")
                    continue
                degs = [deg_expr(r.get("exps") or {}) for r in surv]
                idx = [loadhyp[ld].index(g) for g in degs]
                nh = len(loadhyp[ld])
                pat = ("g0" if nh == 1 else
                       "⟨" + ", ".join(f"g{t}" for t in range(nh)) + "⟩")
                out.append(f"    rcases hb{ld} with rfl | {pat}")
                out.append(f"    · rw [{nm}_zero]")
                out.append("      simpa using hdpos")
                out.append(f"    · exact {nm}_natDegree_lt_of_live_{S} {ld} "
                           "A B C D E F G hdpos"
                           + (f" {zargs}" if zargs else "")
                           + (" " + " ".join(f"g{t}" for t in idx) if idx else ""))
        out.append(f"  simp only [{rname}]")
        acc = pieces[0]
        for h in pieces[1:]:
            acc = (f"natDegree_add_lt810 ({acc}) {h}" if " " in acc
                   else f"natDegree_add_lt810 {acc} {h}")
        out.append(f"  exact {acc}")
        out.append("")
        blocks.append("\n".join(out) + "\n")
        nb += 1
    names = []
    groups, cur, curl, curc = [], [], 0, 0
    for b in blocks:
        # a reflective bound costs a declaration too, so it counts the
        # same way towards the per-module declaration budget
        nl, nc = b.count("\n"), (b.count("  compute_degree\n")
                                 + b.count(REFL_NS + ".natDegree_"))
        if cur and (curl + nl > 2200 or curc + nc > 65):
            groups.append(cur)
            cur, curl, curc = [], 0, 0
        cur.append(b)
        curl += nl
        curc += nc
    if cur:
        groups.append(cur)
    groups = groups or [[]]
    for gi, grp in enumerate(groups):
        nm = f"Grok810ScaleZeroQuarticChamber{tag}Rests{gi + 1}Scratch"
        doc = (f"# {tag} chamber rests, part {gi + 1}/{len(groups)}\n\n"
               f"{len(grp)} of the {nlf} load-free and {nb} full (packet,\n"
               "live-set) rest bounds the kills need.  Independent of its\n"
               "siblings.  Untracked working note.")
        sec = f"QuarticChamber{tag}Rests{gi + 1}810"
        out = header(prev, doc) + f"section {sec}\n\n"
        out += "".join(grp) + f"\nend {sec}\n" + FOOTER
        ln = write(nm + ".lean", out)
        MODULES.append((nm, ln, f"{len(grp)} {tag} rest bounds"))
        names.append(nm)
    return names


UNOWNED_BAND = {"kappa-letter": ("quarticSigma_kappaLoadBands810", LADDER,
                                 "hb{}", " hkap", []),
                "kappa-cost": ("quarticSigmaKappaCostBands810",
                               ["l", "beta", "delta", "zeta"], "hkb{}",
                               " hkap", []),
                "n2-cost": ("quarticSigmaN2CostBands810", LADDER, "hnb{}",
                            " hnu hkap", ["nu"]),
                "n5-cost": ("quarticSigmaN5CostBands810", LADDER, "h5b{}",
                            " homi hnu hkap", ["omicron", "nu"]),
                "n7-cost": ("quarticSigmaN7CostBands810", LADDER, "h7b{}",
                            " hprim homi hnu hkap",
                            ["primitive", "omicron", "nu"])}


def unowned_band_disjuncts(source, ld):
    if source == "kappa-letter":
        return [(X, ineq_of(X, TOP[ld][X])) for X in SIG]
    aux = {"kappa-cost": "kappa", "n2-cost": "n2",
           "n5-cost": "n5", "n7-cost": "n7"}[source]
    cc = n7_cost_conjuncts(ld) if aux == "n7" else cost_conjuncts(aux, ld)
    return [(None, cost_le(m, w)) for m, w in cc]


def refined_leaf_extra():
    """`(cell name, leaf index) -> number of extra conjuncts` of the refined
    leaf `Prop`s of module 30."""
    txt = (ROOT / "Grok810ScaleZeroQuarticChamberRefineScratch.lean").read_text()
    out = {}
    for m in re.finditer(r"^def QuarticRefined(\w+?)L(\d+)810 \(A B C D E F G : "
                         r"k\[X\]\) : Prop :=\n(.*?)\n\n", txt, re.S | re.M):
        out[(m.group(1), int(m.group(2)))] = m.group(3).count("∧")
    return out


def emit_unowned_kills(coords, chambers, plan, packets, have, prev):
    cham = {c.name: c for c in chambers}
    rex = refined_leaf_extra()
    entries = [e for e in plan["chambers"] + plan["leaves"]
               if e["mode"] == "single"]
    face_blocks = []
    facedeg, seen_f = {}, set()
    for e in entries:
        r = e["carriers"][0]
        form, p = r["carrier"], r["packet"]
        face, _rest = unowned_face(coords, form, packets[(form, p)]["face"])
        exps = face[0].get("exps") or {}
        d = deg_expr(exps)
        chain, need, haspow = mono_ne(exps)
        nm = f"{form}QuarticChamberFace{p}810_natDegree"
        facedeg[(form, p)] = (nm, need, d, face)
        if nm in have or nm in seen_f:
            continue
        seen_f.add(nm)
        qn, qd = int(face[0]["qn"]), int(face[0]["qd"])
        coef = (f"({qn} / {qd} : k)" if qd != 1 else f"({qn} : k)")
        if qn < 0:
            coef = (f"(-({-qn} / {qd} : k))" if qd != 1 else f"(-({-qn} : k))")
        out = ["set_option maxHeartbeats 64000000 in", f"theorem {nm}",
               "    (A B C D E F G : k[X])"]
        for L in need:
            out.append(f"    (h{L}ne : {L} ≠ 0)")
        out[-1] += " :"
        out.append(f"    ({form}QuarticChamberFace{p}810 A B C D E F G)"
                   ".natDegree =")
        out.append(f"      {d} := by")
        out.append(f"  have hc : {coef} ≠ 0 := by norm_num")
        out.append(f"  simp only [{form}QuarticChamberFace{p}810]")
        out.append("  rw [natDegree_smul _ hc" + "".join(f", {c}" for c in chain)
                   + "]")
        if haspow:
            out.append("  simp only [natDegree_pow]")
        out.append("  all_goals omega")
        out.append("")
        face_blocks.append("\n".join(out) + "\n")
    blocks, nk, killmap = [], 0, {}
    for e in entries:
        c = cham[e["name"]]
        S, live = e["live"], set(e["live"])
        r = e["carriers"][0]
        form, p = r["carrier"], r["packet"]
        nm, need, d, face = facedeg[(form, p)]
        _f, rest = unowned_face(coords, form, packets[(form, p)]["face"])
        surv_lf = surviving(rest, live)
        srcs = {v.get("source") for v in r["loads"].values()
                if v["status"].startswith("band")}
        aux_hyps = []
        for s in sorted(srcs):
            for f in UNOWNED_BAND[s][4]:
                if f not in aux_hyps:
                    aux_hyps.append(f)
        if form in ("nu", "omicron", "primitive") or form in AUXDEFS:
            for f in (AUXNEEDS.get(form) or
                      ([form] if form in ("nu", "omicron", "primitive") else [])):
                if f != "kappa" and f not in aux_hyps:
                    aux_hyps.append(f)
        if form in AUXDEFS:
            for f, _a, _co in AUXDEFS[form][2]:
                if f != "kappa" and f not in aux_hyps:
                    aux_hyps.append(f)
        order = ["primitive", "omicron", "nu"]
        aux_hyps = [f for f in order if f in aux_hyps]
        leafi = e.get("leaf")
        if leafi is None:
            thname = f"quarticChamber{c.name}810_impossible"
            hyptype = c.defname
            extra = 0
        else:
            thname = f"quarticRefined{c.name}L{leafi}810_impossible"
            hyptype = f"QuarticRefined{c.name}L{leafi}810"
            extra = rex[(c.name, leafi)]
        out = ["set_option maxHeartbeats 64000000 in",
               f"/-- Unowned chamber `{S}` / `{'·'.join(e['argmin'])}`"
               + (f" leaf {leafi}" if leafi is not None else "")
               + f" dies on the `{GREEK_ALL[form]}` face `{d}`. -/",
               f"theorem {thname}",
               f"    ({LOADSIG8} : k)", "    (A B C D E F G : k[X])",
               f"    (hch : {hyptype} A B C D E F G)",
               "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
               "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))",
               f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}",
               "          A B C D E F G).natDegree = 0)"]
        hyps = ["hkap"]
        for f in aux_hyps:
            h, rel = AUXHYP[f]
            hyps.append(h)
            out.append(f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            out.append(f"          A B C D E F G).natDegree {rel})")
        if form not in AUXDEFS and form not in ("kappa", "nu", "omicron",
                                                "primitive"):
            hyps.append(CC.DEG_HYP[form])
            out.append(f"    ({CC.DEG_HYP[form]} : ({CC.FORM_LEAN[form]} {LOADSIG8}")
            out.append("          A B C D E F G).natDegree = 0)")
        killmap[(e["name"], leafi)] = (thname, hyps)
        out[-1] += " :"
        out.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        src = "hch"
        if extra:
            out.append("  obtain ⟨hcell, "
                       + ", ".join(f"hx{t}" for t in range(extra)) + "⟩ := hch")
            src = "hcell"
        out.append(f"  obtain ⟨{', '.join(names)}⟩ := {src}")
        out.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                out.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        if "A" in need:
            out += ["  have hAne : A ≠ 0 := by", "    intro h0",
                    "    have hz0 : A.natDegree = 0 := by simp [h0]",
                    "    clear * - hApos hz0; omega"]
        # the refined-leaf extras `hx…` are not ℕ-degree data this pass can
        # read, so they are always kept; every other keep-list is an exact
        # rational Farkas support
        xtra = tuple(f"hx{t}" for t in range(extra))
        base = (chamber_cons_named(c.nums()) + CONE_CONS + dead_cons(live)
                + NONNEG_CONS)
        withd = base + [("hdpos", CC.lin(d), True)]
        out.append(f"  have hdpos : 0 < {d} := by")
        out += HNC_BLOCK
        for s in sorted(srcs):
            casc, loads, var, extra_h, _needs = UNOWNED_BAND[s]
            vs = ", ".join(var.format(x) for x in loads)
            out.append(f"  obtain ⟨{vs}⟩ :=")
            out.append(f"    {casc} {LOADSIG8}")
            out.append(f"      A B C D E F G hA{extra_h}")
        args, hi = [], 0
        for ld in LOADS:
            v = r["loads"][ld]
            if v["status"] == "empty":
                continue
            recs = [x for cnk in carrier_col_chunks(coords, form, ld)
                    for x in cnk[1]]
            uniq = []
            for x in surviving(recs, live):
                g = deg_expr(x.get("exps") or {})
                if g not in uniq:
                    uniq.append(g)
            hnc = v["status"].endswith("-hnc")
            band = not v["status"].startswith("dominated")
            comps = []
            for g in uniq:
                if hnc and band:
                    # `hnc` here needs this branch's own band disjunct,
                    # so prove it inside the rcases
                    comps.append(HNC_INLINE)
                elif hnc:
                    hn = f"hh{hi}"
                    hi += 1
                    out.append(f"  have {hn} : {g} < {d} := by")
                    out += HNC_BLOCK
                    comps.append(hn)
                else:
                    comps.append("by omega")
            plain = all(x == "by omega" for x in comps)
            if plain:
                kd = keep_str(withd,
                              [CC.target_of(f"{g} < {d}")[0] for g in uniq],
                              xtra)
                conj = ("(by " + (f"clear * - {kd}; " if kd else "")
                        + "omega)")
            else:
                conj = (comps[0] if len(comps) == 1
                        else "⟨" + ", ".join(comps) + "⟩")
            if v["status"].startswith("dominated"):
                args.append(f"(Or.inr {conj})")
                continue
            hn = f"hz{ld}"
            args.append(hn)
            dis = unowned_band_disjuncts(v["source"], ld)
            hv = UNOWNED_BAND[v["source"]][2].format(ld)
            if plain:
                out += band_block(hn, ld, hv, dis, uniq, d, base, withd, live,
                                  always=xtra)
                continue
            out.append(f"  have {hn} : {ld} = 0 ∨ ("
                       + " ∧ ".join(f"{g} < {d}" for g in uniq) + ") := by")
            out.append(f"    rcases {hv} "
                       "with h | " + " | ".join("h" for _ in dis))
            out.append("    · exact Or.inl h")
            for X, _s in dis:
                if X is not None and TOP[ld][X] == "hard":
                    out.append(f"    · exact absurd h{X}z h")
                else:
                    out.append(f"    · exact Or.inr {conj}")
        zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
        seenlf = []
        for x in surv_lf:
            g = deg_expr(x.get("exps") or {})
            if g not in seenlf:
                seenlf.append(g)
        lfa = []
        for g in seenlf:
            kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]],
                          xtra)
            lfa.append("(by " + (f"clear * - {kg}; " if kg else "")
                       + "omega)")
        lfargs = " ".join(lfa)
        rname = f"{form}QuarticChamberRest{p}810"
        out.append(f"  have hrest : ({rname} {LOADSIG8}")
        out.append(f"      A B C D E F G).natDegree < {d} :=")
        out.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
        out.append(f"      A B C D E F G hdpos" + (f" {zargs}" if zargs else "")
                   + (f" {lfargs}" if lfargs else "") + " " + " ".join(args))
        out.append(f"  have hlead : ({form}QuarticChamberFace{p}810 "
                   "A B C D E F G).natDegree =")
        out.append(f"      {d} :=")
        out.append(f"    {nm} A B C D E F G " + " ".join(f"h{L}ne" for L in need))
        if form in AUXDEFS:
            pre = ""
            hargs = aux_le_argstr(form)
            out.append(f"  have hle := {CARRIER_LEAN[form]}_natDegree_le {LOADSIG8}")
            out.append(f"    A B C D E F G {pre}{hargs}")
            tgt = "hle"
        else:
            tgt = (CC.DEG_HYP[form] if form not in ("kappa", "nu", "omicron",
                                                    "primitive")
                   else {"kappa": "hkap", "nu": "hnu", "omicron": "homi",
                         "primitive": "hprim"}[form])
        out.append(f"  rw [{CARRIER_LEAN[form]}_eq_face{p}_add_rest,")
        out.append("    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),"
                   " hlead]")
        out.append(f"    at {tgt}")
        out.append("  omega")
        out.append("")
        blocks.append(prune_arith(name_chamber_facts("\n".join(out))) + "\n")
        nk += 1
    names_out = []
    groups, cur, curlen = [], [], 0
    for b in blocks:
        n = b.count("\n")
        if cur and curlen + n > 2100:
            groups.append(cur)
            cur, curlen = [], 0
        cur.append(b)
        curlen += n
    if cur:
        groups.append(cur)
    groups = groups or [[]]
    for gi, grp in enumerate(groups):
        nm = f"Grok810ScaleZeroQuarticChamberUnownedKills{gi + 1}Scratch"
        doc = (f"# Unowned single-carrier kills, part {gi + 1}/{len(groups)}\n\n"
               f"{len(grp)} of the {nk} chambers `UNOWNED_CHAMBERS.md` closes with a\n"
               "single-monomial face, after the carrier change (including `N₂, N₃,\n"
               "`N₅`, `N₆`) and the `n5-cost`/`n7-cost` bands.  A column marked\n"
               "`*-hnc` is discharged by `by_contra` plus the chamber's ℕ conjuncts,\n"
               "which force every letter constant and contradict `hnc`.\n"
               "Untracked working note.")
        grp = (face_blocks if gi == 0 else []) + grp
        split_decls(nm, f"QuarticChamberUnownedKills{gi + 1}810", doc, grp,
                    prev)
        MODULES.append((nm, sum(b.count("\n") for b in grp),
                        f"{len(grp)} unowned single-carrier kills"))
        names_out.append(nm)
    return names_out, killmap


# ------------------------------------------------- exact band-disjunct verdicts
def band_disjunct_vecs(src, ld):
    """The band's disjuncts as `('lin', vec >= 0)` or `('hard', letter)`."""
    out = []
    if src == "kappa-letter":
        for X in SIG:
            spec = TOP[ld][X]
            if spec == "hard":
                out.append(("hard", X))
            else:
                p, q = spec
                out.append(("lin", CC.sub7(CC.scal7(q, CC.unit(LET.index(X))),
                                           CC.scal7(p, CC.unit(0)))))
        return out
    aux = {"kappa-cost": "kappa", "n2-cost": "n2",
           "n5-cost": "n5", "n7-cost": "n7"}[src]
    cc = n7_cost_conjuncts(ld) if aux == "n7" else cost_conjuncts(aux, ld)
    for m, w in cc:
        out.append(("lin", CC.sub7(CC.scal7(w, CC.unit(0)), CC.cform(m))))
    return out


def _mon_exps(m):
    ex = {}
    for v, p in re.findall(r"([a-g])(?:\^(\d+))?", m):
        ex[v.upper()] = ex.get(v.upper(), 0) + int(p or 1)
    return ex


def _dvec(ex):
    return tuple(int((ex or {}).get(L, 0) or 0) for L in LET)


def _unit(i):
    return tuple(1 if j == i else 0 for j in range(7))


def _lt_or_hnc(cons, dvec, g):
    """`deg g < deg dvec` on `cons`, or on `cons` plus "some letter is not
    constant" (the `hnc` idiom)."""
    if CC.derive(cons, CC.sub7(dvec, g), True) is not None:
        return "dominated"
    c2 = cons + [(CC.sub7(g, dvec), False)]
    if all(CC.derive(c2, tuple(-t for t in _unit(LET.index(X))), False)
           is not None for X in SIG):
        return "hnc"
    return None


def load_verdict(cons, live, dvec, cols, ld, sources):
    """`(status, source)` for one load column, all of it Farkas-certified."""
    if not cols:
        return ("empty", None)
    sts = [_lt_or_hnc(cons, dvec, g) for g in cols]
    if all(s is not None for s in sts):
        return ("dominated-hnc" if "hnc" in sts else "dominated", None)
    if ld not in PUREA:
        return (None, None)
    for src in sources:
        ok = True
        for kind, val in band_disjunct_vecs(src, ld):
            if kind == "hard":
                if val in live:
                    ok = all(s is not None for s in sts)
                    if not ok:
                        break
                continue
            c2 = cons + [(val, False)]
            if not CC.feasible(c2):
                continue                      # vacuous disjunct: `omega` closes
            for g, s in zip(cols, sts):
                if s is not None:
                    continue
                if _lt_or_hnc(c2, dvec, g) is None:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return ("band-hnc" if "hnc" in sts else "band", src)
    return (None, None)


BAND_ORDER = ["kappa-letter", "kappa-cost", "n2-cost", "n5-cost", "n7-cost"]


def refined_leaf_conjuncts():
    """`(cell, leaf) -> the extra conjuncts of module 30's `QuarticRefined…`
    Prop`.  The cell's JSON `conjuncts` alone are strictly weaker (they are the
    parent cell), so every verdict must be taken against cell + these."""
    txt = (ROOT / "Grok810ScaleZeroQuarticChamberRefineScratch.lean").read_text()
    out = {}
    for m in re.finditer(r"^def QuarticRefined(\w+?)L(\d+)810 \(A B C D E F G : "
                         r"k\[X\]\) : Prop :=\n((?:.*\n)*?)\n", txt, re.M):
        body = m.group(3)
        parts = [x.strip() for x in body.split("∧")]
        out[(m.group(1), int(m.group(2)))] = [x for x in parts[1:] if x]
    return out


_REFCJ = None


def entry_cons(cham, e):
    """The sub-chamber constraints of a plan entry (cell or refined leaf),
    with the dead letters pinned to zero."""
    global _REFCJ
    c = cham[e["name"]]
    live = set(e["live"])
    cj = (c.leaves[e["leaf"]]["conjuncts"] if e.get("leaf") is not None
          else c.conjuncts)
    cons = list(CC.chamber_cons(cj))
    if e.get("leaf") is not None:
        if _REFCJ is None:
            _REFCJ = refined_leaf_conjuncts()
        for x in _REFCJ.get((c.name, e["leaf"]), []):
            cons += CC.constraints_of(x)
    for X in SIG:
        if X not in live:
            cons.append((tuple(-t for t in _unit(LET.index(X))), False))
    return cons, live


def certify_plan(coords, chambers, plan):
    """Re-decide every load column of every `single` entry with the exact
    Farkas machinery, band disjuncts included, and drop the entries whose
    recorded verdict does not hold.  Nothing is emitted on the plan's word."""
    cham = {c.name: c for c in chambers}
    out = {"packets": plan["packets"], "chambers": [], "leaves": [],
           "open": plan.get("open", [])}
    dropped = []
    for key in ("chambers", "leaves"):
        for e in plan[key]:
            if e["mode"] != "single":
                out[key].append(e)
                continue
            cons, live = entry_cons(cham, e)
            r = dict(e["carriers"][0])
            face, _rest = unowned_face(coords, r["carrier"], r["face"])
            df = _dvec(face[0].get("exps"))
            loads, bad = {}, None
            for ld in LOADS:
                cols = [_dvec(x.get("exps")) for x in surviving(
                    [y for cnk in carrier_col_chunks(coords, r["carrier"], ld)
                     for y in cnk[1]], live)]
                srcs = [r["loads"][ld].get("source")] if r["loads"].get(
                    ld, {}).get("source") else []
                srcs += [s for s in BAND_ORDER if s not in srcs]
                st, src = load_verdict(cons, live, df, cols, ld, srcs)
                if st is None:
                    bad = (r["carrier"], ld)
                    break
                loads[ld] = ({"status": st} if src is None
                             else {"status": st, "source": src})
            if bad:
                dropped.append((e["name"], e.get("leaf"), "single", bad))
                continue
            r["loads"] = loads
            f = dict(e)
            f["carriers"] = [r]
            out[key].append(f)
    return out, dropped


# ------------- the 48 multi-carrier top-coefficient systems
def poly_lean(expr, var):
    """A `sympy`-parsed rational polynomial in `a..g` as a Lean term over `k`,
    with `var` naming the Lean variable that plays the letter `X`."""
    import sympy as sp
    syms = [sp.Symbol(c) for c in "abcdefg"]
    e = sp.expand(sp.sympify(str(expr).replace("^", "**"),
                             locals={s.name: s for s in syms}))
    if e == 0:
        return "0"
    out = []
    for mono, coef in sp.Poly(e, *syms).terms():
        c = sp.Rational(coef)
        n, dd = int(c.p), int(c.q)
        head = f"({n} : k)" if dd == 1 else f"({n} / {dd} : k)"
        fac = [head]
        for i, ex in enumerate(mono):
            if ex == 1:
                fac.append(var(LET[i]))
            elif ex > 1:
                fac.append(f"{var(LET[i])} ^ {ex}")
        out.append(" * ".join(fac))
    return " + ".join(out)


def target_factors(target):
    import sympy as sp
    syms = {s.name: s for s in sp.symbols("a b c d e f g")}
    d = sp.sympify(target.replace("^", "**"), locals=syms).as_powers_dict()
    return [(L, int(d.get(syms[L.lower()], 0))) for L in LET
            if int(d.get(syms[L.lower()], 0)) > 0]


def target_ne_term(target, hname):
    """`mul_ne_zero (…) (…)` proving the Lean product `target_lean` is ≠ 0."""
    fac = target_factors(target)

    def leaf(L, e):
        h = hname(L)
        return h if e == 1 else f"(pow_ne_zero {e} {h})"
    acc = leaf(*fac[0])
    for L, e in fac[1:]:
        acc = f"(mul_ne_zero {acc} {leaf(L, e)})"
    return acc


KDEG_ALL = {"kappa": 0, "mu": 0, "nu": 0, "xi": 0, "omicron": 0, "pi": 0,
            "primitive": 1, "n2": 1, "n3": 1, "n4": 1, "n5": 2, "n6": 2,
            "n7": 3}
CARRIER_ORDER = ["kappa", "mu", "xi", "pi", "nu", "omicron", "n2", "n3",
                 "n5", "n6", "primitive", "n4", "n7"]
DEGHYP_ALL = {"kappa": ("hkap", "= 0"), "nu": ("hnu", "= 0"),
              "omicron": ("homi", "= 0"), "primitive": ("hprim", "= 1"),
              "mu": ("hmuDeg", "= 0"), "xi": ("hxiDeg", "= 0"),
              "pi": ("hpiDeg", "= 0")}
HYP_ORDER = ["kappa", "primitive", "omicron", "nu", "mu", "xi", "pi"]


def system_entries(coords, chambers, plan):
    """The 48 systems as `single`-shaped records — one synthesised face packet
    per (carrier, face) with an exact Farkas verdict on every load column and
    on the carrier's own `k·a < deg(face)` side condition.  Entries with a
    column that is neither dominated, `hnc`-dominated nor banded are dropped
    (and reported), never emitted on a guess."""
    cham = {c.name: c for c in chambers}
    pid, ids = collections.Counter(), {}
    out, dropped = [], []
    for e in [x for x in plan["chambers"] + plan["leaves"]
              if x["mode"] == "system"]:
        c = cham[e["name"]]
        cons, live = entry_cons(cham, e)
        recs, bad = [], None
        for cr in e["system_carriers"]:
            r = e["rows"][cr]
            want = {tuple(_mon_exps(t["mon"]).get(L, 0) for L in LET)
                    for t in r["terms"]}
            lf = carrier_lf_records(coords, cr)
            face = [x for x in lf if _dvec(x.get("exps")) in want]
            df = _dvec(face[0].get("exps"))
            key = (cr, frozenset(_dvec(x.get("exps")) for x in face))
            if key not in ids:
                ids[key] = 6000 + pid[cr]
                pid[cr] += 1
            k = KDEG_ALL[cr]
            side = CC.sub7(df, tuple(k * t for t in _unit(0)))
            hncside = CC.derive(cons, side, True) is None
            if hncside:
                c2 = cons + [(CC.sub7(tuple(k * t for t in _unit(0)), df),
                              False)]
                if not all(CC.derive(c2, tuple(-t for t in
                                               _unit(LET.index(X))),
                                     False) is not None for X in SIG):
                    bad = (cr, "side", r["T"])
                    break
            loads = {}
            for ld in LOADS:
                cols = [_dvec(x.get("exps")) for x in surviving(
                    [y for cnk in carrier_col_chunks(coords, cr, ld)
                     for y in cnk[1]], live)]
                srcs = ([r["bands"][ld]] if ld in r["bands"] else [])
                srcs += [x for x in BAND_ORDER if x not in srcs]
                st, src = load_verdict(cons, live, df, cols, ld, srcs)
                if st is None:
                    bad = (cr, "load", ld)
                    break
                loads[ld] = ({"status": st} if src is None
                             else {"status": st, "source": src})
            if bad:
                break
            recs.append({"carrier": cr, "packet": ids[key],
                         "d": deg_expr(face[0].get("exps") or {}),
                         "k": k, "kside_hnc": hncside,
                         "face": [list(_dvec(x.get("exps"))) for x in face],
                         "loads": loads})
        if bad:
            dropped.append((e["name"], e["leaf"], bad))
            continue
        f = dict(e)
        f["mode"] = "single"
        f["carriers"] = recs
        out.append(f)
    return out, dropped


def emit_unowned_systems(coords, chambers, entries, packets, have, prev):
    """The multi-carrier top-coefficient systems of `UNOWNED_CHAMBERS.md` §3.3:
    one `_coeff_top` bridge per face packet, one Singular-lifted scalar
    certificate per chamber, and the chamber kill that joins them."""
    cham = {c.name: c for c in chambers}
    rex = refined_leaf_extra()
    bblocks = []
    bridge = {}
    for e in entries:
        for ci, r in enumerate(e["carriers"]):
            form, p = r["carrier"], r["packet"]
            if (form, p) in bridge:
                continue
            face, _rest = unowned_face(coords, form, packets[(form, p)]["face"])
            d = deg_expr(face[0].get("exps") or {})
            nm = f"{form}QuarticChamberFace{p}810_coeff_top"
            poly = poly_lean(e["row_polynomials"][ci], lambda L: LC[L])
            bridge[(form, p)] = (nm, d, face, poly)
            if nm in have:
                continue
            bblocks.append(coeff_top_lemma(form, p, face, d, nm, poly))
    blocks, nk, killmap = [], 0, {}
    for e in entries:
        c = cham[e["name"]]
        S, live = e["live"], set(e["live"])
        leafi = e.get("leaf")
        stem = f"{c.name}" + (f"L{leafi}" if leafi is not None else "")
        cert = f"quarticUnownedSystem{stem}810_cert"
        tf = target_factors(e["target"])
        out = ["set_option maxHeartbeats 64000000 in",
               f"/-- The Singular-lifted certificate of chamber `{S}` / "
               f"`{'·'.join(e['argmin'])}`"
               + (f" leaf {leafi}" if leafi is not None else "")
               + f": the {len(e['carriers'])} face rows force "
               f"`{target_lean(e['target'])} = 0`. -/",
               f"theorem {cert}", "    (a b c d e f g : k)"]
        for i, rp in enumerate(e["row_polynomials"]):
            out.append(f"    (hr{i} : {poly_lean(rp, lambda L: L.lower())} = 0)")
        for L, _n in tf:
            out.append(f"    (h{L}c : ({L.lower()} : k) ≠ 0)")
        out[-1] += " :"
        out.append("    False := by")
        # the Singular lift is sparse: most rows carry a zero cofactor and
        # contribute nothing to the certificate.  The kill below derives only
        # the rows it actually combines - deriving a carrier row costs a rest
        # bound, a band disjunction per load and a top-coefficient rewrite,
        # all of which then sit in every later arithmetic context.
        used = [i for i, co in enumerate(e["cofactors"])
                if str(co).strip() not in ("0", "")]
        comb = [f"({poly_lean(e['cofactors'][i], lambda L: L.lower())}) "
                f"* hr{i}" for i in used]
        out.append(f"  have ht : {target_lean(e['target'])} = 0 := by")
        out.append("    linear_combination " + " + ".join(comb))
        out.append(f"  exact {target_ne_term(e['target'], lambda L: f'h{L}c')} ht")
        out.append("")
        certblk = "\n".join(out) + "\n"
        # ---- the chamber kill
        if leafi is None:
            thname = f"quarticChamber{c.name}810_impossible"
            hyptype = c.defname
            extra = 0
        else:
            thname = f"quarticRefined{c.name}L{leafi}810_impossible"
            hyptype = f"QuarticRefined{c.name}L{leafi}810"
            extra = rex[(c.name, leafi)]
        srcs = set()
        for r in e["carriers"]:
            srcs |= {v.get("source") for v in r["loads"].values()
                     if v["status"].startswith("band")}
        needf = []
        for r in e["carriers"]:
            f = r["carrier"]
            for x in (AUXNEEDS[f] if f in AUXDEFS else [f]):
                if x not in needf:
                    needf.append(x)
        for s in sorted(srcs):
            for x in UNOWNED_BAND[s][4]:
                if x not in needf:
                    needf.append(x)
        needf = [f for f in HYP_ORDER if f in needf or f == "kappa"]
        k = ["set_option maxHeartbeats 64000000 in",
             f"/-- Unowned chamber `{S}` / `{'·'.join(e['argmin'])}`"
             + (f" leaf {leafi}" if leafi is not None else "")
             + f" dies on the {len(e['carriers'])}-carrier system "
             + "(" + ", ".join(GREEK_ALL[r["carrier"]]
                               for r in e["carriers"]) + "). -/",
             f"theorem {thname}", f"    ({LOADSIG8} : k)",
             "    (A B C D E F G : k[X])",
             f"    (hch : {hyptype} A B C D E F G)",
             "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
             "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))"]
        for f in needf:
            h, rel = DEGHYP_ALL[f]
            k.append(f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            k.append(f"          A B C D E F G).natDegree {rel})")
        killmap[(e["name"], leafi)] = (thname,
                                       [DEGHYP_ALL[f][0] for f in needf])
        k[-1] += " :"
        k.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        src = "hch"
        if extra:
            k.append("  obtain ⟨hcell, "
                     + ", ".join(f"hx{t}" for t in range(extra)) + "⟩ := hch")
            src = "hcell"
        k.append(f"  obtain ⟨{', '.join(names)}⟩ := {src}")
        k.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                k.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        k += ["  have hAne : A ≠ 0 := by", "    intro h0",
              "    have hz0 : A.natDegree = 0 := by simp [h0]",
              "    clear * - hApos hz0; omega"]
        # the refined-leaf extras `hx…` are not ℕ-degree data this pass can
        # read, so they are always kept; every other keep-list is an exact
        # rational Farkas support
        xtra = tuple(f"hx{tt}" for tt in range(extra))
        base = (chamber_cons_named(c.nums()) + CONE_CONS + dead_cons(live)
                + NONNEG_CONS)
        for s in sorted(srcs):
            casc, loads, var, ex, _n = UNOWNED_BAND[s]
            k.append("  obtain ⟨" + ", ".join(var.format(x) for x in loads)
                     + "⟩ :=")
            k.append(f"    {casc} {LOADSIG8}")
            k.append(f"      A B C D E F G hA{ex}")
        hi = 0
        for ci, r in enumerate(e["carriers"]):
            if ci not in used:
                continue
            form, p = r["carrier"], r["packet"]
            nm, d, face, _poly = bridge[(form, p)]
            _f, rest = unowned_face(coords, form, packets[(form, p)]["face"])
            surv_lf = surviving(rest, live)
            lhs = "0" if r["k"] == 0 else (
                "A.natDegree" if r["k"] == 1 else f"{r['k']} * A.natDegree")
            k.append(f"  have hdp{ci} : {lhs} < {d} := by")
            if r["kside_hnc"]:
                k += HNC_BLOCK
            else:
                k.append("    omega")
            # the rest lemmas bind `hdpos : 0 < d`; the k-side fact
            # above is stronger but is not that statement
            k.append(f"  have hdz{ci} : 0 < {d} := by omega")
            withd = base + [(f"hdz{ci}", CC.lin(d), True)]
            args = []
            for ld in LOADS:
                v = r["loads"][ld]
                if v["status"] == "empty":
                    continue
                cols = [x for cnk in carrier_col_chunks(coords, form, ld)
                        for x in cnk[1]]
                uniq = []
                for x in surviving(cols, live):
                    g = deg_expr(x.get("exps") or {})
                    if g not in uniq:
                        uniq.append(g)
                comps = []
                band = not v["status"].startswith("dominated")
                for g in uniq:
                    if v["status"].endswith("-hnc") and band:
                        # `hnc` here needs this branch's own band
                        # disjunct, so prove it inside the rcases
                        comps.append(HNC_INLINE)
                    elif v["status"].endswith("-hnc"):
                        hn = f"hh{hi}"
                        hi += 1
                        k.append(f"  have {hn} : {g} < {d} := by")
                        k += HNC_BLOCK
                        comps.append(hn)
                    else:
                        comps.append("by omega")
                plain = all(x == "by omega" for x in comps)
                if plain:
                    kd = keep_str(withd,
                                  [CC.target_of(f"{g} < {d}")[0] for g in uniq],
                                  xtra)
                    conj = ("(by " + (f"clear * - {kd}; " if kd else "")
                            + "omega)")
                else:
                    conj = (comps[0] if len(comps) == 1
                            else "⟨" + ", ".join(comps) + "⟩")
                if v["status"].startswith("dominated"):
                    args.append(f"(Or.inr {conj})")
                    continue
                hn = f"hz{ci}{ld}"
                args.append(hn)
                dis = unowned_band_disjuncts(v["source"], ld)
                hv = UNOWNED_BAND[v["source"]][2].format(ld)
                if plain:
                    k += band_block(hn, ld, hv, dis, uniq, d, base, withd,
                                    live, always=xtra)
                    continue
                k.append(f"  have {hn} : {ld} = 0 ∨ ("
                         + " ∧ ".join(f"{g} < {d}" for g in uniq) + ") := by")
                k.append(f"    rcases {hv} "
                         "with h | " + " | ".join("h" for _ in dis))
                k.append("    · exact Or.inl h")
                for X, _s in dis:
                    if X is not None and TOP[ld][X] == "hard":
                        k.append(f"    · exact absurd h{X}z h")
                    else:
                        k.append(f"    · exact Or.inr {conj}")
            zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
            seenlf = []
            for x in surv_lf:
                g = deg_expr(x.get("exps") or {})
                if g not in seenlf:
                    seenlf.append(g)
            lfa = []
            for g in seenlf:
                kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]], xtra)
                lfa.append("(by " + (f"clear * - {kg}; " if kg else "")
                           + "omega)")
            lfargs = " ".join(lfa)
            rname = f"{form}QuarticChamberRest{p}810"
            k.append(f"  have hr{ci} : ({rname} {LOADSIG8}")
            k.append(f"      A B C D E F G).natDegree < {d} :=")
            k.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
            k.append(f"      A B C D E F G hdz{ci}"
                     + (f" {zargs}" if zargs else "")
                     + (f" {lfargs}" if lfargs else "")
                     + (" " + " ".join(args) if args else ""))
            ne = sorted({L for x in face for L in LET
                         if int((x.get("exps") or {}).get(L, 0) or 0) > 0},
                        key=LET.index)
            tie = " ".join("(by omega)" for _ in face[1:])
            k.append(f"  have hct{ci} := {nm} "
                     + " ".join(f"h{L}ne" if L != "A" else "hAne" for L in ne)
                     + coeff_top_named(ne) + (f" {tie}" if tie else ""))
            k.append(f"  have hq{ci} : ({CARRIER_LEAN[form]} {LOADSIG8}")
            k.append(f"      A B C D E F G).coeff ({d}) = 0 := by")
            k.append("    apply coeff_eq_zero_of_natDegree_lt")
            if form in AUXDEFS:
                pre = ""
                hargs = aux_le_argstr(form)
                k.append(f"    have hle := {CARRIER_LEAN[form]}_natDegree_le "
                         f"{LOADSIG8}")
                k.append(f"      A B C D E F G {pre}{hargs}")
                k.append("    omega")
            else:
                k.append(f"    rw [{DEGHYP_ALL[form][0]}]")
                k.append("    omega")
            k.append(f"  rw [{CARRIER_LEAN[form]}_eq_face{p}_add_rest,")
            k.append(f"    coeff_add, coeff_eq_zero_of_natDegree_lt hr{ci},")
            k.append(f"    add_zero] at hq{ci}")
            k.append(f"  have hin{ci} : {bridge[(form, p)][3]} = 0 :=")
            k.append(f"    hct{ci}.symm.trans hq{ci}")
        for L, _n in target_factors(e["target"]):
            s2 = "hAne" if L == "A" else f"h{L}ne"
            k.append(f"  have h{L}c : {L}.leadingCoeff ≠ 0 := "
                     f"leadingCoeff_ne_zero.mpr {s2}")
        # the same scalar identity as `cert`, instantiated here on the rows
        # that were derived; `cert` itself is unchanged and still checked.
        k.append(f"  have ht : {target_lean(e['target'], LC.get)} = 0 := by")
        k.append("    linear_combination "
                 + " + ".join(f"({poly_lean(e['cofactors'][i], LC.get)}) "
                              f"* hin{i}" for i in used))
        k.append(f"  exact {target_ne_term(e['target'], lambda L: f'h{L}c')} "
                 "ht")
        k.append("")
        blocks.append([certblk,
                       prune_arith(name_chamber_facts("\n".join(k))) + "\n"])
        nk += 1
    bparts, bcur, bcurl = [], [], 0
    for blk in bblocks:
        n = blk.count("\n")
        if bcur and bcurl + n > 2100:
            bparts.append(bcur)
            bcur, bcurl = [], 0
        bcur.append(blk)
        bcurl += n
    if bcur:
        bparts.append(bcur)
    bnames = []
    for bi, bgrp in enumerate(bparts or [[]]):
        bname = ("Grok810ScaleZeroQuarticChamberUnownedSystemBridgesScratch"
                 if len(bparts) <= 1 else
                 f"Grok810ScaleZeroQuarticChamberUnownedSystemBridges{bi + 1}"
                 "Scratch")
        bsec = ("QuarticChamberUnownedSystemBridges810" if len(bparts) <= 1
                else f"QuarticChamberUnownedSystemBridges{bi + 1}810")
        bdoc = ("# `_coeff_top` bridges for the unowned systems, part "
                f"{bi + 1}/{max(len(bparts), 1)}\n\n"
                f"{len(bgrp)} of the {len(bridge)} top-coefficient bridges, "
                "one per (carrier,\nface packet) the multi-carrier systems "
                "use.  Untracked working note.")
        bout = (header(prev, bdoc) + f"section {bsec}\n\n"
                + "/-! ## Top-coefficient bridges -/\n\n" + "".join(bgrp)
                + f"\nend {bsec}\n" + FOOTER)
        bln = write(bname + ".lean", bout)
        MODULES.append((bname, bln, f"{len(bgrp)} `_coeff_top` bridges for the "
                                    "unowned systems"))
        bnames.append(bname)
    prev = list(prev) + bnames
    names_out = list(bnames)
    groups, cur, curlen = [], [], 0
    for b in blocks:
        n = sum(x.count("\n") for x in b)
        if cur and curlen + n > 1800:
            groups.append(cur)
            cur, curlen = [], 0
        cur.append(b)
        curlen += n
    if cur:
        groups.append(cur)
    for gi, grp in enumerate(groups or [[]]):
        grp = [x for pair in grp for x in pair]
        nm = f"Grok810ScaleZeroQuarticChamberUnownedSystems{gi + 1}Scratch"
        doc = (f"# Unowned multi-carrier systems, part {gi + 1}/"
               f"{len(groups)}\n\n"
               f"{len(grp)} of the {nk} chambers `UNOWNED_CHAMBERS.md` §3.3 "
               "closes with a\nSingular-lifted top-coefficient system.  Every "
               "load column of every row\ncarries an exact rational Farkas "
               "verdict (`dominated`, `dominated-hnc` or\na named band).\n"
               "Untracked working note.")
        sec = f"QuarticChamberUnownedSystems{gi + 1}810"
        split_decls(nm, sec, doc, grp, prev)
        MODULES.append((nm, sum(b.count("\n") for b in grp),
                        f"{len(grp) // 2} unowned multi-carrier system kills"))
        names_out.append(nm)
    return names_out, killmap


# ------------- the `n_X = 0` splits and the load trichotomies
def branch_record(coords, form, live, cons, pid, ids):
    """A `single`-shaped carrier record for `form` on a sub-chamber, or None
    when a load column has no exact verdict."""
    recs = surviving(carrier_lf_records(coords, form), live)
    if not recs:
        return None
    face = [x for x in recs
            if all(CC.derive(cons, CC.sub7(_dvec(x.get("exps")),
                                           _dvec(y.get("exps"))), False)
                   is not None for y in recs if y is not x)]
    if not face:
        return None
    df = _dvec(face[0].get("exps"))
    key = (form, frozenset(_dvec(x.get("exps")) for x in face))
    if key not in ids:
        ids[key] = 7000 + pid[form]
        pid[form] += 1
    k = KDEG_ALL[form]
    side = CC.sub7(df, tuple(k * t for t in _unit(0)))
    hncside = CC.derive(cons, side, True) is None
    if hncside:
        c2 = cons + [(CC.sub7(tuple(k * t for t in _unit(0)), df), False)]
        if not all(CC.derive(c2, tuple(-t for t in _unit(LET.index(X))),
                             False) is not None for X in SIG):
            return None
    loads = {}
    for ld in LOADS:
        cols = [_dvec(x.get("exps")) for x in surviving(
            [y for cnk in carrier_col_chunks(coords, form, ld)
             for y in cnk[1]], live)]
        st, src = load_verdict(cons, live, df, cols, ld, BAND_ORDER)
        if st is None:
            return None
        loads[ld] = {"status": st} if src is None else {"status": st,
                                                        "source": src}
    return {"carrier": form, "packet": ids[key], "k": k, "kside_hnc": hncside,
            "d": deg_expr(face[0].get("exps") or {}),
            "face": [list(_dvec(x.get("exps"))) for x in face],
            "loads": loads}


def split_entries(coords, chambers, plan):
    """The `n_X = 0` splits and the load trichotomies whose every branch is a
    plain single-carrier kill.  Branches of kind `loadkill` or `system` are
    not emitted (they need their own proof shape) and the entry is dropped."""
    cham = {c.name: c for c in chambers}
    pid, ids = collections.Counter(), {}
    out, dropped = [], []
    for e in [x for x in plan["chambers"] + plan["leaves"]
              if x["mode"] in ("split", "trichotomy")]:
        c = cham[e["name"]]
        base, live = entry_cons(cham, e)
        brs, bad = [], None
        if e["mode"] == "split":
            lets = e["split"]["letters"]
            for bits in itertools.product([1, 0], repeat=len(lets)):
                tag = ",".join(f"n_{X}" + (">0" if b else "=0")
                               for X, b in zip(lets, bits))
                form = e["split"]["branches"].get(tag)
                if not isinstance(form, str):
                    bad = tag
                    break
                extra = []
                for X, b in zip(lets, bits):
                    u = _unit(LET.index(X))
                    extra.append((u, True) if b
                                 else (tuple(-t for t in u), False))
                r = branch_record(coords, form, live, base + extra, pid, ids)
                if r is None:
                    bad = tag
                    break
                brs.append((list(zip(lets, bits)), r))
        else:
            pv = e["pivot"]
            lhs, rhs = [x.strip() for x in pv["comparison"].split("<")]
            u, v = CC.lin(lhs), CC.lin(rhs)
            for tag, extra in (("<", [(CC.sub7(v, u), True)]),
                               ("=", [(CC.sub7(v, u), False),
                                      (CC.sub7(u, v), False)]),
                               (">", [(CC.sub7(u, v), True)])):
                br = pv["branches"][tag]
                if br.get("kind") != "single":
                    bad = f"{tag}:{br.get('kind')}"
                    break
                r = branch_record(coords, br["carrier"], live, base + extra,
                                  pid, ids)
                if r is None:
                    bad = tag
                    break
                brs.append((tag, r))
        if bad:
            dropped.append((e["name"], e["mode"], bad))
            continue
        f = dict(e)
        f["kind"] = e["mode"]
        f["mode"] = "single"
        f["carriers"] = [r for _t, r in brs]
        f["branches"] = brs
        out.append(f)
    return out, dropped


def face_degree_lemma(coords, form, p, packets, have, seen):
    """The `natDegree` of a one-term face packet (the `_natDegree` shape)."""
    face, _rest = unowned_face(coords, form, packets[(form, p)]["face"])
    exps = face[0].get("exps") or {}
    d = deg_expr(exps)
    chain, need, haspow = mono_ne(exps)
    nm = f"{form}QuarticChamberFace{p}810_natDegree"
    if nm in have or nm in seen:
        return "", nm, need, d, face
    if len(face) > 1:
        # A multi-monomial face has no standalone `_natDegree`: its degree is
        # pinned only under the cell's inequalities, which this lemma's `≠ 0`
        # hypotheses do not carry.  Kills on such a packet go through the
        # `_coeff_top` bridge instead; emitting the single-monomial shape here
        # would `rw [natDegree_smul …]` against a sum.
        return "", nm, need, d, face
    seen.add(nm)
    qn, qd = int(face[0]["qn"]), int(face[0]["qd"])
    coef = (f"({qn} / {qd} : k)" if qd != 1 else f"({qn} : k)")
    if qn < 0:
        coef = (f"(-({-qn} / {qd} : k))" if qd != 1 else f"(-({-qn} : k))")
    out = ["set_option maxHeartbeats 64000000 in", f"theorem {nm}",
           "    (A B C D E F G : k[X])"]
    for L in need:
        out.append(f"    (h{L}ne : {L} ≠ 0)")
    out[-1] += " :"
    out.append(f"    ({form}QuarticChamberFace{p}810 A B C D E F G).natDegree =")
    out.append(f"      {d} := by")
    out.append(f"  have hc : {coef} ≠ 0 := by norm_num")
    out.append(f"  simp only [{form}QuarticChamberFace{p}810]")
    out.append("  rw [natDegree_smul _ hc" + "".join(f", {c}" for c in chain) + "]")
    if haspow:
        out.append("  simp only [natDegree_pow]")
    out.append("  all_goals omega")
    out.append("")
    return "\n".join(out) + "\n", nm, need, d, face


def branch_kill_lines(coords, S, live, r, packets, facedeg, ind, base=None):
    """The body of a single-carrier kill on one sub-chamber, indented.

    `base` is the exact-LP context of the enclosing chamber (see
    `chamber_cons_named`); when it is given, every band column whose conjuncts
    are all plain `omega` goes through `band_block`, which keeps only a Farkas
    support and proves the 7-/21-way band into the head of the column.  A
    branch whose obligation needs the tree's own path values has no
    certificate over `base`, so it falls back to the plain `omega` that
    `prune_arith` then prunes by scope."""
    form, p, d = r["carrier"], r["packet"], r["d"]
    nm, need, _d, face = facedeg[(form, p)]
    _f, rest = unowned_face(coords, form, packets[(form, p)]["face"])
    surv_lf = surviving(rest, live)
    o = []
    lhs = "0" if r["k"] == 0 else ("A.natDegree" if r["k"] == 1
                                   else f"{r['k']} * A.natDegree")
    o.append(f"have hdpos : {lhs} < {d} := by")
    o += (["  " + x.strip() for x in HNC_BLOCK] if r["kside_hnc"]
          else ["  omega"])
    o.append(f"have hdzpos : 0 < {d} := by omega")
    withd = (base + [("hdzpos", CC.lin(d), True)]) if base else None
    srcs = sorted({v.get("source") for v in r["loads"].values()
                   if v["status"].startswith("band")})
    for s in srcs:
        casc, loads, var, ex, _n = UNOWNED_BAND[s]
        o.append("obtain ⟨" + ", ".join(var.format(x) for x in loads) + "⟩ :=")
        o.append(f"  {casc} {LOADSIG8}")
        o.append(f"    A B C D E F G hA{ex}")
    args, hi = [], 0
    for ld in LOADS:
        v = r["loads"][ld]
        if v["status"] == "empty":
            continue
        if v["status"] == "zero":
            args.append(f"(Or.inl hzero{ld})")
            continue
        cols = [x for cnk in carrier_col_chunks(coords, form, ld)
                for x in cnk[1]]
        uniq = []
        for x in surviving(cols, live):
            g = deg_expr(x.get("exps") or {})
            if g not in uniq:
                uniq.append(g)
        comps = []
        band = not v["status"].startswith("dominated")
        for g in uniq:
            if v["status"].endswith("-hnc") and band:
                # `hnc` here needs this branch's own band disjunct,
                # so prove it inside the rcases
                comps.append(HNC_INLINE)
            elif v["status"].endswith("-hnc"):
                hn = f"hh{hi}"
                hi += 1
                o.append(f"have {hn} : {g} < {d} := by")
                o += ["  " + x.strip() for x in HNC_BLOCK]
                comps.append(hn)
            else:
                comps.append("by omega")
        plain = all(x == "by omega" for x in comps)
        if plain and withd:
            kd = keep_str(withd, [CC.target_of(f"{g} < {d}")[0] for g in uniq])
            conj = "(by " + (f"clear * - {kd}; " if kd else "") + "omega)"
        elif plain:
            conj = "(by omega)"
        else:
            conj = (comps[0] if len(comps) == 1
                    else "⟨" + ", ".join(comps) + "⟩")
        if v["status"].startswith("dominated"):
            args.append(f"(Or.inr {conj})")
            continue
        hn = f"hz{ld}"
        args.append(hn)
        dis = unowned_band_disjuncts(v["source"], ld)
        hv = UNOWNED_BAND[v["source"]][2].format(ld)
        if plain and withd:
            o += band_block(hn, ld, hv, dis, uniq, d, base, withd, live,
                            ind="")
            continue
        o.append(f"have {hn} : {ld} = 0 ∨ ("
                 + " ∧ ".join(f"{g} < {d}" for g in uniq) + ") := by")
        o.append(f"  rcases {hv} with h | "
                 + " | ".join("h" for _ in dis))
        o.append("  · exact Or.inl h")
        for X, _s in dis:
            if X is not None and TOP[ld][X] == "hard":
                o.append(f"  · exact absurd h{X}z h")
            else:
                o.append(f"  · exact Or.inr {conj}")
    zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
    seenlf = []
    for x in surv_lf:
        g = deg_expr(x.get("exps") or {})
        if g not in seenlf:
            seenlf.append(g)
    lfa = []
    for g in seenlf:
        kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]]) if withd else None
        lfa.append("(by " + (f"clear * - {kg}; " if kg else "") + "omega)")
    lfargs = " ".join(lfa)
    rname = f"{form}QuarticChamberRest{p}810"
    o.append(f"have hrest : ({rname} {LOADSIG8}")
    o.append(f"    A B C D E F G).natDegree < {d} :=")
    o.append(f"  {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
    o.append(f"    A B C D E F G hdzpos" + (f" {zargs}" if zargs else "")
             + (f" {lfargs}" if lfargs else "")
             + (" " + " ".join(args) if args else ""))
    o.append(f"have hlead : ({form}QuarticChamberFace{p}810 "
             "A B C D E F G).natDegree =")
    o.append(f"    {d} :=")
    o.append(f"  {nm} A B C D E F G "
             + " ".join(f"h{L}ne" if L != "A" else "hAne" for L in need))
    if form in AUXDEFS:
        pre = ""
        hargs = aux_le_argstr(form)
        o.append(f"have hle := {CARRIER_LEAN[form]}_natDegree_le {LOADSIG8}")
        o.append(f"  A B C D E F G {pre}{hargs}")
        tgt = "hle"
    else:
        tgt = DEGHYP_ALL[form][0]
    o.append(f"rw [{CARRIER_LEAN[form]}_eq_face{p}_add_rest,")
    o.append("  natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]")
    o.append(f"  at {tgt}")
    o.append("omega")
    return [ind + x for x in o]


def emit_unowned_splits(coords, chambers, entries, packets, have, prev):
    """The `n_X = 0` splits and the load trichotomies: one `by_cases` /
    `lt_trichotomy` per chamber, a single-carrier kill on every branch."""
    cham = {c.name: c for c in chambers}
    body, facedeg, seen = "/-! ## Face degrees -/\n\n", {}, set()
    for e in entries:
        for r in e["carriers"]:
            t, nm, need, d, face = face_degree_lemma(
                coords, r["carrier"], r["packet"], packets, have, seen)
            body += t
            facedeg[(r["carrier"], r["packet"])] = (nm, need, d, face)
    body += "/-! ## The split and trichotomy kills -/\n\n"
    nk, killmap = 0, {}
    for e in entries:
        c = cham[e["name"]]
        S, live = e["live"], set(e["live"])
        needf, srcs = [], set()
        for r in e["carriers"]:
            f = r["carrier"]
            for x in (AUXNEEDS[f] if f in AUXDEFS else [f]):
                if x not in needf:
                    needf.append(x)
            srcs |= {v.get("source") for v in r["loads"].values()
                     if v["status"].startswith("band")}
        for s in sorted(srcs):
            for x in UNOWNED_BAND[s][4]:
                if x not in needf:
                    needf.append(x)
        needf = [f for f in HYP_ORDER if f in needf or f == "kappa"]
        o = ["set_option maxHeartbeats 64000000 in",
             f"/-- Unowned chamber `{S}` / `{'·'.join(e['argmin'])}` dies on a "
             + ("letter split" if e["kind"] == "split" else "load trichotomy")
             + f" with {len(e['carriers'])} branches. -/",
             f"theorem quarticChamber{c.name}810_impossible",
             f"    ({LOADSIG8} : k)", "    (A B C D E F G : k[X])",
             f"    (hch : {c.defname} A B C D E F G)",
             "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
             "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))"]
        for f in needf:
            h, rel = DEGHYP_ALL[f]
            o.append(f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            o.append(f"          A B C D E F G).natDegree {rel})")
        killmap[(e["name"], None)] = (
            f"quarticChamber{c.name}810_impossible",
            [DEGHYP_ALL[f][0] for f in needf])
        o[-1] += " :"
        o.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        o.append(f"  obtain ⟨{', '.join(names)}⟩ := hch")
        o.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                o.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        o += ["  have hAne : A ≠ 0 := by", "    intro h0",
              "    have hz0 : A.natDegree = 0 := by simp [h0]", "    omega"]
        # the chamber keeps its `hq…` names here (no `name_chamber_facts`)
        cbase = (chamber_cons_named(c.nums(), tag="hq") + CONE_CONS
                 + dead_cons(live) + NONNEG_CONS)
        if e["kind"] == "split":
            lets = e["split"]["letters"]
            order = [r for _t, r in e["branches"]]

            def rec(i, ind, lo, hi):
                if i == len(lets):
                    return branch_kill_lines(coords, S, live, order[lo],
                                             packets, facedeg, ind, cbase)
                X = lets[i]
                half = (hi - lo) // 2
                ls = [f"{ind}by_cases hs{i} : 0 < {X}.natDegree", f"{ind}·"]
                ls += rec(i + 1, ind + "  ", lo, lo + half)
                ls.append(f"{ind}·")
                ls.append(f"{ind}  have hs{i}z : {X}.natDegree = 0 := by omega")
                ls += rec(i + 1, ind + "  ", lo + half, hi)
                return ls
            o += rec(0, "  ", 0, len(order))
        else:
            pv = e["pivot"]
            lhs, rhs = [x.strip() for x in pv["comparison"].split("<")]
            o.append(f"  rcases lt_trichotomy ({lhs}) ({rhs}) with "
                     "hpv | hpv | hpv")
            for _t, r in e["branches"]:
                o.append("  ·")
                o += branch_kill_lines(coords, S, live, r, packets, facedeg,
                                       "    ", cbase)
        o.append("")
        body += "\n".join(o) + "\n"
        nk += 1
    name = "Grok810ScaleZeroQuarticChamberUnownedSplitsScratch"
    doc = ("# Unowned letter splits and load trichotomies, `(8,10)` scale "
           "zero\n\n"
           f"{nk} chambers of `UNOWNED_CHAMBERS.md` §3.2/§3.4 that need a case\n"
           "distinction: an `n_X = 0` split or an `lt_trichotomy` against a load\n"
           "column, with a single-carrier kill on every branch.  Every branch\n"
           "verdict is an exact rational Farkas certificate on the sub-chamber.\n"
           "Untracked working note.")
    out = (header(prev, doc) + "section QuarticChamberUnownedSplits810\n\n"
           + body + "\nend QuarticChamberUnownedSplits810\n" + FOOTER)
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{nk} split / trichotomy chamber kills"))
    return name, killmap


# ------------- the recursive refinement trees (`UNOWNED_CHAMBERS.md` §11)
def try_single_kill(coords, cons, live, form, zero=frozenset()):
    """A one-monomial-face kill of `form` on the sub-chamber, all verdicts
    Farkas-certified, or None."""
    recs = surviving(carrier_lf_records(coords, form), live)
    if not recs:
        return None
    face = [x for x in recs
            if all(CC.derive(cons, CC.sub7(_dvec(x.get("exps")),
                                           _dvec(y.get("exps"))), False)
                   is not None for y in recs if y is not x)]
    if len(face) != 1:
        return None
    df = _dvec(face[0].get("exps"))
    k = KDEG_ALL[form]
    side = CC.sub7(df, tuple(k * t for t in _unit(0)))
    hncside = CC.derive(cons, side, True) is None
    if hncside:
        c2 = cons + [(tuple(-t for t in side), False)]
        if not all(CC.derive(c2, tuple(-t for t in _unit(LET.index(X))),
                             False) is not None for X in SIG):
            return None
    loads = {}
    for ld in LOADS:
        if ld in (zero or ()):
            loads[ld] = {"status": "zero"}
            continue
        cols = [_dvec(x.get("exps")) for x in surviving(
            [y for cnk in carrier_col_chunks(coords, form, ld)
             for y in cnk[1]], live)]
        st, src = load_verdict(cons, live, df, cols, ld, BAND_ORDER)
        if st is None:
            return None
        loads[ld] = {"status": st} if src is None else {"status": st,
                                                        "source": src}
    return {"carrier": form, "k": k, "kside_hnc": hncside,
            "d": deg_expr(face[0].get("exps") or {}),
            "face": [list(df)], "loads": loads}


def collect_pivots(node, out=None):
    if out is None:
        out = []
    if isinstance(node, dict) and "branches" in node:
        if node["comparison"] not in out:
            out.append(node["comparison"])
        for b in node["branches"].values():
            collect_pivots(b, out)
    return out


def refine_search(coords, cons, live, pivots, used, depth, budget):
    """A decision tree closing the sub-chamber, or an `open` leaf."""
    if not CC.feasible(cons):
        return {"kind": "infeasible"}
    for form in CARRIER_ORDER:
        r = try_single_kill(coords, cons, live, form)
        if r is not None:
            return {"kind": "single", "rec": r}
    if depth >= budget:
        return {"kind": "open", "cons": cons}
    for p in pivots:
        if p in used:
            continue
        lhs, rhs = [x.strip() for x in p.split("=")]
        u, v = CC.lin(lhs), CC.lin(rhs)
        subs = [("<", [(CC.sub7(v, u), True)]),
                ("=", [(CC.sub7(u, v), False), (CC.sub7(v, u), False)]),
                (">", [(CC.sub7(u, v), True)])]
        if not any(CC.feasible(cons + ex) for _t, ex in subs):
            continue
        kids = {}
        ok = True
        for t, ex in subs:
            kids[t] = refine_search(coords, cons + ex, live, pivots,
                                    used | {p}, depth + 1, budget)
            if kids[t]["kind"] == "open":
                ok = False
                break
        if ok:
            return {"kind": "split", "comparison": p, "lhs": lhs, "rhs": rhs,
                    "branches": kids}
    return {"kind": "open", "cons": cons}


def tree_records(t, out=None):
    if out is None:
        out = []
    if t["kind"] == "single":
        out.append(t["rec"])
    for b in (t.get("branches") or {}).values():
        tree_records(b, out)
    return out


def tree_lines(coords, S, live, t, packets, facedeg, ind, base=None):
    """The tactic block closing one node of a refinement tree."""
    if t["kind"] == "infeasible":
        return [ind + "omega"]
    if t["kind"] == "single":
        return branch_kill_lines(coords, S, live, t["rec"], packets, facedeg,
                                 ind, base)
    o = [ind + f"rcases lt_trichotomy ({t['lhs']}) ({t['rhs']}) with "
         "hpv | hpv | hpv"]
    for tag in ("<", "=", ">"):
        o.append(ind + "·")
        o += tree_lines(coords, S, live, t["branches"][tag], packets, facedeg,
                        ind + "  ", base)
    return o


def emit_refine_trees(coords, chambers, entries, packets, have, prev):
    """The recursive refinement trees of `UNOWNED_CHAMBERS.md` §11, re-derived
    here: every pivot is an `lt_trichotomy` on a linear form in the exponents,
    every leaf is either Farkas-infeasible (`omega`) or a single-carrier kill
    whose every column verdict is an exact rational certificate."""
    cham = {c.name: c for c in chambers}
    rex = refined_leaf_extra()
    body, facedeg, seen = "/-! ## Face degrees -/\n\n", {}, set()
    for e in entries:
        for r in e["carriers"]:
            txt, nm, need, d, face = face_degree_lemma(
                coords, r["carrier"], r["packet"], packets, have, seen)
            body += txt
            facedeg[(r["carrier"], r["packet"])] = (nm, need, d, face)
    body += "/-! ## The refinement-tree kills -/\n\n"
    nk, killmap = 0, {}
    for e in entries:
        c = cham[e["name"]]
        S, live = e["live"], set(e["live"])
        leafi = e.get("leaf")
        if leafi is None:
            thname = f"quarticChamber{c.name}810_impossible"
            hyptype = c.defname
            extra = 0
        else:
            thname = f"quarticRefined{c.name}L{leafi}810_impossible"
            hyptype = f"QuarticRefined{c.name}L{leafi}810"
            extra = rex[(c.name, leafi)]
        needf, srcs = [], set()
        for r in e["carriers"]:
            f = r["carrier"]
            for x in (AUXNEEDS[f] if f in AUXDEFS else [f]):
                if x not in needf:
                    needf.append(x)
            srcs |= {v.get("source") for v in r["loads"].values()
                     if v["status"].startswith("band")}
        for s2 in sorted(srcs):
            for x in UNOWNED_BAND[s2][4]:
                if x not in needf:
                    needf.append(x)
        needf = [f for f in HYP_ORDER if f in needf or f == "kappa"]
        o = ["set_option maxHeartbeats 64000000 in",
             f"/-- Unowned chamber `{S}` / `{'·'.join(e['argmin'])}`"
             + (f" leaf {leafi}" if leafi is not None else "")
             + f" dies on a {e['nleaf']}-leaf refinement tree "
             f"({e['ndepth']} nested pivots). -/",
             f"theorem {thname}", f"    ({LOADSIG8} : k)",
             "    (A B C D E F G : k[X])",
             f"    (hch : {hyptype} A B C D E F G)",
             "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
             "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))"]
        for f in needf:
            h, rel = DEGHYP_ALL[f]
            o.append(f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            o.append(f"          A B C D E F G).natDegree {rel})")
        killmap[(e["name"], leafi)] = (thname,
                                       [DEGHYP_ALL[f][0] for f in needf])
        o[-1] += " :"
        o.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        src = "hch"
        if extra:
            o.append("  obtain ⟨hcell, "
                     + ", ".join(f"hx{t}" for t in range(extra)) + "⟩ := hch")
            src = "hcell"
        o.append(f"  obtain ⟨{', '.join(names)}⟩ := {src}")
        o.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                o.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        o += ["  have hAne : A ≠ 0 := by", "    intro h0",
              "    have hz0 : A.natDegree = 0 := by simp [h0]", "    omega"]
        cbase = (chamber_cons_named(c.nums(), tag="hq") + CONE_CONS
                 + dead_cons(live) + NONNEG_CONS)
        o += tree_lines(coords, S, live, e["tree"], packets, facedeg, "  ",
                        cbase)
        o.append("")
        body += "\n".join(o) + "\n"
        nk += 1
    name = "Grok810ScaleZeroQuarticChamberUnownedRefineScratch"
    doc = ("# Unowned refinement trees, `(8,10)` scale zero\n\n"
           f"{nk} chambers of `UNOWNED_CHAMBERS.md` §11 that need a nested case\n"
           "split.  The pivots come from the plan; the tree itself, every leaf's\n"
           "carrier and face, and every load-column verdict are re-derived here\n"
           "with the exact rational Farkas engine, so no branch is emitted on the\n"
           "plan's word.  Untracked working note.")
    out = (header(prev, doc) + "section QuarticChamberUnownedRefine810\n\n"
           + body + "\nend QuarticChamberUnownedRefine810\n" + FOOTER)
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{nk} refinement-tree chamber kills"))
    return name, killmap


def refine_entries(coords, chambers, plan):
    """The `refinement`/`partial` entries whose tree this pass can close."""
    cham = {c.name: c for c in chambers}
    pid, ids = collections.Counter(), {}
    out, dropped = [], []
    for e in [x for x in plan["chambers"] + plan["leaves"]
              + plan.get("open", []) if x["mode"] in ("refinement", "partial")]:
        cons, live = entry_cons(cham, e)
        piv = collect_pivots(e["refinement"])
        t = refine_search(coords, cons, live, piv, frozenset(), 0, len(piv))

        def openleaf(n):
            if n["kind"] == "open":
                return True
            return any(openleaf(b) for b in (n.get("branches") or {}).values())
        if openleaf(t):
            dropped.append((e["name"], e.get("leaf"), e["mode"]))
            continue
        recs = tree_records(t)
        for r in recs:
            key = (r["carrier"], tuple(map(tuple, r["face"])))
            if key not in ids:
                ids[key] = 8000 + pid[r["carrier"]]
                pid[r["carrier"]] += 1
            r["packet"] = ids[key]
        f = dict(e)
        f["mode"] = "single"
        f["carriers"] = recs
        f["tree"] = t
        f["nleaf"] = len(recs)

        def depth(n):
            if not (n.get("branches") or {}):
                return 0
            return 1 + max(depth(b) for b in n["branches"].values())
        f["ndepth"] = depth(t)
        out.append(f)
    return out, dropped


# ------------------------------------------------------ the residual, module 7
RESID_CTX = {"hkap": "hkapDeg", "hnu": "hnuDeg", "homi": "homiDeg",
             "hprim": "hprimdeg", "hmuDeg": "hmuDeg", "hxiDeg": "hxiDeg",
             "hpiDeg": "hpiDeg", "hmu": "hmuDeg", "hxi": "hxiDeg",
             "hpi": "hpiDeg", "hom": "homiDeg", "homiDeg": "homiDeg",
             "hnuDeg": "hnuDeg", "hkapDeg": "hkapDeg"}
_KILLSIG = None


def kill_binders():
    """`kill theorem -> its hypothesis binder names`, read off the emitted
    modules.  The kill maps record what each *emitter* believed the telescope
    was; when two families plan the same refined leaf and only one of them
    emits it, the surviving map entry can disagree with the theorem that is
    actually on disk.  The file is the ground truth."""
    global _KILLSIG
    if _KILLSIG is None:
        _KILLSIG = {}
        pat = re.compile(r"^theorem (\w+810_impossible)\b")
        for q in sorted(ROOT.glob("Grok810*.lean")) + sorted(
                ROOT.glob("Astra810*.lean")):
            L = q.read_text().split("\n")
            for i, x in enumerate(L):
                m = pat.match(x)
                if not m:
                    continue
                names, j = [], i + 1
                while j < len(L):
                    mm = re.match(r"^    \((h\w+) :", L[j])
                    if mm:
                        names.append(mm.group(1))
                    if L[j].rstrip().endswith(" :") or "False := by" in L[j]:
                        break
                    j += 1
                _KILLSIG.setdefault(m.group(1), names)
    return _KILLSIG


def resid_call_args(nm, hc):
    """The argument list for `nm` after `A B C D E F G`, in the order the
    theorem itself binds them.  `None` when the theorem is not on disk."""
    b = kill_binders().get(nm)
    if not b:
        return None
    out = []
    for x in b:
        if x in ("hch", "hcell", "hleaf"):
            out.append(hc)
        elif x == "hnc":
            out.append("hnc")
        elif x in RESID_CTX:
            out.append(RESID_CTX[x])
        else:
            return None
    return out


TOWER_FILE = "Grok810ScaleZeroQuarticTowerScratch"
ASTRA_FILE = "Astra810ScaleZeroQuarticFactoredCellsScratch"


def load_wall_theorems():
    """`chamber Prop -> {wall equation: theorem name}` for the wall-split
    lane's leaf theorems that take only the chamber and the wall equation."""
    f = ROOT / "Grok810ScaleZeroQuarticWallSplitsScratch.lean"
    if not f.exists():
        return {}
    txt = f.read_text()
    out = {}
    for blk in txt.split("\ntheorem quarticWeakBandLeaf")[1:]:
        nm = "quarticWeakBandLeaf" + blk.split("\n")[0].strip()
        i = blk.find("False :=")
        head = blk[:i if i > 0 else 2000]
        if "hrows" in head or "hN7" in head:
            continue
        ch = re.search(r"\(hc : (QuarticChamber\w+) A B C D E F G\)", head)
        hw = re.search(r"\(hw : ([^)]*?)\)\s*:?\s*\n", head)
        if not ch or not hw:
            continue
        out.setdefault(ch.group(1), {}).setdefault(
            " ".join(hw.group(1).split()), nm)
    return out


def emit_residual7(chambers, kills, refkills, newk, prev):
    """The exhaust dispatched through every kill set of Files B and C,
    including the unowned tranche (single, system, split/trichotomy, tree)."""
    resid_hyp = {"kappa": "hkapDeg", "mu": "hmuDeg", "xi": "hxiDeg",
                 "pi": "hpiDeg", "nu": "hnuDeg", "omicron": "homiDeg"}
    astra, astraleaf, astrafiles = {}, {}, []
    for _p in sorted(ROOT.glob("Astra810*.lean")):
        _atx = _p.read_text()
        hit = False
        for _m in re.finditer(r"^theorem (quarticUnownedCell_r(\w+)"
                              r"_impossible)\s*\n?\s*\{j t : k\}",
                              _atx, re.M):
            astra[_m.group(2)] = _m.group(1)
            hit = True
        for _m in re.finditer(r"^theorem (quarticUnownedLeaf_(\w+?)L(\d+)"
                              r"_impossible)", _atx, re.M):
            astraleaf[(_m.group(2), int(_m.group(3)))] = _m.group(1)
            hit = True
        if hit:
            astrafiles.append(_p.stem)
    walls = load_wall_theorems()
    rex_extra = refined_leaf_extra()
    refined = {c.name: c for c in chambers if c.refined}
    surv, survref = [], []
    for c in chambers:
        if c.name in refined:
            for i in range(len(c.leaves)):
                if ((c.name, i) not in refkills and (c.name, i) not in newk
                        and (c.name, i) not in astraleaf):
                    survref.append((c, i))
        elif ((c.live, c.argmin) not in kills
              and (c.name, None) not in newk
              and c.name not in astra):
            surv.append(c)
    wall = {c.name: sorted(walls[c.defname].items())
            for c in ({x for x in surv} | {y for y, _i in survref})
            if c.defname in walls}
    ind = "QuarticChamberResidual7810"
    body = "/-! ## The chamber residual after the unowned tranche -/\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- The {len(surv)} whole chambers and {len(survref)} refined "
             "leaves\nno kill module of Files B/C reaches. -/\n")
    body += f"inductive {ind} (A B C D E F G : k[X]) : Prop\n"

    def wallhyp(c):
        return "".join(f"      ¬ ({w}) →\n" for w, _n in wall.get(c.name, []))
    for c in surv:
        body += (f"  | r{c.name} : {c.defname} A B C D E F G →\n"
                 + wallhyp(c) + f"      {ind} A B C D E F G\n")
    for c, i in survref:
        body += (f"  | r{c.name}L{i} : QuarticRefined{c.name}L{i}810 "
                 f"A B C D E F G →\n" + wallhyp(c)
                 + f"      {ind} A B C D E F G\n")
    body += "\n"

    def newcall(key, hc):
        nm, hyps = newk[key]
        want = resid_call_args(nm, hc)
        rec = [hc, "hnc"] + [RESID_CTX[h] for h in hyps]
        if want is None:
            want = rec
        elif want != rec:
            log(f"{nm}: kill map says {rec[1:]}, the theorem binds "
                f"{want[1:]} - using the theorem")
        return [f"          exact ({nm}",
                f"            {LOADSIG8}",
                f"            A B C D E F G " + " ".join(want) + ").elim"]

    thm = "normalized810ScaleZero_quarticChamber7Residual"
    # `SPLIT_RESIDUAL7` moves each support size's dispatch into a theorem of
    # its own, under its own heartbeat guard; the top-level theorem then only
    # `cases`es the support and forwards.  Same module, same statement.
    mode7 = os.environ.get("SPLIT_RESIDUAL7", "")
    split7 = bool(mode7)
    # `fine` additionally gives every chamber its own helper theorem, so the
    # ~1100 kills are independent declarations Lean can elaborate in parallel
    # and the kernel only ever checks small terms
    fine7 = mode7 == "fine"
    lines, parts, helpers = [], {}, []
    for s in range(1, 7):
        grp = [c for c in chambers if len(c.live) == s]
        base = len(lines)
        cidx = []
        lines.append(f"      | size{s} h =>")
        lines.append("        cases h with")
        for c in grp:
            cidx.append((c, len(lines)))
            lines.append(f"        | {c.ctor} hc =>")
            if c.name in refined:
                n = len(c.leaves)
                lines.append(f"          rcases quarticChamber{c.name}810_refine "
                             "A B C D E F G hc with")
                lines.append("            " + " | ".join(f"h{t}" for t in range(n)))
                for t in range(n):
                    if (c.name, t) in newk:
                        cl = newcall((c.name, t), f"h{t}")
                        lines.append("          · " + cl[0].strip())
                        lines += ["    " + x for x in cl[1:]]
                    elif (c.name, t) in refkills:
                        _cr, nu, forms = refkills[(c.name, t)]
                        extra = " hnuDeg" if (nu or "nu" in forms) else ""
                        for f in forms:
                            if f not in ("kappa", "nu"):
                                extra += f" {resid_hyp[f]}"
                        rnm = f"quarticRefined{c.name}L{t}810_impossible"
                        want = resid_call_args(rnm, f"h{t}")
                        rec = [f"h{t}", "hnc", "hkapDeg"] + extra.split()
                        if want is None:
                            want = rec
                        elif want != rec:
                            log(f"{rnm}: refined map says {rec[1:]}, the "
                                f"theorem binds {want[1:]} - using the theorem")
                        lines.append(f"          · exact ({rnm}")
                        lines.append(f"              {LOADSIG8}")
                        lines.append("              A B C D E F G "
                                     + " ".join(want) + ").elim")
                    elif (c.name, t) in astraleaf:
                        nex = len(_REFCJ.get((c.name, t), [])) if _REFCJ \
                            else rex_extra[(c.name, t)]
                        lines.append("          · obtain ⟨_, "
                                     + ", ".join(f"hx{u}" for u in range(nex))
                                     + f"⟩ := h{t}")
                        lines.append("            exact "
                                     f"({astraleaf[(c.name, t)]}")
                        lines.append(f"              {LOADSIG8}")
                        lines.append("              A B C D E F G hjdiv hder "
                                     "hxiDeg hmuDeg homiDeg hkapDeg")
                        lines.append("              hnuDeg hpiDeg hconeA hc "
                                     + " ".join(f"hx{u}"
                                                for u in range(nex))
                                     + ").elim")
                    elif c.name in wall:
                        ws = wall[c.name]
                        for wi, (w, _n) in enumerate(ws):
                            ind2 = "            " + "  " * wi
                            lines.append(("          · " if wi == 0 else ind2)
                                         + f"by_cases hw{wi} : {w}")
                            lines.append(ind2 + f"· exact ({ws[wi][1]}")
                            lines.append(ind2 + "    A B C D E F G hc "
                                         f"hw{wi}).elim")
                            lines.append(ind2 + "·")
                        ind2 = "            " + "  " * len(ws)
                        lines.append(ind2 + f"exact {ind}.r{c.name}L{t} h{t} "
                                     + " ".join(f"hw{wi}"
                                                for wi in range(len(ws))))
                    else:
                        lines.append(f"          · exact {ind}.r{c.name}L{t} h{t}")
                continue
            if c.name in astra:
                lines.append(f"          exact ({astra[c.name]}")
                lines.append(f"            {LOADSIG8}")
                lines.append("            A B C D E F G hjdiv hder hxiDeg "
                             "hmuDeg homiDeg hkapDeg")
                lines.append("            hnuDeg hpiDeg hconeA hc).elim")
                continue
            if (c.name, None) in newk:
                lines += newcall((c.name, None), "hc")
                continue
            key = (c.live, c.argmin)
            if key in kills:
                extra = kill_extra_args(kills[key], resid_hyp)
                knm = f"quarticChamber{c.name}810_impossible"
                want = resid_call_args(knm, "hc")
                rec = ["hc", "hnc", "hkapDeg"] + extra.split()
                if want is None:
                    want = rec
                elif want != rec:
                    log(f"{knm}: kill map says {rec[1:]}, the theorem binds "
                        f"{want[1:]} - using the theorem")
                lines.append(f"          exact ({knm}")
                lines.append(f"            {LOADSIG8}")
                lines.append("            A B C D E F G " + " ".join(want)
                             + ").elim")
            elif c.name in wall:
                ws = wall[c.name]
                for wi, (w, _n) in enumerate(ws):
                    ind2 = "          " + "  " * wi
                    lines.append(ind2 + f"by_cases hw{wi} : {w}")
                    lines.append(ind2 + f"· exact ({ws[wi][1]}")
                    lines.append(ind2 + f"    A B C D E F G hc hw{wi}).elim")
                    lines.append(ind2 + "·")
                ind2 = "          " + "  " * len(ws)
                lines.append(ind2 + f"exact {ind}.r{c.name} hc "
                             + " ".join(f"hw{wi}" for wi in range(len(ws))))
            else:
                lines.append(f"          exact {ind}.r{c.name} hc")
        if fine7:
            bounds = [i for _c, i in cidx] + [len(lines)]
            blk = []
            for k2, (c, i) in enumerate(cidx):
                cb = lines[i + 1:bounds[k2 + 1]]
                used = [h for h in RESID7_HYPS
                        if re.search(r"\b" + h + r"\b", "\n".join(cb))]
                helpers.append((c, used, cb))
                jt = "j t " if ("hjdiv" in used or "hder" in used) else ""
                blk.append(f"        | {c.ctor} hc =>")
                blk.append(f"          exact {thm}_c{c.name} "
                           f"{jt}{LOADSIG8}")
                blk.append("            A B C D E F G "
                           + " ".join(used) + (" " if used else "") + "hc")
            del lines[base + 2:]
            lines += blk
        if split7:
            parts[s] = (grp, lines[base + 2:])
            del lines[base:]
            lines.append(f"      | size{s} h =>")
            lines.append(f"        exact {thm}_part{s} j t {LOADSIG8}")
            lines.append("          A B C D E F G hjdiv hder hprimdeg hxiDeg "
                         "hmuDeg homiDeg")
            lines.append("          hkapDeg hnuDeg hpiDeg hconeA hnc h")
    note = ("Honest leftover after every chamber kill of Files B/C, the "
            "unowned tranche included.  Closed relative to "
            "`normalized810ScaleZero_quarticLoadLadderResidual`: the "
            "1115-chamber exhaust, the tournament on the 11 carrier-refined "
            "cells, and every kill of modules 14, 19, 23, 29, 35, 37 and of "
            f"the unowned single / system / split / tree / tower modules.  "
            f"Remaining: `{ind}` — {len(surv)} whole chambers and "
            f"{len(survref)} refined leaves — plus the all-constant corner.  "
            "No `sorry`, no new axioms, no finite-root shortcut.")
    if fine7:
        for c, used, cb in helpers:
            body += "set_option maxHeartbeats 64000000 in\n"
            body += (f"/-- Chamber `{c.name}`: its own declaration, so this "
                     "kill elaborates\nand is kernel-checked on its own. -/\n")
            body += f"theorem {thm}_c{c.name} [IsAlgClosed k]\n"
            if "hjdiv" in used or "hder" in used:
                body += "    (j t : k)\n"
            body += f"    ({LOADSIG8} : k)\n"
            body += "    (A B C D E F G : k[X])\n"
            for h in used:
                body += "    (" + RESID7_HYPS[h].replace("{L}", LOADSIG8) + ")\n"
            body += f"    (hc : {c.defname} A B C D E F G) :\n"
            body += f"    {ind} A B C D E F G := by\n"
            body += "\n".join(x[8:] if x.startswith(" " * 8) else x
                              for x in cb) + "\n\n"
    if split7:
        degs = (("hxiDeg", "Xi"), ("hmuDeg", "Mu"), ("homiDeg", "Omicron"),
                ("hkapDeg", "Kappa"), ("hnuDeg", "Nu"), ("hpiDeg", "Pi"))
        for s in range(1, 7):
            grp, blk = parts[s]
            body += "set_option maxHeartbeats 256000000 in\n"
            body += (f"/-- Support size {s}: the dispatch for the {len(grp)} "
                     "chambers of that size.\nSplit off so that each block "
                     "elaborates inside its own heartbeat budget; the\n"
                     "hypothesis telescope is the one the kills of every "
                     "block need. -/\n")
            body += f"theorem {thm}_part{s} [IsAlgClosed k]\n"
            body += f"    (j t {LOADSIG8} : k)\n"
            body += "    (A B C D E F G : k[X])\n"
            body += "    (hjdiv : j / t ≠ 0)\n"
            body += ("    (hder : derivative\n"
                     f"        (degreeZeroPrimitiveQuartic810 {LOADSIG8}\n"
                     "          A B C D E F G) =\n"
                     "      Polynomial.C (j / t))\n")
            body += ("    (hprimdeg : (degreeZeroPrimitiveQuartic810 "
                     f"{LOADSIG8}\n        A B C D E F G).natDegree = 1)\n")
            for hn, cn in degs:
                body += (f"    ({hn} : (degreeZero{cn}Quartic810 {LOADSIG8}\n"
                         "        A B C D E F G).natDegree = 0)\n")
            body += "    (hconeA : QuarticRatioConeA810 A B C D E F G)\n"
            body += ("    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ "
                     "D.natDegree = 0 ∧\n        E.natDegree = 0 ∧ "
                     "F.natDegree = 0 ∧ G.natDegree = 0))\n")
            body += (f"    (h : QuarticChamberSupportSize{s}810 "
                     "A B C D E F G) :\n")
            body += f"    {ind} A B C D E F G := by\n"
            body += "  cases h with\n"
            body += "\n".join(x[6:] if x.startswith(" " * 6) else x
                              for x in blk) + "\n\n"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += f"/-- {note} -/\n"
    body += f"""theorem {thm}
    {{P Q : MvPolynomial (Fin 2) k}} {{H : k[X]}}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧
              B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
              E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0) ∨
            {ind} A B C D E F G)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticLoadLadderResidual hsource
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · obtain ⟨hconeA, hexh, hlK, hbK, hdK, hzK, htK, hconst, hevenC, hevenE⟩ := hA
    refine Or.inl ⟨hconeA, ?_⟩
    by_cases hnc : B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
    · rcases hconst with ⟨hl0, hb0, hd0, hz0⟩ | hn
      · exact Or.inl ⟨hl0, hb0, hd0, hz0, hnc.1, hnc.2.1, hnc.2.2.1,
          hnc.2.2.2.1, hnc.2.2.2.2.1, hnc.2.2.2.2.2⟩
      · exact absurd hnc hn
    · refine Or.inr ?_
      have hsupp := quarticChamberSupport810_of (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G hconeA
        hjdiv hder
      cases hsupp with
"""
    body += "\n".join(lines) + "\n"
    body += "  · exact Or.inr hABCDEFG\n\n"
    body += f"#print axioms {thm}\n\n"
    if not surv and not survref:
        body += ("set_option maxHeartbeats 64000000 in\n"
                 f"/-- `{ind}` has no constructors: every one of the 1115\n"
                 "chambers is killed.  This is the `hresid` obligation of\n"
                 "`…AssemblyCore2Scratch`, discharged. -/\n"
                 "theorem quarticChamberResidual7810_impossible\n"
                 f"    (j t {LOADSIG8} : k)\n"
                 "    (A B C D E F G : k[X])\n"
                 "    (hjdiv : j / t ≠ 0)\n"
                 "    (hder : derivative\n"
                 f"        (degreeZeroPrimitiveQuartic810 {LOADSIG8}\n"
                 "          A B C D E F G) =\n"
                 "      Polynomial.C (j / t))\n"
                 f"    (hxi : (degreeZeroXiQuartic810 {LOADSIG8}\n"
                 "        A B C D E F G).natDegree = 0)\n"
                 f"    (hmu : (degreeZeroMuQuartic810 {LOADSIG8}\n"
                 "        A B C D E F G).natDegree = 0)\n"
                 f"    (homi : (degreeZeroOmicronQuartic810 {LOADSIG8}\n"
                 "        A B C D E F G).natDegree = 0)\n"
                 f"    (hkap : (degreeZeroKappaQuartic810 {LOADSIG8}\n"
                 "        A B C D E F G).natDegree = 0)\n"
                 f"    (hnu : (degreeZeroNuQuartic810 {LOADSIG8}\n"
                 "        A B C D E F G).natDegree = 0)\n"
                 f"    (hpi : (degreeZeroPiQuartic810 {LOADSIG8}\n"
                 "        A B C D E F G).natDegree = 0)\n"
                 "    (hcone : QuarticRatioConeA810 A B C D E F G)\n"
                 f"    (hres : {ind} A B C D E F G) :\n"
                 "    False := by\n"
                 "  cases hres\n\n"
                 "#print axioms quarticChamberResidual7810_impossible\n")
    name = "Grok810ScaleZeroQuarticChamberResidual7Scratch"
    doc = ("# The chamber residual after the unowned tranche, `(8,10)` scale "
           "zero\n\n"
           f"`{ind}` ({len(surv)} whole chambers + {len(survref)} refined "
           f"leaves)\nand `{thm}`.  Untracked working note.")
    imps = list(prev) + astrafiles
    out = (header(imps, doc) + "section QuarticChamberResidual7810\n\n"
           + "variable [IsAlgClosed k]\n\n"
           # every helper states `[IsAlgClosed k]` itself, so that the kill it
           # forwards to never has to go looking for the section instance
           + "set_option linter.overlappingInstances false\n\n" + body)
    out += "\nend QuarticChamberResidual7810\n" + FOOTER
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"`{ind}` ({len(surv)} chambers + {len(survref)} "
                              f"refined leaves) and `{thm}`"))
    try:
        import json as _json
        _un = _json.loads((ROOT / "scripts" /
                           "out_810_scale_zero_quartic_unowned.json").read_text())
        _own = {(e["name"], e["leaf"]): e["mode"]
                for e in _un["chambers"] + _un["leaves"]}
        for _o in _un.get("open", []):
            _own[(_o["name"], _o.get("leaf"))] = _o.get("mode", "open")
    except Exception:
        _own = {}
    _rows = []
    for c in surv:
        _w = "; ".join(f"`¬ ({w})`" for w, _n in wall.get(c.name, [])) or "—"
        _rows.append(f"| `r{c.name}` | `{c.defname}` | `{c.live}` | "
                     f"`{'·'.join(c.argmin)}` | "
                     + _own.get((c.name, None), "tower lane") + f" | {_w} |")
    for c, i2 in survref:
        _w = "; ".join(f"`¬ ({w})`" for w, _n in wall.get(c.name, [])) or "—"
        _rows.append(f"| `r{c.name}L{i2}` | `QuarticRefined{c.name}L{i2}810` | "
                     f"`{c.live}` | `{'·'.join(c.argmin)}` | "
                     + _own.get((c.name, i2), "tower lane") + f" | {_w} |")
    (Path.home() / "lean/tools/sigma810/RESIDUAL7_ENTRIES.md").write_text(
        f"# `QuarticChamberResidual7810` — the {len(surv) + len(survref)} "
        "entries Files B/C do not close\n\n"
        "`owner` is the remedy of `UNOWNED_CHAMBERS.md` that would close the "
        "entry,\nor `tower lane` for the entries "
        "`Grok810ScaleZeroQuarticTowerScratch` owns.\n`off-wall` records the "
        "extra `¬ (wall)` argument the constructor carries,\ncourtesy of "
        "`Grok810ScaleZeroQuarticWallSplitsScratch`.\n\n"
        "| constructor | `Prop` | live | argmin | owner | off-wall |\n"
        "|---|---|---|---|---|---|\n" + "\n".join(_rows) + "\n")
    log("wrote ~/lean/tools/sigma810/RESIDUAL7_ENTRIES.md")
    TRANCHE["wall"] = sum(len(wall.get(c.name, [])) for c in surv) + sum(
        len(wall.get(c.name, [])) for c, _i in survref)
    log(f"residual 7: {TRANCHE['wall']} constructors sharpened by a wall "
        "theorem")
    return name, surv, survref


# ------------------------------------------- the tower lane's deep-rescue 21
def _lean_to_sympy(body):
    import sympy as sp
    syms = {c: sp.Symbol(c) for c in "abcdefg"}
    s = re.sub(r"\(([-0-9/ ]+) : k\)", r"(\1)", body).replace("^", "**")
    return sp.sympify(re.sub(r"\s+", " ", s).strip(), locals=syms)


def tower_plan():
    """(tag -> {cell, live, argmin, carriers, faces, nezero}) from the tower
    file's own doc comments and theorem signatures."""
    txt = (ROOT / (TOWER_FILE + ".lean")).read_text()
    # a speed lane lifted the tower's heavy declarations into
    # `…SpeedTPart<n>Scratch` helper modules; the plan reads the signatures, so
    # follow those imports (the aggregator keeps only the import lines).
    _seen, _todo = set(), re.findall(r"^import (\S*SpeedTPart\d+\S*)\s*$",
                                    txt, re.M)
    while _todo:
        _m = _todo.pop()
        if _m in _seen:
            continue
        _seen.add(_m)
        _q = ROOT / (_m + ".lean")
        if not _q.exists():
            continue
        _t = _q.read_text()
        txt += "\n" + _t
        _todo += re.findall(r"^import (\S*SpeedTPart\d+\S*)\s*$", _t, re.M)
    faces = {m.group(1): _lean_to_sympy(m.group(2)) for m in re.finditer(
        r"^def (\w+QuarticCostChamber\w+Face810) \(a b c d e f g : k\) : k :="
        r"\n((?:  .*\n)+)", txt, re.M)}
    tags = {}
    for m in re.finditer(r"/-- Deep-rescue #\d+: `([A-G]+)` / `([^`]+)`, "
                         r"target `([^`]+)`[^/]*?-/\n"
                         r"theorem quarticCostChamber(\w+)810_identity", txt):
        live, argmin, target, tag = m.groups()
        tags[tag] = {"live": live, "argmin": tuple(argmin.split("·")),
                     "target": target}
    for m in re.finditer(r"theorem quarticCostChamber(\w+)810_impossible\n"
                         r"(.*?)\n    False", txt, re.S):
        tag, sig = m.group(1), m.group(2)
        if tag not in tags:
            continue
        tags[tag]["carriers"] = re.findall(
            r"\((\w+) : (\w+)QuarticCostChamber\w+Face810", sig)
        tags[tag]["nezero"] = re.findall(r"\(h(\w) : (\w) ≠ 0\)", sig)
    return tags, faces


def tower_entries(coords, chambers, have):
    """One `single`-shaped record per (tower certificate, sub-chamber) whose
    face really is the tower's face and whose every column clears."""
    import sympy as sp
    syms = {c: sp.Symbol(c) for c in "abcdefg"}
    cham = {c.name: c for c in chambers}
    tags, faces = tower_plan()
    bykey = {(c.live, c.argmin): c for c in chambers}
    pid, ids = collections.Counter(), {}
    out, skipped = [], []
    for tag, t in sorted(tags.items()):
        c = bykey.get((t["live"], t["argmin"]))
        if c is None or "carriers" not in t:
            skipped.append((tag, "no cell"))
            continue
        live = set(t["live"])
        cands = ([None] if not c.refined else list(range(len(c.leaves))))
        for li in cands:
            cons, _lv = entry_cons(cham, {"name": c.name, "leaf": li,
                                          "live": t["live"]})
            recs, ok = [], True
            for _hyp, cr in t["carriers"]:
                lf = surviving(carrier_lf_records(coords, cr), live)
                face = [x for x in lf
                        if all(CC.derive(cons, CC.sub7(_dvec(x.get("exps")),
                                                       _dvec(y.get("exps"))),
                                         False) is not None
                               for y in lf if y is not x)]
                if not face:
                    ok = False
                    break
                expr = 0
                for x in face:
                    q = sp.Rational(int(x["qn"]), int(x["qd"]))
                    for L in LET:
                        n = int((x.get("exps") or {}).get(L, 0) or 0)
                        if n:
                            q *= syms[L.lower()] ** n
                    expr += q
                tw = faces[f"{cr}QuarticCostChamber{tag}Face810"]
                ratio = sp.simplify(expr / tw)
                if not ratio.is_number:
                    ok = False
                    break
                df = _dvec(face[0].get("exps"))
                k = KDEG_ALL[cr]
                side = CC.sub7(df, tuple(k * x for x in _unit(0)))
                hncside = CC.derive(cons, side, True) is None
                if hncside:
                    c2 = cons + [(tuple(-x for x in side), False)]
                    if not all(CC.derive(c2, tuple(-x for x in
                                                   _unit(LET.index(X))),
                                         False) is not None for X in SIG):
                        ok = False
                        break
                loads = {}
                for ld in LOADS:
                    cols = [_dvec(x.get("exps")) for x in surviving(
                        [y for cnk in carrier_col_chunks(coords, cr, ld)
                         for y in cnk[1]], live)]
                    st, src = load_verdict(cons, live, df, cols, ld, BAND_ORDER)
                    if st is None:
                        ok = False
                        break
                    loads[ld] = ({"status": st} if src is None
                                 else {"status": st, "source": src})
                if not ok:
                    break
                key = (cr, tuple(_dvec(x.get("exps")) for x in face))
                if key not in ids:
                    ids[key] = 9000 + pid[cr]
                    pid[cr] += 1
                recs.append({"carrier": cr, "packet": ids[key], "k": k,
                             "kside_hnc": hncside,
                             "d": deg_expr(face[0].get("exps") or {}),
                             "face": [list(_dvec(x.get("exps"))) for x in face],
                             "loads": loads,
                             "towerface":
                                 f"{cr}QuarticCostChamber{tag}Face810",
                             "scale": sp.Rational(ratio)})
            if not ok:
                continue
            thname = (f"quarticChamber{c.name}810_impossible" if li is None
                      else f"quarticRefined{c.name}L{li}810_impossible")
            if thname in have or any(e["thname"] == thname for e in out):
                continue
            out.append({"name": c.name, "leaf": li, "live": t["live"],
                        "argmin": list(t["argmin"]), "mode": "single",
                        "tag": tag, "thname": thname, "carriers": recs,
                        "nezero": t["nezero"], "target": t["target"]})
    return out, skipped


def rat_lean(q):
    n, dd = int(q.p), int(q.q)
    if dd == 1:
        return f"({n} : k)"
    return f"({n} / {dd} : k)"


def emit_tower_kills(coords, chambers, entries, packets, have, prev):
    """The tower lane's scalar certificates, wired to the chambers: one
    `_coeff_top` bridge per (carrier, packet) against the tower's own face
    definition, then the chamber kill."""
    cham = {c.name: c for c in chambers}
    rex = refined_leaf_extra()
    body = "/-! ## Top-coefficient bridges to the tower's face definitions -/\n\n"
    bridge = {}
    for e in entries:
        for r in e["carriers"]:
            form, p = r["carrier"], r["packet"]
            if (form, p) in bridge:
                continue
            face, _rest = unowned_face(coords, form, packets[(form, p)]["face"])
            d = deg_expr(face[0].get("exps") or {})
            nm = f"{form}QuarticChamberFace{p}810_coeff_top"
            call = (f"{rat_lean(r['scale'])} * {r['towerface']} "
                    + " ".join(LC[L] for L in LET))
            bridge[(form, p)] = (nm, d, face, call, r["scale"], r["towerface"])
            if nm in have:
                continue
            body += coeff_top_lemma(form, p, face, d, nm, call,
                                    unfold=(r["towerface"],))
    blocks, nk, killmap = [], 0, {}
    for e in entries:
        c = cham[e["name"]]
        S, live = e["live"], set(e["live"])
        leafi = e["leaf"]
        extra = 0 if leafi is None else rex[(c.name, leafi)]
        hyptype = (c.defname if leafi is None
                   else f"QuarticRefined{c.name}L{leafi}810")
        srcs = set()
        needf = []
        for r in e["carriers"]:
            f = r["carrier"]
            for x in (AUXNEEDS[f] if f in AUXDEFS else [f]):
                if x not in needf:
                    needf.append(x)
            srcs |= {v.get("source") for v in r["loads"].values()
                     if v["status"].startswith("band")}
        for s2 in sorted(srcs):
            for x in UNOWNED_BAND[s2][4]:
                if x not in needf:
                    needf.append(x)
        needf = [f for f in HYP_ORDER if f in needf or f == "kappa"]
        k = ["set_option maxHeartbeats 64000000 in",
             f"/-- Tower deep-rescue `{e['tag']}` on chamber `{S}` / "
             f"`{'·'.join(e['argmin'])}`"
             + (f" leaf {leafi}" if leafi is not None else "")
             + f", target `{e['target']}`. -/",
             f"theorem {e['thname']}", f"    ({LOADSIG8} : k)",
             "    (A B C D E F G : k[X])",
             f"    (hch : {hyptype} A B C D E F G)",
             "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
             "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))"]
        for f in needf:
            h, rel = DEGHYP_ALL[f]
            k.append(f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            k.append(f"          A B C D E F G).natDegree {rel})")
        killmap[(e["name"], leafi)] = (e["thname"],
                                       [DEGHYP_ALL[f][0] for f in needf])
        k[-1] += " :"
        k.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        src = "hch"
        if extra:
            k.append("  obtain ⟨hcell, "
                     + ", ".join(f"hx{t}" for t in range(extra)) + "⟩ := hch")
            src = "hcell"
        k.append(f"  obtain ⟨{', '.join(names)}⟩ := {src}")
        k.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                k.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        k += ["  have hAne : A ≠ 0 := by", "    intro h0",
              "    have hz0 : A.natDegree = 0 := by simp [h0]",
              "    clear * - hApos hz0; omega"]
        # the refined-leaf extras `hx…` are not ℕ-degree data this pass can
        # read, so they are always kept; every other keep-list is an exact
        # rational Farkas support
        xtra = tuple(f"hx{tt}" for tt in range(extra))
        base = (chamber_cons_named(c.nums()) + CONE_CONS + dead_cons(live)
                + NONNEG_CONS)
        for s2 in sorted(srcs):
            casc, loads, var, ex, _n = UNOWNED_BAND[s2]
            k.append("  obtain ⟨" + ", ".join(var.format(x) for x in loads)
                     + "⟩ :=")
            k.append(f"    {casc} {LOADSIG8}")
            k.append(f"      A B C D E F G hA{ex}")
        hi = 0
        for ci, r in enumerate(e["carriers"]):
            form, p = r["carrier"], r["packet"]
            nm, d, face, call, scale, twf = bridge[(form, p)]
            _f, rest = unowned_face(coords, form, packets[(form, p)]["face"])
            surv_lf = surviving(rest, live)
            lhs = "0" if r["k"] == 0 else ("A.natDegree" if r["k"] == 1
                                           else f"{r['k']} * A.natDegree")
            k.append(f"  have hdp{ci} : {lhs} < {d} := by")
            k += HNC_BLOCK if r["kside_hnc"] else ["    omega"]
            # the rest lemmas bind `hdpos : 0 < d`; the k-side fact
            # above is stronger but is not that statement
            k.append(f"  have hdz{ci} : 0 < {d} := by omega")
            withd = base + [(f"hdz{ci}", CC.lin(d), True)]
            args = []
            for ld in LOADS:
                v = r["loads"][ld]
                if v["status"] == "empty":
                    continue
                cols = [x for cnk in carrier_col_chunks(coords, form, ld)
                        for x in cnk[1]]
                uniq = []
                for x in surviving(cols, live):
                    g = deg_expr(x.get("exps") or {})
                    if g not in uniq:
                        uniq.append(g)
                comps = []
                band = not v["status"].startswith("dominated")
                for g in uniq:
                    if v["status"].endswith("-hnc") and band:
                        # `hnc` here needs this branch's own band
                        # disjunct, so prove it inside the rcases
                        comps.append(HNC_INLINE)
                    elif v["status"].endswith("-hnc"):
                        hn = f"hh{hi}"
                        hi += 1
                        k.append(f"  have {hn} : {g} < {d} := by")
                        k += HNC_BLOCK
                        comps.append(hn)
                    else:
                        comps.append("by omega")
                plain = all(x == "by omega" for x in comps)
                if plain:
                    kd = keep_str(withd,
                                  [CC.target_of(f"{g} < {d}")[0] for g in uniq],
                                  xtra)
                    conj = ("(by " + (f"clear * - {kd}; " if kd else "")
                            + "omega)")
                else:
                    conj = (comps[0] if len(comps) == 1
                            else "⟨" + ", ".join(comps) + "⟩")
                if v["status"].startswith("dominated"):
                    args.append(f"(Or.inr {conj})")
                    continue
                hn = f"hz{ci}{ld}"
                args.append(hn)
                dis = unowned_band_disjuncts(v["source"], ld)
                hv = UNOWNED_BAND[v["source"]][2].format(ld)
                if plain:
                    k += band_block(hn, ld, hv, dis, uniq, d, base, withd,
                                    live, always=xtra)
                    continue
                k.append(f"  have {hn} : {ld} = 0 ∨ ("
                         + " ∧ ".join(f"{g} < {d}" for g in uniq) + ") := by")
                k.append(f"    rcases {hv} "
                         "with h | " + " | ".join("h" for _ in dis))
                k.append("    · exact Or.inl h")
                for X, _s in dis:
                    if X is not None and TOP[ld][X] == "hard":
                        k.append(f"    · exact absurd h{X}z h")
                    else:
                        k.append(f"    · exact Or.inr {conj}")
            zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
            seenlf = []
            for x in surv_lf:
                g = deg_expr(x.get("exps") or {})
                if g not in seenlf:
                    seenlf.append(g)
            lfa = []
            for g in seenlf:
                kg = keep_str(withd, [CC.target_of(f"{g} < {d}")[0]], xtra)
                lfa.append("(by " + (f"clear * - {kg}; " if kg else "")
                           + "omega)")
            lfargs = " ".join(lfa)
            rname = f"{form}QuarticChamberRest{p}810"
            k.append(f"  have hr{ci} : ({rname} {LOADSIG8}")
            k.append(f"      A B C D E F G).natDegree < {d} :=")
            k.append(f"    {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
            k.append(f"      A B C D E F G hdz{ci}"
                     + (f" {zargs}" if zargs else "")
                     + (f" {lfargs}" if lfargs else "")
                     + (" " + " ".join(args) if args else ""))
            ne = sorted({L for x in face for L in LET
                         if int((x.get("exps") or {}).get(L, 0) or 0) > 0},
                        key=LET.index)
            tie = " ".join("(by omega)" for _ in face[1:])
            k.append(f"  have hct{ci} := {nm} "
                     + " ".join(f"h{L}ne" if L != "A" else "hAne" for L in ne)
                     + coeff_top_named(ne) + (f" {tie}" if tie else ""))
            k.append(f"  have hq{ci} : ({CARRIER_LEAN[form]} {LOADSIG8}")
            k.append(f"      A B C D E F G).coeff ({d}) = 0 := by")
            k.append("    apply coeff_eq_zero_of_natDegree_lt")
            if form in AUXDEFS:
                pre = ""
                hargs = aux_le_argstr(form)
                k.append(f"    have hle := {CARRIER_LEAN[form]}_natDegree_le "
                         f"{LOADSIG8}")
                k.append(f"      A B C D E F G {pre}{hargs}")
                k.append("    omega")
            else:
                k.append(f"    rw [{DEGHYP_ALL[form][0]}]")
                k.append("    omega")
            k.append(f"  rw [{CARRIER_LEAN[form]}_eq_face{p}_add_rest,")
            k.append(f"    coeff_add, coeff_eq_zero_of_natDegree_lt hr{ci},")
            k.append(f"    add_zero] at hq{ci}")
            k.append(f"  have hs{ci} : {call} = 0 :=")
            k.append(f"    hct{ci}.symm.trans hq{ci}")
            k.append(f"  have hin{ci} : {twf} "
                     + " ".join(LC[L] for L in LET) + " = 0 := by")
            k.append(f"    rcases mul_eq_zero.mp hs{ci} with h | h")
            k.append("    · exact absurd h (by norm_num)")
            k.append("    · exact h")
        for _h, L in e["nezero"]:
            s2 = "hAne" if L.upper() == "A" else f"h{L.upper()}ne"
            k.append(f"  have h{L.upper()}c : {L.upper()}.leadingCoeff ≠ 0 := "
                     f"leadingCoeff_ne_zero.mpr {s2}")
        k.append(f"  exact quarticCostChamber{e['tag']}810_impossible "
                 + " ".join(LC[L] for L in LET) + " "
                 + " ".join(f"hin{i}" for i in range(len(e["carriers"])))
                 + " " + " ".join(f"h{L.upper()}c" for _h, L in e["nezero"]))
        k.append("")
        blocks.append(prune_arith(name_chamber_facts("\n".join(k))) + "\n")
        nk += 1
    bname = "Grok810ScaleZeroQuarticChamberTowerBridgesScratch"
    bdoc = ("# `_coeff_top` bridges to the tower lane, `(8,10)` scale zero\n\n"
            f"{len(bridge)} bridges, one per (carrier, face packet) the tower's\n"
            "deep-rescue certificates use.  Each proves that the chamber face's\n"
            "top coefficient is a non-zero rational multiple of the tower file's\n"
            "own `<carrier>QuarticCostChamber<tag>Face810`.  Untracked note.")
    bout = (header(list(prev) + [TOWER_FILE], bdoc)
            + "section QuarticChamberTowerBridges810\n\n" + body
            + "\nend QuarticChamberTowerBridges810\n" + FOOTER)
    bln = write(bname + ".lean", bout)
    MODULES.append((bname, bln, f"{len(bridge)} `_coeff_top` bridges to the "
                                "tower's face definitions"))
    names_out = [bname]
    groups, cur, curl = [], [], 0
    for b in blocks:
        n = b.count("\n")
        if cur and curl + n > 2000:
            groups.append(cur)
            cur, curl = [], 0
        cur.append(b)
        curl += n
    if cur:
        groups.append(cur)
    for gi, grp in enumerate(groups or [[]]):
        nm = f"Grok810ScaleZeroQuarticChamberTowerKills{gi + 1}Scratch"
        doc = (f"# Tower deep-rescue chamber kills, part {gi + 1}/"
               f"{len(groups)}\n\n"
               f"{len(grp)} of the {nk} chambers `{TOWER_FILE}` owns: the "
               "bridges of\n`…ChamberTowerBridgesScratch` feed the tower's own "
               "scalar\n`quarticCostChamber<tag>810_impossible`.  Every face is "
               "checked to be\nthe tower's face (exactly, up to the recorded "
               "rational scale) and every\nload column carries a Farkas "
               "certificate.  Untracked working note.")
        sec = f"QuarticChamberTowerKills{gi + 1}810"
        # a kill whose five carrier rows do not fit the runner in one
        # declaration has each row lifted into a module of its own
        stem = nm[:-len("Scratch")]
        blocks, extra = [], []
        for bi2, b in enumerate(grp):
            if re.search(r"^theorem (%s)$" % "|".join(TOWER_ROW_SPLIT), b,
                         re.M):
                wrap, lem = split_carrier_rows(b, f"{stem}Part{bi2}")
                blocks.append(wrap)
                extra += lem
            else:
                blocks.append(b)
        for mod, lem in extra:
            write(mod + ".lean",
                  header(["Mathlib"], doc) + f"section {sec}\n\n"
                  + lem.rstrip("\n") + "\n" + f"\nend {sec}\n" + FOOTER)
        split_decls(nm, sec, doc, blocks, list(prev) + [bname, TOWER_FILE])
        MODULES.append((nm, sum(b.count("\n") for b in grp),
                        f"{len(grp)} tower deep-rescue chamber kills"))
        names_out.append(nm)
    return names_out, killmap




# ------------- the two remaining leaf shapes: load kills and tied-load systems
LOADSYM = {"ga": "gamma", "ep": "epsilon", "et": "eta", "l": "l",
           "beta": "beta", "delta": "delta", "zeta": "zeta", "theta": "theta"}


def carrier_all_records(coords, form):
    """Every term of the carrier, load columns included."""
    T = carrier_terms(coords, form)
    return EC.sort_records([as_record(k, c) for k, c in T.items()])


def rec_load(r):
    ld = list((r.get("loads") or {}))
    return ld[0] if ld else None


def loaded_top(coords, form, live, cons, ld, mono):
    """The record of `ld`'s column at monomial `mono` together with an exact
    verdict that everything else in `Φ` is strictly below it: the load-free
    part and every other column monomial dominated (or `hnc`-dominated, or
    covered by a band — in which case the `p = 0` disjunct closes the goal on
    its own).  Returns `(top record, {load: verdict}, load-free degrees)`."""
    ex = {}
    for ch in mono:
        ex[ch] = ex.get(ch, 0) + 1
    want = tuple(ex.get(L, 0) for L in LET)
    recs = surviving(carrier_all_records(coords, form), live)
    top = [r for r in recs if rec_load(r) == ld and _dvec(r.get("exps")) == want]
    if len(top) != 1:
        return None
    df = _dvec(top[0].get("exps"))
    lf = [r for r in recs if rec_load(r) is None]
    for r in lf:
        if _lt_or_hnc(cons, df, _dvec(r.get("exps"))) is None:
            return None
    lfface = [x for x in lf
              if all(CC.derive(cons, CC.sub7(_dvec(x.get("exps")),
                                             _dvec(y.get("exps"))), False)
                     is not None for y in lf if y is not x)]
    if not lfface:
        return None
    loads = {}
    for p2 in LOADS:
        cols = [_dvec(r.get("exps")) for r in recs
                if rec_load(r) == p2 and (p2 != ld or
                                          _dvec(r.get("exps")) != df)]
        st, src = load_verdict(cons, live, df, cols, p2, BAND_ORDER)
        if st is None:
            return None
        loads[p2] = ({"status": st} if src is None
                     else {"status": st, "source": src})
    return {"carrier": form, "load": ld, "mono": mono, "top": top[0],
            "d": deg_expr(top[0].get("exps") or {}), "loads": loads,
            "lf": lf, "lfface": lfface,
            "lfd": deg_expr(lfface[0].get("exps") or {})}


def mixed_face(coords, form, live, cons, zero=frozenset()):
    """The cost-maximal terms of `Φ` on a sub-chamber, load columns included,
    together with an exact verdict on every term that is not in the face."""
    recs = surviving(carrier_all_records(coords, form), live)
    # the pure-`A` loads are decided by a band, so their columns never sit in
    # the face: in each disjunct they are either zero or strictly below
    recs = [r for r in recs if rec_load(r) not in (zero or ())]
    cand = [r for r in recs if rec_load(r) is None or rec_load(r) in NOPUREA]
    if not cand:
        return None
    face = [x for x in cand
            if all(CC.derive(cons, CC.sub7(_dvec(x.get("exps")),
                                           _dvec(y.get("exps"))), False)
                   is not None for y in cand if y is not x)]
    if not face:
        return None
    df = _dvec(face[0].get("exps"))
    fk = {id(x) for x in face}
    for r in cand:
        if id(r) in fk:
            continue
        if rec_load(r) is not None:
            continue
        if _lt_or_hnc(cons, df, _dvec(r.get("exps"))) is None:
            return None
    loads = {}
    for p2 in LOADS:
        if p2 in (zero or ()):
            loads[p2] = {"status": "zero"}
            continue
        cols = [_dvec(r.get("exps")) for r in recs
                if rec_load(r) == p2 and id(r) not in fk]
        st, src = load_verdict(cons, live, df, cols, p2, BAND_ORDER)
        if st is None:
            return None
        loads[p2] = ({"status": st} if src is None
                     else {"status": st, "source": src})
    return {"carrier": form, "face": face, "d": deg_expr(
        face[0].get("exps") or {}), "loads": loads}


def face_poly_sympy(face):
    """The face's top coefficient as a sympy polynomial in `a..g` and the
    loads, matching the plan's `polys` convention (`ga, ep, et`)."""
    import sympy as sp
    syms = {c: sp.Symbol(c) for c in "abcdefg"}
    lsym = {"gamma": sp.Symbol("ga"), "epsilon": sp.Symbol("ep"),
            "eta": sp.Symbol("et"), "l": sp.Symbol("l"),
            "beta": sp.Symbol("beta"), "delta": sp.Symbol("delta"),
            "zeta": sp.Symbol("zeta"), "theta": sp.Symbol("theta")}
    e = 0
    for r in face:
        t = sp.Rational(int(r["qn"]), int(r["qd"]))
        for L in LET:
            n = int((r.get("exps") or {}).get(L, 0) or 0)
            if n:
                t *= syms[L.lower()] ** n
        ld = rec_load(r)
        if ld:
            t *= lsym[ld]
        e += t
    return sp.expand(e)


def _sub_cons(cons, comp, tag, orient):
    sep = "<" if "<" in comp else "="
    lhs, rhs = [x.strip() for x in comp.split(sep)]
    u, v = CC.lin(lhs), CC.lin(rhs)
    if tag == "=":
        return cons + [(CC.sub7(u, v), False), (CC.sub7(v, u), False)], lhs, rhs
    lt = (tag == "<") != orient
    return (cons + ([(CC.sub7(v, u), True)] if lt else [(CC.sub7(u, v), True)]),
            lhs, rhs)


def build_tree(coords, node, cons, live, zero, leafdata):
    """Validate one node of a plan tree against the Farkas engine, choosing the
    orientation of every pivot so that all three sub-cones check out.  Returns
    the validated node, or None."""
    import sympy as sp
    syms = {c: sp.Symbol(c) for c in "abcdefg"}
    loc = dict(syms)
    for k2 in ("ga", "ep", "et", "l", "beta", "delta", "zeta", "theta"):
        loc[k2] = sp.Symbol(k2)
    if not isinstance(node, dict):
        return None
    kind = node.get("kind")
    if "branches" in node:
        for orient in (False, True):
            kids, ok = {}, True
            for tag in ("<", "=", ">"):
                if tag not in node["branches"]:
                    ok = False
                    break
                c2, lhs, rhs = _sub_cons(cons, node["comparison"], tag, orient)
                k = build_tree(coords, node["branches"][tag], c2, live, zero,
                               leafdata)
                if k is None:
                    ok = False
                    break
                kids[tag] = k
            if ok:
                _c, lhs, rhs = _sub_cons(cons, node["comparison"], "=", orient)
                return {"kind": "split", "lhs": lhs, "rhs": rhs,
                        "orient": orient, "branches": kids}
        return None
    if kind == "infeasible":
        return None if CC.feasible(cons) else {"kind": "infeasible"}
    if kind == "single":
        if "carrier" not in node:
            return None
        for form in ([node["carrier"]] + [f for f in CARRIER_ORDER
                                          if f != node["carrier"]]):
            r = try_single_kill(coords, cons, live, form, zero)
            if r is not None:
                leafdata.append(("single", r))
                return {"kind": "single", "rec": r}
        return None
    if kind == "loadkill":
        if "kill" not in node or "then" not in node:
            return None
        kl = node["kill"]
        t = loaded_top(coords, kl["carrier"], live, cons, kl["load"],
                       kl["mono"])
        if t is None:
            return None
        nxt = build_tree(coords, node["then"], cons, live,
                         zero | {kl["load"]}, leafdata)
        if nxt is None:
            return None
        leafdata.append(("loadkill", t))
        return {"kind": "loadkill", "kill": t, "then": nxt}
    if kind == "system":
        if not all(x in node for x in ("carriers", "polys", "cofactors",
                                       "rows", "target")):
            return None
        rows = []
        for cr in node["carriers"]:
            m = mixed_face(coords, cr, live, cons, zero)
            if m is None:
                return None
            want = sp.sympify(str(node["polys"][cr]).replace("^", "**"),
                              locals=loc)
            got = face_poly_sympy(m["face"])
            ratio = sp.simplify(got / want) if want != 0 else None
            if ratio is None or not ratio.is_number:
                return None
            m["scale"] = sp.Rational(ratio)
            rows.append(m)
        acc = 0
        for co, rp in zip(node["cofactors"], node["rows"]):
            acc += (sp.sympify(str(co).replace("^", "**"), locals=loc)
                    * sp.sympify(str(rp).replace("^", "**"), locals=loc))
        tgt = sp.sympify(str(node["target"]).replace("^", "**"), locals=loc)
        if sp.expand(acc - tgt) != 0:
            return None
        leafdata.append(("system", rows))
        return {"kind": "system", "rows": rows, "target": node["target"],
                "cofactors": node["cofactors"], "polys": node["rows"],
                "carriers": node["carriers"]}
    return None


def tree_entries(coords, chambers, plan):
    """The `trichotomy`/`refinement` entries whose plan tree validates against
    the Farkas engine, load kills and tied-load systems included."""
    cham = {c.name: c for c in chambers}
    out, dropped = [], []
    for e in [x for x in plan["chambers"] + plan["leaves"]
              + plan.get("open", [])
              if x["mode"] in ("trichotomy", "refinement", "partial")]:
        tree = e.get("refinement") or e.get("pivot")
        if tree is None:
            continue
        cons, live = entry_cons(cham, e)
        leafdata = []
        t = build_tree(coords, tree, cons, live, frozenset(), leafdata)
        if t is None:
            dropped.append((e["name"], e.get("leaf"), e["mode"]))
            continue
        f = dict(e)
        f["tree"] = t
        f["leafdata"] = leafdata
        out.append(f)
    return out, dropped


# ------------- Lean for the two new leaf shapes
def _coef_lean(r):
    qn, qd = int(r["qn"]), int(r["qd"])
    if qn < 0:
        return (f"(-({-qn} / {qd} : k))" if qd != 1 else f"(-({-qn} : k))")
    return (f"({qn} / {qd} : k)" if qd != 1 else f"({qn} : k)")


def bound_block(name, param, recs, live, S):
    """`name.natDegree < d` from one hypothesis per surviving degree, chunked
    so that no `compute_degree` ever sees more than `CD_MAX` monomials."""
    surv = surviving(recs, live)
    hyps, seen = [], {}
    for r in surv:
        g = deg_expr(r.get("exps") or {})
        if g not in seen:
            seen[g] = f"hd{len(seen)}"
            hyps.append((seen[g], g))
    parts = split_chunks(surv, CD_MAX) if len(surv) > CD_MAX else []
    body = ""
    for pi, chunk in enumerate(parts):
        pn = f"{name}Part{S}{pi + 1}810"
        body += "set_option maxHeartbeats 64000000 in\n"
        body += (f"/-- Piece {pi + 1}/{len(parts)} of `{name}` on the live set "
                 f"`{S}` ({len(chunk)} monomials). -/\n")
        body += poly_def(pn, param, chunk)
        ph, pseen = [], {}
        for r in chunk:
            g = deg_expr(r.get("exps") or {})
            if g not in pseen:
                pseen[g] = f"hd{len(pseen)}"
                ph.append((pseen[g], g))
        q = ["set_option maxHeartbeats 64000000 in",
             f"theorem {pn}_natDegree_lt", "    {d : \u2115}"]
        if param:
            q.append(f"    ({param} : k)")
        q += ["    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
        for h, g in ph:
            q.append(f"    ({h} : {g} < d)")
        q[-1] += " :"
        q.append(f"    ({pn}{' ' + param if param else ''} A B C D E F G)"
                 ".natDegree < d := by")
        if refl_ok(pn):
            q += refl_bnd_proof(pn)
        else:
            q.append(f"  simp only [{pn}]")
            q.append("  compute_degree")
            q.append("  omega")
        q.append("")
        body += "\n".join(q) + "\n"
    if parts:
        q = ["set_option maxHeartbeats 64000000 in",
             f"theorem {name}_split_of_live_{S}"]
        if param:
            q.append(f"    ({param} : k)")
        q.append("    (A B C D E F G : k[X])")
        for X in SIG:
            if X not in live:
                q.append(f"    (h{X}z : {X} = 0)")
        q[-1] += " :"
        q.append(f"    {name}{' ' + param if param else ''} A B C D E F G =")
        q.append("      " + " +\n        ".join(
            f"{name}Part{S}{pi + 1}810{' ' + param if param else ''} "
            "A B C D E F G" for pi in range(len(parts))) + " := by")
        for X in SIG:
            if X not in live:
                q.append(f"  subst h{X}z")
        for e2 in range(2, 9):
            q.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                     "zero_pow (by decide)")
        q.append("  simp only [" + name + ", "
                 + ", ".join(f"{name}Part{S}{pi + 1}810"
                             for pi in range(len(parts)))
                 + f", {POWNAMES}, {ZERO_SIMP}]")
        q.append("  all_goals module")
        q.append("")
        body += "\n".join(q) + "\n"
    o = ["set_option maxHeartbeats 64000000 in",
         f"theorem {name}_natDegree_lt_of_live_{S}", "    {d : \u2115}"]
    if param:
        o.append(f"    ({param} : k)")
    o += ["    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
    for X in SIG:
        if X not in live:
            o.append(f"    (h{X}z : {X} = 0)")
    for h, g in hyps:
        o.append(f"    ({h} : {g} < d)")
    o[-1] += " :"
    o.append(f"    ({name}{' ' + param if param else ''} A B C D E F G)"
             ".natDegree < d := by")
    if parts:
        zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
        o.append(f"  rw [{name}_split_of_live_{S}"
                 + (f" {param}" if param else "") + " A B C D E F G"
                 + (f" {zargs}" if zargs else "") + "]")
        accs = []
        for pi, chunk in enumerate(parts):
            pn = f"{name}Part{S}{pi + 1}810"
            aa, ps = [], []
            for r in chunk:
                g = deg_expr(r.get("exps") or {})
                if g not in ps:
                    ps.append(g)
                    aa.append(seen[g])
            accs.append(f"({pn}_natDegree_lt"
                        + (f" {param}" if param else "")
                        + " A B C D E F G hdpos"
                        + "".join(f" {x}" for x in aa) + ")")
        acc = accs[0]
        for a in accs[1:]:
            acc = f"(natDegree_add_lt810 {acc} {a})"
        o.append(f"  exact {acc}")
    else:
        for X in SIG:
            if X not in live:
                o.append(f"  subst h{X}z")
        for e2 in range(2, 9):
            o.append(f"  have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                     "zero_pow (by decide)")
        if surv and refl_ok(name):
            o += refl_degok_proof(name)
        else:
            o.append(f"  simp only [{name}, {POWNAMES}, {ZERO_SIMP}]")
            if surv:
                o.append("  compute_degree")
            o.append("  omega")
    o.append("")
    return body + "\n".join(o) + "\n"


def loaded_pieces(coords, form, ld, tops, live, S, packet, idx):
    """Everything a tied load column needs: the tied top terms as their own
    polynomial, the chunk without them, the two split identities, the combined
    rest without them and its degree bound, and the top's `coeff` value."""
    chunks = carrier_col_chunks(coords, form, ld)
    keys = {_dvec(r.get("exps")) for r in tops}
    hit = None
    for nm, recs in chunks:
        if any(_dvec(r.get("exps")) in keys for r in recs):
            if hit is not None and hit[0] != nm:
                return None
            hit = (nm, recs)
    if hit is None:
        return None
    cname, recs = hit
    tt = [r for r in recs if _dvec(r.get("exps")) in keys]
    if len(tt) != len(keys):
        return None
    off = [r for r in recs if _dvec(r.get("exps")) not in keys]
    topname = f"{form}QuarticColumnTop{idx}810"
    offname = f"{form}QuarticColumn{CC.LOAD_CAP[ld]}Off{idx}810"
    restname = f"{form}QuarticChamberRestOff{idx}810"
    d = deg_expr(tt[0].get("exps") or {})
    body = "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- The tied top of the `{ld}` column of `{GREEK_ALL[form]}` "
             f"({len(tt)} monomial, degree `{d}`). -/\n")
    body += poly_def(topname, ld, tt)
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"/-- That column without its tied top ({len(off)} monomials). "
             "-/\n")
    body += poly_def(offname, ld, off)
    o = ["set_option maxHeartbeats 64000000 in",
         f"theorem {cname}_split{idx}", f"    ({ld} : k)",
         "    (A B C D E F G : k[X]) :",
         f"    {cname} {ld} A B C D E F G =",
         f"      {topname} {ld} A B C D E F G + "
         f"{offname} {ld} A B C D E F G := by",
         f"  simp only [{cname}, {topname}, {offname}]", "  module", ""]
    body += "\n".join(o) + "\n"
    others = [(nm, ld2) for ld2 in LOADS
              for nm, _r in carrier_col_chunks(coords, form, ld2)
              if nm != cname]
    rhs = f"{form}QuarticChamberRestLF{packet}810 A B C D E F G"
    for nm, ld2 in others:
        rhs += f" +\n    {nm} {ld2} A B C D E F G"
    rhs += f" +\n    {offname} {ld} A B C D E F G"
    body += "set_option maxHeartbeats 64000000 in\n"
    body += (f"def {restname}\n    ({LOADSIG8} : k)\n"
             "    (A B C D E F G : k[X]) : k[X] :=\n"
             f"  {rhs}\n\n")
    rq = f"{form}QuarticChamberRest{packet}810"
    o = ["set_option maxHeartbeats 64000000 in",
         f"theorem {rq}_split{idx}",
         f"    ({LOADSIG8} : k)", "    (A B C D E F G : k[X]) :",
         f"    {rq} {LOADSIG8} A B C D E F G =",
         f"      {topname} {ld} A B C D E F G +",
         f"        {restname} {LOADSIG8} A B C D E F G := by",
         f"  simp only [{rq}, {restname}, {cname}, {topname}, {offname}]",
         "  all_goals module", ""]
    body += "\n".join(o) + "\n"
    # the coefficient of the tied top
    lets = sorted({L for r in tt for L in LET
                   if int((r.get("exps") or {}).get(L, 0) or 0) > 0},
                  key=LET.index)
    o = ["set_option maxHeartbeats 64000000 in",
         f"theorem {topname}_coeff", f"    ({ld} : k)",
         "    {A B C D E F G : k[X]}"]
    for L in lets:
        o.append(f"    (h{L}ne : {L} ≠ 0)")
    ties = []
    for t, r in enumerate(tt[1:], start=1):
        ties.append((f"ht{t}", f"{deg_expr(r.get('exps') or {})} = {d}"))
    for h, st in ties:
        o.append(f"    ({h} : {st})")
    o[-1] += " :"
    o.append(f"    ({topname} {ld} A B C D E F G).coeff ({d}) =")
    val = " + ".join(
        f"{_coef_lean(r)} * {ld} * ("
        + " * ".join((LC[L] if int((r.get('exps') or {}).get(L, 0) or 0) == 1
                      else f"{LC[L]} ^ {int((r.get('exps') or {}).get(L, 0))}")
                     for L in LET
                     if int((r.get('exps') or {}).get(L, 0) or 0) > 0) + ")"
        for r in tt)
    o.append(f"      {val} := by")
    o.append(f"  simp only [{topname}, coeff_add, coeff_sub, coeff_smul,")
    o.append("    smul_eq_mul]")
    rw = []
    for t, r in enumerate(tt):
        exps = r.get("exps") or {}
        chain, _need, haspow = mono_ne(exps)
        mon = EC.monomial_lean(exps)
        o.append(f"  have hd{t} : ({mon}).natDegree = {d} := by")
        if chain:
            o.append("    rw [" + ", ".join(chain) + "]")
        if haspow:
            o.append("    simp only [natDegree_pow]")
        o.append("    all_goals omega")
        lc = " * ".join(
            (LC[L] if int(exps.get(L, 0) or 0) == 1
             else f"{LC[L]} ^ {int(exps.get(L, 0) or 0)}")
            for L in LET if int(exps.get(L, 0) or 0) > 0)
        o.append(f"  have hc{t} : ({mon}).coeff ({d}) = {lc} := by")
        o.append(f"    rw [← hd{t}, coeff_natDegree]")
        # a `rw` can close the goal outright; guard every trailing tactic
        o.append("    all_goals simp only [leadingCoeff_mul, "
                 "leadingCoeff_pow]")
        rw.append(f"hc{t}")
    o.append("  rw [" + ", ".join(rw) + "]")
    o.append("  all_goals ring")
    o.append("")
    body += "\n".join(o) + "\n"
    return {"body": body, "topname": topname, "offname": offname,
            "restname": restname, "cname": cname, "d": d, "lets": lets,
            "tt": tt,
            "ties": len(ties), "off": off, "others": others,
            "splitname": f"{rq}_split{idx}", "idx": idx, "ld": ld,
            "value": val}


def restoff_bound(coords, form, packet, live, S, pc):
    """`RestOff<i>.natDegree < d`, chained over the load-free rest, the
    untouched column chunks and the chunk minus its tied top."""
    off_surv = surviving(pc["off"], live)
    hyps, seen = [], {}
    _f, rest = None, None
    lfname = f"{form}QuarticChamberRestLF{packet}810"
    lf_recs = None
    out = ["set_option maxHeartbeats 64000000 in",
           f"theorem {pc['restname']}_natDegree_lt_of_live_{S}",
           "    {d : ℕ}", f"    ({LOADSIG8} : k)",
           "    (A B C D E F G : k[X])", "    (hdpos : 0 < d)"]
    for X in SIG:
        if X not in live:
            out.append(f"    (h{X}z : {X} = 0)")
    out.append("    (hlf : "
               f"({lfname} A B C D E F G).natDegree < d)")
    loadhyp = {}
    for ld in LOADS:
        recs = [r for c in carrier_col_chunks(coords, form, ld) for r in c[1]]
        if ld == pc["ld"]:
            recs = pc["off"] + [r for nm, rr in carrier_col_chunks(
                coords, form, ld) if nm != pc["cname"] for r in rr]
        surv = surviving(recs, live)
        if not surv:
            continue
        degs = []
        for r in surv:
            g = deg_expr(r.get("exps") or {})
            if g not in degs:
                degs.append(g)
        loadhyp[ld] = degs
        out.append(f"    (hb{ld} : {ld} = 0 ∨ ("
                   + " ∧ ".join(f"{g} < d" for g in degs) + "))")
    out[-1] += " :"
    out.append(f"    ({pc['restname']} {LOADSIG8} A B C D E F G).natDegree "
               "< d := by")
    zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
    pieces, ci = ["hlf"], 0
    for nm, ld in pc["others"] + [(pc["offname"], pc["ld"])]:
        recs = (pc["off"] if nm == pc["offname"] else
                next(r for n2, r in carrier_col_chunks(coords, form, ld)
                     if n2 == nm))
        surv = surviving(recs, live)
        hn = f"hc{ci}"
        ci += 1
        pieces.append(hn)
        out.append(f"  have {hn} : ({nm} {ld} A B C D E F G).natDegree "
                   "< d := by")
        if not surv:
            for X in SIG:
                if X not in live:
                    out.append(f"    subst h{X}z")
            for e2 in range(2, 9):
                out.append(f"    have hpow{e2} : (0 : k[X]) ^ {e2} = 0 := "
                           "zero_pow (by decide)")
            out.append(f"    simp only [{nm}, {POWNAMES}, {ZERO_SIMP}]")
            out.append("    omega")
            continue
        degs = [deg_expr(r.get("exps") or {}) for r in surv]
        idx = [loadhyp[ld].index(g) for g in degs]
        nh = len(loadhyp[ld])
        pat = ("g0" if nh == 1 else
               "⟨" + ", ".join(f"g{t}" for t in range(nh)) + "⟩")
        out.append(f"    rcases hb{ld} with rfl | {pat}")
        out.append(f"    · rw [{nm}_zero]")
        out.append("      simpa using hdpos")
        out.append(f"    · exact {nm}_natDegree_lt_of_live_{S} {ld} "
                   "A B C D E F G hdpos"
                   + (f" {zargs}" if zargs else "")
                   + (" " + " ".join(f"g{t}" for t in idx) if idx else ""))
    out.append(f"  simp only [{pc['restname']}]")
    acc = pieces[0]
    for h in pieces[1:]:
        acc = (f"natDegree_add_lt810 ({acc}) {h}" if " " in acc
               else f"natDegree_add_lt810 {acc} {h}")
    out.append(f"  exact {acc}")
    out.append("")
    return "\n".join(out) + "\n"


def tree_faces(coords, entries):
    """Assign a face packet to every load-free face a validated tree needs,
    and attach the tied-column data of every loaded face."""
    pid, ids = collections.Counter(), {}

    def pk(form, recs):
        key = (form, frozenset(_dvec(x.get("exps")) for x in recs))
        if key not in ids:
            ids[key] = 9500 + pid[form]
            pid[form] += 1
        return ids[key]
    packets, tied = collections.OrderedDict(), []

    def note(form, recs, live):
        p = pk(form, recs)
        packets.setdefault((form, p), {
            "carrier": form, "packet": p,
            "face": [list(_dvec(x.get("exps"))) for x in recs],
            "d": deg_expr(recs[0].get("exps") or {}), "lives": set()})
        packets[(form, p)]["lives"].add(live)
        return p

    for e in entries:
        S = e["live"]

        def walk(n):
            if n["kind"] == "single":
                r = n["rec"]
                r["packet"] = note(r["carrier"],
                                   [x for x in surviving(
                                       carrier_lf_records(coords, r["carrier"]),
                                       set(S))
                                    if _dvec(x.get("exps")) ==
                                    tuple(r["face"][0])], S)
            elif n["kind"] == "loadkill":
                kl = n["kill"]
                kl["packet"] = note(kl["carrier"], kl["lfface"], S)
                tied.append((kl, S))
                walk(n["then"])
            elif n["kind"] == "system":
                for m in n["rows"]:
                    lf = [x for x in m["face"] if rec_load(x) is None]
                    ld = [x for x in m["face"] if rec_load(x) is not None]
                    m["packet"] = note(m["carrier"], lf, S)
                    m["lf"] = lf
                    m["tied"] = ld
                    if ld:
                        tied.append((m, S))
            for b in (n.get("branches") or {}).values():
                walk(b)
        walk(e["tree"])
    return packets, tied


def emit_tree_pieces(coords, tied, packets, have, prev):
    """The tied-column declarations: one group per (carrier, packet, load)."""
    body, seen, idx = "", {}, collections.Counter()
    info = {}
    for rec, S in tied:
        form = rec["carrier"]
        tops = ([rec["top"]] if "top" in rec else rec["tied"])
        ld = rec_load(tops[0]) or rec.get("load")
        key = (form, rec["packet"], ld,
               frozenset(_dvec(x.get("exps")) for x in tops))
        if key not in seen:
            idx[form] += 1
            i = idx[form]
            pc = loaded_pieces(coords, form, ld, tops, set(S), S,
                               rec["packet"], i)
            if pc is None:
                continue
            body += pc["body"]
            body += ("set_option maxHeartbeats 64000000 in\n"
                     f"theorem {pc['offname']}_zero (A B C D E F G : k[X]) :\n"
                     f"    {pc['offname']} 0 A B C D E F G = 0 := by\n"
                     f"  simp [{pc['offname']}]\n\n")
            seen[key] = pc
        pc = seen[key]
        if (pc["offname"], S) not in info:
            body += bound_block(pc["offname"], ld, pc["off"], set(S), S)
            info[(pc["offname"], S)] = True
        if (pc["restname"], S) not in info:
            body += restoff_bound(coords, form, rec["packet"], set(S), S, pc)
            info[(pc["restname"], S)] = True
        rec["pieces"] = pc
    name = "Grok810ScaleZeroQuarticChamberUnownedTreePiecesScratch"
    doc = ("# Tied load columns, `(8,10)` scale zero\n\n"
           f"{len(seen)} tied tops: the load column's top terms as their own\n"
           "polynomial, the column and the combined rest without them, the two\n"
           "split identities, the rest bound and the top's `coeff` value.  This\n"
           "is what a load kill and a tied-load system row need on top of the\n"
           "ordinary face packets.  Untracked working note.")
    out = (header(prev, doc) + "section QuarticChamberUnownedTreePieces810\n\n"
           + body + "\nend QuarticChamberUnownedTreePieces810\n" + FOOTER)
    ln = write(name + ".lean", out)
    MODULES.append((name, ln, f"{len(seen)} tied load-column splits"))
    return name


def recs_lean(recs, var, loadvar):
    """A list of coordinate records as a Lean scalar expression."""
    out = []
    for r in recs:
        parts = [_coef_lean(r)]
        ld = rec_load(r)
        if ld:
            parts.append(loadvar(ld))
        for L in LET:
            e = int((r.get("exps") or {}).get(L, 0) or 0)
            if e == 1:
                parts.append(var(L))
            elif e > 1:
                parts.append(f"{var(L)} ^ {e}")
        out.append(" * ".join(parts))
    return " + ".join(out) if out else "0"


def ne_chain(exps, hname):
    fac = [(L, int((exps or {}).get(L, 0) or 0)) for L in LET
           if int((exps or {}).get(L, 0) or 0) > 0]

    def leaf(L, e):
        return hname(L) if e == 1 else f"(pow_ne_zero {e} {hname(L)})"
    acc = leaf(*fac[0])
    for L, e in fac[1:]:
        acc = f"(mul_ne_zero {acc} {leaf(L, e)})"
    return acc


def tree_node_lines(coords, S, live, node, packets, facedeg, bridges, ind,
                    ctr, base=None):
    """The tactic block closing one node of a validated plan tree."""
    if node["kind"] == "infeasible":
        return [ind + "omega"]
    if node["kind"] == "single":
        return branch_kill_lines(coords, S, live, node["rec"], packets,
                                 facedeg, ind, base)
    if node["kind"] == "split":
        o = [ind + f"rcases lt_trichotomy ({node['lhs']}) ({node['rhs']}) "
             "with hpv | hpv | hpv"]
        for tag in ("<", "=", ">") if not node["orient"] else (">", "=", "<"):
            o.append(ind + "·")
            o += tree_node_lines(coords, S, live, node["branches"][tag],
                                 packets, facedeg, bridges, ind + "  ", ctr,
                                 base)
        return o
    if node["kind"] == "loadkill":
        kl = node["kill"]
        o = _carrier_coeff_lines(coords, S, live, kl, packets, facedeg,
                                 bridges, ind, ctr, "hlk")
        pc = kl["pieces"]
        ld = kl["load"]
        exps = kl["top"].get("exps") or {}
        o.append(ind + f"have hzero{ld} : {ld} = 0 := by")
        o.append(ind + "  rcases mul_eq_zero.mp hlk with h | h")
        o.append(ind + "  · rcases mul_eq_zero.mp h with h2 | h2")
        o.append(ind + "    · exact absurd h2 (by norm_num)")
        o.append(ind + "    · exact h2")
        o.append(ind + "  · exact absurd h "
                 + ne_chain(exps, lambda L: (f"h{L}c" if L != "A" else "hAc")))
        for L in LET:
            if int(exps.get(L, 0) or 0) > 0:
                pass
        return o + tree_node_lines(coords, S, live, node["then"], packets,
                                   facedeg, bridges, ind, ctr, base)
    # a multi-carrier system, possibly with tied load columns
    o, ins = [], []
    for m in node["rows"]:
        nm = f"hsy{ctr[0]}"
        ctr[0] += 1
        o += _carrier_coeff_lines(coords, S, live, m, packets, facedeg,
                                  bridges, ind, ctr, nm)
        pcm = m.get("pieces")
        if pcm and len(pcm["tt"]) > 1:
            # the rewrite leaves the tied top as its own parenthesised sum,
            # `face + (top₁ + top₂)`, while the certificate states the row
            # flat; `exact` is syntactic, so re-associate on the way in
            ins.append(f"(by linear_combination {nm})")
        else:
            ins.append(nm)
    lets = sorted({L for m in node["rows"] for r in m["face"] for L in LET
                   if int((r.get("exps") or {}).get(L, 0) or 0) > 0},
                  key=LET.index)
    tl = target_factors(node["target"])
    for L, _n in tl:
        if L not in lets:
            lets.append(L)
    o.append(ind + f"exact {node['cert']} "
             + " ".join(LC[L] for L in LET) + " "
             + " ".join(LOADSYM.get(x, x) for x in node["certloads"]) + " "
             + " ".join(ins) + " "
             + " ".join(f"h{L}c" for L, _n in tl))
    return o


def _carrier_coeff_lines(coords, S, live, m, packets, facedeg, bridges, ind,
                         ctr, hname):
    """`hname : <face coefficient> = 0` for one carrier on one sub-chamber,
    with the tied load column split off when there is one."""
    form, p = m["carrier"], m["packet"]
    d = m["d"]
    pc = m.get("pieces")
    lf = m.get("lf", m.get("lfface"))
    fnm, need, fd, face = facedeg[(form, p)]
    _f, rest = unowned_face(coords, form, packets[(form, p)]["face"])
    surv_lf = surviving(rest, live)
    k = KDEG_ALL[form]
    lhs = "0" if k == 0 else ("A.natDegree" if k == 1
                              else f"{k} * A.natDegree")
    tag = ctr[0]
    ctr[0] += 1
    o = []
    o.append(ind + f"have hdp{tag} : {lhs} < {d} := by")
    o.append(ind + "  omega")
    o.append(ind + f"have hdz{tag} : 0 < {d} := by omega")
    srcs = sorted({v.get("source") for v in m["loads"].values()
                   if v["status"].startswith("band")})
    for s in srcs:
        casc, loads, var, ex, _n = UNOWNED_BAND[s]
        o.append(ind + "obtain ⟨" + ", ".join(var.format(x) for x in loads)
                 + "⟩ :=")
        o.append(ind + f"  {casc} {LOADSIG8}")
        o.append(ind + f"    A B C D E F G hA{ex}")
    args, hi = [], 0
    for ld in LOADS:
        v = m["loads"][ld]
        if v["status"] == "empty":
            continue
        if v["status"] == "zero":
            args.append(f"(Or.inl hzero{ld})")
            continue
        cols = [x for cnk in carrier_col_chunks(coords, form, ld)
                for x in cnk[1]]
        if pc is not None and ld == pc["ld"]:
            cols = pc["off"] + [x for nm2, rr in carrier_col_chunks(
                coords, form, ld) if nm2 != pc["cname"] for x in rr]
        uniq = []
        for x in surviving(cols, live):
            g = deg_expr(x.get("exps") or {})
            if g not in uniq:
                uniq.append(g)
        if not uniq:
            continue
        comps = []
        for g in uniq:
            if v["status"].endswith("-hnc"):
                hn = f"hg{tag}{hi}"
                hi += 1
                o.append(ind + f"have {hn} : {g} < {d} := by")
                o += [ind + "  " + x.strip() for x in HNC_BLOCK]
                comps.append(hn)
            else:
                comps.append("by omega")
        conj = ("(by omega)" if all(x == "by omega" for x in comps)
                else (comps[0] if len(comps) == 1
                      else "⟨" + ", ".join(comps) + "⟩"))
        if v["status"].startswith("dominated"):
            args.append(f"(Or.inr {conj})")
            continue
        hn = f"hz{tag}{ld}"
        args.append(hn)
        dis = unowned_band_disjuncts(v["source"], ld)
        o.append(ind + f"have {hn} : {ld} = 0 ∨ ("
                 + " ∧ ".join(f"{g} < {d}" for g in uniq) + ") := by")
        o.append(ind + f"  rcases {UNOWNED_BAND[v['source']][2].format(ld)} "
                 "with h | " + " | ".join("h" for _ in dis))
        o.append(ind + "  · exact Or.inl h")
        for X, _s in dis:
            if X is not None and TOP[ld][X] == "hard":
                o.append(ind + f"  · exact absurd h{X}z h")
            else:
                o.append(ind + f"  · exact Or.inr {conj}")
    zargs = " ".join(f"h{X}z" for X in SIG if X not in live)
    seenlf = []
    for x in surv_lf:
        g = deg_expr(x.get("exps") or {})
        if g not in seenlf:
            seenlf.append(g)
    lfargs = " ".join("(by omega)" for _ in seenlf)
    nea = " ".join(f"h{L}ne" if L != "A" else "hAne" for L in need)
    # `need` is the leading monomial's letters, which is what the face
    # `_natDegree` lemma binds; the `_coeff_top` bridge instead binds one
    # `≠ 0` hypothesis per letter of *every* monomial, in `LET` order, and
    # leaves the remaining `A..G` implicit and unsynthesisable
    blets = sorted({L for r in face for L in LET
                    if int((r.get("exps") or {}).get(L, 0) or 0) > 0},
                   key=LET.index)
    bnea = (" ".join(f"h{L}ne" if L != "A" else "hAne" for L in blets)
            + coeff_top_named(blets))
    ftie = " ".join("(by omega)" for _ in face[1:])
    bnm, bval = bridges[(form, p)]
    if pc is None:
        rname = f"{form}QuarticChamberRest{p}810"
        o.append(ind + f"have hr{tag} : ({rname} {LOADSIG8}")
        o.append(ind + f"    A B C D E F G).natDegree < {d} :=")
        o.append(ind + f"  {rname}_natDegree_lt_of_live_{S} {LOADSIG8}")
        o.append(ind + f"    A B C D E F G hdz{tag}"
                 + (f" {zargs}" if zargs else "")
                 + (f" {lfargs}" if lfargs else "")
                 + (" " + " ".join(args) if args else ""))
    else:
        lnm = f"{form}QuarticChamberRestLF{p}810"
        o.append(ind + f"have hlf{tag} : ({lnm} A B C D E F G).natDegree "
                 f"< {d} :=")
        o.append(ind + f"  {lnm}_natDegree_lt_of_live_{S}")
        o.append(ind + f"    A B C D E F G hdz{tag}"
                 + (f" {zargs}" if zargs else "")
                 + (f" {lfargs}" if lfargs else ""))
        o.append(ind + f"have hr{tag} : ({pc['restname']} {LOADSIG8}")
        o.append(ind + f"    A B C D E F G).natDegree < {d} :=")
        o.append(ind + f"  {pc['restname']}_natDegree_lt_of_live_{S} "
                 f"{LOADSIG8}")
        o.append(ind + f"    A B C D E F G hdz{tag}"
                 + (f" {zargs}" if zargs else "")
                 + f" hlf{tag}" + (" " + " ".join(args) if args else ""))
    o.append(ind + f"have {hname} : ({CARRIER_LEAN[form]} {LOADSIG8}")
    o.append(ind + f"    A B C D E F G).coeff ({d}) = 0 := by")
    o.append(ind + "  apply coeff_eq_zero_of_natDegree_lt")
    if form in AUXDEFS:
        pre = ""
        hargs = aux_le_argstr(form)
        o.append(ind + f"  have hle := {CARRIER_LEAN[form]}_natDegree_le "
                 f"{LOADSIG8}")
        o.append(ind + f"    A B C D E F G {pre}{hargs}")
        o.append(ind + "  omega")
    else:
        o.append(ind + f"  rw [{DEGHYP_ALL[form][0]}]")
        o.append(ind + "  omega")
    if pc is None:
        o.append(ind + f"rw [{CARRIER_LEAN[form]}_eq_face{p}_add_rest, "
                 "coeff_add,")
        o.append(ind + f"  coeff_eq_zero_of_natDegree_lt hr{tag}, add_zero,")
        o.append(ind + f"  {bnm} {bnea}" + (f" {ftie}" if ftie else "")
                 + f"] at {hname}")
    else:
        ttie = " ".join("(by omega)" for _ in range(pc["ties"]))
        tne = " ".join(f"h{L}ne" if L != "A" else "hAne" for L in pc["lets"])
        below = "top" in m
        topcall = (f"{pc['topname']}_coeff {pc['ld']} {tne}"
                   + (f" {ttie}" if ttie else ""))
        if pc["d"] != d:
            # on this branch the column ties the face, so its top-coefficient
            # lemma - stated at the column's own degree - has to be restated
            # at the tied degree before it can rewrite the row
            o.append(ind + f"have hcc{tag} : ({pc['topname']} {pc['ld']} "
                     "A B C D E F G).coeff")
            o.append(ind + f"    ({d}) =")
            o.append(ind + f"    {pc['value']} := by")
            o.append(ind + f"  rw [show ({d}) = ({pc['d']}) from by omega]")
            o.append(ind + f"  exact {topcall}")
            topcall = f"hcc{tag}"
        if below:
            o.append(ind + f"have hfl{tag} : ({form}QuarticChamberFace{p}810 "
                     "A B C D E F G).natDegree")
            o.append(ind + f"    < {d} := by")
            o.append(ind + f"  rw [{fnm} A B C D E F G {nea}]")
            o.append(ind + "  omega")
        o.append(ind + f"rw [{CARRIER_LEAN[form]}_eq_face{p}_add_rest,")
        o.append(ind + f"  {pc['splitname']} {LOADSIG8} A B C D E F G,")
        o.append(ind + "  coeff_add, coeff_add,")
        if below:
            o.append(ind + f"  coeff_eq_zero_of_natDegree_lt hfl{tag}, "
                     "zero_add,")
        o.append(ind + f"  coeff_eq_zero_of_natDegree_lt hr{tag}, add_zero,")
        o.append(ind + f"  {topcall}" + ("]" if below else ","))
        if not below:
            o.append(ind + f"  {bnm} {bnea}" + (f" {ftie}" if ftie else "")
                     + "]")
        o[-1] += f" at {hname}"
    return o


def emit_unowned_trees(coords, chambers, entries, packets, have, prev):
    """The trichotomy / refinement trees whose leaves are single-carrier kills,
    load kills, tied-load systems or Farkas-infeasible cones."""
    import sympy as sp
    cham = {c.name: c for c in chambers}
    rex = refined_leaf_extra()
    head, facedeg, seen = "/-! ## Face degrees -/\n\n", {}, set()
    for (form, p), pk in packets.items():
        txt, nm, need, d, face = face_degree_lemma(coords, form, p, packets,
                                                   have, seen)
        head += txt
        facedeg[(form, p)] = (nm, need, d, face)
    head += "/-! ## Top-coefficient bridges -/\n\n"
    bridges = {}
    for (form, p), pk in packets.items():
        face, _r = unowned_face(coords, form, packets[(form, p)]["face"])
        d = deg_expr(face[0].get("exps") or {})
        nm = f"{form}QuarticChamberFace{p}810_coeff_top"
        val = recs_lean(face, lambda L: LC[L], lambda x: x)
        bridges[(form, p)] = (nm, val)
        if nm not in have:
            head += coeff_top_lemma(form, p, face, d, nm, val)
    head += "/-! ## The scalar certificates -/\n\n"
    ctr = [0]
    for e in entries:
        def cert(n):
            if n["kind"] == "system":
                n["cert"] = f"quarticUnownedTree{ctr[0]}810_cert"
                lds = []
                for m in n["rows"]:
                    for r in m["face"]:
                        ld = rec_load(r)
                        if ld and ld not in lds:
                            lds.append(ld)
                n["certloads"] = lds
                ctr[0] += 1
            for b in (n.get("branches") or {}).values():
                cert(b)
            if n["kind"] == "loadkill":
                cert(n["then"])
        cert(e["tree"])
    nsys = 0
    for e in entries:
        def emit_cert(n):
            nonlocal head, nsys
            if n["kind"] == "system":
                lds = n["certloads"]
                syms = {c: sp.Symbol(c) for c in "abcdefg"}
                loc = dict(syms)
                for k2 in ("ga", "ep", "et", "l", "beta", "delta", "zeta",
                           "theta"):
                    loc[k2] = sp.Symbol(k2)
                rows = [face_poly_sympy(m["face"]) for m in n["rows"]]
                cof = [sp.sympify(str(c).replace("^", "**"), locals=loc)
                       / m["scale"]
                       for c, m in zip(n["cofactors"], n["rows"])]
                tgt = sp.sympify(str(n["target"]).replace("^", "**"),
                                 locals=loc)
                assert sp.expand(sum(c * r for c, r in zip(cof, rows))
                                 - tgt) == 0, n["cert"]
                o = ["set_option maxHeartbeats 64000000 in",
                     f"/-- {len(rows)} face rows force "
                     f"`{target_lean(n['target'])} = 0`. -/",
                     f"theorem {n['cert']}", "    (a b c d e f g : k)"]
                if lds:
                    o.append("    (" + " ".join(LOADSYM.get(x, x)
                                                for x in lds) + " : k)")
                for i2, m in enumerate(n["rows"]):
                    o.append(f"    (hr{i2} : "
                             + recs_lean(m["face"], lambda L: L.lower(),
                                         lambda x: LOADSYM.get(x, x))
                             + " = 0)")
                tl = target_factors(n["target"])
                for L, _q in tl:
                    o.append(f"    (h{L}c : ({L.lower()} : k) ≠ 0)")
                o[-1] += " :"
                o.append("    False := by")
                comb = [f"({poly_lean_loads(c, loc)}) * hr{i2}"
                        for i2, c in enumerate(cof) if c != 0]
                o.append(f"  have ht : {target_lean(n['target'])} = 0 := by")
                o.append("    linear_combination " + " + ".join(comb))
                o.append(f"  exact "
                         f"{target_ne_term(n['target'], lambda L: f'h{L}c')} ht")
                o.append("")
                head += "\n".join(o) + "\n"
                nsys += 1
            for b in (n.get("branches") or {}).values():
                emit_cert(b)
            if n["kind"] == "loadkill":
                emit_cert(n["then"])
        emit_cert(e["tree"])
    body, nk, killmap = "/-! ## The tree kills -/\n\n", 0, {}
    for e in entries:
        c = cham[e["name"]]
        S, live = e["live"], set(e["live"])
        leafi = e.get("leaf")
        if leafi is None:
            thname = f"quarticChamber{c.name}810_impossible"
            hyptype = c.defname
            extra = 0
        else:
            thname = f"quarticRefined{c.name}L{leafi}810_impossible"
            hyptype = f"QuarticRefined{c.name}L{leafi}810"
            extra = rex[(c.name, leafi)]
        needf, srcs = [], set()

        def scan(n):
            for m in ([n["rec"]] if n["kind"] == "single" else
                      ([n["kill"]] if n["kind"] == "loadkill" else
                       (n["rows"] if n["kind"] == "system" else []))):
                f = m["carrier"]
                for x in (AUXNEEDS[f] if f in AUXDEFS else [f]):
                    if x not in needf:
                        needf.append(x)
                srcs.update({v.get("source") for v in m["loads"].values()
                             if v["status"].startswith("band")})
            for b in (n.get("branches") or {}).values():
                scan(b)
            if n["kind"] == "loadkill":
                scan(n["then"])
        scan(e["tree"])
        for s2 in sorted(srcs):
            for x in UNOWNED_BAND[s2][4]:
                if x not in needf:
                    needf.append(x)
        needf = [f for f in HYP_ORDER if f in needf or f == "kappa"]
        o = ["set_option maxHeartbeats 64000000 in",
             f"/-- Unowned chamber `{S}` / `{'·'.join(e['argmin'])}`"
             + (f" leaf {leafi}" if leafi is not None else "")
             + " dies on a plan tree (load kills and tied-load systems "
             "included). -/",
             f"theorem {thname}", f"    ({LOADSIG8} : k)",
             "    (A B C D E F G : k[X])",
             f"    (hch : {hyptype} A B C D E F G)",
             "    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧",
             "        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))"]
        for f in needf:
            h, rel = DEGHYP_ALL[f]
            o.append(f"    ({h} : ({CC.FORM_LEAN[f]} {LOADSIG8}")
            o.append(f"          A B C D E F G).natDegree {rel})")
        killmap[(e["name"], leafi)] = (thname,
                                       [DEGHYP_ALL[f][0] for f in needf])
        o[-1] += " :"
        o.append("    False := by")
        names = ["hA"] + [f"h{X}ne" if X in live else f"h{X}z" for X in SIG]
        names += [f"hq{i}" for i in range(len(c.nums()))]
        src = "hch"
        if extra:
            o.append("  obtain ⟨hcell, "
                     + ", ".join(f"hx{t}" for t in range(extra)) + "⟩ := hch")
            src = "hcell"
        o.append(f"  obtain ⟨{', '.join(names)}⟩ := {src}")
        o.append("  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA")
        for X in SIG:
            if X not in live:
                o.append(f"  have h{X}n : {X}.natDegree = 0 := by simp [h{X}z]")
        o += ["  have hAne : A ≠ 0 := by", "    intro h0",
              "    have hz0 : A.natDegree = 0 := by simp [h0]", "    omega"]
        o.append("  have hAc : A.leadingCoeff ≠ 0 := "
                 "leadingCoeff_ne_zero.mpr hAne")
        for X in SIG:
            if X in live:
                o.append(f"  have h{X}c : {X}.leadingCoeff ≠ 0 := "
                         f"leadingCoeff_ne_zero.mpr h{X}ne")
        # the chamber keeps its `hq…` names here (no `name_chamber_facts`)
        cbase = (chamber_cons_named(c.nums(), tag="hq") + CONE_CONS
                 + dead_cons(live) + NONNEG_CONS)
        o += tree_node_lines(coords, S, live, e["tree"], packets, facedeg,
                             bridges, "  ", [0], cbase)
        o.append("")
        body += prune_arith(
            name_path_values(sparse_tree_rows("\n".join(o), head)),
            TREE_KEEP) + "\n"
        nk += 1
    name = "Grok810ScaleZeroQuarticChamberUnownedTreesScratch"
    doc = ("# Unowned plan trees, `(8,10)` scale zero\n\n"
           f"{nk} chambers that need a nested case split whose leaves include "
           f"a\nload kill (a load column alone on top forces `p = 0`) or a "
           "tied-load\ntop-coefficient system.  Every pivot orientation, every "
           "face and every\nload-column verdict is re-derived here with the "
           "exact Farkas engine;\nthe cofactors are the plan's, rescaled to "
           f"these rows and re-checked.\n{nsys} scalar certificates.  "
           "Untracked working note.")
    blocks = [x + "\n" for x in body.split("\nset_option maxHeartbeats")
              if x.strip()]
    blocks = ([blocks[0]] + ["set_option maxHeartbeats" + x
                             for x in blocks[1:]]) if blocks else []
    groups, cur, curl = [], [], 0
    for b in blocks:
        n = b.count("\n")
        if cur and curl + n > 2000:
            groups.append(cur)
            cur, curl = [], 0
        cur.append(b)
        curl += n
    if cur:
        groups.append(cur)
    names = []
    hname = "Grok810ScaleZeroQuarticChamberUnownedTreeCertsScratch"
    hout = (header(prev, "# Plan-tree faces, bridges and scalar certificates\n"
                   "\nUntracked working note.")
            + "section QuarticChamberUnownedTreeCerts810\n\n" + head
            + "\nend QuarticChamberUnownedTreeCerts810\n" + FOOTER)
    hln = write(hname + ".lean", hout)
    MODULES.append((hname, hln, f"{len(bridges)} tree bridges and {nsys} "
                                "scalar certificates"))
    names.append(hname)
    for gi, grp in enumerate(groups or [[]]):
        nm = (f"Grok810ScaleZeroQuarticChamberUnownedTreesScratch"
              if len(groups) <= 1 else
              f"Grok810ScaleZeroQuarticChamberUnownedTrees{gi + 1}Scratch")
        sec = ("QuarticChamberUnownedTrees810" if len(groups) <= 1
               else f"QuarticChamberUnownedTrees{gi + 1}810")
        split_decls(nm, sec, doc, grp, list(prev) + [hname])
        MODULES.append((nm, sum(b.count("\n") for b in grp),
                        f"{len(grp)} plan-tree chamber kills"))
        names.append(nm)
    return names, killmap


def poly_lean_loads(e, loc):
    """A sympy expression in `a..g` and the load symbols as a Lean term."""
    import sympy as sp
    vs = [loc[k] for k in ("a", "b", "c", "d", "e", "f", "g", "ga", "ep",
                           "et", "l", "beta", "delta", "zeta", "theta")]
    ren = {"ga": "gamma", "ep": "epsilon", "et": "eta"}
    e = sp.expand(e)
    if e == 0:
        return "0"
    out = []
    for mono, coef in sp.Poly(e, *vs).terms():
        cq = sp.Rational(coef)
        n, dd = int(cq.p), int(cq.q)
        fac = [f"({n} : k)" if dd == 1 else f"({n} / {dd} : k)"]
        for i2, ex in enumerate(mono):
            if ex == 0:
                continue
            nm = str(vs[i2])
            nm = ren.get(nm, nm)
            fac.append(nm if ex == 1 else f"{nm} ^ {ex}")
        out.append(" * ".join(fac))
    return " + ".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="all")
    args = ap.parse_args()
    data = CC.load_chambers()
    chambers = build_chambers(data)
    log(f"{len(chambers)} chambers ({len(data['chambers'])} JSON leaves, "
        f"{sum(1 for c in chambers if c.refined)} carrier-refined cells)")
    coords = CC.load_coords()
    prev = emit_defs(chambers)
    prev, trees = emit_exhaust(chambers, prev)
    prev, packets = emit_faces(data, coords, chambers, prev)
    prev = emit_aux_tower(coords, prev)
    prev = emit_bands(prev)
    plan = load_plan()
    prev = emit_columns(coords, plan, prev)
    prev = emit_rests(coords, plan, prev)
    prev, killed = emit_kills(data, coords, chambers, plan, prev)
    prev, surv, kills = emit_residual(data, chambers, plan, killed, prev)
    prev = emit_cost_ladder(prev)
    p2 = ROOT / "scripts" / "out_810_quartic_chamber_killplan2.json"
    if p2.exists():
        plan2 = load_plan2()
        have = declared_names([
            "Grok810ScaleZeroQuarticChamberFacesScratch",
            "Grok810ScaleZeroQuarticChamberColumnsScratch",
            "Grok810ScaleZeroQuarticChamberRestsScratch",
            "Grok810ScaleZeroQuarticChamberKillsScratch"])
        prev = emit_columns2(coords, plan2, have, prev)
        prev = emit_rests2(coords, plan2, have, prev)
        prev, killed2 = emit_kills2(data, coords, chambers, plan2, have,
                                    killed, prev)
        prev, surv2, kills2 = emit_residual2(data, chambers, plan, plan2, prev)
    else:
        log("kill plan v2 absent - modules 17-20 skipped")
    p3 = ROOT / "scripts" / "out_810_quartic_chamber_killplan3.json"
    if p2.exists() and p3.exists():
        MOD9 = ["Grok810ScaleZeroQuarticChamberFacesScratch",
                "Grok810ScaleZeroQuarticChamberColumnsScratch",
                "Grok810ScaleZeroQuarticChamberRestsScratch",
                "Grok810ScaleZeroQuarticChamberKillsScratch",
                "Grok810ScaleZeroQuarticChamberColumns2Scratch",
                "Grok810ScaleZeroQuarticChamberRests2Scratch",
                "Grok810ScaleZeroQuarticChamberKills2Scratch"]
        plan3full = plan3_leaves(data, coords, chambers, load_plan3())
        extra = dict(plan3full)
        if (ROOT / "scripts" /
                "out_810_quartic_chamber_killplan4.json").exists():
            p4f = plan4_leaves(data, coords, load_plan4())
            extra = {"packets": plan3full["packets"] + p4f["packets"],
                     "leaves": plan3full["leaves"] + p4f["leaves"]}
        prev = emit_extra_faces(data, coords, extra,
                                declared_names(MOD9), prev)
        MOD9.append("Grok810ScaleZeroQuarticChamberNuFacesScratch")
        prev = emit_columns2(
            coords, plan3full, declared_names(MOD9), prev, tag="3",
            doc="# Load-column bounds for the carrier-change kills, `(8,10)` "
                "scale zero\n\nThe further (carrier, load, live-set) column "
                "bounds the corner-`H` carrier change needs.  Untracked "
                "working note.")
        MOD9.append("Grok810ScaleZeroQuarticChamberColumns3Scratch")
        prev = emit_rests2(
            coords, plan3full, declared_names(MOD9), prev, tag="3",
            doc="# Chamber rests for the carrier-change kills, `(8,10)` scale "
                "zero\n\nUntracked working note.")
        MOD9.append("Grok810ScaleZeroQuarticChamberRests3Scratch")
        killed12 = set(killed) | set(killed2)
        prev, killed3 = emit_kills2(
            data, coords, chambers, plan3full,
            declared_names(MOD9), killed12, prev, tag="3",
            doc="# Carrier-change chamber kills, `(8,10)` scale zero\n\nThe "
                "certificate carrier is not sacred: any integral whose face on "
                "the chamber is a single monomial kills it once all eight load "
                "columns clear.  `π` and `ξ` have `γ`/`ε` columns of letter "
                "count ≥ 2, which is what corner `H` needs (plan §2.4).  "
                "Decided by "
                "`scripts/derive_810_quartic_chamber_killplan3.py`.  Untracked "
                "working note.")
        allkills = dict(kills2)
        for e in plan3full["leaves"]:
            key = (e["live"], tuple(e["argmin"]))
            if key in allkills or key not in killed3:
                continue
            r = e["carriers"][0]
            srcs = {v.get("source") for v in r["loads"].values()
                    if v["status"] == "band"}
            allkills[key] = (r["carrier"], "n2-cost" in srcs)
        note = ("Honest leftover after the carrier change.  Closed relative to "
                "`normalized810ScaleZero_quarticLoadLadderResidual`: the "
                "1115-chamber exhaust and every single-monomial kill of "
                "modules 14, 19 and 23.  Remaining: the all-constant corner, "
                "the `power_target`/`no_monomial_target` leaves (which need "
                "the `_coeff_top` extraction), the 11 carrier-refined cells, "
                "the leaves with no single-monomial carrier, and the "
                "open/rescue/weak-band families of "
                "`~/lean/tools/sigma810/OPEN_CHAMBERS.md`, which the parallel "
                "tower lane closes.  No `sorry`, no new axioms, no "
                "finite-root shortcut.")
        prev, surv3 = emit_residual_gen(
            chambers, allkills, prev, "3",
            "# Residual after the carrier change, `(8,10)` scale zero\n\n"
            "Untracked working note.", note)
    else:
        log("kill plan v3 absent - modules 21-24 skipped")
    p4 = ROOT / "scripts" / "out_810_quartic_chamber_killplan4.json"
    if p3.exists() and p4.exists():
        MOD9 += ["Grok810ScaleZeroQuarticChamberKills3Scratch"]
        plan4full = plan4_leaves(data, coords, load_plan4())
        prev = emit_columns2(
            coords, plan4full, declared_names(MOD9), prev, tag="4",
            kinds=("multi",),
            doc="# Load-column bounds for the multi-carrier kills, `(8,10)` "
                "scale zero\n\nUntracked note.")
        MOD9.append("Grok810ScaleZeroQuarticChamberColumns4Scratch")
        prev = emit_rests2(
            coords, plan4full, declared_names(MOD9), prev, tag="4",
            kinds=("multi",),
            doc="# Chamber rests for the multi-carrier kills, `(8,10)` scale "
                "zero\n\nUntracked working note.")
        MOD9.append("Grok810ScaleZeroQuarticChamberRests4Scratch")
        prev, innername, sysname, ctname, systems = emit_inner(
            data, coords, plan4full, declared_names(MOD9), prev)
        MOD9.append("Grok810ScaleZeroQuarticChamberInnerScratch")
        prev, killed4 = emit_kills4(
            data, coords, chambers, plan4full, innername, sysname, ctname,
            declared_names(MOD9), prev)
        for key in killed4:
            e = next(x for x in plan4full["leaves"]
                     if (x["live"], tuple(x["argmin"])) == key)
            r = e["carriers"][0]
            srcs = {v.get("source") for rr in e["carriers"]
                    for v in rr["loads"].values() if v["status"] == "band"}
            forms = [rr["carrier"] for rr in e["carriers"]]
            _rh = {"kappa": "hkapDeg", "mu": "hmuDeg", "xi": "hxiDeg",
                   "pi": "hpiDeg", "nu": "hnuDeg", "omicron": "homiDeg"}
            allkills[key] = (r["carrier"],
                             ("n2-cost" in srcs) or ("nu" in forms),
                             [_rh[f] for f in forms
                              if f not in ("kappa", "nu")])
        note4 = ("Honest leftover after the multi-carrier kills.  Closed "
                 "relative to "
                 "`normalized810ScaleZero_quarticLoadLadderResidual`: the "
                 "1115-chamber exhaust and every kill of modules 14, 19, 23 "
                 "and 29.  Remaining: the all-constant corner, the "
                 "`power_target` leaves whose cofactors the taxonomy never "
                 "recorded, the 11 carrier-refined cells, corner `H`, and the "
                 "open/rescue/weak-band families of "
                 "`~/lean/tools/sigma810/OPEN_CHAMBERS.md`.  No `sorry`, no "
                 "new axioms, no finite-root shortcut.")
        prev, surv4 = emit_residual_gen(
            chambers, allkills, prev, "4",
            "# Residual after the multi-carrier kills, `(8,10)` scale zero\n\n"
            "Untracked working note.", note4)
        prev, refined, refinj = emit_refine(data, chambers, prev)
        p5 = ROOT / "scripts" / "out_810_quartic_chamber_killplan5.json"
        if p5.exists():
            MOD9 += ["Grok810ScaleZeroQuarticChamberKills4Scratch",
                     "Grok810ScaleZeroQuarticChamberInnerScratch",
                     "Grok810ScaleZeroQuarticChamberRests4Scratch"]
            plan5full = plan5_leaves(data, coords, load_plan5())
            prev = emit_columns2(
                coords, plan5full, declared_names(MOD9), prev, tag="5",
                kinds=("power",),
                doc="# Load-column bounds for the power-target kills, `(8,10)` "
                    "scale zero\n\nUntracked note.")
            MOD9.append("Grok810ScaleZeroQuarticChamberColumns5Scratch")
            prev = emit_rests2(
                coords, plan5full, declared_names(MOD9), prev, tag="5",
                kinds=("power",),
                doc="# Chamber rests for the power-target kills, `(8,10)` "
                    "scale zero\n\nUntracked working note.")
            MOD9.append("Grok810ScaleZeroQuarticChamberRests5Scratch")
            prev, kill5 = emit_power_kills(
                data, coords, chambers, plan5full, declared_names(MOD9), prev)
            allkills.update(kill5)
            note5 = ("Honest leftover after the power-target certificates.  "
                     "Closed relative to "
                     "`normalized810ScaleZero_quarticLoadLadderResidual`: the "
                     "1115-chamber exhaust and every kill of modules 14, 19, "
                     "23, 29 and 35.  Remaining: the all-constant corner and "
                     "the chambers of `QuarticChamberResidual5810` — the tower "
                     "lane's 2 open / 19 deep-rescue / weak-band families, the "
                     "carrier-refined cells, corner `H`, and the power systems "
                     "whose columns do not clear.  No `sorry`, no new axioms, "
                     "no finite-root shortcut.")
            prev, surv5 = emit_residual_gen(
                chambers, allkills, prev, "5",
                "# Residual after the power-target kills, `(8,10)` scale "
                "zero\n\nUntracked working note.", note5)
            surv4 = surv5
            p6 = ROOT / "scripts" / "out_810_quartic_chamber_killplan6.json"
            if p6.exists():
                MOD9 += ["Grok810ScaleZeroQuarticChamberRests5Scratch",
                         "Grok810ScaleZeroQuarticChamberColumns5Scratch",
                         "Grok810ScaleZeroQuarticChamberPowerKillsScratch"]
                plan6full = plan6_leaves(data, coords, load_plan6())
                prev = emit_columns2(
                    coords, plan6full, declared_names(MOD9), prev, tag="6",
                    kinds=("refined",),
                    doc="# Load-column bounds for the refined-leaf kills\n\n"
                        "Untracked working note.")
                MOD9.append("Grok810ScaleZeroQuarticChamberColumns6Scratch")
                prev = emit_rests2(
                    coords, plan6full, declared_names(MOD9), prev, tag="6",
                    kinds=("refined",),
                    doc="# Chamber rests for the refined-leaf kills\n\n"
                        "Untracked working note.")
                MOD9.append("Grok810ScaleZeroQuarticChamberRests6Scratch")
                prev, refkills = emit_refined_kills(
                    data, coords, chambers, plan6full,
                    declared_names(MOD9), prev)
                prev, surv6, survref6 = emit_residual6(
                    chambers, allkills, refkills, prev)
                surv4 = surv6 + [c for c, _i in survref6]
                if (ROOT / "Grok810ScaleZeroQuarticTowerScratch.lean").exists():
                    prev = emit_n7_ladder(prev)
                if (ROOT / "scripts" /
                        "out_810_scale_zero_quartic_unowned.json").exists():
                    # siblings: one common base so they gate in parallel
                    _base = prev
                    _infra = [emit_carrier_infra(coords, _f, _base)
                              for _f in ("n2", "n3", "n4", "n5", "n6",
                                         "n7", "omicron", "primitive")]
                    _n5 = emit_cost_ladder(
                        [_base,
                         "Grok810ScaleZeroQuarticChamberInfraN5Scratch"],
                        auxes=("n5",),
                        name="Grok810ScaleZeroQuarticChamberN5CostLadderScratch",
                        doc="# The cost-form `N₅` load ladder, `(8,10)` scale "
                            "zero\n\n`UNOWNED_CHAMBERS.md` needs an `n5-cost` "
                            "band on 370 system rows and 49 single columns.  "
                            "Same shape as the `κ`/`N₂` ladder: one cost "
                            "inequality per minimal load-free monomial of "
                            "`N₅`, plus one per minimal monomial of each "
                            "lighter `γ/ε/η` column.  Independent of the `N₇` "
                            "ladder.  Untracked working note.")
                    _n7c = emit_n7_bands(_base)
                    prev = [_base] + _infra + [_n5, _n7c]
                    _un, _undrop = certify_plan(coords, chambers,
                                                load_unowned())
                    log(f"unowned singles: {len(_undrop)} dropped for an "
                        f"uncertifiable band: {_undrop}")
                    MODU = MOD9 + _infra + [_n5, _n7c]
                    _pk_mod, _pkts = emit_unowned_packets(coords, _un, prev)
                    MODU += _pk_mod
                    _colmods = emit_unowned_columns(coords, _un,
                                                    declared_names(MODU),
                                                    MODU + _pk_mod)
                    MODU += _colmods
                    _restmods = emit_unowned_rests(coords, _un, _pkts,
                                                   declared_names(MODU),
                                                   MODU + _pk_mod + _colmods)
                    MODU += _restmods
                    _killmods, _unnames = emit_unowned_kills(
                        coords, chambers, _un, _pkts, declared_names(MODU),
                        MODU + _pk_mod + _colmods + _restmods)
                    MODU += _killmods
                    TRANCHE["single"] = len(_unnames)
                    _sysent, _sysdrop = system_entries(coords, chambers, _un)
                    log(f"unowned systems: {len(_sysent)} emitted, "
                        f"{len(_sysdrop)} dropped for an unproved column")
                    TRANCHE["system"] = len(_sysent)
                    TRANCHE["sysdrop"] = len(_sysdrop)
                    _sp = {"chambers": _sysent, "leaves": []}
                    _spk_mod, _spkts = emit_unowned_packets(
                        coords, _sp, prev, tag="UnownedSystem")
                    MODU += _spk_mod
                    _scol = emit_unowned_columns(coords, _sp,
                                                 declared_names(MODU),
                                                 MODU + _spk_mod,
                                                 tag="UnownedSystem")
                    MODU += _scol
                    _srest = emit_unowned_rests(coords, _sp, _spkts,
                                                declared_names(MODU),
                                                MODU + _spk_mod + _scol,
                                                tag="UnownedSystem")
                    MODU += _srest
                    _sysmods, _sysnames = emit_unowned_systems(
                        coords, chambers, _sysent, _spkts,
                        declared_names(MODU),
                        MODU + _spk_mod + _scol + _srest)
                    MODU += _sysmods
                    _spent, _spdrop = split_entries(coords, chambers, _un)
                    log(f"unowned splits: {len(_spent)} emitted, "
                        f"{len(_spdrop)} dropped: {_spdrop}")
                    TRANCHE["split"] = len(_spent)
                    TRANCHE["splitdrop"] = len(_spdrop)
                    _bp = {"chambers": _spent, "leaves": []}
                    _bpk, _bpkts = emit_unowned_packets(
                        coords, _bp, prev, tag="UnownedSplit")
                    MODU += _bpk
                    _bcol = emit_unowned_columns(coords, _bp,
                                                 declared_names(MODU),
                                                 MODU + _bpk,
                                                 tag="UnownedSplit")
                    MODU += _bcol
                    _brest = emit_unowned_rests(coords, _bp, _bpkts,
                                                declared_names(MODU),
                                                MODU + _bpk + _bcol,
                                                tag="UnownedSplit")
                    MODU += _brest
                    _spmod, _spnames = emit_unowned_splits(
                        coords, chambers, _spent, _bpkts,
                        declared_names(MODU),
                        MODU + _bpk + _bcol + _brest)
                    MODU.append(_spmod)
                    _rfent, _rfdrop = refine_entries(coords, chambers, _un)
                    log(f"unowned refinement trees: {len(_rfent)} emitted, "
                        f"{len(_rfdrop)} left open: {_rfdrop}")
                    _rfnames = {}
                    _rfmods = []
                    if _rfent:
                        _rp = {"chambers": _rfent, "leaves": []}
                        _rpk, _rpkts = emit_unowned_packets(
                            coords, _rp, prev, tag="UnownedRefine")
                        _rcol = emit_unowned_columns(
                            coords, _rp, declared_names(MODU + _rpk), _rpk,
                            tag="UnownedRefine")
                        _rrest = emit_unowned_rests(
                            coords, _rp, _rpkts,
                            declared_names(MODU + _rpk + _rcol),
                            MODU + _rpk + _rcol, tag="UnownedRefine")
                        _rfmod, _rfnames = emit_refine_trees(
                            coords, chambers, _rfent, _rpkts,
                            declared_names(MODU + _rpk + _rcol + _rrest),
                            MODU + _rpk + _rcol + _rrest)
                        _rfmods = _rpk + _rcol + _rrest + [_rfmod]
                        MODU += _rfmods
                        prev = prev + _rfmods
                    _trent, _trdrop = tree_entries(coords, chambers, _un)
                    _known = declared_names(MODU)
                    _trent = [x for x in _trent
                              if (f"quarticChamber{x['name']}810_impossible"
                                  if x.get("leaf") is None else
                                  f"quarticRefined{x['name']}L{x['leaf']}"
                                  "810_impossible") not in _known]
                    log(f"unowned plan trees: {len(_trent)} emitted, "
                        f"{len(_trdrop)} not validated: {_trdrop}")
                    _trnames, _trmods = {}, []
                    if _trent:
                        _tpk2, _ttied = tree_faces(coords, _trent)
                        _tent = [{"live": lv, "mode": "single",
                                  "name": "tree", "argmin": [],
                                  "carriers": [dict(v, loads={
                                      ld: {"status": "dominated"}
                                      for ld in LOADS})]}
                                 for v in _tpk2.values() for lv in v["lives"]]
                        _tp2 = {"chambers": _tent, "leaves": []}
                        _trp, _trpk = emit_unowned_packets(
                            coords, _tp2, prev, tag="UnownedTree")
                        _trc = emit_unowned_columns(
                            coords, _tp2, declared_names(MODU + _trp),
                            MODU + _trp, tag="UnownedTree")
                        _trr = emit_unowned_rests(
                            coords, _tp2, _trpk,
                            declared_names(MODU + _trp + _trc),
                            MODU + _trp + _trc, tag="UnownedTree")
                        _trpc = emit_tree_pieces(
                            coords, _ttied, _trpk,
                            declared_names(MODU + _trp + _trc + _trr),
                            MODU + _trp + _trc + _trr)
                        _trmod, _trnames = emit_unowned_trees(
                            coords, chambers, _trent, _trpk,
                            declared_names(MODU + _trp + _trc + _trr
                                           + [_trpc]),
                            MODU + _trp + _trc + _trr + [_trpc])
                        _trmods = _trp + _trc + _trr + [_trpc] + _trmod
                        MODU += _trmods
                        prev = prev + _trmods
                    _twnames, _twmods = {}, []
                    if (ROOT / (TOWER_FILE + ".lean")).exists():
                        _allnames = declared_names(
                            MODU + [m for m, _l, _d in MODULES])
                        _twent, _twskip = tower_entries(
                            coords, chambers, _allnames)
                        log(f"tower entries: {len(_twent)} emitted, "
                            f"skipped {_twskip}")
                        if _twent:
                            _tp = {"chambers": _twent, "leaves": []}
                            _tpk, _tpkts = emit_unowned_packets(
                                coords, _tp, prev, tag="Tower")
                            _tcol = emit_unowned_columns(
                                coords, _tp, declared_names(MODU + _tpk),
                                MODU + _tpk, tag="Tower")
                            _trest = emit_unowned_rests(
                                coords, _tp, _tpkts,
                                declared_names(MODU + _tpk + _tcol),
                                MODU + _tpk + _tcol, tag="Tower")
                            _tkm, _twnames = emit_tower_kills(
                                coords, chambers, _twent, _tpkts,
                                declared_names(MODU + _tpk + _tcol + _trest),
                                MODU + _tpk + _tcol + _trest)
                            _twmods = _tpk + _tcol + _trest + _tkm
                            MODU += _twmods
                            prev = prev + _twmods
                    newk = {}
                    newk.update(_unnames)
                    newk.update(_rfnames)
                    newk.update(_twnames)
                    newk.update(_sysnames)
                    newk.update(_spnames)
                    newk.update(_trnames)
                    prev, surv7, survref7 = emit_residual7(
                        chambers, allkills, refkills, newk,
                        MODU + _killmods + _sysmods + [_spmod]
                        + _trmods + _twmods)
                    log(f"residual 7: {len(surv7)} whole chambers + "
                        f"{len(survref7)} refined leaves")
                    TRANCHE["surv"] = len(surv7)
                    TRANCHE["survref"] = len(survref7)
                    prev = emit_assembly(
                        chambers, surv7 + [c for c, _i in survref7], prev,
                        tag="7",
                        names=("Grok810ScaleZeroQuarticAssemblyCore2Scratch",
                               "Grok810ScaleZeroQuarticAssembly2Scratch"))
                else:
                    prev = emit_assembly(chambers, surv4, prev, tag="6")
            else:
                prev = emit_assembly(chambers, surv4, prev, tag="5")
        else:
            prev = emit_assembly(chambers, surv4, prev)
    else:
        log("kill plan v4 absent - modules 26-32 skipped")
    emit_manifest(data, chambers, packets)
    if REGEN_VERDICT:
        diff = [nm for nm, ok in REGEN_VERDICT if not ok]
        log(f"gated modules regenerated: {len(REGEN_VERDICT)}, "
            f"differing: {len(diff)}" + (f" {diff}" if diff else ""))
    if GREEN_SKIPPED:
        log(f"green receipts respected: {len(GREEN_SKIPPED)} modules left "
            f"untouched {GREEN_SKIPPED}")
    log("done")


if __name__ == "__main__":
    main()
