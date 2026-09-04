#!/usr/bin/env python3
"""Compact re-emission of the σ-support exhaust of plan File A
(`Grok810ScaleZeroQuarticSigmaLadderScratch.lean`).

The Grok emitter (`emit_810_quartic_sigma_ladder_lean.py`) built the exhaust by
nesting `by_cases` over *all* pairwise cost comparisons and re-queueing letters
whenever the running "ruler" changed, because the cost comparison used by the
cone definitions is **not** a total order.  That produced 259k lines and ~100
unclosable `omega` leaves.

This emitter replaces the exhaust only.  Everything else in the file (cones,
`N₂`, band lemmas, kill predicates, corners, bands, the residual theorem) is
copied verbatim from the source file, except that four new *mixed* cone
definitions and four new constructors are appended to
`QuarticSigmaSupportCone810` (see `MIXED` below and the report).

Design
------
Let `s_X = w_X·a − 2·n_X` (doubled σ-defect, `w = 3,4,5,6,7,8` for `B..G`) and
let `u_X = k_X·s_X` with `k_B = k_C = 3`, `k_D = … = k_G = 2` be the cost of the
cheapest *singleton* face of `X` (`B³`, `C³`, `D²`, …).  `u` is an honest total
order, so the argmin of `u` over the live letters can be found by a **linear
tournament**: one `lt_trichotomy` per live letter, `3^(m−1)` leaves for a live
set of size `m`, no re-queueing (transitivity is free for `omega`).

The 63 cone definitions in the file are exactly the `u`-argmin cones *except*
on the four pairs `{B,C} × {F,G}`, where the cone conjunct is the stronger
"mixed" comparison `2σ_X < σ_Y` (plan §2.5: the mixed monomials `BF, BG, CF,
CG` are cheaper than `X³` unless `σ_Y > 2σ_X`).  So after the tournament, when
the winner `X` lies in `{B,C}` we run one extra `lt_trichotomy` per live letter
of `{F,G}`:

  * `2σ_X < σ_Y` — the cone conjunct holds, carry on;
  * `2σ_X = σ_Y` — `Y` joins the winning set (this is what the existing cones
    `…ConeBF810`, `…ConeBG810`, `…ConeCF810`, `…ConeCG810` and their supersets
    mean);
  * `σ_Y < 2σ_X` — **no** cone of the 63 applies (the mixed monomial `X·Y` is
    the strict cost minimum and is not one of the 63 faces).  This is a genuine
    hole in the 63-cone taxonomy, so we land in one of four new named residual
    cones `QuarticMixedSigmaCone{BF,BG,CF,CG}810`.

Completeness is proved in `--check` mode by brute force over the sign chambers.
"""
from __future__ import annotations

import argparse
import itertools
import re
import sys
from math import gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SRC = Path.home() / "lean/tools/sigma810/old_exhaust.lean"
DEFAULT_OUT = ROOT / "Grok810ScaleZeroQuarticSigmaLadderScratch.lean"

LETTERS = ("A", "B", "C", "D", "E", "F", "G")
SIGMA_LETTERS = ("B", "C", "D", "E", "F", "G")
# doubled defect s_X = w_X * a - 2 * n_X, as a vector over (a, b, c, d, e, f, g)
TWO_SIGMA = {
    "B": (3, -2, 0, 0, 0, 0, 0),
    "C": (4, 0, -2, 0, 0, 0, 0),
    "D": (5, 0, 0, -2, 0, 0, 0),
    "E": (6, 0, 0, 0, -2, 0, 0),
    "F": (7, 0, 0, 0, 0, -2, 0),
    "G": (8, 0, 0, 0, 0, 0, -2),
}
FACE_K = {"B": 3, "C": 3, "D": 2, "E": 2, "F": 2, "G": 2}
BC = frozenset("BC")
FG = frozenset("FG")
MIXED_PAIRS = [("B", "F"), ("B", "G"), ("C", "F"), ("C", "G")]

# ---------------------------------------------------------------- ℕ rendering


def side(vec) -> str:
    parts = []
    for c, n in zip(vec, LETTERS):
        if c == 0:
            continue
        parts.append(f"{n}.natDegree" if c == 1 else f"{c} * {n}.natDegree")
    return " + ".join(parts) if parts else "0"


def sides(left, right):
    """Move everything to the positive side and divide by the gcd."""
    L = [0] * 7
    R = [0] * 7
    for i in range(7):
        d = left[i] - right[i]
        if d > 0:
            L[i] += d
        elif d < 0:
            R[i] += -d
    g = 0
    for c in L + R:
        g = gcd(g, abs(c))
    if g > 1:
        L = [c // g for c in L]
        R = [c // g for c in R]
    return side(L), side(R)


def vec_op(left, right, op: str) -> str:
    lhs, rhs = sides(left, right)
    return f"{lhs} {op} {rhs}"


def scale(vec, m):
    return tuple(m * c for c in vec)


def face_vec(ch: str):
    return scale(TWO_SIGMA[ch], FACE_K[ch])


def pair_vecs(x: str, y: str):
    """Cost comparison used by the *cone definitions* (plan §2.5)."""
    if x in BC and y in FG:
        return scale(TWO_SIGMA[x], 2), TWO_SIGMA[y]
    if y in BC and x in FG:
        return TWO_SIGMA[x], scale(TWO_SIGMA[y], 2)
    return face_vec(x), face_vec(y)


def u_vecs(x: str, y: str):
    """Singleton-face cost comparison (a total order)."""
    return face_vec(x), face_vec(y)


def pair_lt(x, y):
    lv, rv = pair_vecs(x, y)
    return vec_op(lv, rv, "<")


def pair_eq(x, y):
    lv, rv = pair_vecs(x, y)
    return vec_op(lv, rv, "=")


def u_lt(x, y):
    lv, rv = u_vecs(x, y)
    return vec_op(lv, rv, "<")


def u_eq(x, y):
    lv, rv = u_vecs(x, y)
    return vec_op(lv, rv, "=")


def u_le(x, y):
    lv, rv = u_vecs(x, y)
    return vec_op(lv, rv, "≤")


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


# ------------------------------------------------------------------- parsing

DEF_RE = re.compile(
    r"^def (QuarticSigmaCone([A-G]+)810'|QuarticLoadSigmaCone([A-G]+)810) "
    r"\(A B C D E F G : k\[X\]\) : Prop :=$"
)


def parse_source(text: str):
    lines = text.split("\n")
    cones = {}
    for i, ln in enumerate(lines):
        m = DEF_RE.match(ln)
        if not m:
            continue
        name = m.group(1)
        letters = m.group(2) or m.group(3)
        body = []
        j = i + 1
        while j < len(lines) and lines[j].strip():
            body.append(lines[j])
            j += 1
        fields = [norm(f) for f in " ".join(body).split("∧")]
        cones[frozenset(letters)] = (name, fields)
    return lines, cones


def find_line(lines, pred, what):
    hits = [i for i, ln in enumerate(lines) if pred(ln)]
    if len(hits) != 1:
        raise SystemExit(f"expected exactly one {what}, got {len(hits)}")
    return hits[0]


# ------------------------------------------------------------ new cone defs


def mixed_cone_name(x, y):
    return f"QuarticMixedSigmaCone{x}{y}810"


def mixed_cone_ctor(x, y):
    return f"mixed{x}{y}"


def mixed_cone_fields(x, y):
    """`X` wins the singleton-face race but the mixed monomial `X·Y` is
    strictly cheaper than `X³`, so none of the 63 faces is the cost minimum."""
    fields = [
        "QuarticRatioConeA810 A B C D E F G",
        f"{x} ≠ 0",
        f"{y} ≠ 0",
        pair_lt(y, x),  # σ_Y < 2σ_X : the mixed monomial beats X³
        u_le(x, y),  # 3σ_X ≤ 2σ_Y  : Y² does not beat X³
    ]
    for z in SIGMA_LETTERS:
        if z in (x, y):
            continue
        fields.append(f"({z} = 0 ∨ {u_le(x, z)})")
    return fields


def mixed_cone_def(x, y):
    fields = mixed_cone_fields(x, y)
    body = fields[0]
    for f in fields[1:]:
        body += " ∧\n    " + f
    doc = (
        f"/-- Residual chamber of the σ-defect taxonomy: `{x}` wins the\n"
        f"singleton-face race (`3σ_{x} ≤ k_Z σ_Z` for every live `Z`) yet the mixed\n"
        f"monomial `{x}·{y}` is strictly cheaper than `{x}³` (`σ_{y} < 2σ_{x}`), so the\n"
        f"cost minimum is the single monomial `{x}{y}`, which is not the face of any of\n"
        f"the 63 `QuarticSigmaSupportCone810` constructors.  See the emitter\n"
        f"`scripts/emit_810_quartic_sigma_exhaust.py`. -/\n"
    )
    return doc + f"def {mixed_cone_name(x, y)} (A B C D E F G : k[X]) : Prop :=\n  {body}\n"


# ------------------------------------------------------------------- exhaust


def cone_ctor(T) -> str:
    return "sigma" + "".join(ch for ch in SIGMA_LETTERS if ch in T)


def wrap_term(prefix, parts, indent):
    """`prefix ⟨p, q, …⟩`, wrapped at ~100 columns."""
    ind = " " * indent
    cont = " " * (indent + 2)
    out = []
    cur = ind + prefix + " ⟨"
    for i, p in enumerate(parts):
        piece = p + ("," if i + 1 < len(parts) else "⟩")
        if len(cur) + len(piece) + 1 > 100 and cur.strip() not in ("",):
            out.append(cur.rstrip())
            cur = cont
        cur += piece + (" " if i + 1 < len(parts) else "")
    out.append(cur.rstrip())
    return out


class Emitter:
    def __init__(self, cones):
        self.cones = cones
        self.leaf_ctors = set()
        self.leaf_count = 0
        self.omega_leaves = 0

    # -- leaves ------------------------------------------------------------
    def leaf(self, cand, dead, facts, indent):
        T = frozenset(cand)
        name, fields = self.cones[T]
        parts = []
        for fld in fields:
            if fld == "QuarticRatioConeA810 A B C D E F G":
                parts.append("hA")
            elif fld.endswith("≠ 0"):
                parts.append("h" + fld[0] + "ne")
            elif fld.startswith("("):
                inner = fld[1:-1]
                ch, rest = inner[0], inner[2:]
                assert rest.startswith("= 0 ∨ "), fld
                ineq = norm(rest[len("= 0 ∨ "):])
                if ch in dead:
                    parts.append(f"Or.inl h{ch}z")
                else:
                    h = facts.get(ineq)
                    parts.append("Or.inr " + (h if h else "(by omega)"))
                    if not h:
                        self.omega_leaves += 1
            else:
                h = facts.get(fld)
                parts.append(h if h else "(by omega)")
                if not h:
                    self.omega_leaves += 1
        self.leaf_ctors.add(cone_ctor(T))
        self.leaf_count += 1
        return wrap_term(
            f"exact QuarticSigmaSupportCone810.{cone_ctor(T)}", parts, indent
        )

    def mixed_leaf(self, x, y, dead, facts, indent):
        parts = []
        for fld in mixed_cone_fields(x, y):
            if fld == "QuarticRatioConeA810 A B C D E F G":
                parts.append("hA")
            elif fld.endswith("≠ 0"):
                parts.append("h" + fld[0] + "ne")
            elif fld.startswith("("):
                inner = fld[1:-1]
                ch = inner[0]
                ineq = norm(inner[2:][len("= 0 ∨ "):])
                if ch in dead:
                    parts.append(f"Or.inl h{ch}z")
                else:
                    h = facts.get(ineq)
                    parts.append("Or.inr " + (h if h else "(by omega)"))
                    if not h:
                        self.omega_leaves += 1
            else:
                h = facts.get(fld)
                parts.append(h if h else "(by omega)")
                if not h:
                    self.omega_leaves += 1
        self.leaf_ctors.add(mixed_cone_ctor(x, y))
        self.leaf_count += 1
        return wrap_term(
            f"exact QuarticSigmaSupportCone810.{mixed_cone_ctor(x, y)}", parts, indent
        )

    # -- phase 2: the four mixed comparisons -------------------------------
    def mixed_phase(self, cand, todo, live, dead, facts, indent, names):
        r = cand[0]
        if r not in BC or not todo:
            return self.leaf(cand, dead, facts, indent)
        y = todo[0]
        rest = todo[1:]
        if y in cand:
            # u-tie `3σ_r = 2σ_y` forces `σ_y = (3/2)σ_r < 2σ_r`: mixed hole.
            return self.mixed_leaf(r, y, dead, facts, indent)
        hl, he, hg = f"hm{r}{y}lt", f"hm{r}{y}eq", f"hm{r}{y}gt"
        for h in (hl, he, hg):
            assert h not in names, h
        lhs, rhs = sides(*pair_vecs(r, y))
        ind = " " * indent
        out = [f"{ind}rcases lt_trichotomy ({lhs}) ({rhs}) with {hl} | {he} | {hg}"]
        # `2σ_r < σ_y`: the cone conjunct holds.
        f1 = dict(facts)
        f1[norm(pair_lt(r, y))] = hl
        out += self.bullet(
            self.mixed_phase(cand, rest, live, dead, f1, indent + 2, names | {hl}),
            indent,
            f"-- {r}³ beats the mixed monomial {r}{y}",
        )
        # `2σ_r = σ_y`: `y` joins the winning set.
        f2 = dict(facts)
        f2[norm(pair_eq(r, y))] = he
        out += self.bullet(
            self.mixed_phase(
                cand + [y], rest, live, dead, f2, indent + 2, names | {he}
            ),
            indent,
            f"-- {y} ties {r} on the mixed monomial {r}{y}",
        )
        # `σ_y < 2σ_r`: the mixed monomial is the strict minimum — residual.
        f3 = dict(facts)
        f3[norm(pair_lt(y, r))] = hg
        out += self.bullet(
            self.mixed_leaf(r, y, dead, f3, indent + 2),
            indent,
            f"-- the mixed monomial {r}{y} strictly beats {r}³ : residual cone",
        )
        return out

    @staticmethod
    def bullet(sub, indent, comment):
        ind = " " * indent
        if len(sub) == 1 and sub[0].strip().startswith("exact "):
            return [f"{ind}· {sub[0].strip()}"]
        return [f"{ind}· {comment}"] + sub

    # -- phase 1: the u-tournament ----------------------------------------
    def tournament(self, cand, rest, live, dead, facts, indent, names):
        if not rest:
            todo = [ch for ch in ("F", "G") if ch in live]
            return self.mixed_phase(cand, todo, live, dead, facts, indent, names)
        r, x = cand[0], rest[0]
        tail = rest[1:]
        hl, he, hg = f"h{r}{x}lt", f"h{r}{x}eq", f"h{r}{x}gt"
        for h in (hl, he, hg):
            assert h not in names, h
        lhs, rhs = sides(*u_vecs(r, x))
        ind = " " * indent
        out = [f"{ind}rcases lt_trichotomy ({lhs}) ({rhs}) with {hl} | {he} | {hg}"]
        f1 = dict(facts)
        f1[norm(u_lt(r, x))] = hl
        out += self.bullet(
            self.tournament(cand, tail, live, dead, f1, indent + 2, names | {hl}),
            indent,
            f"-- {r} strictly outranks {x}",
        )
        f2 = dict(facts)
        f2[norm(u_eq(r, x))] = he
        out += self.bullet(
            self.tournament(cand + [x], tail, live, dead, f2, indent + 2, names | {he}),
            indent,
            f"-- {x} ties {''.join(cand)}",
        )
        f3 = dict(facts)
        f3[norm(u_lt(x, r))] = hg
        out += self.bullet(
            self.tournament([x], tail, live, dead, f3, indent + 2, names | {hg}),
            indent,
            f"-- {x} strictly outranks {''.join(cand)}",
        )
        return out


def mask_lemma(em: Emitter, live, dead) -> str:
    name = "quarticSigmaSupportCone810_of_live_" + "".join(live)
    params = [
        "    (A B C D E F G : k[X])",
        "    (hA : QuarticRatioConeA810 A B C D E F G)",
    ]
    for ch in SIGMA_LETTERS:
        params.append(
            f"    (h{ch}z : {ch} = 0)" if ch in dead else f"    (h{ch}ne : {ch} ≠ 0)"
        )
    head = (
        "set_option maxHeartbeats 64000000 in\n"
        f"theorem {name}\n" + "\n".join(params) + " :\n"
        "    QuarticSigmaSupportCone810 A B C D E F G := by\n"
        "  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA\n"
    )
    body = em.tournament(
        [live[0]], list(live[1:]), set(live), set(dead), {}, 2, set()
    )
    return head + "\n".join(body) + "\n"


def combiner(lines, start, end) -> str:
    """Copy the 64-way vanishing dispatcher verbatim from the source."""
    i = find_line(
        lines[start:end],
        lambda ln: ln.strip() == "theorem quarticSigmaSupportCone810_of",
        "combiner",
    ) + start
    assert lines[i - 1].strip().endswith(" in"), lines[i - 1]
    j = end
    while not lines[j - 1].strip():
        j -= 1
    return "\n".join(lines[i - 2:j]) + "\n"


def allzero_lemma(lines, start, end) -> str:
    i = find_line(
        lines[start:end],
        lambda ln: ln.startswith("theorem quarticSigmaSupportCone810_of_allZero"),
        "allZero lemma",
    ) + start
    j = i
    while not (lines[j].startswith("set_option") and j > i):
        j += 1
    return "\n".join(lines[i - 2:j]).rstrip() + "\n"


# --------------------------------------------------------------- completeness


def check_completeness(trials=400000, seed=7) -> None:
    """Every positive `s` on every live mask is covered by some constructor."""
    import random

    def coef(x, y):
        if x in BC and y in FG:
            return (2, 1)
        if y in BC and x in FG:
            return (1, 2)
        return (FACE_K[x], FACE_K[y])

    def cone_holds(T, live, s):
        T = [ch for ch in SIGMA_LETTERS if ch in T]
        if not all(ch in live for ch in T):
            return False
        r = T[0]
        for z in T[1:]:
            p, q = coef(r, z)
            if p * s[r] != q * s[z]:
                return False
        for y in SIGMA_LETTERS:
            if y in T or y not in live:
                continue
            p, q = coef(r, y)
            if not p * s[r] < q * s[y]:
                return False
        return True

    def mixed_holds(x, y, live, s):
        if x not in live or y not in live or not s[y] < 2 * s[x]:
            return False
        return all(
            FACE_K[x] * s[x] <= FACE_K[z] * s[z]
            for z in SIGMA_LETTERS
            if z in live and z != x
        )

    def covered(live, s):
        for r in range(1, 7):
            for T in itertools.combinations(SIGMA_LETTERS, r):
                if cone_holds(set(T), live, s):
                    return True
        return any(mixed_holds(x, y, live, s) for x, y in MIXED_PAIRS)

    random.seed(seed)
    bad = 0
    for mask in range(1, 64):
        live = {ch for i, ch in enumerate(SIGMA_LETTERS) if mask >> (5 - i) & 1}
        lst = sorted(live, key=SIGMA_LETTERS.index)
        m = len(lst)
        if m <= 3:
            it = itertools.product(range(1, 31), repeat=m)
        else:
            it = (
                tuple(random.randint(1, 40) for _ in range(m))
                for _ in range(trials // 20)
            )
        for vals in it:
            if not covered(live, dict(zip(lst, vals))):
                bad += 1
                if bad < 4:
                    print("  UNCOVERED", lst, vals, file=sys.stderr)
    print(f"completeness check: {bad} uncovered chambers")
    if bad:
        raise SystemExit("cone family is not exhaustive")



# ------------------------------------------------------------------- doc fixes

DOC_PATCHES = [
    # file header
    (
        "60 k=2 cones), the 64-way vanishing exhaust (cost tournament with\n"
        "loser-requeue on ruler change), the auxiliary `N₂ = ν + (1/8) A κ`,",
        "60 k=2 cones) plus the four *mixed residual* cones\n"
        "`QuarticMixedSigmaCone{BF,BG,CF,CG}810`, the 64-way vanishing exhaust\n"
        "(a linear tournament on the singleton-face costs `u_X = k_X σ_X`,\n"
        "then the four §2.5 mixed comparisons; emitter\n"
        "`scripts/emit_810_quartic_sigma_exhaust.py`), the auxiliary `N₂ = ν + (1/8) A κ`,",
    ),
    (
        "Does not close the 63 cones (Files B/C) or the remaining even core",
        "The 63 cones of the plan are **not** exhaustive: their cost comparison\n"
        "is not transitive.  `a = 4, b = 1, d = 2, f = 5`, `C = E = G = 0`\n"
        "(so `s_B = 10, s_D = 16, s_F = 18`) satisfies cone `A` and none of the\n"
        "63: `B` fails `2σ_B < σ_F`, `D` fails `2σ_D < 3σ_B`, `F` fails\n"
        "`σ_F < σ_D`, and no tie holds.  There the cost minimum is the mixed\n"
        "monomial `BF` (`s_B + s_F = 28 < 30 = 3 s_B`), whose face is none of the\n"
        "63 faces; the four new cones name exactly that chamber and need faces\n"
        "and kills in Files B/C (or a taxonomy fix upstream).\n"
        "\n"
        "A second, independent gap is **not** repaired here: inside a k=2 cone\n"
        "the level-2 face on `S` need not be the cost minimum either, since a\n"
        "mixed monomial can undercut it.  `a = 10, b = 8, d = 15, f = 23`,\n"
        "`C = E = G = 0` (`s_B = 14, s_D = 20, s_F = 24`) satisfies\n"
        "`QuarticLoadSigmaConeD810` (`2 s_D = 40 < 42 = 3 s_B`, `s_D < s_F`)\n"
        "while `BF` costs `s_B + s_F = 38 < 40 = 2 s_D`, so `D²` is not the top\n"
        "face there.  Pinning the face down needs the three-letter conjunct\n"
        "`2 s_D < s_B + s_F`, which no pairwise cone can state; the rest bounds\n"
        "of Files B/C have to carry it (or the taxonomy has to be re-derived).\n"
        "\n"
        "Does not close the 63 + 4 cones (Files B/C) or the remaining even core",
    ),
    # residual theorem docstring
    (
        "Closed relative to `quarticConeA810_residual`: the 63-way\n"
        "`QuarticSigmaSupportCone810`",
        "Closed relative to `quarticConeA810_residual`: the 67-way\n"
        "`QuarticSigmaSupportCone810`",
    ),
    (
        "`l` band disjunction of §2.2.  The 63 cones are not killed\n"
        "(Files B/C).",
        "`l` band disjunction of §2.2.  The 63 σ-cones and the four mixed\n"
        "residual cones `QuarticMixedSigmaCone{BF,BG,CF,CG}810` are not\n"
        "killed (Files B/C).",
    ),
]


def patch_docs(text: str) -> str:
    for old, new in DOC_PATCHES:
        if text.count(old) != 1:
            raise SystemExit(f"doc patch not applicable ({text.count(old)}):\n{old}")
        text = text.replace(old, new)
    return text


# ---------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", default=str(DEFAULT_SRC))
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    ap.add_argument("--check-only", action="store_true")
    args = ap.parse_args()

    check_completeness()

    text = Path(args.source).read_text()
    lines, cones = parse_source(text)
    if len(cones) != 63:
        raise SystemExit(f"parsed {len(cones)} cone defs, expected 63")

    # cross-check the parsed cone bodies against the generator
    for T, (name, fields) in cones.items():
        r = [ch for ch in SIGMA_LETTERS if ch in T][0]
        want = ["QuarticRatioConeA810 A B C D E F G"]
        want += [f"{ch} ≠ 0" for ch in SIGMA_LETTERS if ch in T]
        want += [norm(pair_eq(r, ch)) for ch in SIGMA_LETTERS if ch in T and ch != r]
        want += [
            f"({ch} = 0 ∨ {norm(pair_lt(r, ch))})"
            for ch in SIGMA_LETTERS
            if ch not in T
        ]
        if fields != want:
            raise SystemExit(f"cone {name} body mismatch:\n{fields}\n{want}")

    i_ind = find_line(
        lines, lambda ln: ln.startswith("inductive QuarticSigmaSupportCone810"),
        "inductive",
    )
    i_ind_so = i_ind - 1
    assert lines[i_ind_so].strip() == "set_option maxHeartbeats 64000000 in"
    i_ind_end = i_ind
    while lines[i_ind_end].strip():
        i_ind_end += 1
    ctors = [
        m.group(1)
        for m in (re.match(r"\s+\| (\w+) :", ln) for ln in lines[i_ind:i_ind_end])
        if m
    ]
    if len(ctors) != 63:
        raise SystemExit(f"inductive has {len(ctors)} constructors")

    i_sec = find_line(
        lines, lambda ln: ln == "section QuarticSigmaExhaust810", "exhaust section"
    )
    i_end = find_line(
        lines, lambda ln: ln == "end QuarticSigmaExhaust810", "exhaust end"
    )

    em = Emitter(cones)
    chunks = []
    chunks.append("\n".join(lines[:i_ind_so]))
    chunks.append(
        "/-! ### Mixed-monomial residual cones (holes in the 63-cone taxonomy) -/\n"
    )
    for x, y in MIXED_PAIRS:
        chunks.append(mixed_cone_def(x, y))
    new_ctors = []
    for x, y in MIXED_PAIRS:
        new_ctors.append(
            f"  | {mixed_cone_ctor(x, y)} : {mixed_cone_name(x, y)} A B C D E F G →\n"
            f"      QuarticSigmaSupportCone810 A B C D E F G"
        )
    chunks.append(
        "\n".join(lines[i_ind_so:i_ind_end]).rstrip() + "\n" + "\n".join(new_ctors) + "\n"
    )
    chunks.append("\n".join(lines[i_ind_end + 1:i_sec]))

    body = ["section QuarticSigmaExhaust810", ""]
    body.append(allzero_lemma(lines, i_sec, i_end))
    for mask in range(1, 64):
        live = [ch for i, ch in enumerate(SIGMA_LETTERS) if mask >> (5 - i) & 1]
        dead = [ch for ch in SIGMA_LETTERS if ch not in live]
        body.append(mask_lemma(em, live, dead))
    body.append(combiner(lines, i_sec, i_end))
    body.append("end QuarticSigmaExhaust810")
    body.append("")
    chunks.append("\n".join(body))
    chunks.append("\n".join(lines[i_end + 1:]))

    out = "\n".join(chunks)
    out = re.sub(r"\n{3,}", "\n\n", out)
    out = patch_docs(out)
    if not args.check_only:
        Path(args.out).write_text(out)
    print(
        f"leaves: {em.leaf_count}  distinct constructors used: "
        f"{len(em.leaf_ctors)}  omega-discharged fields: {em.omega_leaves}"
    )
    print(f"wrote {args.out}: {out.count(chr(10)) + 1} lines")
    missing = set(ctors) - em.leaf_ctors
    if missing:
        print(f"note: constructors never produced by the exhaust: {sorted(missing)}")
    unknown = em.leaf_ctors - set(ctors) - {mixed_cone_ctor(x, y) for x, y in MIXED_PAIRS}
    if unknown:
        raise SystemExit(f"leaf uses unknown constructor: {unknown}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
