import Grok810ScaleZeroQuarticChamberDefs2Scratch

/-! # Cost-argmin chamber definitions (3/4), `(8,10)` scale zero

The 354 chambers whose live-letter set `S` has |S| ∈ {5}, machine-generated from
`scripts/out_810_scale_zero_quartic_chambers.json` by
`scripts/emit_810_quartic_chambers_lean.py`.  A chamber is one
argmin cell of `cost(m) = Σ m_X s_X`, `s_X = w_X·a − 2·natDegree X`,
on cone `A`; the conjuncts are the cross-multiplied ℕ cost ties and
strict comparisons of `~/lean/tools/sigma810/CHAMBERS.md` §1.
Definitions only — no proofs.  Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

/-- Cost-argmin chamber `BCDEF` / `BBB` (leaf BCDEF#8.0). -/
def QuarticChamberBCDEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDEF` / `BBB·BBC·BCC·CCC` (leaf BCDEF#8.0). -/
def QuarticChamberBCDEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·BBB` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·DD` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·DD·BBB·BBC·BCC·CCC` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·DD·DE·DF·EE·EF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·DD·DE·EE` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·DD·DF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·EE` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·EE·BBB·BBC·BCC·CCC` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·EE·EF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·CF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·DD` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·DD·BBB` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·DD·DE·DF·EE·EF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·DD·DE·EE` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·DD·DE·EE·BBB` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·DD·DF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·EE` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·EE·BBB` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·EE·EF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `BF·FF` (leaf BCDEF#0.0). -/
def QuarticChamberBCDEF25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CCC` (leaf BCDEF#15.0). -/
def QuarticChamberBCDEF26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 6 * C.natDegree ∧
    D.natDegree + F.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·CCC` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·DD` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·DD·CCC` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·DD·DE·DF·EE·EF·FF` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·DD·DE·EE` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·DD·DE·EE·CCC` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF33810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·DD·DF·FF` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF34810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·EE` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF35810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·EE·CCC` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF36810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·EE·EF·FF` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF37810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `CF·FF` (leaf BCDEF#1.0). -/
def QuarticChamberBCDEF38810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF39810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·BBB` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF40810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·BBB·BBC·BCC·CCC` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF41810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·CCC` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF42810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·DE·DF·EE·EF·FF` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF43810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 4 * D.natDegree = 2 * E.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·DE·EE` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF44810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·DE·EE·BBB` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF45810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF46810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·DE·EE·CCC` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF47810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `DD·DF·FF` (leaf BCDEF#2.0). -/
def QuarticChamberBCDEF48810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEF` / `EE` (leaf BCDEF#5.0). -/
def QuarticChamberBCDEF49810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEF` / `EE·BBB` (leaf BCDEF#5.0). -/
def QuarticChamberBCDEF50810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEF` / `EE·BBB·BBC·BCC·CCC` (leaf BCDEF#5.0). -/
def QuarticChamberBCDEF51810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree ∧
    4 * E.natDegree = A.natDegree + 2 * B.natDegree + 4 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEF` / `EE·CCC` (leaf BCDEF#5.0). -/
def QuarticChamberBCDEF52810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEF` / `EE·EF·FF` (leaf BCDEF#5.0). -/
def QuarticChamberBCDEF53810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEF` / `FF` (leaf BCDEF#7.0). -/
def QuarticChamberBCDEF54810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BCDEG` / `BBB` (leaf BCDEG#8.0). -/
def QuarticChamberBCDEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDEG` / `BBB·BBC·BCC·CCC` (leaf BCDEG#8.0). -/
def QuarticChamberBCDEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·BBB` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·DD` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·DD·BBB·BBC·BCC·CCC` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·DD·DE·DG·EE·EG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·DD·DE·EE` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·DD·DG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·EE` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·EE·BBB·BBC·BCC·CCC` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·EE·EG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·CG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·DD` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·DD·BBB` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·DD·DE·DG·EE·EG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·DD·DE·EE` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·DD·DE·EE·BBB` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·DD·DG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·EE` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·EE·BBB` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·EE·EG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `BG·GG` (leaf BCDEG#0.0). -/
def QuarticChamberBCDEG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CCC` (leaf BCDEG#15.0). -/
def QuarticChamberBCDEG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 6 * C.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·CCC` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·DD` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·DD·CCC` (leafs BCDEG#1.0, BCDEG#1.1, BCDEG#1.2, BCDEG#1.3, BCDEG#1.4). -/
def QuarticChamberBCDEG30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·DD·DE·DG·EE·EG·GG` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·DD·DE·EE` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·DD·DE·EE·CCC` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG33810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·DD·DG·GG` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG34810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·EE` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG35810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·EE·CCC` (leafs BCDEG#1.0, BCDEG#1.1, BCDEG#1.2). -/
def QuarticChamberBCDEG36810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·EE·EG·GG` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG37810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `CG·GG` (leaf BCDEG#1.0). -/
def QuarticChamberBCDEG38810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG39810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·BBB` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG40810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·BBB·BBC·BCC·CCC` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG41810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·CCC` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG42810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·DE·DG·EE·EG·GG` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG43810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + 2 * D.natDegree = E.natDegree + G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·DE·EE` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG44810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·DE·EE·BBB` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG45810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG46810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·DE·EE·CCC` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG47810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `DD·DG·GG` (leaf BCDEG#2.0). -/
def QuarticChamberBCDEG48810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEG` / `EE` (leaf BCDEG#5.0). -/
def QuarticChamberBCDEG49810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEG` / `EE·BBB` (leaf BCDEG#5.0). -/
def QuarticChamberBCDEG50810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEG` / `EE·BBB·BBC·BCC·CCC` (leaf BCDEG#5.0). -/
def QuarticChamberBCDEG51810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree ∧
    4 * E.natDegree = A.natDegree + 2 * B.natDegree + 4 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEG` / `EE·CCC` (leaf BCDEG#5.0). -/
def QuarticChamberBCDEG52810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEG` / `EE·EG·GG` (leaf BCDEG#5.0). -/
def QuarticChamberBCDEG53810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEG` / `GG` (leaf BCDEG#7.0). -/
def QuarticChamberBCDEG54810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + E.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BBB` (leaf BCDFG#10.0). -/
def QuarticChamberBCDFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCDFG` / `BBB·BBC·BCC·CCC` (leaf BCDFG#10.0). -/
def QuarticChamberBCDFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BBB` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·BBB` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·CF·CG` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (leafs BCDFG#0.0, BCDFG#0.1, BCDFG#0.2). -/
def QuarticChamberBCDFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·CF·CG·DD` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·CF·CG·DD·BBB·BBC·BCC·CCC` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·CF·CG·FF·FG·GG` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·DD` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·DD·BBB` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·DD·DF·DG·FF·FG·GG` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·BG·FF·FG·GG` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·CF` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·CF·DD` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·CF·DD·BBB·BBC·BCC·CCC` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·CF·DD·DF·FF` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·CF·FF` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·DD` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·DD·BBB` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·DD·DF·FF` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BF·FF` (leaf BCDFG#0.0). -/
def QuarticChamberBCDFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·BBB` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·CG` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·CG·DD` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·CG·DD·BBB·BBC·BCC·CCC` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·CG·DD·DG·GG` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·CG·GG` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG33810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·DD` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG34810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·DD·BBB` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG35810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·DD·DG·GG` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG36810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `BG·GG` (leaf BCDFG#1.0). -/
def QuarticChamberBCDFG37810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDFG` / `CCC` (leaf BCDFG#15.0). -/
def QuarticChamberBCDFG38810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    D.natDegree + F.natDegree < 3 * C.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG39810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·CCC` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG40810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·CG` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG41810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·CG·CCC` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG42810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·CG·DD` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG43810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·CG·DD·CCC` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG44810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·CG·DD·DF·DG·FF·FG·GG` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG45810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree = D.natDegree + G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·CG·FF·FG·GG` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG46810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·DD` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG47810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·DD·CCC` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG48810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·DD·DF·FF` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG49810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CF·FF` (leaf BCDFG#2.0). -/
def QuarticChamberBCDFG50810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDFG` / `CG` (leaf BCDFG#3.0). -/
def QuarticChamberBCDFG51810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDFG` / `CG·CCC` (leaf BCDFG#3.0). -/
def QuarticChamberBCDFG52810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDFG` / `CG·DD` (leaf BCDFG#3.0). -/
def QuarticChamberBCDFG53810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDFG` / `CG·DD·CCC` (leafs BCDFG#3.0, BCDFG#3.1, BCDFG#3.2, BCDFG#3.3, BCDFG#3.4). -/
def QuarticChamberBCDFG54810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDFG` / `CG·DD·DG·GG` (leaf BCDFG#3.0). -/
def QuarticChamberBCDFG55810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDFG` / `CG·GG` (leaf BCDFG#3.0). -/
def QuarticChamberBCDFG56810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDFG` / `DD` (leaf BCDFG#4.0). -/
def QuarticChamberBCDFG57810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDFG` / `DD·BBB` (leaf BCDFG#4.0). -/
def QuarticChamberBCDFG58810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDFG` / `DD·BBB·BBC·BCC·CCC` (leaf BCDFG#4.0). -/
def QuarticChamberBCDFG59810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDFG` / `DD·CCC` (leaf BCDFG#4.0). -/
def QuarticChamberBCDFG60810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDFG` / `DD·DF·DG·FF·FG·GG` (leaf BCDFG#4.0). -/
def QuarticChamberBCDFG61810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    5 * A.natDegree + 4 * D.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDFG` / `DD·DF·FF` (leaf BCDFG#4.0). -/
def QuarticChamberBCDFG62810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDFG` / `DD·DG·GG` (leaf BCDFG#4.0). -/
def QuarticChamberBCDFG63810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDFG` / `FF` (leaf BCDFG#7.0). -/
def QuarticChamberBCDFG64810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `FF·FG·GG` (leaf BCDFG#7.0). -/
def QuarticChamberBCDFG65810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BCDFG` / `GG` (leaf BCDFG#9.0). -/
def QuarticChamberBCDFG66810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BBB` (leaf BCEFG#10.0). -/
def QuarticChamberBCEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCEFG` / `BBB·BBC·BCC·CCC` (leaf BCEFG#10.0). -/
def QuarticChamberBCEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BBB` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·BBB` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·CF·CG` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (leafs BCEFG#0.0, BCEFG#0.1, BCEFG#0.2). -/
def QuarticChamberBCEFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·CF·CG·EE` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·CF·CG·EE·BBB·BBC·BCC·CCC` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·CF·CG·FF·FG·GG` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·EE` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·EE·BBB` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·EE·EF·EG·FF·FG·GG` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·BG·FF·FG·GG` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·CF` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·CF·EE` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·CF·EE·BBB·BBC·BCC·CCC` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·CF·EE·EF·FF` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·CF·FF` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·EE` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·EE·BBB` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·EE·EF·FF` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BF·FF` (leaf BCEFG#0.0). -/
def QuarticChamberBCEFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·BBB` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·CG` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·CG·EE` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·CG·EE·BBB·BBC·BCC·CCC` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·CG·EE·EG·GG` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·CG·GG` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG33810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·EE` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG34810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·EE·BBB` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG35810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·EE·EG·GG` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG36810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `BG·GG` (leaf BCEFG#1.0). -/
def QuarticChamberBCEFG37810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEFG` / `CCC` (leaf BCEFG#15.0). -/
def QuarticChamberBCEFG38810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 6 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG39810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·CCC` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG40810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·CG` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG41810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·CG·CCC` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG42810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·CG·EE` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG43810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·CG·EE·CCC` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG44810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·CG·EE·EF·EG·FF·FG·GG` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG45810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 2 * E.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·CG·FF·FG·GG` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG46810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·EE` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG47810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·EE·CCC` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG48810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·EE·EF·FF` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG49810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CF·FF` (leaf BCEFG#2.0). -/
def QuarticChamberBCEFG50810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `CG` (leaf BCEFG#3.0). -/
def QuarticChamberBCEFG51810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEFG` / `CG·CCC` (leaf BCEFG#3.0). -/
def QuarticChamberBCEFG52810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEFG` / `CG·EE` (leaf BCEFG#3.0). -/
def QuarticChamberBCEFG53810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEFG` / `CG·EE·CCC` (leafs BCEFG#3.0, BCEFG#3.1, BCEFG#3.2). -/
def QuarticChamberBCEFG54810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEFG` / `CG·EE·EG·GG` (leaf BCEFG#3.0). -/
def QuarticChamberBCEFG55810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEFG` / `CG·GG` (leaf BCEFG#3.0). -/
def QuarticChamberBCEFG56810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEFG` / `EE` (leaf BCEFG#4.0). -/
def QuarticChamberBCEFG57810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEFG` / `EE·BBB` (leaf BCEFG#4.0). -/
def QuarticChamberBCEFG58810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEFG` / `EE·BBB·BBC·BCC·CCC` (leaf BCEFG#4.0). -/
def QuarticChamberBCEFG59810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree ∧
    4 * E.natDegree = A.natDegree + 2 * B.natDegree + 4 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEFG` / `EE·CCC` (leaf BCEFG#4.0). -/
def QuarticChamberBCEFG60810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEFG` / `EE·EF·EG·FF·FG·GG` (leaf BCEFG#4.0). -/
def QuarticChamberBCEFG61810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    3 * A.natDegree + 4 * E.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEFG` / `EE·EF·FF` (leaf BCEFG#4.0). -/
def QuarticChamberBCEFG62810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEFG` / `EE·EG·GG` (leaf BCEFG#4.0). -/
def QuarticChamberBCEFG63810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEFG` / `FF` (leaf BCEFG#7.0). -/
def QuarticChamberBCEFG64810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `FF·FG·GG` (leaf BCEFG#7.0). -/
def QuarticChamberBCEFG65810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BCEFG` / `GG` (leaf BCEFG#9.0). -/
def QuarticChamberBCEFG66810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * E.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + E.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BBB` (leaf BDEFG#12.0). -/
def QuarticChamberBDEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·DD` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·DD·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·DD·DE·EE` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·DD·DE·EE·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·EE` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·EE·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·BG·FF·FG·GG` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·DD` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·DD·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·DD·DE·DF·EE·EF·FF` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·DD·DE·EE` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·DD·DE·EE·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·DD·DF·FF` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·EE` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·EE·BBB` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·EE·EF·FF` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BF·FF` (leaf BDEFG#0.0). -/
def QuarticChamberBDEFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·BBB` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·DD` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·DD·BBB` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·DD·DE·DG·EE·EG·GG` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·DD·DE·EE` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·DD·DE·EE·BBB` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·DD·DG·GG` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·EE` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG33810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·EE·BBB` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG34810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·EE·EG·GG` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG35810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `BG·GG` (leaf BDEFG#1.0). -/
def QuarticChamberBDEFG36810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG37810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·BBB` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG38810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG39810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 4 * D.natDegree = 2 * E.natDegree + 2 * F.natDegree ∧
    2 * A.natDegree + 2 * D.natDegree = E.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    5 * A.natDegree + 4 * D.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DE·DF·EE·EF·FF` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG40810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 4 * D.natDegree = 2 * E.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DE·DG·EE·EG·GG` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG41810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + 2 * D.natDegree = E.natDegree + G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DE·EE` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG42810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DE·EE·BBB` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG43810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DF·DG·FF·FG·GG` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG44810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    5 * A.natDegree + 4 * D.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DF·FF` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG45810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `DD·DG·GG` (leaf BDEFG#2.0). -/
def QuarticChamberBDEFG46810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEFG` / `EE` (leaf BDEFG#6.0). -/
def QuarticChamberBDEFG47810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEFG` / `EE·BBB` (leaf BDEFG#6.0). -/
def QuarticChamberBDEFG48810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEFG` / `EE·EF·EG·FF·FG·GG` (leaf BDEFG#6.0). -/
def QuarticChamberBDEFG49810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    3 * A.natDegree + 4 * E.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEFG` / `EE·EF·FF` (leaf BDEFG#6.0). -/
def QuarticChamberBDEFG50810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEFG` / `EE·EG·GG` (leaf BDEFG#6.0). -/
def QuarticChamberBDEFG51810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEFG` / `FF` (leaf BDEFG#9.0). -/
def QuarticChamberBDEFG52810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BDEFG` / `FF·FG·GG` (leaf BDEFG#9.0). -/
def QuarticChamberBDEFG53810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BDEFG` / `GG` (leaf BDEFG#11.0). -/
def QuarticChamberBDEFG54810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * E.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CCC` (leaf CDEFG#12.0). -/
def QuarticChamberCDEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 6 * C.natDegree ∧
    D.natDegree + F.natDegree < 3 * C.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 6 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·DD` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·DD·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree = D.natDegree + G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 2 * E.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·DD·DE·EE` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·DD·DE·EE·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree = D.natDegree + G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·EE` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·EE·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 2 * E.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·CG·FF·FG·GG` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·DD` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·DD·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·DD·DE·DF·EE·EF·FF` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·DD·DE·EE` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·DD·DE·EE·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·DD·DF·FF` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·EE` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·EE·CCC` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·EE·EF·FF` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CF·FF` (leaf CDEFG#0.0). -/
def QuarticChamberCDEFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·CCC` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·DD` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·DD·CCC` (leafs CDEFG#1.0, CDEFG#1.1, CDEFG#1.2, CDEFG#1.3, CDEFG#1.4). -/
def QuarticChamberCDEFG28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·DD·DE·DG·EE·EG·GG` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·DD·DE·EE` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·DD·DE·EE·CCC` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·DD·DG·GG` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·EE` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG33810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·EE·CCC` (leafs CDEFG#1.0, CDEFG#1.1, CDEFG#1.2). -/
def QuarticChamberCDEFG34810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·EE·EG·GG` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG35810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `CG·GG` (leaf CDEFG#1.0). -/
def QuarticChamberCDEFG36810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG37810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·CCC` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG38810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG39810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 4 * D.natDegree = 2 * E.natDegree + 2 * F.natDegree ∧
    2 * A.natDegree + 2 * D.natDegree = E.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    5 * A.natDegree + 4 * D.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DE·DF·EE·EF·FF` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG40810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 4 * D.natDegree = 2 * E.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DE·DG·EE·EG·GG` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG41810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + 2 * D.natDegree = E.natDegree + G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DE·EE` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG42810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DE·EE·CCC` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG43810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DF·DG·FF·FG·GG` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG44810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    5 * A.natDegree + 4 * D.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DF·FF` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG45810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `DD·DG·GG` (leaf CDEFG#2.0). -/
def QuarticChamberCDEFG46810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEFG` / `EE` (leaf CDEFG#6.0). -/
def QuarticChamberCDEFG47810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEFG` / `EE·CCC` (leaf CDEFG#6.0). -/
def QuarticChamberCDEFG48810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEFG` / `EE·EF·EG·FF·FG·GG` (leaf CDEFG#6.0). -/
def QuarticChamberCDEFG49810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    3 * A.natDegree + 4 * E.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEFG` / `EE·EF·FF` (leaf CDEFG#6.0). -/
def QuarticChamberCDEFG50810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEFG` / `EE·EG·GG` (leaf CDEFG#6.0). -/
def QuarticChamberCDEFG51810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEFG` / `FF` (leaf CDEFG#9.0). -/
def QuarticChamberCDEFG52810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `FF·FG·GG` (leaf CDEFG#9.0). -/
def QuarticChamberCDEFG53810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CDEFG` / `GG` (leaf CDEFG#11.0). -/
def QuarticChamberCDEFG54810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * E.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + E.natDegree < 2 * G.natDegree


end Max11DegreeRoutes
