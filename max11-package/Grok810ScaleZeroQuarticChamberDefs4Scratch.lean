import Grok810ScaleZeroQuarticChamberDefs3Scratch

/-! # Cost-argmin chamber definitions (4/4), `(8,10)` scale zero

The 135 chambers whose live-letter set `S` has |S| ∈ {6}, machine-generated from
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

/-- Cost-argmin chamber `BCDEFG` / `BBB` (leaf BCDEFG#14.0). -/
def QuarticChamberBCDEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
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
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BBB·BBC·BCC·CCC` (leaf BCDEFG#14.0). -/
def QuarticChamberBCDEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (leafs BCDEFG#0.0, BCDEFG#0.1, BCDEFG#0.2, BCDEFG#0.3, BCDEFG#0.4, BCDEFG#0.5, BCDEFG#0.6). -/
def QuarticChamberBCDEFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·DD` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·DD·BBB·BBC·BCC·CCC` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
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
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·DD·DE·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
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
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·CF·CG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·DD` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·DD·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
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
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·DD·DE·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·DD·DE·EE·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
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
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·EE·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
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
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·BG·FF·FG·GG` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·CF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·DD` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·DD·BBB·BBC·BCC·CCC` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
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
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·DD·DE·DF·EE·EF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·DD·DE·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG33810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG34810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·DD·DF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG35810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG36810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG37810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·EE·EF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG38810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·CF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG39810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·DD` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG40810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·DD·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG41810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·DD·DE·DF·EE·EF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG42810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
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
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·DD·DE·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG43810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·DD·DE·EE·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG44810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·DD·DF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG45810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·EE` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG46810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·EE·BBB` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG47810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BF·EE·EF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG48810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BF·FF` (leaf BCDEFG#0.0). -/
def QuarticChamberBCDEFG49810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
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
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG50810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·BBB` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG51810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG52810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG53810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·DD` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG54810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·DD·BBB·BBC·BCC·CCC` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG55810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
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
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·DD·DE·DG·EE·EG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG56810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·DD·DE·EE` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG57810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG58810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·DD·DG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG59810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·EE` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG60810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG61810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·EE·EG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG62810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·CG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG63810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·DD` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG64810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·DD·BBB` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG65810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·DD·DE·DG·EE·EG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG66810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
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
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·DD·DE·EE` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG67810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·DD·DE·EE·BBB` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG68810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·DD·DG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG69810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·EE` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG70810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `BG·EE·BBB` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG71810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·EE·EG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG72810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `BG·GG` (leaf BCDEFG#1.0). -/
def QuarticChamberBCDEFG73810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CCC` (leaf BCDEFG#21.0). -/
def QuarticChamberBCDEFG74810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
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
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG75810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG76810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·CG` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG77810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG78810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·DD` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG79810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·DD·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG80810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG81810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·DD·DE·EE` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG82810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·DD·DE·EE·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG83810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG84810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·EE` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG85810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·EE·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG86810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG87810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·CG·FF·FG·GG` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG88810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·DD` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG89810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·DD·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG90810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·DD·DE·DF·EE·EF·FF` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG91810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·DD·DE·EE` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG92810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·DD·DE·EE·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG93810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·DD·DF·FF` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG94810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·EE` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG95810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·EE·CCC` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG96810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CF·EE·EF·FF` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG97810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CF·FF` (leaf BCDEFG#2.0). -/
def QuarticChamberBCDEFG98810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG99810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·CCC` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG100810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
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
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CG·DD` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG101810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·DD·CCC` (leafs BCDEFG#3.0, BCDEFG#3.1, BCDEFG#3.2, BCDEFG#3.3, BCDEFG#3.4, BCDEFG#3.5, BCDEFG#3.6, BCDEFG#3.7, BCDEFG#3.8, BCDEFG#3.9, BCDEFG#3.10, BCDEFG#3.11, BCDEFG#3.12, BCDEFG#3.13, BCDEFG#3.14). -/
def QuarticChamberBCDEFG102810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
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
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CG·DD·DE·DG·EE·EG·GG` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG103810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·DD·DE·EE` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG104810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·DD·DE·EE·CCC` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG105810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·DD·DG·GG` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG106810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·EE` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG107810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·EE·CCC` (leafs BCDEFG#3.0, BCDEFG#3.1, BCDEFG#3.2, BCDEFG#3.3, BCDEFG#3.4, BCDEFG#3.5, BCDEFG#3.6). -/
def QuarticChamberBCDEFG108810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
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
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDEFG` / `CG·EE·EG·GG` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG109810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `CG·GG` (leaf BCDEFG#3.0). -/
def QuarticChamberBCDEFG110810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG111810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·BBB` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG112810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
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
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEFG` / `DD·BBB·BBC·BCC·CCC` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG113810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
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
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEFG` / `DD·CCC` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG114810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
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
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG115810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DE·DF·EE·EF·FF` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG116810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DE·DG·EE·EG·GG` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG117810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DE·EE` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG118810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DE·EE·BBB` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG119810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG120810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
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
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDEFG` / `DD·DE·EE·CCC` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG121810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DF·DG·FF·FG·GG` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG122810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DF·FF` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG123810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `DD·DG·GG` (leaf BCDEFG#4.0). -/
def QuarticChamberBCDEFG124810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `EE` (leaf BCDEFG#8.0). -/
def QuarticChamberBCDEFG125810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `EE·BBB` (leaf BCDEFG#8.0). -/
def QuarticChamberBCDEFG126810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
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
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEFG` / `EE·BBB·BBC·BCC·CCC` (leaf BCDEFG#8.0). -/
def QuarticChamberBCDEFG127810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
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
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEFG` / `EE·CCC` (leaf BCDEFG#8.0). -/
def QuarticChamberBCDEFG128810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
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
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDEFG` / `EE·EF·EG·FF·FG·GG` (leaf BCDEFG#8.0). -/
def QuarticChamberBCDEFG129810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
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
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `EE·EF·FF` (leaf BCDEFG#8.0). -/
def QuarticChamberBCDEFG130810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `EE·EG·GG` (leaf BCDEFG#8.0). -/
def QuarticChamberBCDEFG131810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `FF` (leaf BCDEFG#11.0). -/
def QuarticChamberBCDEFG132810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
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

/-- Cost-argmin chamber `BCDEFG` / `FF·FG·GG` (leaf BCDEFG#11.0). -/
def QuarticChamberBCDEFG133810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
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

set_option maxHeartbeats 64000000 in
/-- Cost-argmin chamber `BCDEFG` / `GG` (leaf BCDEFG#13.0). -/
def QuarticChamberBCDEFG134810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
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

/-! ## The taxonomy -/

set_option maxHeartbeats 64000000 in
/-- The 6 cost-argmin chambers with |S| = 1. -/
inductive QuarticChamberSupportSize1810 (A B C D E F G : k[X]) : Prop
  | cB0 : QuarticChamberB0810 A B C D E F G →
      QuarticChamberSupportSize1810 A B C D E F G
  | cC0 : QuarticChamberC0810 A B C D E F G →
      QuarticChamberSupportSize1810 A B C D E F G
  | cD0 : QuarticChamberD0810 A B C D E F G →
      QuarticChamberSupportSize1810 A B C D E F G
  | cE0 : QuarticChamberE0810 A B C D E F G →
      QuarticChamberSupportSize1810 A B C D E F G
  | cF0 : QuarticChamberF0810 A B C D E F G →
      QuarticChamberSupportSize1810 A B C D E F G
  | cG0 : QuarticChamberG0810 A B C D E F G →
      QuarticChamberSupportSize1810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The 53 cost-argmin chambers with |S| = 2. -/
inductive QuarticChamberSupportSize2810 (A B C D E F G : k[X]) : Prop
  | cBC0 : QuarticChamberBC0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBC1 : QuarticChamberBC1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBC2 : QuarticChamberBC2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBD0 : QuarticChamberBD0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBD1 : QuarticChamberBD1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBD2 : QuarticChamberBD2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBE0 : QuarticChamberBE0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBE1 : QuarticChamberBE1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBE2 : QuarticChamberBE2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBF0 : QuarticChamberBF0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBF1 : QuarticChamberBF1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBF2 : QuarticChamberBF2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBF3 : QuarticChamberBF3810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBF4 : QuarticChamberBF4810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBG0 : QuarticChamberBG0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBG1 : QuarticChamberBG1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBG2 : QuarticChamberBG2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBG3 : QuarticChamberBG3810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cBG4 : QuarticChamberBG4810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCD0 : QuarticChamberCD0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCD1 : QuarticChamberCD1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCD2 : QuarticChamberCD2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCE0 : QuarticChamberCE0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCE1 : QuarticChamberCE1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCE2 : QuarticChamberCE2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCF0 : QuarticChamberCF0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCF1 : QuarticChamberCF1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCF2 : QuarticChamberCF2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCF3 : QuarticChamberCF3810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCF4 : QuarticChamberCF4810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCG0 : QuarticChamberCG0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCG1 : QuarticChamberCG1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCG2 : QuarticChamberCG2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCG3 : QuarticChamberCG3810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cCG4 : QuarticChamberCG4810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDE0 : QuarticChamberDE0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDE1 : QuarticChamberDE1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDE2 : QuarticChamberDE2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDF0 : QuarticChamberDF0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDF1 : QuarticChamberDF1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDF2 : QuarticChamberDF2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDG0 : QuarticChamberDG0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDG1 : QuarticChamberDG1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cDG2 : QuarticChamberDG2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cEF0 : QuarticChamberEF0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cEF1 : QuarticChamberEF1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cEF2 : QuarticChamberEF2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cEG0 : QuarticChamberEG0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cEG1 : QuarticChamberEG1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cEG2 : QuarticChamberEG2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cFG0 : QuarticChamberFG0810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cFG1 : QuarticChamberFG1810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G
  | cFG2 : QuarticChamberFG2810 A B C D E F G →
      QuarticChamberSupportSize2810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The 196 cost-argmin chambers with |S| = 3. -/
inductive QuarticChamberSupportSize3810 (A B C D E F G : k[X]) : Prop
  | cBCD0 : QuarticChamberBCD0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCD1 : QuarticChamberBCD1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCD2 : QuarticChamberBCD2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCD3 : QuarticChamberBCD3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCD4 : QuarticChamberBCD4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCD5 : QuarticChamberBCD5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCD6 : QuarticChamberBCD6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCE0 : QuarticChamberBCE0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCE1 : QuarticChamberBCE1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCE2 : QuarticChamberBCE2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCE3 : QuarticChamberBCE3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCE4 : QuarticChamberBCE4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCE5 : QuarticChamberBCE5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCE6 : QuarticChamberBCE6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF0 : QuarticChamberBCF0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF1 : QuarticChamberBCF1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF2 : QuarticChamberBCF2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF3 : QuarticChamberBCF3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF4 : QuarticChamberBCF4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF5 : QuarticChamberBCF5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF6 : QuarticChamberBCF6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF7 : QuarticChamberBCF7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF8 : QuarticChamberBCF8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF9 : QuarticChamberBCF9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF10 : QuarticChamberBCF10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF11 : QuarticChamberBCF11810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCF12 : QuarticChamberBCF12810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG0 : QuarticChamberBCG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG1 : QuarticChamberBCG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG2 : QuarticChamberBCG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG3 : QuarticChamberBCG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG4 : QuarticChamberBCG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG5 : QuarticChamberBCG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG6 : QuarticChamberBCG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG7 : QuarticChamberBCG7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG8 : QuarticChamberBCG8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG9 : QuarticChamberBCG9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG10 : QuarticChamberBCG10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG11 : QuarticChamberBCG11810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBCG12 : QuarticChamberBCG12810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDE0 : QuarticChamberBDE0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDE1 : QuarticChamberBDE1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDE2 : QuarticChamberBDE2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDE3 : QuarticChamberBDE3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDE4 : QuarticChamberBDE4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDE5 : QuarticChamberBDE5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDE6 : QuarticChamberBDE6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF0 : QuarticChamberBDF0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF1 : QuarticChamberBDF1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF2 : QuarticChamberBDF2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF3 : QuarticChamberBDF3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF4 : QuarticChamberBDF4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF5 : QuarticChamberBDF5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF6 : QuarticChamberBDF6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF7 : QuarticChamberBDF7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF8 : QuarticChamberBDF8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF9 : QuarticChamberBDF9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDF10 : QuarticChamberBDF10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG0 : QuarticChamberBDG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG1 : QuarticChamberBDG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG2 : QuarticChamberBDG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG3 : QuarticChamberBDG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG4 : QuarticChamberBDG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG5 : QuarticChamberBDG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG6 : QuarticChamberBDG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG7 : QuarticChamberBDG7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG8 : QuarticChamberBDG8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG9 : QuarticChamberBDG9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBDG10 : QuarticChamberBDG10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF0 : QuarticChamberBEF0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF1 : QuarticChamberBEF1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF2 : QuarticChamberBEF2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF3 : QuarticChamberBEF3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF4 : QuarticChamberBEF4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF5 : QuarticChamberBEF5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF6 : QuarticChamberBEF6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF7 : QuarticChamberBEF7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF8 : QuarticChamberBEF8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF9 : QuarticChamberBEF9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEF10 : QuarticChamberBEF10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG0 : QuarticChamberBEG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG1 : QuarticChamberBEG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG2 : QuarticChamberBEG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG3 : QuarticChamberBEG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG4 : QuarticChamberBEG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG5 : QuarticChamberBEG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG6 : QuarticChamberBEG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG7 : QuarticChamberBEG7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG8 : QuarticChamberBEG8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG9 : QuarticChamberBEG9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBEG10 : QuarticChamberBEG10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG0 : QuarticChamberBFG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG1 : QuarticChamberBFG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG2 : QuarticChamberBFG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG3 : QuarticChamberBFG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG4 : QuarticChamberBFG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG5 : QuarticChamberBFG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG6 : QuarticChamberBFG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG7 : QuarticChamberBFG7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG8 : QuarticChamberBFG8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG9 : QuarticChamberBFG9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG10 : QuarticChamberBFG10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG11 : QuarticChamberBFG11810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cBFG12 : QuarticChamberBFG12810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDE0 : QuarticChamberCDE0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDE1 : QuarticChamberCDE1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDE2 : QuarticChamberCDE2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDE3 : QuarticChamberCDE3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDE4 : QuarticChamberCDE4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDE5 : QuarticChamberCDE5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDE6 : QuarticChamberCDE6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF0 : QuarticChamberCDF0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF1 : QuarticChamberCDF1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF2 : QuarticChamberCDF2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF3 : QuarticChamberCDF3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF4 : QuarticChamberCDF4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF5 : QuarticChamberCDF5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF6 : QuarticChamberCDF6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF7 : QuarticChamberCDF7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF8 : QuarticChamberCDF8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF9 : QuarticChamberCDF9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDF10 : QuarticChamberCDF10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG0 : QuarticChamberCDG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG1 : QuarticChamberCDG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG2 : QuarticChamberCDG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG3 : QuarticChamberCDG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG4 : QuarticChamberCDG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG5 : QuarticChamberCDG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG6 : QuarticChamberCDG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG7 : QuarticChamberCDG7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG8 : QuarticChamberCDG8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG9 : QuarticChamberCDG9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCDG10 : QuarticChamberCDG10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF0 : QuarticChamberCEF0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF1 : QuarticChamberCEF1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF2 : QuarticChamberCEF2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF3 : QuarticChamberCEF3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF4 : QuarticChamberCEF4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF5 : QuarticChamberCEF5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF6 : QuarticChamberCEF6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF7 : QuarticChamberCEF7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF8 : QuarticChamberCEF8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF9 : QuarticChamberCEF9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEF10 : QuarticChamberCEF10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG0 : QuarticChamberCEG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG1 : QuarticChamberCEG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG2 : QuarticChamberCEG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG3 : QuarticChamberCEG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG4 : QuarticChamberCEG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG5 : QuarticChamberCEG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG6 : QuarticChamberCEG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG7 : QuarticChamberCEG7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG8 : QuarticChamberCEG8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG9 : QuarticChamberCEG9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCEG10 : QuarticChamberCEG10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG0 : QuarticChamberCFG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG1 : QuarticChamberCFG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG2 : QuarticChamberCFG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG3 : QuarticChamberCFG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG4 : QuarticChamberCFG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG5 : QuarticChamberCFG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG6 : QuarticChamberCFG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG7 : QuarticChamberCFG7810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG8 : QuarticChamberCFG8810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG9 : QuarticChamberCFG9810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG10 : QuarticChamberCFG10810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG11 : QuarticChamberCFG11810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cCFG12 : QuarticChamberCFG12810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEF0 : QuarticChamberDEF0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEF1 : QuarticChamberDEF1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEF2 : QuarticChamberDEF2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEF3 : QuarticChamberDEF3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEF4 : QuarticChamberDEF4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEF5 : QuarticChamberDEF5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEF6 : QuarticChamberDEF6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEG0 : QuarticChamberDEG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEG1 : QuarticChamberDEG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEG2 : QuarticChamberDEG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEG3 : QuarticChamberDEG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEG4 : QuarticChamberDEG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEG5 : QuarticChamberDEG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDEG6 : QuarticChamberDEG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDFG0 : QuarticChamberDFG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDFG1 : QuarticChamberDFG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDFG2 : QuarticChamberDFG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDFG3 : QuarticChamberDFG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDFG4 : QuarticChamberDFG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDFG5 : QuarticChamberDFG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cDFG6 : QuarticChamberDFG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cEFG0 : QuarticChamberEFG0810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cEFG1 : QuarticChamberEFG1810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cEFG2 : QuarticChamberEFG2810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cEFG3 : QuarticChamberEFG3810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cEFG4 : QuarticChamberEFG4810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cEFG5 : QuarticChamberEFG5810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G
  | cEFG6 : QuarticChamberEFG6810 A B C D E F G →
      QuarticChamberSupportSize3810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The 371 cost-argmin chambers with |S| = 4. -/
inductive QuarticChamberSupportSize4810 (A B C D E F G : k[X]) : Prop
  | cBCDE0 : QuarticChamberBCDE0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE1 : QuarticChamberBCDE1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE2 : QuarticChamberBCDE2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE3 : QuarticChamberBCDE3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE4 : QuarticChamberBCDE4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE5 : QuarticChamberBCDE5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE6 : QuarticChamberBCDE6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE7 : QuarticChamberBCDE7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE8 : QuarticChamberBCDE8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE9 : QuarticChamberBCDE9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE10 : QuarticChamberBCDE10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE11 : QuarticChamberBCDE11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE12 : QuarticChamberBCDE12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE13 : QuarticChamberBCDE13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDE14 : QuarticChamberBCDE14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF0 : QuarticChamberBCDF0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF1 : QuarticChamberBCDF1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF2 : QuarticChamberBCDF2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF3 : QuarticChamberBCDF3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF4 : QuarticChamberBCDF4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF5 : QuarticChamberBCDF5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF6 : QuarticChamberBCDF6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF7 : QuarticChamberBCDF7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF8 : QuarticChamberBCDF8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF9 : QuarticChamberBCDF9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF10 : QuarticChamberBCDF10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF11 : QuarticChamberBCDF11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF12 : QuarticChamberBCDF12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF13 : QuarticChamberBCDF13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF14 : QuarticChamberBCDF14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF15 : QuarticChamberBCDF15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF16 : QuarticChamberBCDF16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF17 : QuarticChamberBCDF17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF18 : QuarticChamberBCDF18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF19 : QuarticChamberBCDF19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF20 : QuarticChamberBCDF20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF21 : QuarticChamberBCDF21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF22 : QuarticChamberBCDF22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF23 : QuarticChamberBCDF23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF24 : QuarticChamberBCDF24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF25 : QuarticChamberBCDF25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDF26 : QuarticChamberBCDF26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG0 : QuarticChamberBCDG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG1 : QuarticChamberBCDG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG2 : QuarticChamberBCDG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG3 : QuarticChamberBCDG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG4 : QuarticChamberBCDG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG5 : QuarticChamberBCDG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG6 : QuarticChamberBCDG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG7 : QuarticChamberBCDG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG8 : QuarticChamberBCDG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG9 : QuarticChamberBCDG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG10 : QuarticChamberBCDG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG11 : QuarticChamberBCDG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG12 : QuarticChamberBCDG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG13 : QuarticChamberBCDG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG14 : QuarticChamberBCDG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG15 : QuarticChamberBCDG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG16 : QuarticChamberBCDG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG17 : QuarticChamberBCDG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG18 : QuarticChamberBCDG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG19 : QuarticChamberBCDG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG20 : QuarticChamberBCDG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG21 : QuarticChamberBCDG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG22 : QuarticChamberBCDG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG23 : QuarticChamberBCDG23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG24 : QuarticChamberBCDG24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG25 : QuarticChamberBCDG25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCDG26 : QuarticChamberBCDG26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF0 : QuarticChamberBCEF0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF1 : QuarticChamberBCEF1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF2 : QuarticChamberBCEF2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF3 : QuarticChamberBCEF3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF4 : QuarticChamberBCEF4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF5 : QuarticChamberBCEF5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF6 : QuarticChamberBCEF6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF7 : QuarticChamberBCEF7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF8 : QuarticChamberBCEF8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF9 : QuarticChamberBCEF9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF10 : QuarticChamberBCEF10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF11 : QuarticChamberBCEF11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF12 : QuarticChamberBCEF12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF13 : QuarticChamberBCEF13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF14 : QuarticChamberBCEF14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF15 : QuarticChamberBCEF15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF16 : QuarticChamberBCEF16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF17 : QuarticChamberBCEF17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF18 : QuarticChamberBCEF18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF19 : QuarticChamberBCEF19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF20 : QuarticChamberBCEF20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF21 : QuarticChamberBCEF21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF22 : QuarticChamberBCEF22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF23 : QuarticChamberBCEF23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF24 : QuarticChamberBCEF24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF25 : QuarticChamberBCEF25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEF26 : QuarticChamberBCEF26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG0 : QuarticChamberBCEG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG1 : QuarticChamberBCEG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG2 : QuarticChamberBCEG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG3 : QuarticChamberBCEG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG4 : QuarticChamberBCEG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG5 : QuarticChamberBCEG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG6 : QuarticChamberBCEG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG7 : QuarticChamberBCEG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG8 : QuarticChamberBCEG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG9 : QuarticChamberBCEG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG10 : QuarticChamberBCEG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG11 : QuarticChamberBCEG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG12 : QuarticChamberBCEG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG13 : QuarticChamberBCEG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG14 : QuarticChamberBCEG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG15 : QuarticChamberBCEG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG16 : QuarticChamberBCEG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG17 : QuarticChamberBCEG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG18 : QuarticChamberBCEG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG19 : QuarticChamberBCEG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG20 : QuarticChamberBCEG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG21 : QuarticChamberBCEG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG22 : QuarticChamberBCEG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG23 : QuarticChamberBCEG23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG24 : QuarticChamberBCEG24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG25 : QuarticChamberBCEG25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCEG26 : QuarticChamberBCEG26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG0 : QuarticChamberBCFG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG1 : QuarticChamberBCFG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG2 : QuarticChamberBCFG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG3 : QuarticChamberBCFG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG4 : QuarticChamberBCFG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG5 : QuarticChamberBCFG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG6 : QuarticChamberBCFG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG7 : QuarticChamberBCFG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG8 : QuarticChamberBCFG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG9 : QuarticChamberBCFG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG10 : QuarticChamberBCFG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG11 : QuarticChamberBCFG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG12 : QuarticChamberBCFG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG13 : QuarticChamberBCFG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG14 : QuarticChamberBCFG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG15 : QuarticChamberBCFG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG16 : QuarticChamberBCFG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG17 : QuarticChamberBCFG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG18 : QuarticChamberBCFG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG19 : QuarticChamberBCFG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG20 : QuarticChamberBCFG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG21 : QuarticChamberBCFG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG22 : QuarticChamberBCFG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG23 : QuarticChamberBCFG23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG24 : QuarticChamberBCFG24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG25 : QuarticChamberBCFG25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG26 : QuarticChamberBCFG26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG27 : QuarticChamberBCFG27810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG28 : QuarticChamberBCFG28810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG29 : QuarticChamberBCFG29810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG30 : QuarticChamberBCFG30810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG31 : QuarticChamberBCFG31810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBCFG32 : QuarticChamberBCFG32810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF0 : QuarticChamberBDEF0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF1 : QuarticChamberBDEF1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF2 : QuarticChamberBDEF2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF3 : QuarticChamberBDEF3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF4 : QuarticChamberBDEF4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF5 : QuarticChamberBDEF5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF6 : QuarticChamberBDEF6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF7 : QuarticChamberBDEF7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF8 : QuarticChamberBDEF8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF9 : QuarticChamberBDEF9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF10 : QuarticChamberBDEF10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF11 : QuarticChamberBDEF11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF12 : QuarticChamberBDEF12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF13 : QuarticChamberBDEF13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF14 : QuarticChamberBDEF14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF15 : QuarticChamberBDEF15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF16 : QuarticChamberBDEF16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF17 : QuarticChamberBDEF17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF18 : QuarticChamberBDEF18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF19 : QuarticChamberBDEF19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF20 : QuarticChamberBDEF20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF21 : QuarticChamberBDEF21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEF22 : QuarticChamberBDEF22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG0 : QuarticChamberBDEG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG1 : QuarticChamberBDEG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG2 : QuarticChamberBDEG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG3 : QuarticChamberBDEG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG4 : QuarticChamberBDEG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG5 : QuarticChamberBDEG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG6 : QuarticChamberBDEG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG7 : QuarticChamberBDEG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG8 : QuarticChamberBDEG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG9 : QuarticChamberBDEG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG10 : QuarticChamberBDEG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG11 : QuarticChamberBDEG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG12 : QuarticChamberBDEG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG13 : QuarticChamberBDEG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG14 : QuarticChamberBDEG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG15 : QuarticChamberBDEG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG16 : QuarticChamberBDEG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG17 : QuarticChamberBDEG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG18 : QuarticChamberBDEG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG19 : QuarticChamberBDEG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG20 : QuarticChamberBDEG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG21 : QuarticChamberBDEG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDEG22 : QuarticChamberBDEG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG0 : QuarticChamberBDFG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG1 : QuarticChamberBDFG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG2 : QuarticChamberBDFG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG3 : QuarticChamberBDFG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG4 : QuarticChamberBDFG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG5 : QuarticChamberBDFG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG6 : QuarticChamberBDFG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG7 : QuarticChamberBDFG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG8 : QuarticChamberBDFG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG9 : QuarticChamberBDFG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG10 : QuarticChamberBDFG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG11 : QuarticChamberBDFG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG12 : QuarticChamberBDFG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG13 : QuarticChamberBDFG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG14 : QuarticChamberBDFG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG15 : QuarticChamberBDFG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG16 : QuarticChamberBDFG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG17 : QuarticChamberBDFG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG18 : QuarticChamberBDFG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG19 : QuarticChamberBDFG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG20 : QuarticChamberBDFG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG21 : QuarticChamberBDFG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG22 : QuarticChamberBDFG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG23 : QuarticChamberBDFG23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG24 : QuarticChamberBDFG24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG25 : QuarticChamberBDFG25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBDFG26 : QuarticChamberBDFG26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG0 : QuarticChamberBEFG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG1 : QuarticChamberBEFG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG2 : QuarticChamberBEFG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG3 : QuarticChamberBEFG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG4 : QuarticChamberBEFG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG5 : QuarticChamberBEFG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG6 : QuarticChamberBEFG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG7 : QuarticChamberBEFG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG8 : QuarticChamberBEFG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG9 : QuarticChamberBEFG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG10 : QuarticChamberBEFG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG11 : QuarticChamberBEFG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG12 : QuarticChamberBEFG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG13 : QuarticChamberBEFG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG14 : QuarticChamberBEFG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG15 : QuarticChamberBEFG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG16 : QuarticChamberBEFG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG17 : QuarticChamberBEFG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG18 : QuarticChamberBEFG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG19 : QuarticChamberBEFG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG20 : QuarticChamberBEFG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG21 : QuarticChamberBEFG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG22 : QuarticChamberBEFG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG23 : QuarticChamberBEFG23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG24 : QuarticChamberBEFG24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG25 : QuarticChamberBEFG25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cBEFG26 : QuarticChamberBEFG26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF0 : QuarticChamberCDEF0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF1 : QuarticChamberCDEF1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF2 : QuarticChamberCDEF2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF3 : QuarticChamberCDEF3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF4 : QuarticChamberCDEF4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF5 : QuarticChamberCDEF5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF6 : QuarticChamberCDEF6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF7 : QuarticChamberCDEF7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF8 : QuarticChamberCDEF8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF9 : QuarticChamberCDEF9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF10 : QuarticChamberCDEF10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF11 : QuarticChamberCDEF11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF12 : QuarticChamberCDEF12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF13 : QuarticChamberCDEF13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF14 : QuarticChamberCDEF14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF15 : QuarticChamberCDEF15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF16 : QuarticChamberCDEF16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF17 : QuarticChamberCDEF17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF18 : QuarticChamberCDEF18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF19 : QuarticChamberCDEF19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF20 : QuarticChamberCDEF20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF21 : QuarticChamberCDEF21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEF22 : QuarticChamberCDEF22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG0 : QuarticChamberCDEG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG1 : QuarticChamberCDEG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG2 : QuarticChamberCDEG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG3 : QuarticChamberCDEG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG4 : QuarticChamberCDEG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG5 : QuarticChamberCDEG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG6 : QuarticChamberCDEG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG7 : QuarticChamberCDEG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG8 : QuarticChamberCDEG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG9 : QuarticChamberCDEG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG10 : QuarticChamberCDEG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG11 : QuarticChamberCDEG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG12 : QuarticChamberCDEG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG13 : QuarticChamberCDEG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG14 : QuarticChamberCDEG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG15 : QuarticChamberCDEG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG16 : QuarticChamberCDEG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG17 : QuarticChamberCDEG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG18 : QuarticChamberCDEG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG19 : QuarticChamberCDEG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG20 : QuarticChamberCDEG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG21 : QuarticChamberCDEG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDEG22 : QuarticChamberCDEG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG0 : QuarticChamberCDFG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG1 : QuarticChamberCDFG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG2 : QuarticChamberCDFG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG3 : QuarticChamberCDFG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG4 : QuarticChamberCDFG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG5 : QuarticChamberCDFG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG6 : QuarticChamberCDFG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG7 : QuarticChamberCDFG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG8 : QuarticChamberCDFG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG9 : QuarticChamberCDFG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG10 : QuarticChamberCDFG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG11 : QuarticChamberCDFG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG12 : QuarticChamberCDFG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG13 : QuarticChamberCDFG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG14 : QuarticChamberCDFG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG15 : QuarticChamberCDFG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG16 : QuarticChamberCDFG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG17 : QuarticChamberCDFG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG18 : QuarticChamberCDFG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG19 : QuarticChamberCDFG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG20 : QuarticChamberCDFG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG21 : QuarticChamberCDFG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG22 : QuarticChamberCDFG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG23 : QuarticChamberCDFG23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG24 : QuarticChamberCDFG24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG25 : QuarticChamberCDFG25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCDFG26 : QuarticChamberCDFG26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG0 : QuarticChamberCEFG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG1 : QuarticChamberCEFG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG2 : QuarticChamberCEFG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG3 : QuarticChamberCEFG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG4 : QuarticChamberCEFG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG5 : QuarticChamberCEFG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG6 : QuarticChamberCEFG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG7 : QuarticChamberCEFG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG8 : QuarticChamberCEFG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG9 : QuarticChamberCEFG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG10 : QuarticChamberCEFG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG11 : QuarticChamberCEFG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG12 : QuarticChamberCEFG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG13 : QuarticChamberCEFG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG14 : QuarticChamberCEFG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG15 : QuarticChamberCEFG15810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG16 : QuarticChamberCEFG16810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG17 : QuarticChamberCEFG17810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG18 : QuarticChamberCEFG18810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG19 : QuarticChamberCEFG19810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG20 : QuarticChamberCEFG20810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG21 : QuarticChamberCEFG21810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG22 : QuarticChamberCEFG22810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG23 : QuarticChamberCEFG23810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG24 : QuarticChamberCEFG24810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG25 : QuarticChamberCEFG25810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cCEFG26 : QuarticChamberCEFG26810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG0 : QuarticChamberDEFG0810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG1 : QuarticChamberDEFG1810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG2 : QuarticChamberDEFG2810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG3 : QuarticChamberDEFG3810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG4 : QuarticChamberDEFG4810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG5 : QuarticChamberDEFG5810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG6 : QuarticChamberDEFG6810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG7 : QuarticChamberDEFG7810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG8 : QuarticChamberDEFG8810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG9 : QuarticChamberDEFG9810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG10 : QuarticChamberDEFG10810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG11 : QuarticChamberDEFG11810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG12 : QuarticChamberDEFG12810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG13 : QuarticChamberDEFG13810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G
  | cDEFG14 : QuarticChamberDEFG14810 A B C D E F G →
      QuarticChamberSupportSize4810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The 354 cost-argmin chambers with |S| = 5. -/
inductive QuarticChamberSupportSize5810 (A B C D E F G : k[X]) : Prop
  | cBCDEF0 : QuarticChamberBCDEF0810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF1 : QuarticChamberBCDEF1810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF2 : QuarticChamberBCDEF2810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF3 : QuarticChamberBCDEF3810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF4 : QuarticChamberBCDEF4810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF5 : QuarticChamberBCDEF5810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF6 : QuarticChamberBCDEF6810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF7 : QuarticChamberBCDEF7810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF8 : QuarticChamberBCDEF8810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF9 : QuarticChamberBCDEF9810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF10 : QuarticChamberBCDEF10810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF11 : QuarticChamberBCDEF11810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF12 : QuarticChamberBCDEF12810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF13 : QuarticChamberBCDEF13810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF14 : QuarticChamberBCDEF14810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF15 : QuarticChamberBCDEF15810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF16 : QuarticChamberBCDEF16810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF17 : QuarticChamberBCDEF17810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF18 : QuarticChamberBCDEF18810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF19 : QuarticChamberBCDEF19810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF20 : QuarticChamberBCDEF20810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF21 : QuarticChamberBCDEF21810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF22 : QuarticChamberBCDEF22810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF23 : QuarticChamberBCDEF23810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF24 : QuarticChamberBCDEF24810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF25 : QuarticChamberBCDEF25810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF26 : QuarticChamberBCDEF26810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF27 : QuarticChamberBCDEF27810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF28 : QuarticChamberBCDEF28810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF29 : QuarticChamberBCDEF29810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF30 : QuarticChamberBCDEF30810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF31 : QuarticChamberBCDEF31810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF32 : QuarticChamberBCDEF32810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF33 : QuarticChamberBCDEF33810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF34 : QuarticChamberBCDEF34810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF35 : QuarticChamberBCDEF35810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF36 : QuarticChamberBCDEF36810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF37 : QuarticChamberBCDEF37810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF38 : QuarticChamberBCDEF38810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF39 : QuarticChamberBCDEF39810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF40 : QuarticChamberBCDEF40810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF41 : QuarticChamberBCDEF41810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF42 : QuarticChamberBCDEF42810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF43 : QuarticChamberBCDEF43810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF44 : QuarticChamberBCDEF44810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF45 : QuarticChamberBCDEF45810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF46 : QuarticChamberBCDEF46810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF47 : QuarticChamberBCDEF47810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF48 : QuarticChamberBCDEF48810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF49 : QuarticChamberBCDEF49810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF50 : QuarticChamberBCDEF50810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF51 : QuarticChamberBCDEF51810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF52 : QuarticChamberBCDEF52810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF53 : QuarticChamberBCDEF53810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEF54 : QuarticChamberBCDEF54810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG0 : QuarticChamberBCDEG0810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG1 : QuarticChamberBCDEG1810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG2 : QuarticChamberBCDEG2810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG3 : QuarticChamberBCDEG3810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG4 : QuarticChamberBCDEG4810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG5 : QuarticChamberBCDEG5810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG6 : QuarticChamberBCDEG6810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG7 : QuarticChamberBCDEG7810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG8 : QuarticChamberBCDEG8810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG9 : QuarticChamberBCDEG9810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG10 : QuarticChamberBCDEG10810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG11 : QuarticChamberBCDEG11810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG12 : QuarticChamberBCDEG12810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG13 : QuarticChamberBCDEG13810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG14 : QuarticChamberBCDEG14810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG15 : QuarticChamberBCDEG15810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG16 : QuarticChamberBCDEG16810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG17 : QuarticChamberBCDEG17810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG18 : QuarticChamberBCDEG18810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG19 : QuarticChamberBCDEG19810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG20 : QuarticChamberBCDEG20810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG21 : QuarticChamberBCDEG21810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG22 : QuarticChamberBCDEG22810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG23 : QuarticChamberBCDEG23810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG24 : QuarticChamberBCDEG24810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG25 : QuarticChamberBCDEG25810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG26 : QuarticChamberBCDEG26810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG27 : QuarticChamberBCDEG27810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG28 : QuarticChamberBCDEG28810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG29 : QuarticChamberBCDEG29810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG30 : QuarticChamberBCDEG30810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG31 : QuarticChamberBCDEG31810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG32 : QuarticChamberBCDEG32810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG33 : QuarticChamberBCDEG33810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG34 : QuarticChamberBCDEG34810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG35 : QuarticChamberBCDEG35810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG36 : QuarticChamberBCDEG36810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG37 : QuarticChamberBCDEG37810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG38 : QuarticChamberBCDEG38810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG39 : QuarticChamberBCDEG39810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG40 : QuarticChamberBCDEG40810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG41 : QuarticChamberBCDEG41810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG42 : QuarticChamberBCDEG42810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG43 : QuarticChamberBCDEG43810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG44 : QuarticChamberBCDEG44810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG45 : QuarticChamberBCDEG45810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG46 : QuarticChamberBCDEG46810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG47 : QuarticChamberBCDEG47810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG48 : QuarticChamberBCDEG48810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG49 : QuarticChamberBCDEG49810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG50 : QuarticChamberBCDEG50810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG51 : QuarticChamberBCDEG51810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG52 : QuarticChamberBCDEG52810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG53 : QuarticChamberBCDEG53810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDEG54 : QuarticChamberBCDEG54810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG0 : QuarticChamberBCDFG0810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG1 : QuarticChamberBCDFG1810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG2 : QuarticChamberBCDFG2810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG3 : QuarticChamberBCDFG3810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG4 : QuarticChamberBCDFG4810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG5 : QuarticChamberBCDFG5810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG6 : QuarticChamberBCDFG6810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG7 : QuarticChamberBCDFG7810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG8 : QuarticChamberBCDFG8810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG9 : QuarticChamberBCDFG9810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG10 : QuarticChamberBCDFG10810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG11 : QuarticChamberBCDFG11810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG12 : QuarticChamberBCDFG12810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG13 : QuarticChamberBCDFG13810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG14 : QuarticChamberBCDFG14810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG15 : QuarticChamberBCDFG15810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG16 : QuarticChamberBCDFG16810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG17 : QuarticChamberBCDFG17810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG18 : QuarticChamberBCDFG18810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG19 : QuarticChamberBCDFG19810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG20 : QuarticChamberBCDFG20810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG21 : QuarticChamberBCDFG21810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG22 : QuarticChamberBCDFG22810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG23 : QuarticChamberBCDFG23810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG24 : QuarticChamberBCDFG24810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG25 : QuarticChamberBCDFG25810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG26 : QuarticChamberBCDFG26810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG27 : QuarticChamberBCDFG27810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG28 : QuarticChamberBCDFG28810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG29 : QuarticChamberBCDFG29810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG30 : QuarticChamberBCDFG30810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG31 : QuarticChamberBCDFG31810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG32 : QuarticChamberBCDFG32810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG33 : QuarticChamberBCDFG33810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG34 : QuarticChamberBCDFG34810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG35 : QuarticChamberBCDFG35810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG36 : QuarticChamberBCDFG36810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG37 : QuarticChamberBCDFG37810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG38 : QuarticChamberBCDFG38810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG39 : QuarticChamberBCDFG39810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG40 : QuarticChamberBCDFG40810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG41 : QuarticChamberBCDFG41810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG42 : QuarticChamberBCDFG42810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG43 : QuarticChamberBCDFG43810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG44 : QuarticChamberBCDFG44810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG45 : QuarticChamberBCDFG45810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG46 : QuarticChamberBCDFG46810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG47 : QuarticChamberBCDFG47810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG48 : QuarticChamberBCDFG48810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG49 : QuarticChamberBCDFG49810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG50 : QuarticChamberBCDFG50810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG51 : QuarticChamberBCDFG51810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG52 : QuarticChamberBCDFG52810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG53 : QuarticChamberBCDFG53810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG54 : QuarticChamberBCDFG54810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG55 : QuarticChamberBCDFG55810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG56 : QuarticChamberBCDFG56810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG57 : QuarticChamberBCDFG57810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG58 : QuarticChamberBCDFG58810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG59 : QuarticChamberBCDFG59810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG60 : QuarticChamberBCDFG60810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG61 : QuarticChamberBCDFG61810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG62 : QuarticChamberBCDFG62810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG63 : QuarticChamberBCDFG63810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG64 : QuarticChamberBCDFG64810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG65 : QuarticChamberBCDFG65810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCDFG66 : QuarticChamberBCDFG66810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG0 : QuarticChamberBCEFG0810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG1 : QuarticChamberBCEFG1810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG2 : QuarticChamberBCEFG2810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG3 : QuarticChamberBCEFG3810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG4 : QuarticChamberBCEFG4810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG5 : QuarticChamberBCEFG5810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG6 : QuarticChamberBCEFG6810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG7 : QuarticChamberBCEFG7810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG8 : QuarticChamberBCEFG8810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG9 : QuarticChamberBCEFG9810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG10 : QuarticChamberBCEFG10810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG11 : QuarticChamberBCEFG11810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG12 : QuarticChamberBCEFG12810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG13 : QuarticChamberBCEFG13810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG14 : QuarticChamberBCEFG14810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG15 : QuarticChamberBCEFG15810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG16 : QuarticChamberBCEFG16810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG17 : QuarticChamberBCEFG17810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG18 : QuarticChamberBCEFG18810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG19 : QuarticChamberBCEFG19810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG20 : QuarticChamberBCEFG20810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG21 : QuarticChamberBCEFG21810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG22 : QuarticChamberBCEFG22810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG23 : QuarticChamberBCEFG23810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG24 : QuarticChamberBCEFG24810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG25 : QuarticChamberBCEFG25810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG26 : QuarticChamberBCEFG26810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG27 : QuarticChamberBCEFG27810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG28 : QuarticChamberBCEFG28810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG29 : QuarticChamberBCEFG29810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG30 : QuarticChamberBCEFG30810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG31 : QuarticChamberBCEFG31810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG32 : QuarticChamberBCEFG32810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG33 : QuarticChamberBCEFG33810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG34 : QuarticChamberBCEFG34810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG35 : QuarticChamberBCEFG35810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG36 : QuarticChamberBCEFG36810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG37 : QuarticChamberBCEFG37810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG38 : QuarticChamberBCEFG38810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG39 : QuarticChamberBCEFG39810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG40 : QuarticChamberBCEFG40810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG41 : QuarticChamberBCEFG41810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG42 : QuarticChamberBCEFG42810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG43 : QuarticChamberBCEFG43810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG44 : QuarticChamberBCEFG44810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG45 : QuarticChamberBCEFG45810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG46 : QuarticChamberBCEFG46810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG47 : QuarticChamberBCEFG47810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG48 : QuarticChamberBCEFG48810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG49 : QuarticChamberBCEFG49810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG50 : QuarticChamberBCEFG50810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG51 : QuarticChamberBCEFG51810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG52 : QuarticChamberBCEFG52810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG53 : QuarticChamberBCEFG53810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG54 : QuarticChamberBCEFG54810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG55 : QuarticChamberBCEFG55810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG56 : QuarticChamberBCEFG56810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG57 : QuarticChamberBCEFG57810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG58 : QuarticChamberBCEFG58810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG59 : QuarticChamberBCEFG59810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG60 : QuarticChamberBCEFG60810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG61 : QuarticChamberBCEFG61810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG62 : QuarticChamberBCEFG62810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG63 : QuarticChamberBCEFG63810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG64 : QuarticChamberBCEFG64810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG65 : QuarticChamberBCEFG65810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBCEFG66 : QuarticChamberBCEFG66810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG0 : QuarticChamberBDEFG0810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG1 : QuarticChamberBDEFG1810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG2 : QuarticChamberBDEFG2810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG3 : QuarticChamberBDEFG3810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG4 : QuarticChamberBDEFG4810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG5 : QuarticChamberBDEFG5810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG6 : QuarticChamberBDEFG6810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG7 : QuarticChamberBDEFG7810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG8 : QuarticChamberBDEFG8810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG9 : QuarticChamberBDEFG9810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG10 : QuarticChamberBDEFG10810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG11 : QuarticChamberBDEFG11810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG12 : QuarticChamberBDEFG12810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG13 : QuarticChamberBDEFG13810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG14 : QuarticChamberBDEFG14810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG15 : QuarticChamberBDEFG15810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG16 : QuarticChamberBDEFG16810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG17 : QuarticChamberBDEFG17810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG18 : QuarticChamberBDEFG18810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG19 : QuarticChamberBDEFG19810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG20 : QuarticChamberBDEFG20810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG21 : QuarticChamberBDEFG21810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG22 : QuarticChamberBDEFG22810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG23 : QuarticChamberBDEFG23810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG24 : QuarticChamberBDEFG24810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG25 : QuarticChamberBDEFG25810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG26 : QuarticChamberBDEFG26810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG27 : QuarticChamberBDEFG27810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG28 : QuarticChamberBDEFG28810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG29 : QuarticChamberBDEFG29810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG30 : QuarticChamberBDEFG30810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG31 : QuarticChamberBDEFG31810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG32 : QuarticChamberBDEFG32810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG33 : QuarticChamberBDEFG33810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG34 : QuarticChamberBDEFG34810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG35 : QuarticChamberBDEFG35810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG36 : QuarticChamberBDEFG36810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG37 : QuarticChamberBDEFG37810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG38 : QuarticChamberBDEFG38810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG39 : QuarticChamberBDEFG39810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG40 : QuarticChamberBDEFG40810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG41 : QuarticChamberBDEFG41810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG42 : QuarticChamberBDEFG42810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG43 : QuarticChamberBDEFG43810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG44 : QuarticChamberBDEFG44810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG45 : QuarticChamberBDEFG45810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG46 : QuarticChamberBDEFG46810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG47 : QuarticChamberBDEFG47810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG48 : QuarticChamberBDEFG48810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG49 : QuarticChamberBDEFG49810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG50 : QuarticChamberBDEFG50810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG51 : QuarticChamberBDEFG51810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG52 : QuarticChamberBDEFG52810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG53 : QuarticChamberBDEFG53810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cBDEFG54 : QuarticChamberBDEFG54810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG0 : QuarticChamberCDEFG0810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG1 : QuarticChamberCDEFG1810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG2 : QuarticChamberCDEFG2810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG3 : QuarticChamberCDEFG3810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG4 : QuarticChamberCDEFG4810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG5 : QuarticChamberCDEFG5810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG6 : QuarticChamberCDEFG6810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG7 : QuarticChamberCDEFG7810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG8 : QuarticChamberCDEFG8810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG9 : QuarticChamberCDEFG9810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG10 : QuarticChamberCDEFG10810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG11 : QuarticChamberCDEFG11810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG12 : QuarticChamberCDEFG12810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG13 : QuarticChamberCDEFG13810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG14 : QuarticChamberCDEFG14810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG15 : QuarticChamberCDEFG15810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG16 : QuarticChamberCDEFG16810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG17 : QuarticChamberCDEFG17810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG18 : QuarticChamberCDEFG18810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG19 : QuarticChamberCDEFG19810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG20 : QuarticChamberCDEFG20810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG21 : QuarticChamberCDEFG21810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG22 : QuarticChamberCDEFG22810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG23 : QuarticChamberCDEFG23810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG24 : QuarticChamberCDEFG24810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG25 : QuarticChamberCDEFG25810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG26 : QuarticChamberCDEFG26810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG27 : QuarticChamberCDEFG27810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG28 : QuarticChamberCDEFG28810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG29 : QuarticChamberCDEFG29810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG30 : QuarticChamberCDEFG30810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG31 : QuarticChamberCDEFG31810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG32 : QuarticChamberCDEFG32810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG33 : QuarticChamberCDEFG33810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG34 : QuarticChamberCDEFG34810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG35 : QuarticChamberCDEFG35810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG36 : QuarticChamberCDEFG36810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG37 : QuarticChamberCDEFG37810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG38 : QuarticChamberCDEFG38810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG39 : QuarticChamberCDEFG39810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG40 : QuarticChamberCDEFG40810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG41 : QuarticChamberCDEFG41810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG42 : QuarticChamberCDEFG42810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG43 : QuarticChamberCDEFG43810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG44 : QuarticChamberCDEFG44810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG45 : QuarticChamberCDEFG45810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG46 : QuarticChamberCDEFG46810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG47 : QuarticChamberCDEFG47810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG48 : QuarticChamberCDEFG48810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG49 : QuarticChamberCDEFG49810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG50 : QuarticChamberCDEFG50810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG51 : QuarticChamberCDEFG51810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG52 : QuarticChamberCDEFG52810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG53 : QuarticChamberCDEFG53810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G
  | cCDEFG54 : QuarticChamberCDEFG54810 A B C D E F G →
      QuarticChamberSupportSize5810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The 135 cost-argmin chambers with |S| = 6. -/
inductive QuarticChamberSupportSize6810 (A B C D E F G : k[X]) : Prop
  | cBCDEFG0 : QuarticChamberBCDEFG0810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG1 : QuarticChamberBCDEFG1810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG2 : QuarticChamberBCDEFG2810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG3 : QuarticChamberBCDEFG3810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG4 : QuarticChamberBCDEFG4810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG5 : QuarticChamberBCDEFG5810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG6 : QuarticChamberBCDEFG6810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG7 : QuarticChamberBCDEFG7810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG8 : QuarticChamberBCDEFG8810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG9 : QuarticChamberBCDEFG9810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG10 : QuarticChamberBCDEFG10810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG11 : QuarticChamberBCDEFG11810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG12 : QuarticChamberBCDEFG12810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG13 : QuarticChamberBCDEFG13810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG14 : QuarticChamberBCDEFG14810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG15 : QuarticChamberBCDEFG15810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG16 : QuarticChamberBCDEFG16810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG17 : QuarticChamberBCDEFG17810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG18 : QuarticChamberBCDEFG18810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG19 : QuarticChamberBCDEFG19810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG20 : QuarticChamberBCDEFG20810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG21 : QuarticChamberBCDEFG21810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG22 : QuarticChamberBCDEFG22810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG23 : QuarticChamberBCDEFG23810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG24 : QuarticChamberBCDEFG24810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG25 : QuarticChamberBCDEFG25810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG26 : QuarticChamberBCDEFG26810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG27 : QuarticChamberBCDEFG27810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG28 : QuarticChamberBCDEFG28810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG29 : QuarticChamberBCDEFG29810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG30 : QuarticChamberBCDEFG30810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG31 : QuarticChamberBCDEFG31810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG32 : QuarticChamberBCDEFG32810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG33 : QuarticChamberBCDEFG33810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG34 : QuarticChamberBCDEFG34810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG35 : QuarticChamberBCDEFG35810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG36 : QuarticChamberBCDEFG36810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG37 : QuarticChamberBCDEFG37810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG38 : QuarticChamberBCDEFG38810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG39 : QuarticChamberBCDEFG39810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG40 : QuarticChamberBCDEFG40810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG41 : QuarticChamberBCDEFG41810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG42 : QuarticChamberBCDEFG42810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG43 : QuarticChamberBCDEFG43810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG44 : QuarticChamberBCDEFG44810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG45 : QuarticChamberBCDEFG45810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG46 : QuarticChamberBCDEFG46810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG47 : QuarticChamberBCDEFG47810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG48 : QuarticChamberBCDEFG48810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG49 : QuarticChamberBCDEFG49810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG50 : QuarticChamberBCDEFG50810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG51 : QuarticChamberBCDEFG51810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG52 : QuarticChamberBCDEFG52810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG53 : QuarticChamberBCDEFG53810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG54 : QuarticChamberBCDEFG54810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG55 : QuarticChamberBCDEFG55810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG56 : QuarticChamberBCDEFG56810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG57 : QuarticChamberBCDEFG57810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG58 : QuarticChamberBCDEFG58810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG59 : QuarticChamberBCDEFG59810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG60 : QuarticChamberBCDEFG60810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG61 : QuarticChamberBCDEFG61810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG62 : QuarticChamberBCDEFG62810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG63 : QuarticChamberBCDEFG63810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG64 : QuarticChamberBCDEFG64810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG65 : QuarticChamberBCDEFG65810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG66 : QuarticChamberBCDEFG66810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG67 : QuarticChamberBCDEFG67810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG68 : QuarticChamberBCDEFG68810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG69 : QuarticChamberBCDEFG69810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG70 : QuarticChamberBCDEFG70810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG71 : QuarticChamberBCDEFG71810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG72 : QuarticChamberBCDEFG72810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG73 : QuarticChamberBCDEFG73810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG74 : QuarticChamberBCDEFG74810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG75 : QuarticChamberBCDEFG75810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG76 : QuarticChamberBCDEFG76810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG77 : QuarticChamberBCDEFG77810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG78 : QuarticChamberBCDEFG78810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG79 : QuarticChamberBCDEFG79810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG80 : QuarticChamberBCDEFG80810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG81 : QuarticChamberBCDEFG81810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG82 : QuarticChamberBCDEFG82810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG83 : QuarticChamberBCDEFG83810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG84 : QuarticChamberBCDEFG84810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG85 : QuarticChamberBCDEFG85810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG86 : QuarticChamberBCDEFG86810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG87 : QuarticChamberBCDEFG87810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG88 : QuarticChamberBCDEFG88810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG89 : QuarticChamberBCDEFG89810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG90 : QuarticChamberBCDEFG90810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG91 : QuarticChamberBCDEFG91810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG92 : QuarticChamberBCDEFG92810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG93 : QuarticChamberBCDEFG93810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG94 : QuarticChamberBCDEFG94810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG95 : QuarticChamberBCDEFG95810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG96 : QuarticChamberBCDEFG96810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG97 : QuarticChamberBCDEFG97810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG98 : QuarticChamberBCDEFG98810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG99 : QuarticChamberBCDEFG99810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG100 : QuarticChamberBCDEFG100810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG101 : QuarticChamberBCDEFG101810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG102 : QuarticChamberBCDEFG102810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG103 : QuarticChamberBCDEFG103810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG104 : QuarticChamberBCDEFG104810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG105 : QuarticChamberBCDEFG105810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG106 : QuarticChamberBCDEFG106810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG107 : QuarticChamberBCDEFG107810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG108 : QuarticChamberBCDEFG108810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG109 : QuarticChamberBCDEFG109810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG110 : QuarticChamberBCDEFG110810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG111 : QuarticChamberBCDEFG111810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG112 : QuarticChamberBCDEFG112810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG113 : QuarticChamberBCDEFG113810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG114 : QuarticChamberBCDEFG114810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG115 : QuarticChamberBCDEFG115810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG116 : QuarticChamberBCDEFG116810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG117 : QuarticChamberBCDEFG117810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG118 : QuarticChamberBCDEFG118810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG119 : QuarticChamberBCDEFG119810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG120 : QuarticChamberBCDEFG120810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG121 : QuarticChamberBCDEFG121810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG122 : QuarticChamberBCDEFG122810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG123 : QuarticChamberBCDEFG123810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG124 : QuarticChamberBCDEFG124810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG125 : QuarticChamberBCDEFG125810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG126 : QuarticChamberBCDEFG126810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG127 : QuarticChamberBCDEFG127810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG128 : QuarticChamberBCDEFG128810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG129 : QuarticChamberBCDEFG129810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG130 : QuarticChamberBCDEFG130810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG131 : QuarticChamberBCDEFG131810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG132 : QuarticChamberBCDEFG132810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG133 : QuarticChamberBCDEFG133810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G
  | cBCDEFG134 : QuarticChamberBCDEFG134810 A B C D E F G →
      QuarticChamberSupportSize6810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The full cost-argmin taxonomy of cone `A`: 1115 chambers. -/
inductive QuarticChamberSupport810 (A B C D E F G : k[X]) : Prop
  | size1 : QuarticChamberSupportSize1810 A B C D E F G →
      QuarticChamberSupport810 A B C D E F G
  | size2 : QuarticChamberSupportSize2810 A B C D E F G →
      QuarticChamberSupport810 A B C D E F G
  | size3 : QuarticChamberSupportSize3810 A B C D E F G →
      QuarticChamberSupport810 A B C D E F G
  | size4 : QuarticChamberSupportSize4810 A B C D E F G →
      QuarticChamberSupport810 A B C D E F G
  | size5 : QuarticChamberSupportSize5810 A B C D E F G →
      QuarticChamberSupport810 A B C D E F G
  | size6 : QuarticChamberSupportSize6810 A B C D E F G →
      QuarticChamberSupport810 A B C D E F G


end Max11DegreeRoutes
