import Grok810ScaleZeroQuarticChamberDefs1Scratch

/-! # Cost-argmin chamber definitions (2/4), `(8,10)` scale zero

The 371 chambers whose live-letter set `S` has |S| ∈ {4}, machine-generated from
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

/-- Cost-argmin chamber `BCDE` / `BBB` (leaf BCDE#3.0). -/
def QuarticChamberBCDE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDE` / `BBB·BBC·BCC·CCC` (leaf BCDE#3.0). -/
def QuarticChamberBCDE1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCDE` / `CCC` (leaf BCDE#10.0). -/
def QuarticChamberBCDE2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 6 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCDE` / `DD` (leaf BCDE#0.0). -/
def QuarticChamberBCDE3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
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

/-- Cost-argmin chamber `BCDE` / `DD·BBB` (leaf BCDE#0.0). -/
def QuarticChamberBCDE4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDE` / `DD·BBB·BBC·BCC·CCC` (leaf BCDE#0.0). -/
def QuarticChamberBCDE5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDE` / `DD·CCC` (leaf BCDE#0.0). -/
def QuarticChamberBCDE6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDE` / `DD·DE·EE` (leaf BCDE#0.0). -/
def QuarticChamberBCDE7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
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

/-- Cost-argmin chamber `BCDE` / `DD·DE·EE·BBB` (leaf BCDE#0.0). -/
def QuarticChamberBCDE8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDE` / `DD·DE·EE·BBB·BBC·BCC·CCC` (leaf BCDE#0.0). -/
def QuarticChamberBCDE9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDE` / `DD·DE·EE·CCC` (leaf BCDE#0.0). -/
def QuarticChamberBCDE10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDE` / `EE` (leaf BCDE#2.0). -/
def QuarticChamberBCDE11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
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

/-- Cost-argmin chamber `BCDE` / `EE·BBB` (leaf BCDE#2.0). -/
def QuarticChamberBCDE12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDE` / `EE·BBB·BBC·BCC·CCC` (leaf BCDE#2.0). -/
def QuarticChamberBCDE13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree ∧
    4 * E.natDegree = A.natDegree + 2 * B.natDegree + 4 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDE` / `EE·CCC` (leaf BCDE#2.0). -/
def QuarticChamberBCDE14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    B.natDegree + C.natDegree + D.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCDF` / `BBB` (leaf BCDF#5.0). -/
def QuarticChamberBCDF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCDF` / `BBB·BBC·BCC·CCC` (leaf BCDF#5.0). -/
def QuarticChamberBCDF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCDF` / `BF` (leaf BCDF#0.0). -/
def QuarticChamberBCDF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·BBB` (leaf BCDF#0.0). -/
def QuarticChamberBCDF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·CF` (leaf BCDF#0.0). -/
def QuarticChamberBCDF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCDF#0.0). -/
def QuarticChamberBCDF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·CF·DD` (leaf BCDF#0.0). -/
def QuarticChamberBCDF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·CF·DD·BBB·BBC·BCC·CCC` (leaf BCDF#0.0). -/
def QuarticChamberBCDF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·CF·DD·DF·FF` (leaf BCDF#0.0). -/
def QuarticChamberBCDF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·CF·FF` (leaf BCDF#0.0). -/
def QuarticChamberBCDF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·DD` (leaf BCDF#0.0). -/
def QuarticChamberBCDF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·DD·BBB` (leaf BCDF#0.0). -/
def QuarticChamberBCDF11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·DD·DF·FF` (leaf BCDF#0.0). -/
def QuarticChamberBCDF12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `BF·FF` (leaf BCDF#0.0). -/
def QuarticChamberBCDF13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCDF` / `CCC` (leaf BCDF#10.0). -/
def QuarticChamberBCDF14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    D.natDegree + F.natDegree < 3 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `BCDF` / `CF` (leaf BCDF#1.0). -/
def QuarticChamberBCDF15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDF` / `CF·CCC` (leaf BCDF#1.0). -/
def QuarticChamberBCDF16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDF` / `CF·DD` (leaf BCDF#1.0). -/
def QuarticChamberBCDF17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDF` / `CF·DD·CCC` (leaf BCDF#1.0). -/
def QuarticChamberBCDF18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDF` / `CF·DD·DF·FF` (leaf BCDF#1.0). -/
def QuarticChamberBCDF19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDF` / `CF·FF` (leaf BCDF#1.0). -/
def QuarticChamberBCDF20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BCDF` / `DD` (leaf BCDF#2.0). -/
def QuarticChamberBCDF21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDF` / `DD·BBB` (leaf BCDF#2.0). -/
def QuarticChamberBCDF22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDF` / `DD·BBB·BBC·BCC·CCC` (leaf BCDF#2.0). -/
def QuarticChamberBCDF23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDF` / `DD·CCC` (leaf BCDF#2.0). -/
def QuarticChamberBCDF24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDF` / `DD·DF·FF` (leaf BCDF#2.0). -/
def QuarticChamberBCDF25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDF` / `FF` (leaf BCDF#4.0). -/
def QuarticChamberBCDF26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BCDG` / `BBB` (leaf BCDG#5.0). -/
def QuarticChamberBCDG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCDG` / `BBB·BBC·BCC·CCC` (leaf BCDG#5.0). -/
def QuarticChamberBCDG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCDG` / `BG` (leaf BCDG#0.0). -/
def QuarticChamberBCDG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·BBB` (leaf BCDG#0.0). -/
def QuarticChamberBCDG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·CG` (leaf BCDG#0.0). -/
def QuarticChamberBCDG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCDG#0.0). -/
def QuarticChamberBCDG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·CG·DD` (leaf BCDG#0.0). -/
def QuarticChamberBCDG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·CG·DD·BBB·BBC·BCC·CCC` (leaf BCDG#0.0). -/
def QuarticChamberBCDG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·CG·DD·DG·GG` (leaf BCDG#0.0). -/
def QuarticChamberBCDG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·CG·GG` (leaf BCDG#0.0). -/
def QuarticChamberBCDG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·DD` (leaf BCDG#0.0). -/
def QuarticChamberBCDG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·DD·BBB` (leaf BCDG#0.0). -/
def QuarticChamberBCDG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·DD·DG·GG` (leaf BCDG#0.0). -/
def QuarticChamberBCDG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `BG·GG` (leaf BCDG#0.0). -/
def QuarticChamberBCDG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree

/-- Cost-argmin chamber `BCDG` / `CCC` (leaf BCDG#10.0). -/
def QuarticChamberBCDG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `BCDG` / `CG` (leaf BCDG#1.0). -/
def QuarticChamberBCDG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDG` / `CG·CCC` (leaf BCDG#1.0). -/
def QuarticChamberBCDG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDG` / `CG·DD` (leaf BCDG#1.0). -/
def QuarticChamberBCDG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDG` / `CG·DD·CCC` (leaf BCDG#1.0). -/
def QuarticChamberBCDG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDG` / `CG·DD·DG·GG` (leaf BCDG#1.0). -/
def QuarticChamberBCDG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDG` / `CG·GG` (leaf BCDG#1.0). -/
def QuarticChamberBCDG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCDG` / `DD` (leaf BCDG#2.0). -/
def QuarticChamberBCDG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDG` / `DD·BBB` (leaf BCDG#2.0). -/
def QuarticChamberBCDG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDG` / `DD·BBB·BBC·BCC·CCC` (leaf BCDG#2.0). -/
def QuarticChamberBCDG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDG` / `DD·CCC` (leaf BCDG#2.0). -/
def QuarticChamberBCDG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDG` / `DD·DG·GG` (leaf BCDG#2.0). -/
def QuarticChamberBCDG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCDG` / `GG` (leaf BCDG#4.0). -/
def QuarticChamberBCDG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `BCEF` / `BBB` (leaf BCEF#5.0). -/
def QuarticChamberBCEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCEF` / `BBB·BBC·BCC·CCC` (leaf BCEF#5.0). -/
def QuarticChamberBCEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCEF` / `BF` (leaf BCEF#0.0). -/
def QuarticChamberBCEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·BBB` (leaf BCEF#0.0). -/
def QuarticChamberBCEF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·CF` (leaf BCEF#0.0). -/
def QuarticChamberBCEF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCEF#0.0). -/
def QuarticChamberBCEF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·CF·EE` (leaf BCEF#0.0). -/
def QuarticChamberBCEF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·CF·EE·BBB·BBC·BCC·CCC` (leaf BCEF#0.0). -/
def QuarticChamberBCEF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·CF·EE·EF·FF` (leaf BCEF#0.0). -/
def QuarticChamberBCEF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·CF·FF` (leaf BCEF#0.0). -/
def QuarticChamberBCEF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·EE` (leaf BCEF#0.0). -/
def QuarticChamberBCEF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·EE·BBB` (leaf BCEF#0.0). -/
def QuarticChamberBCEF11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·EE·EF·FF` (leaf BCEF#0.0). -/
def QuarticChamberBCEF12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `BF·FF` (leaf BCEF#0.0). -/
def QuarticChamberBCEF13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCEF` / `CCC` (leaf BCEF#10.0). -/
def QuarticChamberBCEF14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCEF` / `CF` (leaf BCEF#1.0). -/
def QuarticChamberBCEF15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEF` / `CF·CCC` (leaf BCEF#1.0). -/
def QuarticChamberBCEF16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEF` / `CF·EE` (leaf BCEF#1.0). -/
def QuarticChamberBCEF17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEF` / `CF·EE·CCC` (leaf BCEF#1.0). -/
def QuarticChamberBCEF18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEF` / `CF·EE·EF·FF` (leaf BCEF#1.0). -/
def QuarticChamberBCEF19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEF` / `CF·FF` (leaf BCEF#1.0). -/
def QuarticChamberBCEF20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCEF` / `EE` (leaf BCEF#2.0). -/
def QuarticChamberBCEF21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEF` / `EE·BBB` (leaf BCEF#2.0). -/
def QuarticChamberBCEF22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEF` / `EE·BBB·BBC·BCC·CCC` (leaf BCEF#2.0). -/
def QuarticChamberBCEF23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree ∧
    4 * E.natDegree = A.natDegree + 2 * B.natDegree + 4 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEF` / `EE·CCC` (leaf BCEF#2.0). -/
def QuarticChamberBCEF24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEF` / `EE·EF·FF` (leaf BCEF#2.0). -/
def QuarticChamberBCEF25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEF` / `FF` (leaf BCEF#4.0). -/
def QuarticChamberBCEF26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BCEG` / `BBB` (leaf BCEG#5.0). -/
def QuarticChamberBCEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCEG` / `BBB·BBC·BCC·CCC` (leaf BCEG#5.0). -/
def QuarticChamberBCEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCEG` / `BG` (leaf BCEG#0.0). -/
def QuarticChamberBCEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·BBB` (leaf BCEG#0.0). -/
def QuarticChamberBCEG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·CG` (leaf BCEG#0.0). -/
def QuarticChamberBCEG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCEG#0.0). -/
def QuarticChamberBCEG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·CG·EE` (leaf BCEG#0.0). -/
def QuarticChamberBCEG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·CG·EE·BBB·BBC·BCC·CCC` (leaf BCEG#0.0). -/
def QuarticChamberBCEG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·CG·EE·EG·GG` (leaf BCEG#0.0). -/
def QuarticChamberBCEG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·CG·GG` (leaf BCEG#0.0). -/
def QuarticChamberBCEG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·EE` (leaf BCEG#0.0). -/
def QuarticChamberBCEG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·EE·BBB` (leaf BCEG#0.0). -/
def QuarticChamberBCEG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·EE·EG·GG` (leaf BCEG#0.0). -/
def QuarticChamberBCEG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `BG·GG` (leaf BCEG#0.0). -/
def QuarticChamberBCEG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCEG` / `CCC` (leaf BCEG#10.0). -/
def QuarticChamberBCEG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCEG` / `CG` (leaf BCEG#1.0). -/
def QuarticChamberBCEG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEG` / `CG·CCC` (leaf BCEG#1.0). -/
def QuarticChamberBCEG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEG` / `CG·EE` (leaf BCEG#1.0). -/
def QuarticChamberBCEG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEG` / `CG·EE·CCC` (leaf BCEG#1.0). -/
def QuarticChamberBCEG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEG` / `CG·EE·EG·GG` (leaf BCEG#1.0). -/
def QuarticChamberBCEG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEG` / `CG·GG` (leaf BCEG#1.0). -/
def QuarticChamberBCEG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + E.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `BCEG` / `EE` (leaf BCEG#2.0). -/
def QuarticChamberBCEG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEG` / `EE·BBB` (leaf BCEG#2.0). -/
def QuarticChamberBCEG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEG` / `EE·BBB·BBC·BCC·CCC` (leaf BCEG#2.0). -/
def QuarticChamberBCEG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree ∧
    4 * E.natDegree = A.natDegree + 2 * B.natDegree + 4 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEG` / `EE·CCC` (leaf BCEG#2.0). -/
def QuarticChamberBCEG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEG` / `EE·EG·GG` (leaf BCEG#2.0). -/
def QuarticChamberBCEG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCEG` / `GG` (leaf BCEG#4.0). -/
def QuarticChamberBCEG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + E.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * C.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BCFG` / `BBB` (leaf BCFG#7.0). -/
def QuarticChamberBCFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BCFG` / `BBB·BBC·BCC·CCC` (leaf BCFG#7.0). -/
def QuarticChamberBCFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
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
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCFG` / `BF` (leaf BCFG#0.0). -/
def QuarticChamberBCFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·BBB` (leaf BCFG#0.0). -/
def QuarticChamberBCFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·BG` (leaf BCFG#0.0). -/
def QuarticChamberBCFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·BG·BBB` (leaf BCFG#0.0). -/
def QuarticChamberBCFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·BG·CF·CG` (leaf BCFG#0.0). -/
def QuarticChamberBCFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (leaf BCFG#0.0). -/
def QuarticChamberBCFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
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
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·BG·CF·CG·FF·FG·GG` (leaf BCFG#0.0). -/
def QuarticChamberBCFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·BG·FF·FG·GG` (leaf BCFG#0.0). -/
def QuarticChamberBCFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·CF` (leaf BCFG#0.0). -/
def QuarticChamberBCFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCFG#0.0). -/
def QuarticChamberBCFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
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
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·CF·FF` (leaf BCFG#0.0). -/
def QuarticChamberBCFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BF·FF` (leaf BCFG#0.0). -/
def QuarticChamberBCFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCFG` / `BG` (leaf BCFG#1.0). -/
def QuarticChamberBCFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCFG` / `BG·BBB` (leaf BCFG#1.0). -/
def QuarticChamberBCFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCFG` / `BG·CG` (leaf BCFG#1.0). -/
def QuarticChamberBCFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCFG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCFG#1.0). -/
def QuarticChamberBCFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
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
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BCFG` / `BG·CG·GG` (leaf BCFG#1.0). -/
def QuarticChamberBCFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCFG` / `BG·GG` (leaf BCFG#1.0). -/
def QuarticChamberBCFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCFG` / `CCC` (leaf BCFG#10.0). -/
def QuarticChamberBCFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree

/-- Cost-argmin chamber `BCFG` / `CF` (leaf BCFG#2.0). -/
def QuarticChamberBCFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCFG` / `CF·CCC` (leaf BCFG#2.0). -/
def QuarticChamberBCFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree

/-- Cost-argmin chamber `BCFG` / `CF·CG` (leaf BCFG#2.0). -/
def QuarticChamberBCFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCFG` / `CF·CG·CCC` (leaf BCFG#2.0). -/
def QuarticChamberBCFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree

/-- Cost-argmin chamber `BCFG` / `CF·CG·FF·FG·GG` (leaf BCFG#2.0). -/
def QuarticChamberBCFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCFG` / `CF·FF` (leaf BCFG#2.0). -/
def QuarticChamberBCFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCFG` / `CG` (leaf BCFG#3.0). -/
def QuarticChamberBCFG27810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `BCFG` / `CG·CCC` (leaf BCFG#3.0). -/
def QuarticChamberBCFG28810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BCFG` / `CG·GG` (leaf BCFG#3.0). -/
def QuarticChamberBCFG29810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `BCFG` / `FF` (leaf BCFG#4.0). -/
def QuarticChamberBCFG30810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BCFG` / `FF·FG·GG` (leaf BCFG#4.0). -/
def QuarticChamberBCFG31810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BCFG` / `GG` (leaf BCFG#6.0). -/
def QuarticChamberBCFG32810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BDEF` / `BBB` (leaf BDEF#7.0). -/
def QuarticChamberBDEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BDEF` / `BF` (leaf BDEF#0.0). -/
def QuarticChamberBDEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·BBB` (leaf BDEF#0.0). -/
def QuarticChamberBDEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·DD` (leaf BDEF#0.0). -/
def QuarticChamberBDEF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·DD·BBB` (leaf BDEF#0.0). -/
def QuarticChamberBDEF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·DD·DE·DF·EE·EF·FF` (leaf BDEF#0.0). -/
def QuarticChamberBDEF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·DD·DE·EE` (leaf BDEF#0.0). -/
def QuarticChamberBDEF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·DD·DE·EE·BBB` (leaf BDEF#0.0). -/
def QuarticChamberBDEF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·DD·DF·FF` (leaf BDEF#0.0). -/
def QuarticChamberBDEF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·EE` (leaf BDEF#0.0). -/
def QuarticChamberBDEF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·EE·BBB` (leaf BDEF#0.0). -/
def QuarticChamberBDEF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·EE·EF·FF` (leaf BDEF#0.0). -/
def QuarticChamberBDEF11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `BF·FF` (leaf BDEF#0.0). -/
def QuarticChamberBDEF12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BDEF` / `DD` (leaf BDEF#1.0). -/
def QuarticChamberBDEF13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEF` / `DD·BBB` (leaf BDEF#1.0). -/
def QuarticChamberBDEF14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEF` / `DD·DE·DF·EE·EF·FF` (leaf BDEF#1.0). -/
def QuarticChamberBDEF15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEF` / `DD·DE·EE` (leaf BDEF#1.0). -/
def QuarticChamberBDEF16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEF` / `DD·DE·EE·BBB` (leaf BDEF#1.0). -/
def QuarticChamberBDEF17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEF` / `DD·DF·FF` (leaf BDEF#1.0). -/
def QuarticChamberBDEF18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEF` / `EE` (leaf BDEF#4.0). -/
def QuarticChamberBDEF19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEF` / `EE·BBB` (leaf BDEF#4.0). -/
def QuarticChamberBDEF20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEF` / `EE·EF·FF` (leaf BDEF#4.0). -/
def QuarticChamberBDEF21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEF` / `FF` (leaf BDEF#6.0). -/
def QuarticChamberBDEF22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BDEG` / `BBB` (leaf BDEG#7.0). -/
def QuarticChamberBDEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BDEG` / `BG` (leaf BDEG#0.0). -/
def QuarticChamberBDEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·BBB` (leaf BDEG#0.0). -/
def QuarticChamberBDEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·DD` (leaf BDEG#0.0). -/
def QuarticChamberBDEG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·DD·BBB` (leaf BDEG#0.0). -/
def QuarticChamberBDEG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·DD·DE·DG·EE·EG·GG` (leaf BDEG#0.0). -/
def QuarticChamberBDEG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·DD·DE·EE` (leaf BDEG#0.0). -/
def QuarticChamberBDEG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·DD·DE·EE·BBB` (leaf BDEG#0.0). -/
def QuarticChamberBDEG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·DD·DG·GG` (leaf BDEG#0.0). -/
def QuarticChamberBDEG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·EE` (leaf BDEG#0.0). -/
def QuarticChamberBDEG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·EE·BBB` (leaf BDEG#0.0). -/
def QuarticChamberBDEG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·EE·EG·GG` (leaf BDEG#0.0). -/
def QuarticChamberBDEG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `BG·GG` (leaf BDEG#0.0). -/
def QuarticChamberBDEG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BDEG` / `DD` (leaf BDEG#1.0). -/
def QuarticChamberBDEG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEG` / `DD·BBB` (leaf BDEG#1.0). -/
def QuarticChamberBDEG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEG` / `DD·DE·DG·EE·EG·GG` (leaf BDEG#1.0). -/
def QuarticChamberBDEG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEG` / `DD·DE·EE` (leaf BDEG#1.0). -/
def QuarticChamberBDEG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEG` / `DD·DE·EE·BBB` (leaf BDEG#1.0). -/
def QuarticChamberBDEG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEG` / `DD·DG·GG` (leaf BDEG#1.0). -/
def QuarticChamberBDEG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDEG` / `EE` (leaf BDEG#4.0). -/
def QuarticChamberBDEG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEG` / `EE·BBB` (leaf BDEG#4.0). -/
def QuarticChamberBDEG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEG` / `EE·EG·GG` (leaf BDEG#4.0). -/
def QuarticChamberBDEG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDEG` / `GG` (leaf BDEG#6.0). -/
def QuarticChamberBDEG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BDFG` / `BBB` (leaf BDFG#8.0). -/
def QuarticChamberBDFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree

/-- Cost-argmin chamber `BDFG` / `BF` (leaf BDFG#0.0). -/
def QuarticChamberBDFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·BBB` (leaf BDFG#0.0). -/
def QuarticChamberBDFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·BG` (leaf BDFG#0.0). -/
def QuarticChamberBDFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·BG·BBB` (leaf BDFG#0.0). -/
def QuarticChamberBDFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·BG·DD` (leaf BDFG#0.0). -/
def QuarticChamberBDFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·BG·DD·BBB` (leaf BDFG#0.0). -/
def QuarticChamberBDFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·BG·DD·DF·DG·FF·FG·GG` (leaf BDFG#0.0). -/
def QuarticChamberBDFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·BG·FF·FG·GG` (leaf BDFG#0.0). -/
def QuarticChamberBDFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·DD` (leaf BDFG#0.0). -/
def QuarticChamberBDFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·DD·BBB` (leaf BDFG#0.0). -/
def QuarticChamberBDFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·DD·DF·FF` (leaf BDFG#0.0). -/
def QuarticChamberBDFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BF·FF` (leaf BDFG#0.0). -/
def QuarticChamberBDFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `BG` (leaf BDFG#1.0). -/
def QuarticChamberBDFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDFG` / `BG·BBB` (leaf BDFG#1.0). -/
def QuarticChamberBDFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDFG` / `BG·DD` (leaf BDFG#1.0). -/
def QuarticChamberBDFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDFG` / `BG·DD·BBB` (leaf BDFG#1.0). -/
def QuarticChamberBDFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDFG` / `BG·DD·DG·GG` (leaf BDFG#1.0). -/
def QuarticChamberBDFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDFG` / `BG·GG` (leaf BDFG#1.0). -/
def QuarticChamberBDFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDFG` / `DD` (leaf BDFG#2.0). -/
def QuarticChamberBDFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDFG` / `DD·BBB` (leaf BDFG#2.0). -/
def QuarticChamberBDFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDFG` / `DD·DF·DG·FF·FG·GG` (leaf BDFG#2.0). -/
def QuarticChamberBDFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDFG` / `DD·DF·FF` (leaf BDFG#2.0). -/
def QuarticChamberBDFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDFG` / `DD·DG·GG` (leaf BDFG#2.0). -/
def QuarticChamberBDFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDFG` / `FF` (leaf BDFG#5.0). -/
def QuarticChamberBDFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `FF·FG·GG` (leaf BDFG#5.0). -/
def QuarticChamberBDFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BDFG` / `GG` (leaf BDFG#7.0). -/
def QuarticChamberBDFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `BEFG` / `BBB` (leaf BEFG#8.0). -/
def QuarticChamberBEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BEFG` / `BF` (leaf BEFG#0.0). -/
def QuarticChamberBEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·BBB` (leaf BEFG#0.0). -/
def QuarticChamberBEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·BG` (leaf BEFG#0.0). -/
def QuarticChamberBEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·BG·BBB` (leaf BEFG#0.0). -/
def QuarticChamberBEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·BG·EE` (leaf BEFG#0.0). -/
def QuarticChamberBEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·BG·EE·BBB` (leaf BEFG#0.0). -/
def QuarticChamberBEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·BG·EE·EF·EG·FF·FG·GG` (leaf BEFG#0.0). -/
def QuarticChamberBEFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·BG·FF·FG·GG` (leaf BEFG#0.0). -/
def QuarticChamberBEFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·EE` (leaf BEFG#0.0). -/
def QuarticChamberBEFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·EE·BBB` (leaf BEFG#0.0). -/
def QuarticChamberBEFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·EE·EF·FF` (leaf BEFG#0.0). -/
def QuarticChamberBEFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BF·FF` (leaf BEFG#0.0). -/
def QuarticChamberBEFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEFG` / `BG` (leaf BEFG#1.0). -/
def QuarticChamberBEFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEFG` / `BG·BBB` (leaf BEFG#1.0). -/
def QuarticChamberBEFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEFG` / `BG·EE` (leaf BEFG#1.0). -/
def QuarticChamberBEFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEFG` / `BG·EE·BBB` (leaf BEFG#1.0). -/
def QuarticChamberBEFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEFG` / `BG·EE·EG·GG` (leaf BEFG#1.0). -/
def QuarticChamberBEFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEFG` / `BG·GG` (leaf BEFG#1.0). -/
def QuarticChamberBEFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEFG` / `EE` (leaf BEFG#2.0). -/
def QuarticChamberBEFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEFG` / `EE·BBB` (leaf BEFG#2.0). -/
def QuarticChamberBEFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEFG` / `EE·EF·EG·FF·FG·GG` (leaf BEFG#2.0). -/
def QuarticChamberBEFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
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
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEFG` / `EE·EF·FF` (leaf BEFG#2.0). -/
def QuarticChamberBEFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEFG` / `EE·EG·GG` (leaf BEFG#2.0). -/
def QuarticChamberBEFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEFG` / `FF` (leaf BEFG#5.0). -/
def QuarticChamberBEFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BEFG` / `FF·FG·GG` (leaf BEFG#5.0). -/
def QuarticChamberBEFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BEFG` / `GG` (leaf BEFG#7.0). -/
def QuarticChamberBEFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * E.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `CDEF` / `CCC` (leaf CDEF#7.0). -/
def QuarticChamberCDEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 6 * C.natDegree ∧
    D.natDegree + F.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CDEF` / `CF` (leaf CDEF#0.0). -/
def QuarticChamberCDEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·CCC` (leaf CDEF#0.0). -/
def QuarticChamberCDEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·DD` (leaf CDEF#0.0). -/
def QuarticChamberCDEF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·DD·CCC` (leaf CDEF#0.0). -/
def QuarticChamberCDEF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·DD·DE·DF·EE·EF·FF` (leaf CDEF#0.0). -/
def QuarticChamberCDEF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·DD·DE·EE` (leaf CDEF#0.0). -/
def QuarticChamberCDEF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·DD·DE·EE·CCC` (leaf CDEF#0.0). -/
def QuarticChamberCDEF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·DD·DF·FF` (leaf CDEF#0.0). -/
def QuarticChamberCDEF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·EE` (leaf CDEF#0.0). -/
def QuarticChamberCDEF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·EE·CCC` (leaf CDEF#0.0). -/
def QuarticChamberCDEF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·EE·EF·FF` (leaf CDEF#0.0). -/
def QuarticChamberCDEF11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `CF·FF` (leaf CDEF#0.0). -/
def QuarticChamberCDEF12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CDEF` / `DD` (leaf CDEF#1.0). -/
def QuarticChamberCDEF13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEF` / `DD·CCC` (leaf CDEF#1.0). -/
def QuarticChamberCDEF14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEF` / `DD·DE·DF·EE·EF·FF` (leaf CDEF#1.0). -/
def QuarticChamberCDEF15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEF` / `DD·DE·EE` (leaf CDEF#1.0). -/
def QuarticChamberCDEF16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEF` / `DD·DE·EE·CCC` (leaf CDEF#1.0). -/
def QuarticChamberCDEF17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEF` / `DD·DF·FF` (leaf CDEF#1.0). -/
def QuarticChamberCDEF18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEF` / `EE` (leaf CDEF#4.0). -/
def QuarticChamberCDEF19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEF` / `EE·CCC` (leaf CDEF#4.0). -/
def QuarticChamberCDEF20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEF` / `EE·EF·FF` (leaf CDEF#4.0). -/
def QuarticChamberCDEF21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEF` / `FF` (leaf CDEF#6.0). -/
def QuarticChamberCDEF22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CDEG` / `CCC` (leaf CDEG#7.0). -/
def QuarticChamberCDEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 6 * C.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CDEG` / `CG` (leaf CDEG#0.0). -/
def QuarticChamberCDEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·CCC` (leaf CDEG#0.0). -/
def QuarticChamberCDEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·DD` (leaf CDEG#0.0). -/
def QuarticChamberCDEG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·DD·CCC` (leaf CDEG#0.0). -/
def QuarticChamberCDEG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·DD·DE·DG·EE·EG·GG` (leaf CDEG#0.0). -/
def QuarticChamberCDEG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·DD·DE·EE` (leaf CDEG#0.0). -/
def QuarticChamberCDEG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·DD·DE·EE·CCC` (leaf CDEG#0.0). -/
def QuarticChamberCDEG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree = A.natDegree + 2 * D.natDegree + 2 * E.natDegree ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·DD·DG·GG` (leaf CDEG#0.0). -/
def QuarticChamberCDEG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·EE` (leaf CDEG#0.0). -/
def QuarticChamberCDEG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·EE·CCC` (leaf CDEG#0.0). -/
def QuarticChamberCDEG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·EE·EG·GG` (leaf CDEG#0.0). -/
def QuarticChamberCDEG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `CG·GG` (leaf CDEG#0.0). -/
def QuarticChamberCDEG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CDEG` / `DD` (leaf CDEG#1.0). -/
def QuarticChamberCDEG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEG` / `DD·CCC` (leaf CDEG#1.0). -/
def QuarticChamberCDEG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEG` / `DD·DE·DG·EE·EG·GG` (leaf CDEG#1.0). -/
def QuarticChamberCDEG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEG` / `DD·DE·EE` (leaf CDEG#1.0). -/
def QuarticChamberCDEG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEG` / `DD·DE·EE·CCC` (leaf CDEG#1.0). -/
def QuarticChamberCDEG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEG` / `DD·DG·GG` (leaf CDEG#1.0). -/
def QuarticChamberCDEG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDEG` / `EE` (leaf CDEG#4.0). -/
def QuarticChamberCDEG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEG` / `EE·CCC` (leaf CDEG#4.0). -/
def QuarticChamberCDEG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEG` / `EE·EG·GG` (leaf CDEG#4.0). -/
def QuarticChamberCDEG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDEG` / `GG` (leaf CDEG#6.0). -/
def QuarticChamberCDEG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `CDFG` / `CCC` (leaf CDFG#8.0). -/
def QuarticChamberCDFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    D.natDegree + F.natDegree < 3 * C.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `CDFG` / `CF` (leaf CDFG#0.0). -/
def QuarticChamberCDFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·CCC` (leaf CDFG#0.0). -/
def QuarticChamberCDFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·CG` (leaf CDFG#0.0). -/
def QuarticChamberCDFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·CG·CCC` (leaf CDFG#0.0). -/
def QuarticChamberCDFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·CG·DD` (leaf CDFG#0.0). -/
def QuarticChamberCDFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·CG·DD·CCC` (leaf CDFG#0.0). -/
def QuarticChamberCDFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·CG·DD·DF·DG·FF·FG·GG` (leaf CDFG#0.0). -/
def QuarticChamberCDFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·CG·FF·FG·GG` (leaf CDFG#0.0). -/
def QuarticChamberCDFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·DD` (leaf CDFG#0.0). -/
def QuarticChamberCDFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·DD·CCC` (leaf CDFG#0.0). -/
def QuarticChamberCDFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·DD·DF·FF` (leaf CDFG#0.0). -/
def QuarticChamberCDFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CF·FF` (leaf CDFG#0.0). -/
def QuarticChamberCDFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDFG` / `CG` (leaf CDFG#1.0). -/
def QuarticChamberCDFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDFG` / `CG·CCC` (leaf CDFG#1.0). -/
def QuarticChamberCDFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDFG` / `CG·DD` (leaf CDFG#1.0). -/
def QuarticChamberCDFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDFG` / `CG·DD·CCC` (leaf CDFG#1.0). -/
def QuarticChamberCDFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDFG` / `CG·DD·DG·GG` (leaf CDFG#1.0). -/
def QuarticChamberCDFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDFG` / `CG·GG` (leaf CDFG#1.0). -/
def QuarticChamberCDFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    D.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDFG` / `DD` (leaf CDFG#2.0). -/
def QuarticChamberCDFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDFG` / `DD·CCC` (leaf CDFG#2.0). -/
def QuarticChamberCDFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDFG` / `DD·DF·DG·FF·FG·GG` (leaf CDFG#2.0). -/
def QuarticChamberCDFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDFG` / `DD·DF·FF` (leaf CDFG#2.0). -/
def QuarticChamberCDFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDFG` / `DD·DG·GG` (leaf CDFG#2.0). -/
def QuarticChamberCDFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDFG` / `FF` (leaf CDFG#5.0). -/
def QuarticChamberCDFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `CDFG` / `FF·FG·GG` (leaf CDFG#5.0). -/
def QuarticChamberCDFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `CDFG` / `GG` (leaf CDFG#7.0). -/
def QuarticChamberCDFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `CEFG` / `CCC` (leaf CEFG#8.0). -/
def QuarticChamberCEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 6 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CEFG` / `CF` (leaf CEFG#0.0). -/
def QuarticChamberCEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·CCC` (leaf CEFG#0.0). -/
def QuarticChamberCEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·CG` (leaf CEFG#0.0). -/
def QuarticChamberCEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·CG·CCC` (leaf CEFG#0.0). -/
def QuarticChamberCEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·CG·EE` (leaf CEFG#0.0). -/
def QuarticChamberCEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·CG·EE·CCC` (leaf CEFG#0.0). -/
def QuarticChamberCEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·CG·EE·EF·EG·FF·FG·GG` (leaf CEFG#0.0). -/
def QuarticChamberCEFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·CG·FF·FG·GG` (leaf CEFG#0.0). -/
def QuarticChamberCEFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·EE` (leaf CEFG#0.0). -/
def QuarticChamberCEFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·EE·CCC` (leaf CEFG#0.0). -/
def QuarticChamberCEFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·EE·EF·FF` (leaf CEFG#0.0). -/
def QuarticChamberCEFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CF·FF` (leaf CEFG#0.0). -/
def QuarticChamberCEFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `CG` (leaf CEFG#1.0). -/
def QuarticChamberCEFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEFG` / `CG·CCC` (leaf CEFG#1.0). -/
def QuarticChamberCEFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEFG` / `CG·EE` (leaf CEFG#1.0). -/
def QuarticChamberCEFG15810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEFG` / `CG·EE·CCC` (leaf CEFG#1.0). -/
def QuarticChamberCEFG16810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEFG` / `CG·EE·EG·GG` (leaf CEFG#1.0). -/
def QuarticChamberCEFG17810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEFG` / `CG·GG` (leaf CEFG#1.0). -/
def QuarticChamberCEFG18810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 2 * C.natDegree + 2 * G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEFG` / `EE` (leaf CEFG#2.0). -/
def QuarticChamberCEFG19810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEFG` / `EE·CCC` (leaf CEFG#2.0). -/
def QuarticChamberCEFG20810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEFG` / `EE·EF·EG·FF·FG·GG` (leaf CEFG#2.0). -/
def QuarticChamberCEFG21810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEFG` / `EE·EF·FF` (leaf CEFG#2.0). -/
def QuarticChamberCEFG22810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEFG` / `EE·EG·GG` (leaf CEFG#2.0). -/
def QuarticChamberCEFG23810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEFG` / `FF` (leaf CEFG#5.0). -/
def QuarticChamberCEFG24810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `FF·FG·GG` (leaf CEFG#5.0). -/
def QuarticChamberCEFG25810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CEFG` / `GG` (leaf CEFG#7.0). -/
def QuarticChamberCEFG26810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * E.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `DEFG` / `DD` (leaf DEFG#0.0). -/
def QuarticChamberDEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` (leaf DEFG#0.0). -/
def QuarticChamberDEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree

/-- Cost-argmin chamber `DEFG` / `DD·DE·DF·EE·EF·FF` (leaf DEFG#0.0). -/
def QuarticChamberDEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEFG` / `DD·DE·DG·EE·EG·GG` (leaf DEFG#0.0). -/
def QuarticChamberDEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree

/-- Cost-argmin chamber `DEFG` / `DD·DE·EE` (leaf DEFG#0.0). -/
def QuarticChamberDEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEFG` / `DD·DF·DG·FF·FG·GG` (leaf DEFG#0.0). -/
def QuarticChamberDEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEFG` / `DD·DF·FF` (leaf DEFG#0.0). -/
def QuarticChamberDEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEFG` / `DD·DG·GG` (leaf DEFG#0.0). -/
def QuarticChamberDEFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree

/-- Cost-argmin chamber `DEFG` / `EE` (leaf DEFG#4.0). -/
def QuarticChamberDEFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `DEFG` / `EE·EF·EG·FF·FG·GG` (leaf DEFG#4.0). -/
def QuarticChamberDEFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
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
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree

/-- Cost-argmin chamber `DEFG` / `EE·EF·FF` (leaf DEFG#4.0). -/
def QuarticChamberDEFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `DEFG` / `EE·EG·GG` (leaf DEFG#4.0). -/
def QuarticChamberDEFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree

/-- Cost-argmin chamber `DEFG` / `FF` (leaf DEFG#7.0). -/
def QuarticChamberDEFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `DEFG` / `FF·FG·GG` (leaf DEFG#7.0). -/
def QuarticChamberDEFG13810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `DEFG` / `GG` (leaf DEFG#9.0). -/
def QuarticChamberDEFG14810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * E.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree


end Max11DegreeRoutes
