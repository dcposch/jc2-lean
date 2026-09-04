import Grok810ScaleZeroQuarticSigmaLadderScratch

/-! # Cost-argmin chamber definitions (1/4), `(8,10)` scale zero

The 255 chambers whose live-letter set `S` has |S| ∈ {1, 2, 3}, machine-generated from
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

/-- Cost-argmin chamber `B` / `BBB` (leaf B#0.0). -/
def QuarticChamberB0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0

/-- Cost-argmin chamber `C` / `CCC` (leaf C#0.0). -/
def QuarticChamberC0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0

/-- Cost-argmin chamber `D` / `DD` (leaf D#0.0). -/
def QuarticChamberD0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0

/-- Cost-argmin chamber `E` / `EE` (leaf E#0.0). -/
def QuarticChamberE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0

/-- Cost-argmin chamber `F` / `FF` (leaf F#0.0). -/
def QuarticChamberF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0

/-- Cost-argmin chamber `G` / `GG` (leaf G#0.0). -/
def QuarticChamberG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0

/-- Cost-argmin chamber `BC` / `BBB` (leaf BC#0.0). -/
def QuarticChamberBC0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BC` / `BBB·BBC·BCC·CCC` (leaf BC#0.0). -/
def QuarticChamberBC1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree

/-- Cost-argmin chamber `BC` / `CCC` (leaf BC#3.0). -/
def QuarticChamberBC2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree

/-- Cost-argmin chamber `BD` / `BBB` (leaf BD#1.0). -/
def QuarticChamberBD0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree

/-- Cost-argmin chamber `BD` / `DD` (leaf BD#0.0). -/
def QuarticChamberBD1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BD` / `DD·BBB` (leaf BD#0.0). -/
def QuarticChamberBD2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BE` / `BBB` (leaf BE#1.0). -/
def QuarticChamberBE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BE` / `EE` (leaf BE#0.0). -/
def QuarticChamberBE1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BE` / `EE·BBB` (leaf BE#0.0). -/
def QuarticChamberBE2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BF` / `BBB` (leaf BF#2.0). -/
def QuarticChamberBF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BF` / `BF` (leaf BF#0.0). -/
def QuarticChamberBF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BF` / `BF·BBB` (leaf BF#0.0). -/
def QuarticChamberBF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree

/-- Cost-argmin chamber `BF` / `BF·FF` (leaf BF#0.0). -/
def QuarticChamberBF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BF` / `FF` (leaf BF#1.0). -/
def QuarticChamberBF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BG` / `BBB` (leaf BG#2.0). -/
def QuarticChamberBG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BG` / `BG` (leaf BG#0.0). -/
def QuarticChamberBG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree

/-- Cost-argmin chamber `BG` / `BG·BBB` (leaf BG#0.0). -/
def QuarticChamberBG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BG` / `BG·GG` (leaf BG#0.0). -/
def QuarticChamberBG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree

/-- Cost-argmin chamber `BG` / `GG` (leaf BG#1.0). -/
def QuarticChamberBG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `CD` / `CCC` (leaf CD#1.0). -/
def QuarticChamberCD0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `CD` / `DD` (leaf CD#0.0). -/
def QuarticChamberCD1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CD` / `DD·CCC` (leaf CD#0.0). -/
def QuarticChamberCD2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CE` / `CCC` (leaf CE#1.0). -/
def QuarticChamberCE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CE` / `EE` (leaf CE#0.0). -/
def QuarticChamberCE1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CE` / `EE·CCC` (leaf CE#0.0). -/
def QuarticChamberCE2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CF` / `CCC` (leaf CF#2.0). -/
def QuarticChamberCF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree

/-- Cost-argmin chamber `CF` / `CF` (leaf CF#0.0). -/
def QuarticChamberCF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CF` / `CF·CCC` (leaf CF#0.0). -/
def QuarticChamberCF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `CF` / `CF·FF` (leaf CF#0.0). -/
def QuarticChamberCF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CF` / `FF` (leaf CF#1.0). -/
def QuarticChamberCF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CG` / `CCC` (leaf CG#2.0). -/
def QuarticChamberCG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree

/-- Cost-argmin chamber `CG` / `CG` (leaf CG#0.0). -/
def QuarticChamberCG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `CG` / `CG·CCC` (leaf CG#0.0). -/
def QuarticChamberCG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree

/-- Cost-argmin chamber `CG` / `CG·GG` (leaf CG#0.0). -/
def QuarticChamberCG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `CG` / `GG` (leaf CG#1.0). -/
def QuarticChamberCG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `DE` / `DD` (leaf DE#0.0). -/
def QuarticChamberDE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DE` / `DD·DE·EE` (leaf DE#0.0). -/
def QuarticChamberDE1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree

/-- Cost-argmin chamber `DE` / `EE` (leaf DE#2.0). -/
def QuarticChamberDE2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree

/-- Cost-argmin chamber `DF` / `DD` (leaf DF#0.0). -/
def QuarticChamberDF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree

/-- Cost-argmin chamber `DF` / `DD·DF·FF` (leaf DF#0.0). -/
def QuarticChamberDF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree

/-- Cost-argmin chamber `DF` / `FF` (leaf DF#2.0). -/
def QuarticChamberDF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree

/-- Cost-argmin chamber `DG` / `DD` (leaf DG#0.0). -/
def QuarticChamberDG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DG` / `DD·DG·GG` (leaf DG#0.0). -/
def QuarticChamberDG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree

/-- Cost-argmin chamber `DG` / `GG` (leaf DG#2.0). -/
def QuarticChamberDG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `EF` / `EE` (leaf EF#0.0). -/
def QuarticChamberEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree

/-- Cost-argmin chamber `EF` / `EE·EF·FF` (leaf EF#0.0). -/
def QuarticChamberEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree

/-- Cost-argmin chamber `EF` / `FF` (leaf EF#2.0). -/
def QuarticChamberEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `EG` / `EE` (leaf EG#0.0). -/
def QuarticChamberEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `EG` / `EE·EG·GG` (leaf EG#0.0). -/
def QuarticChamberEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree

/-- Cost-argmin chamber `EG` / `GG` (leaf EG#2.0). -/
def QuarticChamberEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree

/-- Cost-argmin chamber `FG` / `FF` (leaf FG#0.0). -/
def QuarticChamberFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `FG` / `FF·FG·GG` (leaf FG#0.0). -/
def QuarticChamberFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree

/-- Cost-argmin chamber `FG` / `GG` (leaf FG#2.0). -/
def QuarticChamberFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BCD` / `BBB` (leaf BCD#1.0). -/
def QuarticChamberBCD0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCD` / `BBB·BBC·BCC·CCC` (leaf BCD#1.0). -/
def QuarticChamberBCD1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree + 3 * B.natDegree

/-- Cost-argmin chamber `BCD` / `CCC` (leaf BCD#6.0). -/
def QuarticChamberBCD2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 6 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    B.natDegree + D.natDegree < 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `BCD` / `DD` (leaf BCD#0.0). -/
def QuarticChamberBCD3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCD` / `DD·BBB` (leaf BCD#0.0). -/
def QuarticChamberBCD4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCD` / `DD·BBB·BBC·BCC·CCC` (leaf BCD#0.0). -/
def QuarticChamberBCD5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree = 2 * B.natDegree + C.natDegree ∧
    A.natDegree + 4 * D.natDegree = 2 * B.natDegree + 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCD` / `DD·CCC` (leaf BCD#0.0). -/
def QuarticChamberBCD6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + 4 * C.natDegree < A.natDegree + 4 * D.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BCE` / `BBB` (leaf BCE#1.0). -/
def QuarticChamberBCE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCE` / `BBB·BBC·BCC·CCC` (leaf BCE#1.0). -/
def QuarticChamberBCE1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    C.natDegree + E.natDegree < 2 * A.natDegree + 2 * B.natDegree ∧
    4 * C.natDegree + 2 * E.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCE` / `CCC` (leaf BCE#6.0). -/
def QuarticChamberBCE2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + E.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 4 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `BCE` / `EE` (leaf BCE#0.0). -/
def QuarticChamberBCE3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCE` / `EE·BBB` (leaf BCE#0.0). -/
def QuarticChamberBCE4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCE` / `EE·BBB·BBC·BCC·CCC` (leaf BCE#0.0). -/
def QuarticChamberBCE5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree ∧
    4 * E.natDegree = A.natDegree + 2 * B.natDegree + 4 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCE` / `EE·CCC` (leaf BCE#0.0). -/
def QuarticChamberBCE6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 2 * B.natDegree + C.natDegree < 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `BCF` / `BBB` (leaf BCF#3.0). -/
def QuarticChamberBCF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BCF` / `BBB·BBC·BCC·CCC` (leaf BCF#3.0). -/
def QuarticChamberBCF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    C.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCF` / `BF` (leaf BCF#0.0). -/
def QuarticChamberBCF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCF` / `BF·BBB` (leaf BCF#0.0). -/
def QuarticChamberBCF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCF` / `BF·CF` (leaf BCF#0.0). -/
def QuarticChamberBCF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCF` / `BF·CF·BBB·BBC·BCC·CCC` (leaf BCF#0.0). -/
def QuarticChamberBCF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree

/-- Cost-argmin chamber `BCF` / `BF·CF·FF` (leaf BCF#0.0). -/
def QuarticChamberBCF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCF` / `BF·FF` (leaf BCF#0.0). -/
def QuarticChamberBCF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * C.natDegree < A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BCF` / `CCC` (leaf BCF#6.0). -/
def QuarticChamberBCF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree

/-- Cost-argmin chamber `BCF` / `CF` (leaf BCF#1.0). -/
def QuarticChamberBCF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCF` / `CF·CCC` (leaf BCF#1.0). -/
def QuarticChamberBCF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree

/-- Cost-argmin chamber `BCF` / `CF·FF` (leaf BCF#1.0). -/
def QuarticChamberBCF11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BCF` / `FF` (leaf BCF#2.0). -/
def QuarticChamberBCF12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BCG` / `BBB` (leaf BCG#3.0). -/
def QuarticChamberBCG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BCG` / `BBB·BBC·BCC·CCC` (leaf BCG#3.0). -/
def QuarticChamberBCG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BCG` / `BG` (leaf BCG#0.0). -/
def QuarticChamberBCG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCG` / `BG·BBB` (leaf BCG#0.0). -/
def QuarticChamberBCG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCG` / `BG·CG` (leaf BCG#0.0). -/
def QuarticChamberBCG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCG` / `BG·CG·BBB·BBC·BCC·CCC` (leaf BCG#0.0). -/
def QuarticChamberBCG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree = A.natDegree + 2 * B.natDegree + 2 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 6 * C.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BCG` / `BG·CG·GG` (leaf BCG#0.0). -/
def QuarticChamberBCG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCG` / `BG·GG` (leaf BCG#0.0). -/
def QuarticChamberBCG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    6 * C.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BCG` / `CCC` (leaf BCG#6.0). -/
def QuarticChamberBCG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 6 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree

/-- Cost-argmin chamber `BCG` / `CG` (leaf BCG#1.0). -/
def QuarticChamberBCG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `BCG` / `CG·CCC` (leaf BCG#1.0). -/
def QuarticChamberBCG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BCG` / `CG·GG` (leaf BCG#1.0). -/
def QuarticChamberBCG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree < 2 * C.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 2 * C.natDegree + 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `BCG` / `GG` (leaf BCG#2.0). -/
def QuarticChamberBCG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + C.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree + 4 * C.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BDE` / `BBB` (leaf BDE#3.0). -/
def QuarticChamberBDE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BDE` / `DD` (leaf BDE#0.0). -/
def QuarticChamberBDE1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDE` / `DD·BBB` (leaf BDE#0.0). -/
def QuarticChamberBDE2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDE` / `DD·DE·EE` (leaf BDE#0.0). -/
def QuarticChamberBDE3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDE` / `DD·DE·EE·BBB` (leaf BDE#0.0). -/
def QuarticChamberBDE4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDE` / `EE` (leaf BDE#2.0). -/
def QuarticChamberBDE5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDE` / `EE·BBB` (leaf BDE#2.0). -/
def QuarticChamberBDE6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BDF` / `BBB` (leaf BDF#4.0). -/
def QuarticChamberBDF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    2 * D.natDegree + 2 * F.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree

/-- Cost-argmin chamber `BDF` / `BF` (leaf BDF#0.0). -/
def QuarticChamberBDF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDF` / `BF·BBB` (leaf BDF#0.0). -/
def QuarticChamberBDF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDF` / `BF·DD` (leaf BDF#0.0). -/
def QuarticChamberBDF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDF` / `BF·DD·BBB` (leaf BDF#0.0). -/
def QuarticChamberBDF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDF` / `BF·DD·DF·FF` (leaf BDF#0.0). -/
def QuarticChamberBDF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDF` / `BF·FF` (leaf BDF#0.0). -/
def QuarticChamberBDF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `BDF` / `DD` (leaf BDF#1.0). -/
def QuarticChamberBDF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDF` / `DD·BBB` (leaf BDF#1.0). -/
def QuarticChamberBDF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDF` / `DD·DF·FF` (leaf BDF#1.0). -/
def QuarticChamberBDF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDF` / `FF` (leaf BDF#3.0). -/
def QuarticChamberBDF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BDG` / `BBB` (leaf BDG#4.0). -/
def QuarticChamberBDG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree < A.natDegree + 6 * B.natDegree ∧
    D.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree

/-- Cost-argmin chamber `BDG` / `BG` (leaf BDG#0.0). -/
def QuarticChamberBDG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDG` / `BG·BBB` (leaf BDG#0.0). -/
def QuarticChamberBDG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDG` / `BG·DD` (leaf BDG#0.0). -/
def QuarticChamberBDG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDG` / `BG·DD·BBB` (leaf BDG#0.0). -/
def QuarticChamberBDG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDG` / `BG·DD·DG·GG` (leaf BDG#0.0). -/
def QuarticChamberBDG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDG` / `BG·GG` (leaf BDG#0.0). -/
def QuarticChamberBDG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * B.natDegree + 2 * G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree

/-- Cost-argmin chamber `BDG` / `DD` (leaf BDG#1.0). -/
def QuarticChamberBDG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDG` / `DD·BBB` (leaf BDG#1.0). -/
def QuarticChamberBDG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDG` / `DD·DG·GG` (leaf BDG#1.0). -/
def QuarticChamberBDG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 6 * B.natDegree < 4 * D.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `BDG` / `GG` (leaf BDG#3.0). -/
def QuarticChamberBDG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `BEF` / `BBB` (leaf BEF#4.0). -/
def QuarticChamberBEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BEF` / `BF` (leaf BEF#0.0). -/
def QuarticChamberBEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEF` / `BF·BBB` (leaf BEF#0.0). -/
def QuarticChamberBEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEF` / `BF·EE` (leaf BEF#0.0). -/
def QuarticChamberBEF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEF` / `BF·EE·BBB` (leaf BEF#0.0). -/
def QuarticChamberBEF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEF` / `BF·EE·EF·FF` (leaf BEF#0.0). -/
def QuarticChamberBEF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEF` / `BF·FF` (leaf BEF#0.0). -/
def QuarticChamberBEF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `BEF` / `EE` (leaf BEF#1.0). -/
def QuarticChamberBEF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEF` / `EE·BBB` (leaf BEF#1.0). -/
def QuarticChamberBEF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEF` / `EE·EF·FF` (leaf BEF#1.0). -/
def QuarticChamberBEF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEF` / `FF` (leaf BEF#3.0). -/
def QuarticChamberBEF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BEG` / `BBB` (leaf BEG#4.0). -/
def QuarticChamberBEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree + 2 * G.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BEG` / `BG` (leaf BEG#0.0). -/
def QuarticChamberBEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEG` / `BG·BBB` (leaf BEG#0.0). -/
def QuarticChamberBEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEG` / `BG·EE` (leaf BEG#0.0). -/
def QuarticChamberBEG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEG` / `BG·EE·BBB` (leaf BEG#0.0). -/
def QuarticChamberBEG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEG` / `BG·EE·EG·GG` (leaf BEG#0.0). -/
def QuarticChamberBEG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree = 2 * E.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEG` / `BG·GG` (leaf BEG#0.0). -/
def QuarticChamberBEG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + 2 * E.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `BEG` / `EE` (leaf BEG#1.0). -/
def QuarticChamberBEG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEG` / `EE·BBB` (leaf BEG#1.0). -/
def QuarticChamberBEG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEG` / `EE·EG·GG` (leaf BEG#1.0). -/
def QuarticChamberBEG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree ∧
    3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree ∧
    2 * B.natDegree < E.natDegree

/-- Cost-argmin chamber `BEG` / `GG` (leaf BEG#3.0). -/
def QuarticChamberBEG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + 2 * B.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `BFG` / `BBB` (leaf BFG#5.0). -/
def QuarticChamberBFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 4 * B.natDegree ∧
    G.natDegree < A.natDegree + 2 * B.natDegree ∧
    4 * F.natDegree < 5 * A.natDegree + 6 * B.natDegree ∧
    F.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧
    4 * G.natDegree < 7 * A.natDegree + 6 * B.natDegree

/-- Cost-argmin chamber `BFG` / `BF` (leaf BFG#0.0). -/
def QuarticChamberBFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BFG` / `BF·BBB` (leaf BFG#0.0). -/
def QuarticChamberBFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BFG` / `BF·BG` (leaf BFG#0.0). -/
def QuarticChamberBFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BFG` / `BF·BG·BBB` (leaf BFG#0.0). -/
def QuarticChamberBFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree

/-- Cost-argmin chamber `BFG` / `BF·BG·FF·FG·GG` (leaf BFG#0.0). -/
def QuarticChamberBFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + B.natDegree + F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BFG` / `BF·FF` (leaf BFG#0.0). -/
def QuarticChamberBFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree = F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `BFG` / `BG` (leaf BFG#1.0). -/
def QuarticChamberBFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree

/-- Cost-argmin chamber `BFG` / `BG·BBB` (leaf BFG#1.0). -/
def QuarticChamberBFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree

/-- Cost-argmin chamber `BFG` / `BG·GG` (leaf BFG#1.0). -/
def QuarticChamberBFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    4 * F.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree

/-- Cost-argmin chamber `BFG` / `FF` (leaf BFG#2.0). -/
def QuarticChamberBFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BFG` / `FF·FG·GG` (leaf BFG#2.0). -/
def QuarticChamberBFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * A.natDegree + B.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    5 * A.natDegree + 6 * B.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `BFG` / `GG` (leaf BFG#4.0). -/
def QuarticChamberBFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C = 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + B.natDegree + F.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    7 * A.natDegree + 6 * B.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `CDE` / `CCC` (leaf CDE#3.0). -/
def QuarticChamberCDE0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 6 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CDE` / `DD` (leaf CDE#0.0). -/
def QuarticChamberCDE1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDE` / `DD·CCC` (leaf CDE#0.0). -/
def QuarticChamberCDE2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDE` / `DD·DE·EE` (leaf CDE#0.0). -/
def QuarticChamberCDE3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDE` / `DD·DE·EE·CCC` (leaf CDE#0.0). -/
def QuarticChamberCDE4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDE` / `EE` (leaf CDE#2.0). -/
def QuarticChamberCDE5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDE` / `EE·CCC` (leaf CDE#2.0). -/
def QuarticChamberCDE6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < A.natDegree + 4 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CDF` / `CCC` (leaf CDF#4.0). -/
def QuarticChamberCDF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    D.natDegree + F.natDegree < 3 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `CDF` / `CF` (leaf CDF#0.0). -/
def QuarticChamberCDF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDF` / `CF·CCC` (leaf CDF#0.0). -/
def QuarticChamberCDF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDF` / `CF·DD` (leaf CDF#0.0). -/
def QuarticChamberCDF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDF` / `CF·DD·CCC` (leaf CDF#0.0). -/
def QuarticChamberCDF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDF` / `CF·DD·DF·FF` (leaf CDF#0.0). -/
def QuarticChamberCDF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDF` / `CF·FF` (leaf CDF#0.0). -/
def QuarticChamberCDF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    A.natDegree + 4 * D.natDegree < 2 * C.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

/-- Cost-argmin chamber `CDF` / `DD` (leaf CDF#1.0). -/
def QuarticChamberCDF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDF` / `DD·CCC` (leaf CDF#1.0). -/
def QuarticChamberCDF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDF` / `DD·DF·FF` (leaf CDF#1.0). -/
def QuarticChamberCDF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDF` / `FF` (leaf CDF#3.0). -/
def QuarticChamberCDF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `CDG` / `CCC` (leaf CDG#4.0). -/
def QuarticChamberCDG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < 3 * C.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree

/-- Cost-argmin chamber `CDG` / `CG` (leaf CDG#0.0). -/
def QuarticChamberCDG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDG` / `CG·CCC` (leaf CDG#0.0). -/
def QuarticChamberCDG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDG` / `CG·DD` (leaf CDG#0.0). -/
def QuarticChamberCDG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDG` / `CG·DD·CCC` (leaf CDG#0.0). -/
def QuarticChamberCDG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDG` / `CG·DD·DG·GG` (leaf CDG#0.0). -/
def QuarticChamberCDG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * C.natDegree = 2 * D.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDG` / `CG·GG` (leaf CDG#0.0). -/
def QuarticChamberCDG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * D.natDegree < C.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    2 * C.natDegree + 2 * D.natDegree < A.natDegree + 2 * G.natDegree

/-- Cost-argmin chamber `CDG` / `DD` (leaf CDG#1.0). -/
def QuarticChamberCDG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDG` / `DD·CCC` (leaf CDG#1.0). -/
def QuarticChamberCDG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDG` / `DD·DG·GG` (leaf CDG#1.0). -/
def QuarticChamberCDG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧
    3 * C.natDegree < A.natDegree + 2 * D.natDegree ∧
    4 * C.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `CDG` / `GG` (leaf CDG#3.0). -/
def QuarticChamberCDG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree < 4 * G.natDegree

/-- Cost-argmin chamber `CEF` / `CCC` (leaf CEF#4.0). -/
def QuarticChamberCEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < A.natDegree + 6 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CEF` / `CF` (leaf CEF#0.0). -/
def QuarticChamberCEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEF` / `CF·CCC` (leaf CEF#0.0). -/
def QuarticChamberCEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEF` / `CF·EE` (leaf CEF#0.0). -/
def QuarticChamberCEF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEF` / `CF·EE·CCC` (leaf CEF#0.0). -/
def QuarticChamberCEF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEF` / `CF·EE·EF·FF` (leaf CEF#0.0). -/
def QuarticChamberCEF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEF` / `CF·FF` (leaf CEF#0.0). -/
def QuarticChamberCEF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    4 * E.natDegree < A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CEF` / `EE` (leaf CEF#1.0). -/
def QuarticChamberCEF7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEF` / `EE·CCC` (leaf CEF#1.0). -/
def QuarticChamberCEF8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEF` / `EE·EF·FF` (leaf CEF#1.0). -/
def QuarticChamberCEF9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEF` / `FF` (leaf CEF#3.0). -/
def QuarticChamberCEF10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CEG` / `CCC` (leaf CEG#4.0). -/
def QuarticChamberCEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * E.natDegree < 3 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree

/-- Cost-argmin chamber `CEG` / `CG` (leaf CEG#0.0). -/
def QuarticChamberCEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEG` / `CG·CCC` (leaf CEG#0.0). -/
def QuarticChamberCEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEG` / `CG·EE` (leaf CEG#0.0). -/
def QuarticChamberCEG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEG` / `CG·EE·CCC` (leaf CEG#0.0). -/
def QuarticChamberCEG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEG` / `CG·EE·EG·GG` (leaf CEG#0.0). -/
def QuarticChamberCEG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree = 2 * E.natDegree ∧
    A.natDegree + C.natDegree = E.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEG` / `CG·GG` (leaf CEG#0.0). -/
def QuarticChamberCEG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    2 * E.natDegree < C.natDegree + G.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree

/-- Cost-argmin chamber `CEG` / `EE` (leaf CEG#1.0). -/
def QuarticChamberCEG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEG` / `EE·CCC` (leaf CEG#1.0). -/
def QuarticChamberCEG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEG` / `EE·EG·GG` (leaf CEG#1.0). -/
def QuarticChamberCEG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    C.natDegree + G.natDegree < 2 * E.natDegree ∧
    3 * C.natDegree < 2 * E.natDegree ∧
    2 * C.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `CEG` / `GG` (leaf CEG#3.0). -/
def QuarticChamberCEG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * C.natDegree + E.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `CFG` / `CCC` (leaf CFG#5.0). -/
def QuarticChamberCFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 4 * C.natDegree ∧
    G.natDegree < 2 * C.natDegree ∧
    2 * F.natDegree < A.natDegree + 3 * C.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 6 * C.natDegree ∧
    2 * G.natDegree < 2 * A.natDegree + 3 * C.natDegree

/-- Cost-argmin chamber `CFG` / `CF` (leaf CFG#0.0). -/
def QuarticChamberCFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `CF·CCC` (leaf CFG#0.0). -/
def QuarticChamberCFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `CF·CG` (leaf CFG#0.0). -/
def QuarticChamberCFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `CF·CG·CCC` (leaf CFG#0.0). -/
def QuarticChamberCFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `CF·CG·FF·FG·GG` (leaf CFG#0.0). -/
def QuarticChamberCFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * G.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `CF·FF` (leaf CFG#0.0). -/
def QuarticChamberCFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    4 * G.natDegree < 5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `CG` (leaf CFG#1.0). -/
def QuarticChamberCFG7810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `CFG` / `CG·CCC` (leaf CFG#1.0). -/
def QuarticChamberCFG8810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    G.natDegree < 2 * A.natDegree + C.natDegree

/-- Cost-argmin chamber `CFG` / `CG·GG` (leaf CFG#1.0). -/
def QuarticChamberCFG9810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * A.natDegree + C.natDegree = G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * F.natDegree < A.natDegree + C.natDegree + G.natDegree ∧
    2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree ∧
    2 * C.natDegree < G.natDegree

/-- Cost-argmin chamber `CFG` / `FF` (leaf CFG#2.0). -/
def QuarticChamberCFG10810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `FF·FG·GG` (leaf CFG#2.0). -/
def QuarticChamberCFG11810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree ∧
    A.natDegree + C.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 3 * C.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `CFG` / `GG` (leaf CFG#4.0). -/
def QuarticChamberCFG12810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C ≠ 0 ∧
    D = 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    5 * A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    2 * A.natDegree + C.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + 3 * C.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `DEF` / `DD` (leaf DEF#0.0). -/
def QuarticChamberDEF0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree

/-- Cost-argmin chamber `DEF` / `DD·DE·DF·EE·EF·FF` (leaf DEF#0.0). -/
def QuarticChamberDEF1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 4 * D.natDegree = 2 * E.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree

/-- Cost-argmin chamber `DEF` / `DD·DE·EE` (leaf DEF#0.0). -/
def QuarticChamberDEF2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree

/-- Cost-argmin chamber `DEF` / `DD·DF·FF` (leaf DEF#0.0). -/
def QuarticChamberDEF3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree + 2 * F.natDegree < 3 * A.natDegree + 4 * D.natDegree

/-- Cost-argmin chamber `DEF` / `EE` (leaf DEF#3.0). -/
def QuarticChamberDEF4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree

/-- Cost-argmin chamber `DEF` / `EE·EF·FF` (leaf DEF#3.0). -/
def QuarticChamberDEF5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    D.natDegree + F.natDegree < 2 * E.natDegree

/-- Cost-argmin chamber `DEF` / `FF` (leaf DEF#5.0). -/
def QuarticChamberDEF6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G = 0 ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `DEG` / `DD` (leaf DEG#0.0). -/
def QuarticChamberDEG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEG` / `DD·DE·DG·EE·EG·GG` (leaf DEG#0.0). -/
def QuarticChamberDEG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * A.natDegree + 2 * D.natDegree = E.natDegree + G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree

/-- Cost-argmin chamber `DEG` / `DD·DE·EE` (leaf DEG#0.0). -/
def QuarticChamberDEG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree = 2 * E.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEG` / `DD·DG·GG` (leaf DEG#0.0). -/
def QuarticChamberDEG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    2 * E.natDegree < A.natDegree + 2 * D.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DEG` / `EE` (leaf DEG#3.0). -/
def QuarticChamberDEG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `DEG` / `EE·EG·GG` (leaf DEG#3.0). -/
def QuarticChamberDEG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    A.natDegree + 2 * D.natDegree < 2 * E.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < A.natDegree + 4 * E.natDegree

/-- Cost-argmin chamber `DEG` / `GG` (leaf DEG#5.0). -/
def QuarticChamberDEG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F = 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    5 * A.natDegree + 2 * D.natDegree + 2 * E.natDegree < 4 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree

/-- Cost-argmin chamber `DFG` / `DD` (leaf DFG#0.0). -/
def QuarticChamberDFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DFG` / `DD·DF·DG·FF·FG·GG` (leaf DFG#0.0). -/
def QuarticChamberDFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    5 * A.natDegree + 4 * D.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree

/-- Cost-argmin chamber `DFG` / `DD·DF·FF` (leaf DFG#0.0). -/
def QuarticChamberDFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree

/-- Cost-argmin chamber `DFG` / `DD·DG·GG` (leaf DFG#0.0). -/
def QuarticChamberDFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree = 2 * G.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 5 * A.natDegree + 4 * D.natDegree

/-- Cost-argmin chamber `DFG` / `FF` (leaf DFG#3.0). -/
def QuarticChamberDFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `DFG` / `FF·FG·GG` (leaf DFG#3.0). -/
def QuarticChamberDFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + 2 * D.natDegree + 2 * G.natDegree < 4 * F.natDegree

/-- Cost-argmin chamber `DFG` / `GG` (leaf DFG#5.0). -/
def QuarticChamberDFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D ≠ 0 ∧
    E = 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    2 * A.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree

/-- Cost-argmin chamber `EFG` / `EE` (leaf EFG#0.0). -/
def QuarticChamberEFG0810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `EFG` / `EE·EF·EG·FF·FG·GG` (leaf EFG#0.0). -/
def QuarticChamberEFG1810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    3 * A.natDegree + 4 * E.natDegree = 2 * F.natDegree + 2 * G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree

/-- Cost-argmin chamber `EFG` / `EE·EF·FF` (leaf EFG#0.0). -/
def QuarticChamberEFG2810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree = 2 * F.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree ∧
    G.natDegree < A.natDegree + E.natDegree

/-- Cost-argmin chamber `EFG` / `EE·EG·GG` (leaf EFG#0.0). -/
def QuarticChamberEFG3810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    A.natDegree + E.natDegree = G.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree < A.natDegree + 2 * E.natDegree ∧
    2 * F.natDegree + 2 * G.natDegree < 3 * A.natDegree + 4 * E.natDegree

/-- Cost-argmin chamber `EFG` / `FF` (leaf EFG#3.0). -/
def QuarticChamberEFG4810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * G.natDegree < A.natDegree + 2 * F.natDegree

/-- Cost-argmin chamber `EFG` / `FF·FG·GG` (leaf EFG#3.0). -/
def QuarticChamberEFG5810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * E.natDegree < 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree

/-- Cost-argmin chamber `EFG` / `GG` (leaf EFG#5.0). -/
def QuarticChamberEFG6810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    D = 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    3 * A.natDegree + 2 * E.natDegree + 2 * F.natDegree < 4 * G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree


end Max11DegreeRoutes
