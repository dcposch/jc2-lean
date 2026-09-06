import Grok810ScaleZeroQuarticChamberResidual4Scratch

/-! # The per-carrier tournament on the 11 refined cells, `(8,10)` scale zero

59 refined leaves over 11
chambers whose leaves share one chamber `Prop` but carry *different*
certificates (the level-0 refinement reached a carrier's own argmin at
different cells).  Each `quarticChamber<name>810_refine` is a decision
tree on the leaves' own refinement conjuncts: at every node one
`lt_trichotomy`, at every leaf exactly one refined `Prop` whose conjuncts
the branch implies (exact rational Farkas certificates in
`scripts/check_810_quartic_chambers_lean.py`).  The refined leaves'
*kills* are not here — they wait on the power-certificate and tower
lanes; the manifest lists which certificate each leaf needs.
Untracked working note.
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

section QuarticChamberRefine810

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCDEG` / `CG·DD·CCC` (JSON `BCDEG#1.0`, certificate `power_target`, carriers kappa, mu, pi). -/
def QuarticRefinedBCDEG30L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG30810 A B C D E F G ∧
    G.natDegree = 2 * C.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCDEG` / `CG·DD·CCC` (JSON `BCDEG#1.1`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDEG30L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG30810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧
    E.natDegree + G.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCDEG` / `CG·DD·CCC` (JSON `BCDEG#1.2`, certificate `power_target`, carriers kappa, nu). -/
def QuarticRefinedBCDEG30L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG30810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + G.natDegree = 2 * C.natDegree + D.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 3 of chamber `BCDEG` / `CG·DD·CCC` (JSON `BCDEG#1.3`, certificate `power_target`, carriers kappa, nu). -/
def QuarticRefinedBCDEG30L3810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG30810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree < D.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    2 * A.natDegree + 3 * B.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < D.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 4 of chamber `BCDEG` / `CG·DD·CCC` (JSON `BCDEG#1.4`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCDEG30L4810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG30810 A B C D E F G ∧
    B.natDegree + G.natDegree < D.natDegree + E.natDegree ∧
    A.natDegree + 3 * B.natDegree < D.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCDEG` / `CG·EE·CCC` (JSON `BCDEG#1.0`, certificate `no_monomial_target`, carriers kappa, mu, pi). -/
def QuarticRefinedBCDEG36L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG36810 A B C D E F G ∧
    G.natDegree = 2 * C.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * G.natDegree = C.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + C.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCDEG` / `CG·EE·CCC` (JSON `BCDEG#1.1`, certificate `power_target`, carriers kappa, xi). -/
def QuarticRefinedBCDEG36L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG36810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCDEG` / `CG·EE·CCC` (JSON `BCDEG#1.2`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCDEG36L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEG36810 A B C D E F G ∧
    B.natDegree + G.natDegree < D.natDegree + E.natDegree ∧
    A.natDegree + 3 * B.natDegree < D.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDFG#0.0`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDFG7L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDFG#0.1`, certificate `deep_rescue`, carriers kappa, mu, n2, nu, omicron, pi, primitive, xi). -/
def QuarticRefinedBCDFG7L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree = B.natDegree + C.natDegree ∧
    D.natDegree + F.natDegree = 4 * B.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + 2 * C.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDFG#0.2`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDFG7L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCDFG` / `CG·DD·CCC` (JSON `BCDFG#3.0`, certificate `power_target`, carriers kappa, mu, pi). -/
def QuarticRefinedBCDFG54L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG54810 A B C D E F G ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCDFG` / `CG·DD·CCC` (JSON `BCDFG#3.1`, certificate `single_monomial`, carriers xi). -/
def QuarticRefinedBCDFG54L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG54810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + F.natDegree < C.natDegree + D.natDegree ∧
    2 * F.natDegree < C.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧
    A.natDegree + B.natDegree < D.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    A.natDegree + 4 * B.natDegree < C.natDegree + 2 * D.natDegree ∧
    3 * B.natDegree < C.natDegree + D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCDFG` / `CG·DD·CCC` (JSON `BCDFG#3.2`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDFG54L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG54810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 3 of chamber `BCDFG` / `CG·DD·CCC` (JSON `BCDFG#3.3`, certificate `power_target`, carriers kappa, nu). -/
def QuarticRefinedBCDFG54L3810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG54810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + G.natDegree = 2 * C.natDegree + D.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + F.natDegree = C.natDegree + D.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 4 of chamber `BCDFG` / `CG·DD·CCC` (JSON `BCDFG#3.4`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCDFG54L4810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDFG54810 A B C D E F G ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCEFG#0.0`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCEFG7L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCEFG#0.1`, certificate `deep_rescue`, carriers kappa, mu, n2, nu, omicron, pi, primitive, xi). -/
def QuarticRefinedBCEFG7L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree = 2 * F.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    E.natDegree = 2 * B.natDegree ∧
    E.natDegree + G.natDegree = B.natDegree + C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    E.natDegree + G.natDegree = A.natDegree + 4 * B.natDegree ∧
    E.natDegree + G.natDegree = 2 * B.natDegree + 2 * C.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCEFG#0.2`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCEFG7L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCEFG` / `CG·EE·CCC` (JSON `BCEFG#3.0`, certificate `no_monomial_target`, carriers kappa, mu, pi). -/
def QuarticRefinedBCEFG54L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCEFG54810 A B C D E F G ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * G.natDegree = C.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCEFG` / `CG·EE·CCC` (JSON `BCEFG#3.1`, certificate `power_target`, carriers kappa, xi). -/
def QuarticRefinedBCEFG54L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCEFG54810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCEFG` / `CG·EE·CCC` (JSON `BCEFG#3.2`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCEFG54L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCEFG54810 A B C D E F G ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `CDEFG` / `CG·DD·CCC` (JSON `CDEFG#1.0`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedCDEFG28L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG28810 A B C D E F G ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `CDEFG` / `CG·DD·CCC` (JSON `CDEFG#1.1`, certificate `single_monomial`, carriers xi). -/
def QuarticRefinedCDEFG28L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG28810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + F.natDegree < C.natDegree + D.natDegree ∧
    E.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree < C.natDegree + 2 * D.natDegree ∧
    C.natDegree + E.natDegree < 2 * D.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `CDEFG` / `CG·DD·CCC` (JSON `CDEFG#1.2`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedCDEFG28L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG28810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * C.natDegree + E.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 3 of chamber `CDEFG` / `CG·DD·CCC` (JSON `CDEFG#1.3`, certificate `power_target`, carriers kappa, mu, nu, pi). -/
def QuarticRefinedCDEFG28L3810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG28810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree = D.natDegree + G.natDegree ∧
    A.natDegree + F.natDegree = C.natDegree + D.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * C.natDegree + E.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 4 of chamber `CDEFG` / `CG·DD·CCC` (JSON `CDEFG#1.4`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedCDEFG28L4810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG28810 A B C D E F G ∧
    C.natDegree + F.natDegree < D.natDegree + E.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `CDEFG` / `CG·EE·CCC` (JSON `CDEFG#1.0`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedCDEFG34L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG34810 A B C D E F G ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `CDEFG` / `CG·EE·CCC` (JSON `CDEFG#1.1`, certificate `power_target`, carriers mu, pi, xi). -/
def QuarticRefinedCDEFG34L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG34810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree = C.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + C.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `CDEFG` / `CG·EE·CCC` (JSON `CDEFG#1.2`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedCDEFG34L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberCDEFG34810 A B C D E F G ∧
    C.natDegree + F.natDegree < D.natDegree + E.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDEFG#0.0`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDEFG7L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + E.natDegree < D.natDegree + F.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    2 * C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDEFG#0.1`, certificate `deep_rescue`, carriers kappa, mu, n2, nu, omicron, pi, primitive, xi). -/
def QuarticRefinedBCDEFG7L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    D.natDegree + F.natDegree = 2 * B.natDegree + E.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * C.natDegree + E.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDEFG#0.2`, certificate `OPEN`, carriers kappa, mu, nu, omicron, pi, xi). -/
def QuarticRefinedBCDEFG7L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    D.natDegree + F.natDegree = 2 * B.natDegree + E.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * C.natDegree + E.natDegree ∧
    D.natDegree + F.natDegree = 4 * B.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + 2 * C.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 3 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDEFG#0.3`, certificate `deep_rescue`, carriers kappa, mu, n2, nu, omicron, pi, primitive, xi). -/
def QuarticRefinedBCDEFG7L3810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree = B.natDegree + C.natDegree ∧
    D.natDegree + F.natDegree = 4 * B.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + 2 * C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    2 * B.natDegree + E.natDegree < D.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 4 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDEFG#0.4`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDEFG7L4810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 5 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDEFG#0.5`, certificate `deep_rescue`, carriers kappa, mu, n2, nu, omicron, pi, primitive, xi). -/
def QuarticRefinedBCDEFG7L5810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    E.natDegree + G.natDegree = 2 * F.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    E.natDegree = 2 * B.natDegree ∧
    E.natDegree + G.natDegree = B.natDegree + C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    E.natDegree + G.natDegree = A.natDegree + 4 * B.natDegree ∧
    E.natDegree + G.natDegree = 2 * B.natDegree + 2 * C.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 6 of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (JSON `BCDEFG#0.6`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDEFG7L6810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG7810 A B C D E F G ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    2 * F.natDegree = 2 * B.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree ∧
    B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * D.natDegree < 2 * F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    3 * B.natDegree + D.natDegree < 2 * F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧
    A.natDegree + D.natDegree < F.natDegree ∧
    E.natDegree + G.natDegree < 2 * F.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < 2 * F.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.0`, certificate `power_target`, carriers kappa, mu, pi). -/
def QuarticRefinedBCDEFG102L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.1`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDEFG102L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    E.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + E.natDegree < D.natDegree + F.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.2`, certificate `power_target`, carriers kappa, nu). -/
def QuarticRefinedBCDEFG102L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + G.natDegree = 2 * C.natDegree + D.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 3 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.3`, certificate `power_target`, carriers kappa, nu). -/
def QuarticRefinedBCDEFG102L3810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree < D.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    E.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    2 * A.natDegree + 3 * B.natDegree < D.natDegree + G.natDegree ∧
    2 * B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < D.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 4 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.4`, certificate `deep_rescue`, carriers kappa, mu, n2, nu, omicron, pi, primitive, xi). -/
def QuarticRefinedBCDEFG102L4810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    D.natDegree + F.natDegree < 2 * A.natDegree + G.natDegree ∧
    2 * E.natDegree < 2 * A.natDegree + G.natDegree ∧
    3 * D.natDegree < 2 * A.natDegree + B.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * C.natDegree + E.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + E.natDegree < D.natDegree + F.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 5 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.5`, certificate `power_target`, carriers kappa, mu, nu, pi). -/
def QuarticRefinedBCDEFG102L5810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + G.natDegree = 2 * C.natDegree + D.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 6 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.6`, certificate `single_monomial`, carriers xi). -/
def QuarticRefinedBCDEFG102L6810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree < D.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    E.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    2 * A.natDegree + 3 * B.natDegree < D.natDegree + G.natDegree ∧
    2 * B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + F.natDegree < C.natDegree + D.natDegree ∧
    E.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree < C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    B.natDegree + E.natDegree < C.natDegree + D.natDegree ∧
    C.natDegree + E.natDegree < 2 * D.natDegree ∧
    A.natDegree + 4 * B.natDegree < C.natDegree + 2 * D.natDegree ∧
    3 * B.natDegree < C.natDegree + D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 7 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.7`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDEFG102L7810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧
    E.natDegree + G.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 8 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.8`, certificate `power_target`, carriers kappa, nu). -/
def QuarticRefinedBCDEFG102L8810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree = D.natDegree ∧
    A.natDegree + B.natDegree + G.natDegree = 2 * C.natDegree + D.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 9 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.9`, certificate `power_target`, carriers kappa, nu). -/
def QuarticRefinedBCDEFG102L9810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree < D.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    E.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    2 * A.natDegree + 3 * B.natDegree < D.natDegree + G.natDegree ∧
    2 * B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < D.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 10 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.10`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCDEFG102L10810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 11 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.11`, certificate `power_target`, carriers kappa, mu, pi, xi). -/
def QuarticRefinedBCDEFG102L11810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * B.natDegree < A.natDegree + C.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = E.natDegree + G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree = 2 * C.natDegree + E.natDegree ∧
    F.natDegree < A.natDegree + D.natDegree ∧
    2 * B.natDegree + E.natDegree < D.natDegree + F.natDegree ∧
    2 * B.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < A.natDegree + D.natDegree ∧
    4 * B.natDegree < D.natDegree + F.natDegree ∧
    3 * B.natDegree < A.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 12 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.12`, certificate `power_target`, carriers kappa, mu, nu, pi). -/
def QuarticRefinedBCDEFG102L12810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree = D.natDegree + G.natDegree ∧
    A.natDegree + F.natDegree = C.natDegree + D.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * B.natDegree < A.natDegree + C.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    C.natDegree + 2 * E.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 13 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.13`, certificate `single_monomial`, carriers xi). -/
def QuarticRefinedBCDEFG102L13810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree < D.natDegree ∧
    A.natDegree + C.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + E.natDegree < G.natDegree ∧
    E.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    2 * A.natDegree + 3 * B.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    2 * B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧
    A.natDegree + B.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < D.natDegree + G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + F.natDegree < C.natDegree + D.natDegree ∧
    E.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧
    2 * F.natDegree < C.natDegree + 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧
    2 * B.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧
    B.natDegree + F.natDegree < 2 * D.natDegree ∧
    B.natDegree + E.natDegree < C.natDegree + D.natDegree ∧
    C.natDegree + E.natDegree < 2 * D.natDegree ∧
    A.natDegree + 4 * B.natDegree < C.natDegree + 2 * D.natDegree ∧
    3 * B.natDegree < C.natDegree + D.natDegree ∧
    2 * B.natDegree + C.natDegree < 2 * D.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 14 of chamber `BCDEFG` / `CG·DD·CCC` (JSON `BCDEFG#3.14`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCDEFG102L14810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG102810 A B C D E F G ∧
    B.natDegree + G.natDegree < D.natDegree + E.natDegree ∧
    C.natDegree + F.natDegree < D.natDegree + E.natDegree ∧
    A.natDegree + 3 * B.natDegree < D.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 0 of chamber `BCDEFG` / `CG·EE·CCC` (JSON `BCDEFG#3.0`, certificate `no_monomial_target`, carriers kappa, mu, pi). -/
def QuarticRefinedBCDEFG108L0810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG108810 A B C D E F G ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    2 * G.natDegree = C.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + C.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 1 of chamber `BCDEFG` / `CG·EE·CCC` (JSON `BCDEFG#3.1`, certificate `power_target`, carriers kappa, xi). -/
def QuarticRefinedBCDEFG108L1810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG108810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    D.natDegree + E.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 2 of chamber `BCDEFG` / `CG·EE·CCC` (JSON `BCDEFG#3.2`, certificate `power_target`, carriers mu, pi, xi). -/
def QuarticRefinedBCDEFG108L2810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG108810 A B C D E F G ∧
    B.natDegree + G.natDegree = C.natDegree + F.natDegree ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    E.natDegree + F.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree < A.natDegree + G.natDegree ∧
    C.natDegree + E.natDegree < A.natDegree + G.natDegree ∧
    2 * D.natDegree < A.natDegree + G.natDegree ∧
    2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + G.natDegree ∧
    2 * G.natDegree = C.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + C.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 3 of chamber `BCDEFG` / `CG·EE·CCC` (JSON `BCDEFG#3.3`, certificate `power_target`, carriers kappa, xi). -/
def QuarticRefinedBCDEFG108L3810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG108810 A B C D E F G ∧
    B.natDegree + G.natDegree = D.natDegree + E.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    C.natDegree + F.natDegree < B.natDegree + G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 4 of chamber `BCDEFG` / `CG·EE·CCC` (JSON `BCDEFG#3.4`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCDEFG108L4810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG108810 A B C D E F G ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    D.natDegree + E.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 5 of chamber `BCDEFG` / `CG·EE·CCC` (JSON `BCDEFG#3.5`, certificate `power_target`, carriers mu, pi, xi). -/
def QuarticRefinedBCDEFG108L5810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG108810 A B C D E F G ∧
    C.natDegree + F.natDegree = D.natDegree + E.natDegree ∧
    B.natDegree + G.natDegree < C.natDegree + F.natDegree ∧
    A.natDegree + 3 * B.natDegree < C.natDegree + F.natDegree ∧
    2 * B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧
    B.natDegree + C.natDegree < F.natDegree ∧
    D.natDegree + G.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    E.natDegree < A.natDegree + C.natDegree ∧
    2 * B.natDegree < A.natDegree + C.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    2 * G.natDegree = C.natDegree + 2 * E.natDegree ∧
    A.natDegree + 2 * F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + B.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + D.natDegree < G.natDegree ∧
    B.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + C.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧
    C.natDegree + D.natDegree + F.natDegree < 2 * G.natDegree ∧
    2 * D.natDegree + E.natDegree < 2 * G.natDegree ∧
    A.natDegree + 3 * B.natDegree + D.natDegree < 2 * G.natDegree ∧
    3 * B.natDegree + F.natDegree < 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧
    2 * B.natDegree + C.natDegree + E.natDegree < 2 * G.natDegree ∧
    B.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧
    A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    2 * F.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    B.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧
    C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree ∧
    A.natDegree + 4 * B.natDegree < E.natDegree + G.natDegree ∧
    3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree ∧
    2 * B.natDegree + 2 * C.natDegree < E.natDegree + G.natDegree

set_option maxHeartbeats 64000000 in
/-- Carrier-refined leaf 6 of chamber `BCDEFG` / `CG·EE·CCC` (JSON `BCDEFG#3.6`, certificate `single_monomial`, carriers kappa). -/
def QuarticRefinedBCDEFG108L6810 (A B C D E F G : k[X]) : Prop :=
  QuarticChamberBCDEFG108810 A B C D E F G ∧
    B.natDegree + G.natDegree < D.natDegree + E.natDegree ∧
    C.natDegree + F.natDegree < D.natDegree + E.natDegree ∧
    A.natDegree + 3 * B.natDegree < D.natDegree + E.natDegree ∧
    2 * B.natDegree < E.natDegree ∧
    B.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree

set_option maxHeartbeats 64000000 in
/-- The 5 carrier-refined leaves cover chamber `BCDEG` / `CG·DD·CCC`. -/
theorem quarticChamberBCDEG30810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG30810 A B C D E F G) :
    QuarticRefinedBCDEG30L0810 A B C D E F G ∨
      QuarticRefinedBCDEG30L1810 A B C D E F G ∨
      QuarticRefinedBCDEG30L2810 A B C D E F G ∨
      QuarticRefinedBCDEG30L3810 A B C D E F G ∨
      QuarticRefinedBCDEG30L4810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (D.natDegree + E.natDegree) (B.natDegree + G.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- D.natDegree + E.natDegree = B.natDegree + G.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega⟩))))

set_option maxHeartbeats 64000000 in
/-- The 3 carrier-refined leaves cover chamber `BCDEG` / `CG·EE·CCC`. -/
theorem quarticChamberBCDEG36810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG36810 A B C D E F G) :
    QuarticRefinedBCDEG36L0810 A B C D E F G ∨
      QuarticRefinedBCDEG36L1810 A B C D E F G ∨
      QuarticRefinedBCDEG36L2810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (D.natDegree + E.natDegree) (B.natDegree + G.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega⟩))

set_option maxHeartbeats 64000000 in
/-- The 3 carrier-refined leaves cover chamber `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`. -/
theorem quarticChamberBCDFG7810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG7810 A B C D E F G) :
    QuarticRefinedBCDFG7L0810 A B C D E F G ∨
      QuarticRefinedBCDFG7L1810 A B C D E F G ∨
      QuarticRefinedBCDFG7L2810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))

set_option maxHeartbeats 64000000 in
/-- The 5 carrier-refined leaves cover chamber `BCDFG` / `CG·DD·CCC`. -/
theorem quarticChamberBCDFG54810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG54810 A B C D E F G) :
    QuarticRefinedBCDFG54L0810 A B C D E F G ∨
      QuarticRefinedBCDFG54L1810 A B C D E F G ∨
      QuarticRefinedBCDFG54L2810 A B C D E F G ∨
      QuarticRefinedBCDFG54L3810 A B C D E F G ∨
      QuarticRefinedBCDFG54L4810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (C.natDegree + F.natDegree) (B.natDegree + G.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- C.natDegree + F.natDegree = B.natDegree + G.natDegree
    rcases lt_trichotomy (A.natDegree + F.natDegree) (C.natDegree + D.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega⟩))))

set_option maxHeartbeats 64000000 in
/-- The 3 carrier-refined leaves cover chamber `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`. -/
theorem quarticChamberBCEFG7810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG7810 A B C D E F G) :
    QuarticRefinedBCEFG7L0810 A B C D E F G ∨
      QuarticRefinedBCEFG7L1810 A B C D E F G ∨
      QuarticRefinedBCEFG7L2810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * F.natDegree) (E.natDegree + G.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))

set_option maxHeartbeats 64000000 in
/-- The 3 carrier-refined leaves cover chamber `BCEFG` / `CG·EE·CCC`. -/
theorem quarticChamberBCEFG54810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG54810 A B C D E F G) :
    QuarticRefinedBCEFG54L0810 A B C D E F G ∨
      QuarticRefinedBCEFG54L1810 A B C D E F G ∨
      QuarticRefinedBCEFG54L2810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (C.natDegree + F.natDegree) (B.natDegree + G.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr (⟨hch, by omega, by omega, by omega⟩))

set_option maxHeartbeats 64000000 in
/-- The 5 carrier-refined leaves cover chamber `CDEFG` / `CG·DD·CCC`. -/
theorem quarticChamberCDEFG28810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG28810 A B C D E F G) :
    QuarticRefinedCDEFG28L0810 A B C D E F G ∨
      QuarticRefinedCDEFG28L1810 A B C D E F G ∨
      QuarticRefinedCDEFG28L2810 A B C D E F G ∨
      QuarticRefinedCDEFG28L3810 A B C D E F G ∨
      QuarticRefinedCDEFG28L4810 A B C D E F G := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  rcases lt_trichotomy (D.natDegree + E.natDegree) (C.natDegree + F.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega⟩
  · -- D.natDegree + E.natDegree = C.natDegree + F.natDegree
    rcases lt_trichotomy (A.natDegree + F.natDegree) (C.natDegree + D.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega⟩))))

set_option maxHeartbeats 64000000 in
/-- The 3 carrier-refined leaves cover chamber `CDEFG` / `CG·EE·CCC`. -/
theorem quarticChamberCDEFG34810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG34810 A B C D E F G) :
    QuarticRefinedCDEFG34L0810 A B C D E F G ∨
      QuarticRefinedCDEFG34L1810 A B C D E F G ∨
      QuarticRefinedCDEFG34L2810 A B C D E F G := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  rcases lt_trichotomy (D.natDegree + E.natDegree) (C.natDegree + F.natDegree) with hr0a | hr0b | hr0c
  · exact Or.inl ⟨hch, by omega⟩
  · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr (⟨hch, by omega⟩))

set_option maxHeartbeats 64000000 in
/-- The 7 carrier-refined leaves cover chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`. -/
theorem quarticChamberBCDEFG7810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG7810 A B C D E F G) :
    QuarticRefinedBCDEFG7L0810 A B C D E F G ∨
      QuarticRefinedBCDEFG7L1810 A B C D E F G ∨
      QuarticRefinedBCDEFG7L2810 A B C D E F G ∨
      QuarticRefinedBCDEFG7L3810 A B C D E F G ∨
      QuarticRefinedBCDEFG7L4810 A B C D E F G ∨
      QuarticRefinedBCDEFG7L5810 A B C D E F G ∨
      QuarticRefinedBCDEFG7L6810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, hq19, hq20, hq21, hq22⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (E.natDegree + G.natDegree) (A.natDegree + D.natDegree + F.natDegree) with hr0a | hr0b | hr0c
  · -- E.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))))
  · -- E.natDegree + G.natDegree = A.natDegree + D.natDegree + F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))))
  · -- E.natDegree + G.natDegree > A.natDegree + D.natDegree + F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (E.natDegree + G.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))))

set_option maxHeartbeats 64000000 in
/-- The 15 carrier-refined leaves cover chamber `BCDEFG` / `CG·DD·CCC`. -/
theorem quarticChamberBCDEFG102810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG102810 A B C D E F G) :
    QuarticRefinedBCDEFG102L0810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L1810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L2810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L3810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L4810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L5810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L6810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L7810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L8810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L9810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L10810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L11810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L12810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L13810 A B C D E F G ∨
      QuarticRefinedBCDEFG102L14810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, hq19, hq20, hq21, hq22⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (C.natDegree + F.natDegree) (B.natDegree + G.natDegree) with hr0a | hr0b | hr0c
  · -- C.natDegree + F.natDegree < B.natDegree + G.natDegree
    rcases lt_trichotomy (D.natDegree + E.natDegree) (B.natDegree + G.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · -- D.natDegree + E.natDegree = B.natDegree + G.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with hr2a | hr2b | hr2c
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
  · -- C.natDegree + F.natDegree = B.natDegree + G.natDegree
    rcases lt_trichotomy (D.natDegree + E.natDegree) (B.natDegree + G.natDegree) with hr1a | hr1b | hr1c
    · -- D.natDegree + E.natDegree < B.natDegree + G.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with hr2a | hr2b | hr2c
      · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    · -- D.natDegree + E.natDegree = B.natDegree + G.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with hr2a | hr2b | hr2c
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))))))))))))
  · -- C.natDegree + F.natDegree > B.natDegree + G.natDegree
    rcases lt_trichotomy (D.natDegree + E.natDegree) (C.natDegree + F.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))))))))
    · -- D.natDegree + E.natDegree = C.natDegree + F.natDegree
      rcases lt_trichotomy (D.natDegree + G.natDegree) (A.natDegree + C.natDegree + F.natDegree) with hr2a | hr2b | hr2c
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))))))))))))

set_option maxHeartbeats 64000000 in
/-- The 7 carrier-refined leaves cover chamber `BCDEFG` / `CG·EE·CCC`. -/
theorem quarticChamberBCDEFG108810_refine
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG108810 A B C D E F G) :
    QuarticRefinedBCDEFG108L0810 A B C D E F G ∨
      QuarticRefinedBCDEFG108L1810 A B C D E F G ∨
      QuarticRefinedBCDEFG108L2810 A B C D E F G ∨
      QuarticRefinedBCDEFG108L3810 A B C D E F G ∨
      QuarticRefinedBCDEFG108L4810 A B C D E F G ∨
      QuarticRefinedBCDEFG108L5810 A B C D E F G ∨
      QuarticRefinedBCDEFG108L6810 A B C D E F G := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, hq19, hq20, hq21, hq22⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (C.natDegree + F.natDegree) (B.natDegree + G.natDegree) with hr0a | hr0b | hr0c
  · -- C.natDegree + F.natDegree < B.natDegree + G.natDegree
    rcases lt_trichotomy (D.natDegree + E.natDegree) (B.natDegree + G.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))))
  · -- C.natDegree + F.natDegree = B.natDegree + G.natDegree
    rcases lt_trichotomy (D.natDegree + E.natDegree) (B.natDegree + G.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))))
  · -- C.natDegree + F.natDegree > B.natDegree + G.natDegree
    rcases lt_trichotomy (D.natDegree + E.natDegree) (C.natDegree + F.natDegree) with hr1a | hr1b | hr1c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hch, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hch, by omega, by omega, by omega, by omega, by omega⟩))))))


end QuarticChamberRefine810

end Max11DegreeRoutes
