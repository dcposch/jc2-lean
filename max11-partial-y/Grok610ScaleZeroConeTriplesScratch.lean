import Grok610ScaleZeroConeFinishScratch

/-! # Scale-zero cone triples for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeFinishScratch` on the constant core
`H = (C t)²`.  Untracked working note.  No tracked file was edited.

The parent residual `normalized610ScaleZero_coneFinishResidual` (green at
content SHA `014b69b2`, commit `35631da`) hands, for every
`Normalized610LeadingCoreSource P Q H 0`, the constant core `H = (C t)²`,
the derivative identity, `natDegree 0` for `λ/κ/μ/ο`, and the negation of
every pair-ratio and unique-`D₀` monomial cone.

This file lands the triples `ABC0` / `ABE0` by extracting tied leading
coefficients of `λ`/`κ`/raw-`ο` and applying the field identities
`abc0_tied_leadings_impossible` / parent `abe0_tied_leadings_impossible`,
and kills every mixed-`D₀` max-set whose companion `μ` face is a unique
monomial (`B D₀²` or `C₀² D₀`) the way `WeightedAD02LeadsCone610` was
killed.  Remaining: `AC0E0` (cusp with `l = 0`), the quadruple `T₂`
branch, and mixed-`D₀` combination max-sets whose companion `κ`/`μ`
faces have more than one monomial.

CAS job `derive_610_scale_zero_cone_triples.py` (extending
`derive_610_scale_zero_cone_ratio_ties.py`).  Groebner certificates:
`C₀⁶` on `A`–`B`–`C₀` (`λ+κ+ο`) and `E₀⁴` on `A`–`B`–`E₀`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-! ## Mixed-`D₀` max-set cones

Named by which of the seven `λ` weights
`{6 deg A, 4 deg B, 3 deg C₀, 2 deg E₀, deg(A D₀²), deg(A² B D₀), deg(B C₀ D₀)}`
attain the global maximum.  Unique maxima and pair-ties are already
empty on the parent residual; these defs cover the leftover mixed-`D₀`
max-sets from the degree enumerator.
-/

section MixedD0Cones610

variable {k : Type*} [Field k] [CharZero k]

/-- Tie `4 deg B = deg(A D₀²)`, other five weights strictly lighter. -/
def MixedADBRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree

/-- Tie `deg(A D₀²) = deg(B C₀ D₀)`, other five strictly lighter. -/
def MixedADBDRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree =
      B.natDegree + C0.natDegree + D0.natDegree ∧
    6 * A.natDegree < A.natDegree + 2 * D0.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D0.natDegree ∧
    3 * C0.natDegree < A.natDegree + 2 * D0.natDegree ∧
    2 * E0.natDegree < A.natDegree + 2 * D0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree <
      A.natDegree + 2 * D0.natDegree

/-- Tie `3 deg C₀ = deg(A D₀²)`, other five strictly lighter. -/
def MixedADCRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 3 * C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * E0.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 3 * C0.natDegree

/-- Tie `2 deg E₀ = deg(A D₀²)`, other five strictly lighter. -/
def MixedADERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 2 * E0.natDegree ∧
    6 * A.natDegree < 2 * E0.natDegree ∧
    4 * B.natDegree < 2 * E0.natDegree ∧
    3 * C0.natDegree < 2 * E0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 2 * E0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 2 * E0.natDegree

/-- Tie `4 deg B = deg(B C₀ D₀)`, other five strictly lighter. -/
def MixedBBDRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    4 * B.natDegree = B.natDegree + C0.natDegree + D0.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree

/-- Tie `3 deg C₀ = deg(B C₀ D₀)`, other five strictly lighter. -/
def MixedBDCRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < D0.natDegree ∧
    3 * C0.natDegree = B.natDegree + C0.natDegree + D0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * E0.natDegree < 3 * C0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree

/-- Tie `2 deg E₀ = deg(B C₀ D₀)`, other five strictly lighter. -/
def MixedBDERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = B.natDegree + C0.natDegree + D0.natDegree ∧
    6 * A.natDegree < 2 * E0.natDegree ∧
    4 * B.natDegree < 2 * E0.natDegree ∧
    3 * C0.natDegree < 2 * E0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 2 * E0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 2 * E0.natDegree

/-- Triple `6 deg A = 3 deg C₀ = deg(A D₀²)`. -/
def MixedAADCRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Triple `6 deg A = 2 deg E₀ = deg(A D₀²)`. -/
def MixedAADERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Triple `4 deg B = deg(A D₀²) = deg(B C₀ D₀)`. -/
def MixedADBBDRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree

/-- Triple `4 deg B = 2 deg E₀ = deg(A D₀²)`. -/
def MixedADBERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree

/-- Triple `3 deg C₀ = deg(A D₀²) = deg(B C₀ D₀)`. -/
def MixedADBDCRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 3 * C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * E0.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree

/-- Triple `2 deg E₀ = deg(A D₀²) = deg(B C₀ D₀)`. -/
def MixedADBDERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 2 * E0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 2 * E0.natDegree ∧
    6 * A.natDegree < 2 * E0.natDegree ∧
    4 * B.natDegree < 2 * E0.natDegree ∧
    3 * C0.natDegree < 2 * E0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 2 * E0.natDegree

/-- Triple `3 deg C₀ = 2 deg E₀ = deg(A D₀²)`. -/
def MixedADCERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = 3 * C0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 3 * C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 3 * C0.natDegree

/-- Triple `4 deg B = 3 deg C₀ = deg(B C₀ D₀)`. -/
def MixedBBDCRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    3 * C0.natDegree = 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree

/-- Triple `4 deg B = 2 deg E₀ = deg(B C₀ D₀)`. -/
def MixedBBDERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree

/-- Triple `3 deg C₀ = 2 deg E₀ = deg(B C₀ D₀)`. -/
def MixedBDCERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 3 * C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree

/-- Quadruple `6 deg A = 4 deg B = deg(A D₀²) = deg(A² B D₀)`. -/
def MixedAA2ADBRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree = 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Quadruple `6 deg A = 3 deg C₀ = 2 deg E₀ = deg(A D₀²)`. -/
def MixedAADCERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Quadruple `4 deg B = 2 deg E₀ = deg(A D₀²) = deg(B C₀ D₀)`. -/
def MixedADBBDERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree

/-- Quadruple `3 deg C₀ = 2 deg E₀ = deg(A D₀²) = deg(B C₀ D₀)`. -/
def MixedADBDCERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < D0.natDegree ∧
    2 * E0.natDegree = 3 * C0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 3 * C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree

/-- Quadruple `4 deg B = 3 deg C₀ = 2 deg E₀ = deg(B C₀ D₀)`. -/
def MixedBBDCERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    3 * C0.natDegree = 4 * B.natDegree ∧
    2 * E0.natDegree = 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree

/-- Five-way `6 deg A = 4 deg B = 2 deg E₀ = deg(A D₀²) = deg(A² B D₀)`. -/
def MixedAA2ADBERatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree = 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Six-way omitting `E₀`. -/
def MixedAA2ADBBDCRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree = 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree

/-- All seven `λ` weights tied. -/
def MixedAllSevenRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree = 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree = 6 * A.natDegree

end MixedD0Cones610

/-! ## Leading-coefficient identities on leftover triples -/

section TripleIdentities610

variable {k : Type*} [Field k] [CharZero k]

/-- Euclidean: `λ` minus `(2 a² - 3 c) κ_inner` on the `A`–`B`–`C₀` triple. -/
theorem lambda_abc0_of_kappa_inner (a b c : k) :
    (7 : k) * a ^ 6 - 63 * a ^ 4 * c - 126 * a ^ 3 * b ^ 2 +
          162 * a ^ 2 * c ^ 2 + 324 * a * b ^ 2 * c + 27 * b ^ 4 -
          81 * c ^ 3 -
        (2 * a ^ 2 - 3 * c) *
          (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2) =
      -7 * a ^ 6 + 30 * a ^ 4 * c - 102 * a ^ 3 * b ^ 2 +
        288 * a * b ^ 2 * c + 27 * b ^ 4 := by
  ring

/-- Euclidean: `3 ο + (8 a³ + 18 a c + 27 b²) κ_inner`. -/
theorem omicron_abc0_of_kappa_inner (a b c : k) :
    (3 : k) *
          (4 * a ^ 7 - 42 * a ^ 5 * c - 105 * a ^ 4 * b ^ 2 +
            144 * a ^ 3 * c ^ 2 + 432 * a ^ 2 * b ^ 2 * c +
            72 * a * b ^ 4 - 162 * a * c ^ 3 - 243 * b ^ 2 * c ^ 2) +
        (8 * a ^ 3 + 18 * a * c + 27 * b ^ 2) *
          (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2) =
      2 * a *
        (34 * a ^ 6 - 144 * a ^ 4 * c - 111 * a ^ 3 * b ^ 2 +
          54 * a * b ^ 2 * c - 54 * b ^ 4) := by
  ring

theorem abc0_lambda_remainder_linear (a b c : k) :
    -7 * a ^ 6 + 30 * a ^ 4 * c - 102 * a ^ 3 * b ^ 2 +
        288 * a * b ^ 2 * c + 27 * b ^ 4 =
      6 * a * (5 * a ^ 3 + 48 * b ^ 2) * c -
        (7 * a ^ 6 + 102 * a ^ 3 * b ^ 2 - 27 * b ^ 4) := by
  ring

theorem abc0_lambda_remainder_of_five_forty_eight (a b : k)
    (h : (5 : k) * a ^ 3 + 48 * b ^ 2 = 0) :
    (25 : k) * (-7 * a ^ 6 - 102 * a ^ 3 * b ^ 2 + 27 * b ^ 4) =
      9027 * b ^ 4 := by
  have h5 : (5 : k) ≠ 0 := by norm_num
  have ha3 : a ^ 3 = -((48 : k) * b ^ 2) / 5 := by
    have : 5 * a ^ 3 = -(48 * b ^ 2) := by linear_combination h
    exact (eq_div_iff_mul_eq h5).mpr (by rw [mul_comm]; exact this)
  have ha6 : a ^ 6 = (a ^ 3) ^ 2 := by ring
  rw [ha6, ha3]
  ring

def abc0KapLambdaResultantP (a b : k) : k :=
  (7 : k) * a ^ 12 - 3780 * a ^ 9 * b ^ 2 - 42714 * a ^ 6 * b ^ 4 -
    96012 * a ^ 3 * b ^ 6 + 2187 * b ^ 8

def abc0RemaindersResultantR (a b : k) : k :=
  (2 : k) * a ^ 9 - 1308 * a ^ 6 * b ^ 2 - 4032 * a ^ 3 * b ^ 4 -
    2835 * b ^ 6

def abc0Pu (u v : k) : k :=
  (7 : k) * u ^ 4 - 3780 * u ^ 3 * v - 42714 * u ^ 2 * v ^ 2 -
    96012 * u * v ^ 3 + 2187 * v ^ 4

def abc0Ru (u v : k) : k :=
  (2 : k) * u ^ 3 - 1308 * u ^ 2 * v - 4032 * u * v ^ 2 - 2835 * v ^ 3

def abc0W (u v : k) : k :=
  (12180 : k) * u ^ 2 + 37597 * u * v + 27984 * v ^ 2

def abc0Q (u v : k) : k :=
  (8003317 : k) * u ^ 2 + 24582864 * u * v + 17265150 * v ^ 2

theorem abc0Pu_of_P (a b : k) :
    abc0Pu (a ^ 3) (b ^ 2) = abc0KapLambdaResultantP a b := by
  simp only [abc0Pu, abc0KapLambdaResultantP]
  ring

theorem abc0Ru_of_R (a b : k) :
    abc0Ru (a ^ 3) (b ^ 2) = abc0RemaindersResultantR a b := by
  simp only [abc0Ru, abc0RemaindersResultantR]
  ring

theorem abc0_L2_kap_is_nine_P (a b : k)
    (L N : k)
    (hL : L = 6 * a * (5 * a ^ 3 + 48 * b ^ 2))
    (hN : N = 7 * a ^ 6 + 102 * a ^ 3 * b ^ 2 - 27 * b ^ 4) :
    (27 : k) * N ^ 2 - 36 * a ^ 2 * N * L +
        (7 * a ^ 4 - 12 * a * b ^ 2) * L ^ 2 =
      9 * abc0KapLambdaResultantP a b := by
  rw [hL, hN]
  simp only [abc0KapLambdaResultantP]
  ring

theorem abc0_LoN_plus_NoL (a b : k)
    (L N Lo No : k)
    (hL : L = 6 * a * (5 * a ^ 3 + 48 * b ^ 2))
    (hN : N = 7 * a ^ 6 + 102 * a ^ 3 * b ^ 2 - 27 * b ^ 4)
    (hLo : Lo = -144 * a ^ 4 + 54 * a * b ^ 2)
    (hNo : No = 34 * a ^ 6 - 111 * a ^ 3 * b ^ 2 - 54 * b ^ 4) :
    Lo * N + No * L = 6 * a * abc0RemaindersResultantR a b := by
  rw [hL, hN, hLo, hNo]
  simp only [abc0RemaindersResultantR]
  ring

theorem abc0_euclidean_step1 (u v : k) :
    (2 : k) * abc0Pu u v - (7 * u + 798 * v) * abc0Ru u v =
      81 * v ^ 2 * abc0W u v := by
  simp only [abc0Pu, abc0Ru, abc0W]
  ring

theorem abc0_euclidean_step2 (u v : k) :
    (2 : k) * u * abc0W u v - 12180 * abc0Ru u v =
      2 * v * abc0Q u v := by
  simp only [abc0W, abc0Ru, abc0Q]
  ring

theorem abc0_euclidean_step3 (u v : k) :
    (8003317 : k) * abc0W u v - 12180 * abc0Q u v =
      7 * v * (211632247 * u + 1953613704 * v) := by
  simp only [abc0W, abc0Q]
  ring

theorem abc0_W_on_line (u v : k)
    (hlin : (211632247 : k) * u + 1953613704 * v = 0) :
    (211632247 : k) ^ 2 * abc0W u v =
      32195228840268749220600 * v ^ 2 := by
  simp only [abc0W]
  have hu : (211632247 : k) * u = -1953613704 * v := by
    linear_combination hlin
  have hsq : ((211632247 : k) * u) ^ 2 = (1953613704 * v) ^ 2 := by
    rw [hu]
    ring
  -- Expand `d^2 W` with `d u = -n v`.
  have : (211632247 : k) ^ 2 *
        (12180 * u ^ 2 + 37597 * u * v + 27984 * v ^ 2) =
      12180 * (211632247 * u) ^ 2 +
        37597 * (211632247 * u) * (211632247 * v) +
        27984 * (211632247) ^ 2 * v ^ 2 := by
    ring
  rw [this, hu]
  ring

/-- The `A`–`B`–`C₀` inner forms cannot vanish together unless `b = 0`. -/
theorem abc0_tied_leadings_impossible (a b c : k)
    (hb : b ≠ 0)
    (hkap :
      (7 : k) * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2 = 0)
    (hlam :
      (7 : k) * a ^ 6 - 63 * a ^ 4 * c - 126 * a ^ 3 * b ^ 2 +
          162 * a ^ 2 * c ^ 2 + 324 * a * b ^ 2 * c + 27 * b ^ 4 -
          81 * c ^ 3 =
        0)
    (homi :
      (4 : k) * a ^ 7 - 42 * a ^ 5 * c - 105 * a ^ 4 * b ^ 2 +
          144 * a ^ 3 * c ^ 2 + 432 * a ^ 2 * b ^ 2 * c +
          72 * a * b ^ 4 - 162 * a * c ^ 3 - 243 * b ^ 2 * c ^ 2 =
        0) :
    False := by
  have hlamRem :
      -7 * a ^ 6 + 30 * a ^ 4 * c - 102 * a ^ 3 * b ^ 2 +
          288 * a * b ^ 2 * c + 27 * b ^ 4 =
        0 := by
    have hid := lambda_abc0_of_kappa_inner a b c
    have : (2 * a ^ 2 - 3 * c) *
        (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2) = 0 := by
      simp [hkap]
    rw [this, hlam, sub_zero] at hid
    exact hid.symm
  have homiInner :
      (2 : k) * a *
          (34 * a ^ 6 - 144 * a ^ 4 * c - 111 * a ^ 3 * b ^ 2 +
            54 * a * b ^ 2 * c - 54 * b ^ 4) =
        0 := by
    have hid := omicron_abc0_of_kappa_inner a b c
    have h3omi : (3 : k) *
        (4 * a ^ 7 - 42 * a ^ 5 * c - 105 * a ^ 4 * b ^ 2 +
          144 * a ^ 3 * c ^ 2 + 432 * a ^ 2 * b ^ 2 * c +
          72 * a * b ^ 4 - 162 * a * c ^ 3 - 243 * b ^ 2 * c ^ 2) =
        0 := by
      simp [homi]
    have hkapm : (8 * a ^ 3 + 18 * a * c + 27 * b ^ 2) *
        (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2) =
        0 := by
      simp [hkap]
    rw [h3omi, hkapm, zero_add] at hid
    exact hid.symm
  have hlin := abc0_lambda_remainder_linear a b c
  rw [hlamRem] at hlin
  by_cases ha0 : a = 0
  · have : (27 : k) * b ^ 4 = 0 := by
      simpa [ha0] using hlamRem
    have h27 : (27 : k) ≠ 0 := by norm_num
    exact hb ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp this).resolve_left h27))
  · by_cases hcoeff : (5 : k) * a ^ 3 + 48 * b ^ 2 = 0
    · have h25 := abc0_lambda_remainder_of_five_forty_eight a b hcoeff
      have hN0 : -7 * a ^ 6 - 102 * a ^ 3 * b ^ 2 + 27 * b ^ 4 = 0 := by
        have hLc0 : 6 * a * (5 * a ^ 3 + 48 * b ^ 2) * c = 0 := by
          simp [hcoeff]
        have hsub : 6 * a * (5 * a ^ 3 + 48 * b ^ 2) * c -
            (7 * a ^ 6 + 102 * a ^ 3 * b ^ 2 - 27 * b ^ 4) = 0 :=
          hlin.symm
        rw [hLc0, zero_sub] at hsub
        linear_combination hsub
      have hb4 : (9027 : k) * b ^ 4 = 0 := by
        rw [← h25, hN0, mul_zero]
      have h9027 : (9027 : k) ≠ 0 := by norm_num
      exact hb ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp
        ((mul_eq_zero.mp hb4).resolve_left h9027))
    · set L := (6 : k) * a * (5 * a ^ 3 + 48 * b ^ 2) with hL
      set N := (7 : k) * a ^ 6 + 102 * a ^ 3 * b ^ 2 - 27 * b ^ 4 with hN
      have hLc : L * c = N := by
        have : L * c - N = 0 := by
          simp only [hL, hN]
          exact hlin.symm
        linear_combination this
      have hLne : L ≠ 0 := by
        intro hL0
        rcases mul_eq_zero.mp (hL ▸ hL0) with h6a | h48
        · rcases mul_eq_zero.mp h6a with h6 | ha
          · exact (by norm_num : (6 : k) ≠ 0) h6
          · exact ha0 ha
        · exact hcoeff h48
      have hP :
          abc0KapLambdaResultantP a b = 0 := by
        have hid := abc0_L2_kap_is_nine_P a b L N hL hN
        have hkapc :
            (27 : k) * c ^ 2 - 36 * a ^ 2 * c +
                (7 * a ^ 4 - 12 * a * b ^ 2) =
              0 := by
          have : (7 : k) * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 +
              27 * c ^ 2 = 0 := hkap
          linear_combination this
        have : (27 : k) * N ^ 2 - 36 * a ^ 2 * N * L +
            (7 * a ^ 4 - 12 * a * b ^ 2) * L ^ 2 =
            L ^ 2 *
              ((27 : k) * c ^ 2 - 36 * a ^ 2 * c +
                (7 * a ^ 4 - 12 * a * b ^ 2)) := by
          have hN' : N = L * c := hLc.symm
          rw [hN']
          ring
        have h9P : (9 : k) * abc0KapLambdaResultantP a b = 0 := by
          rw [← hid, this]
          simp [hkapc]
        have h9 : (9 : k) ≠ 0 := by norm_num
        exact (mul_eq_zero.mp h9P).resolve_left h9
      have hR : abc0RemaindersResultantR a b = 0 := by
        have ha2 := homiInner
        rcases mul_eq_zero.mp ha2 with h2a | hinner
        · rcases mul_eq_zero.mp h2a with h2 | ha
          · exact (False.elim ((by norm_num : (2 : k) ≠ 0) h2))
          · exact False.elim (ha0 ha)
        · set Lo := (-144 : k) * a ^ 4 + 54 * a * b ^ 2 with hLo
          set No := (34 : k) * a ^ 6 - 111 * a ^ 3 * b ^ 2 - 54 * b ^ 4
            with hNo
          have hinner' : Lo * c + No = 0 := by
            rw [hLo, hNo]
            linear_combination hinner
          have hid := abc0_LoN_plus_NoL a b L N Lo No hL hN hLo hNo
          have : Lo * N + No * L = L * (Lo * c + No) := by
            rw [← hLc]
            ring
          have h6aR : (6 : k) * a * abc0RemaindersResultantR a b = 0 := by
            rw [← hid, this]
            simp [hinner']
          have h6a : (6 : k) * a ≠ 0 :=
            mul_ne_zero (by norm_num) ha0
          exact (mul_eq_zero.mp h6aR).resolve_left h6a
      have hPu : abc0Pu (a ^ 3) (b ^ 2) = 0 := by
        simpa [abc0Pu_of_P] using hP
      have hRu : abc0Ru (a ^ 3) (b ^ 2) = 0 := by
        simpa [abc0Ru_of_R] using hR
      have hW :
          (81 : k) * (b ^ 2) ^ 2 * abc0W (a ^ 3) (b ^ 2) = 0 := by
        have hid := abc0_euclidean_step1 (a ^ 3) (b ^ 2)
        rw [hPu, hRu] at hid
        simpa using hid.symm
      have hb2ne : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
      have hpow : (b ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hb2ne
      have h81b : (81 : k) * (b ^ 2) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) hpow
      have hWz : abc0W (a ^ 3) (b ^ 2) = 0 :=
        (mul_eq_zero.mp hW).resolve_left h81b
      have hQ0 : abc0Q (a ^ 3) (b ^ 2) = 0 := by
        have hid := abc0_euclidean_step2 (a ^ 3) (b ^ 2)
        rw [hRu, hWz] at hid
        have : (2 : k) * b ^ 2 * abc0Q (a ^ 3) (b ^ 2) = 0 := by
          simpa using hid.symm
        have h2b : (2 : k) * b ^ 2 ≠ 0 :=
          mul_ne_zero (by norm_num) hb2ne
        exact (mul_eq_zero.mp this).resolve_left h2b
      have hlin7 :
          (7 : k) * b ^ 2 *
            (211632247 * a ^ 3 + 1953613704 * b ^ 2) =
            0 := by
        have hid := abc0_euclidean_step3 (a ^ 3) (b ^ 2)
        rw [hWz, hQ0] at hid
        simpa using hid.symm
      have h7b : (7 : k) * b ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) hb2ne
      have hlineq :
          (211632247 : k) * a ^ 3 + 1953613704 * b ^ 2 = 0 :=
        (mul_eq_zero.mp hlin7).resolve_left h7b
      have hWline := abc0_W_on_line (a ^ 3) (b ^ 2) hlineq
      have hleft : (211632247 : k) ^ 2 * abc0W (a ^ 3) (b ^ 2) = 0 := by
        simp [hWz]
      rw [hWline] at hleft
      have hC : (32195228840268749220600 : k) ≠ 0 := by norm_num
      have hb4 : (b ^ 2) ^ 2 = 0 :=
        (mul_eq_zero.mp hleft).resolve_left hC
      have hb2 : b ^ 2 = 0 :=
        (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hb4
      exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hb2)

/-- `κ` load face on the `A`–`C₀`–`E₀` cusp. -/
theorem ac0e0_kappa_load_at_cusp (a l : k) :
    l * (a ^ 2 - 4 * (a ^ 2 / 3)) *
        (a ^ 3 - 4 * a * (a ^ 2 / 3) + 16 * (a ^ 3 / 27)) =
      -7 * a ^ 5 * l / 81 := by
  ring

/-- On the `A`–`C₀`–`E₀` triple, `λ` and `ο` cannot drop together with the
`κ` load unless `a = 0` or `l = 0`. -/
theorem ac0e0_tied_leadings_impossible (a c e l : k)
    (ha : a ≠ 0) (hl : l ≠ 0)
    (hlam :
      (7 : k) * a ^ 6 - 63 * a ^ 4 * c + 108 * a ^ 3 * e +
          162 * a ^ 2 * c ^ 2 - 486 * a * c * e - 81 * c ^ 3 +
          729 * e ^ 2 =
        0)
    (homi :
      (a ^ 2 - 3 * c) ^ 2 * (2 * a ^ 3 - 9 * a * c + 27 * e) = 0)
    (hkapLoad :
      l * (a ^ 2 - 4 * c) * (a ^ 3 - 4 * a * c + 16 * e) = 0) :
    False := by
  have hcusp (hsq : a ^ 2 = 3 * c) (hlin : a ^ 3 = 27 * e) : False := by
    have h3 : (3 : k) ≠ 0 := by norm_num
    have h27 : (27 : k) ≠ 0 := by norm_num
    have hc : c = a ^ 2 / 3 := by
      have : c * 3 = a ^ 2 := by
        rw [mul_comm]
        exact hsq.symm
      exact (eq_div_iff_mul_eq h3).mpr this
    have he : e = a ^ 3 / 27 := by
      have : e * 27 = a ^ 3 := by
        rw [mul_comm]
        exact hlin.symm
      exact (eq_div_iff_mul_eq h27).mpr this
    have : l * (a ^ 2 - 4 * c) * (a ^ 3 - 4 * a * c + 16 * e) =
        -7 * a ^ 5 * l / 81 := by
      rw [hc, he]
      exact ac0e0_kappa_load_at_cusp a l
    rw [this] at hkapLoad
    have hnum : (-7 : k) * a ^ 5 * l ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 5 ha)) hl
    have h81 : (81 : k) ≠ 0 := by norm_num
    have hzero : (-7 : k) * a ^ 5 * l = 0 ∨ (81 : k) = 0 :=
      (div_eq_zero_iff (a := (-7 : k) * a ^ 5 * l) (b := 81)).mp hkapLoad
    rcases hzero with hn | hz
    · exact hnum hn
    · exact h81 hz
  rcases mul_eq_zero.mp homi with hsq | hcub
  · have hsq0 : a ^ 2 - 3 * c = 0 :=
      (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hsq
    have hc : a ^ 2 = 3 * c := by linear_combination hsq0
    have hlam' := lambda_ac0e0_of_omicron_factor_square a c e hc
    have hpow : (a ^ 3 - 27 * e) ^ 2 = 0 := by
      rw [← hlam', hlam]
    have hlin : a ^ 3 - 27 * e = 0 :=
      (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hpow
    exact hcusp hc (by linear_combination hlin)
  · have hlam' := lambda_ac0e0_of_omicron_factor_cubic a c e hcub
    have hpow : (3 : k) * (a ^ 2 - 3 * c) ^ 3 = 0 := by
      rw [← hlam', hlam]
    have h3 : (3 : k) ≠ 0 := by norm_num
    have hsq : a ^ 2 - 3 * c = 0 :=
      (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp
        ((mul_eq_zero.mp hpow).resolve_left h3)
    have hc : a ^ 2 = 3 * c := by linear_combination hsq
    have hlam2 := lambda_ac0e0_of_omicron_factor_square a c e hc
    have hlin : a ^ 3 - 27 * e = 0 :=
      (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp (by
        have : (a ^ 3 - 27 * e) ^ 2 = 0 := by
          rw [← hlam2, hlam]
        exact this)
    exact hcusp hc (by linear_combination hlin)


/-- `a μ - (a² - 2 c) κ = 6 U` on the quadruple. -/
def abce0U (a b c : k) : k :=
  a ^ 4 * c - 2 * a ^ 3 * b ^ 2 - 6 * a ^ 2 * c ^ 2 + 9 * c ^ 3

def abce0S (a b c : k) : k :=
  (7 : k) * a ^ 8 - 72 * a ^ 6 * c - 150 * a ^ 5 * b ^ 2 +
    270 * a ^ 4 * c ^ 2 + 360 * a ^ 3 * b ^ 2 * c + 12 * a ^ 2 * b ^ 4 -
    432 * a ^ 2 * c ^ 3 - 54 * a * b ^ 2 * c ^ 2 + 243 * c ^ 4

def abce0T1 (a c : k) : k :=
  a ^ 2 - 3 * c

def abce0T2 (a b c : k) : k :=
  a ^ 6 - 9 * a ^ 4 * c + 17 * a ^ 3 * b ^ 2 + 27 * a ^ 2 * c ^ 2 +
    3 * a * b ^ 2 * c - 27 * c ^ 3

theorem abce0_mu_of_kappa (a b c e : k) :
    a *
          (7 * a ^ 5 - 44 * a ^ 3 * c - 24 * a ^ 2 * b ^ 2 +
            54 * a ^ 2 * e + 63 * a * c ^ 2 + 24 * b ^ 2 * c -
            108 * c * e) -
        (a ^ 2 - 2 * c) *
          (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 54 * a * e +
            27 * c ^ 2) =
      6 * abce0U a b c := by
  simp only [abce0U]
  ring

theorem abce0_lambda_of_kappa (a b c e : k) :
    (4 : k) * a ^ 2 *
          (7 * a ^ 6 - 63 * a ^ 4 * c - 126 * a ^ 3 * b ^ 2 +
            108 * a ^ 3 * e + 162 * a ^ 2 * c ^ 2 +
            324 * a * b ^ 2 * c - 486 * a * c * e + 27 * b ^ 4 -
            243 * b ^ 2 * e - 81 * c ^ 3 + 729 * e ^ 2) -
        (54 * a * e + a ^ 4 - 6 * a * b ^ 2 - 27 * c ^ 2) *
          (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 54 * a * e +
            27 * c ^ 2) =
      3 * abce0S a b c := by
  simp only [abce0S]
  ring

theorem abce0_omicron_of_kappa (a b c e : k) :
    a *
          (4 * a ^ 7 - 42 * a ^ 5 * c - 105 * a ^ 4 * b ^ 2 +
            54 * a ^ 4 * e + 144 * a ^ 3 * c ^ 2 +
            432 * a ^ 2 * b ^ 2 * c - 324 * a ^ 2 * c * e +
            72 * a * b ^ 4 - 324 * a * b ^ 2 * e - 162 * a * c ^ 3 -
            243 * b ^ 2 * c ^ 2 + 486 * c ^ 2 * e) -
        (a ^ 4 - 6 * a ^ 2 * c - 6 * a * b ^ 2 + 9 * c ^ 2) *
          (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 54 * a * e +
            27 * c ^ 2) =
      -3 * abce0T1 a c * abce0T2 a b c := by
  simp only [abce0T1, abce0T2]
  ring

theorem abce0U_at_T1 (a b c : k) (h : a ^ 2 = 3 * c) :
    abce0U a b c = -2 * a ^ 3 * b ^ 2 := by
  have h3 : (3 : k) ≠ 0 := by norm_num
  have hc : c = a ^ 2 / 3 := by
    have : c * 3 = a ^ 2 := by
      rw [mul_comm]
      exact h.symm
    exact (eq_div_iff_mul_eq h3).mpr this
  simp only [abce0U, hc]
  ring

theorem abce0_threeU_add_T2 (a b c : k) :
    (3 : k) * abce0U a b c + abce0T2 a b c =
      a ^ 6 - 6 * a ^ 4 * c + 11 * a ^ 3 * b ^ 2 + 9 * a ^ 2 * c ^ 2 +
        3 * a * b ^ 2 * c := by
  simp only [abce0U, abce0T2]
  ring

end TripleIdentities610

/-! ## Combined faces -/

section TripleCombined610

variable {k : Type*} [Field k] [CharZero k]

/-- Load-free `λ` face on the `A`–`B`–`C₀` triple. -/
def lambdaABC0Combined610 (A B C0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) -
    (5 / 81 : k) • C0 ^ 3

/-- Load-free `λ` face on the `A`–`B`–`E₀` triple. -/
def lambdaABE0Combined610 (A B E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (5 / 243 : k) • B ^ 4 -
    (5 / 27 : k) • (B ^ 2 * E0) +
    (5 / 9 : k) • E0 ^ 2

/-- Load-free `λ` face on the `A`–`C₀`–`E₀` triple. -/
def lambdaAC0E0Combined610 (A C0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (35 / 729 : k) • (A ^ 4 * C0) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (5 / 81 : k) • C0 ^ 3 +
    (5 / 9 : k) • E0 ^ 2

/-- Unique `κ` face `B² D₀`. -/
def kappaB2D0Face610 (B D0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D0)

/-- Unique `κ` face `D₀ E₀`. -/
def kappaD0E0Face610 (D0 E0 : k[X]) : k[X] :=
  (10 / 9 : k) • (D0 * E0)

/-- Unique `κ` face `A C₀ D₀`. -/
def kappaAC0D0Face610 (A C0 D0 : k[X]) : k[X] :=
  (-(10 / 27 : k)) • (A * C0 * D0)

/-- Unique `μ` face `B D₀²`. -/
def muBD02Face610 (B D0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B * D0 ^ 2)

/-- Unique `μ` face `C₀² D₀`. -/
def muC02D0Face610 (C0 D0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C0 ^ 2 * D0)

/-- Load-free raw-tail face on the `A`–`B`–`C₀` triple. -/
def rawABC0Combined610 (A B C0 : k[X]) : k[X] :=
  (-(65 / 19683 : k)) • A ^ 7 +
    (70 / 2187 : k) • (A ^ 5 * C0) +
    (175 / 2187 : k) • (A ^ 4 * B ^ 2) -
    (70 / 729 : k) • (A ^ 3 * C0 ^ 2) -
    (70 / 243 : k) • (A ^ 2 * B ^ 2 * C0) -
    (35 / 729 : k) • (A * B ^ 4) +
    (20 / 243 : k) • (A * C0 ^ 3) +
    (10 / 81 : k) • (B ^ 2 * C0 ^ 2)

/-- Load-free raw-tail face on the `A`–`B`–`E₀` triple. -/
def rawABE0Combined610 (A B E0 : k[X]) : k[X] :=
  (-(65 / 19683 : k)) • A ^ 7 +
    (175 / 2187 : k) • (A ^ 4 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * E0) -
    (35 / 729 : k) • (A * B ^ 4) +
    (20 / 81 : k) • (A * B ^ 2 * E0) -
    (5 / 27 : k) • (A * E0 ^ 2)

end TripleCombined610

/-! ## Rest polynomials -/

section TripleRests610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_two_tr {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_tr {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_tr {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_tr {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

private theorem zero_pow_six_tr {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

private theorem zero_pow_seven_tr {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

/-- `λ` with the `A`–`B`–`C₀` combination deleted. -/
def degreeZeroLambdaNoABC0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (3 / 32 * l : k) • (A * B ^ 3)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * E0)
    + (3 / 32 * l : k) • (A ^ 3 * D0)
    + (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * E0)
    - (3 / 16 * l : k) • (B ^ 2 * D0)
    - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (10 / 27 : k) • (A * C0 * E0)
    - (3 / 8 * l : k) • (A * C0 * D0)
    - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)
    + (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (5 / 9 : k) • E0 ^ 2
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)
    + (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)
    - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

/-- `λ` with the `A`–`B`–`E₀` combination deleted. -/
def degreeZeroLambdaNoABE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  - (35 / 729 : k) • (A ^ 4 * C0)
    - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (20 / 81 : k) • (A * B ^ 2 * C0)
    + (3 / 32 * l : k) • (A * B ^ 3)
    + (10 / 81 : k) • (A ^ 2 * C0 ^ 2)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (3 / 32 * l : k) • (A ^ 3 * D0)
    + (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (5 / 81 : k) • C0 ^ 3
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (3 / 16 * l : k) • (B ^ 2 * D0)
    - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (10 / 27 : k) • (A * C0 * E0)
    - (3 / 8 * l : k) • (A * C0 * D0)
    - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)
    + (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)
    + (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)
    - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

/-- `λ` with the `A`–`C₀`–`E₀` combination deleted. -/
def degreeZeroLambdaNoAC0E0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  - (70 / 729 : k) • (A ^ 3 * B ^ 2)
    - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (5 / 243 : k) • B ^ 4
    + (20 / 81 : k) • (A * B ^ 2 * C0)
    + (3 / 32 * l : k) • (A * B ^ 3)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (3 / 32 * l : k) • (A ^ 3 * D0)
    + (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * E0)
    - (3 / 16 * l : k) • (B ^ 2 * D0)
    - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (3 / 8 * l : k) • (A * C0 * D0)
    - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)
    + (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)
    + (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)
    - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

/-- `λ` with the quadruple combination deleted. -/
def degreeZeroLambdaNoABCE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (3 / 32 * l : k) • (A * B ^ 3)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (3 / 32 * l : k) • (A ^ 3 * D0)
    + (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (3 / 16 * l : k) • (B ^ 2 * D0)
    - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (3 / 8 * l : k) • (A * C0 * D0)
    - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)
    + (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)
    + (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)
    - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

/-- `κ` with the `A`–`B`–`C₀` combination deleted. -/
def degreeZeroKappaNoABC0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  - (3 / 256 * l : k) • A ^ 5
    + (9 / 64 * l : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * D0)
    + (3 / 32 * l : k) • (A ^ 3 * C0)
    + (20 / 243 * alpha : k) • (A ^ 3 * B)
    + (385 / 31104 * beta : k) • A ^ 4
    - (5 / 27 : k) • (B ^ 2 * D0)
    - (3 / 16 * l : k) • (B ^ 2 * C0)
    - (4 / 81 * alpha : k) • B ^ 3
    - (10 / 27 : k) • (A * C0 * D0)
    - (3 / 16 * l : k) • (A * C0 ^ 2)
    - (10 / 27 : k) • (A * B * E0)
    - (3 / 8 * l : k) • (A * B * D0)
    - (8 / 27 * alpha : k) • (A * B * C0)
    - (35 / 432 * beta : k) • (A * B ^ 2)
    - (3 / 16 * l : k) • (A ^ 2 * E0)
    - (4 / 27 * alpha : k) • (A ^ 2 * D0)
    - (35 / 432 * beta : k) • (A ^ 2 * C0)
    + (35 / 1296 * delta : k) • A ^ 3
    + (10 / 9 : k) • (D0 * E0)
    + (3 / 8 * l : k) • D0 ^ 2
    + (3 / 4 * l : k) • (C0 * E0)
    + (4 / 9 * alpha : k) • (C0 * D0)
    + (7 / 72 * beta : k) • C0 ^ 2
    + (4 / 9 * alpha : k) • (B * E0)
    + (7 / 36 * beta : k) • (B * D0)
    - (5 / 72 * delta : k) • B ^ 2
    + (7 / 36 * beta : k) • (A * E0)
    - (5 / 36 * delta : k) • (A * C0)
    - (2 / 9 * epsilon : k) • (A * B)
    - (1 / 8 * zeta : k) • A ^ 2
    + (5 / 6 * delta : k) • E0
    + (2 / 3 * epsilon : k) • D0
    + (1 / 2 * zeta : k) • C0
    + (1 / 3 * eta : k) • B
    + (1 / 6 * theta : k) • A

/-- `κ` with the `A`–`B`–`E₀` combination deleted. -/
def degreeZeroKappaNoABE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  - (3 / 256 * l : k) • A ^ 5
    + (20 / 81 : k) • (A ^ 2 * B * C0)
    + (9 / 64 * l : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * D0)
    + (3 / 32 * l : k) • (A ^ 3 * C0)
    + (20 / 243 * alpha : k) • (A ^ 3 * B)
    + (385 / 31104 * beta : k) • A ^ 4
    - (5 / 27 : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * D0)
    - (3 / 16 * l : k) • (B ^ 2 * C0)
    - (4 / 81 * alpha : k) • B ^ 3
    - (10 / 27 : k) • (A * C0 * D0)
    - (3 / 16 * l : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * D0)
    - (8 / 27 * alpha : k) • (A * B * C0)
    - (35 / 432 * beta : k) • (A * B ^ 2)
    - (3 / 16 * l : k) • (A ^ 2 * E0)
    - (4 / 27 * alpha : k) • (A ^ 2 * D0)
    - (35 / 432 * beta : k) • (A ^ 2 * C0)
    + (35 / 1296 * delta : k) • A ^ 3
    + (10 / 9 : k) • (D0 * E0)
    + (3 / 8 * l : k) • D0 ^ 2
    + (3 / 4 * l : k) • (C0 * E0)
    + (4 / 9 * alpha : k) • (C0 * D0)
    + (7 / 72 * beta : k) • C0 ^ 2
    + (4 / 9 * alpha : k) • (B * E0)
    + (7 / 36 * beta : k) • (B * D0)
    - (5 / 72 * delta : k) • B ^ 2
    + (7 / 36 * beta : k) • (A * E0)
    - (5 / 36 * delta : k) • (A * C0)
    - (2 / 9 * epsilon : k) • (A * B)
    - (1 / 8 * zeta : k) • A ^ 2
    + (5 / 6 * delta : k) • E0
    + (2 / 3 * epsilon : k) • D0
    + (1 / 2 * zeta : k) • C0
    + (1 / 3 * eta : k) • B
    + (1 / 6 * theta : k) • A

/-- `κ` with unique `B² D₀` deleted. -/
def degreeZeroKappaNoB2D0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B)
    - (3 / 256 * l : k) • A ^ 5
    + (20 / 243 : k) • (A * B ^ 3)
    + (20 / 81 : k) • (A ^ 2 * B * C0)
    + (9 / 64 * l : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * D0)
    + (3 / 32 * l : k) • (A ^ 3 * C0)
    + (20 / 243 * alpha : k) • (A ^ 3 * B)
    + (385 / 31104 * beta : k) • A ^ 4
    - (5 / 27 : k) • (B * C0 ^ 2)
    - (3 / 16 * l : k) • (B ^ 2 * C0)
    - (4 / 81 * alpha : k) • B ^ 3
    - (10 / 27 : k) • (A * C0 * D0)
    - (3 / 16 * l : k) • (A * C0 ^ 2)
    - (10 / 27 : k) • (A * B * E0)
    - (3 / 8 * l : k) • (A * B * D0)
    - (8 / 27 * alpha : k) • (A * B * C0)
    - (35 / 432 * beta : k) • (A * B ^ 2)
    - (3 / 16 * l : k) • (A ^ 2 * E0)
    - (4 / 27 * alpha : k) • (A ^ 2 * D0)
    - (35 / 432 * beta : k) • (A ^ 2 * C0)
    + (35 / 1296 * delta : k) • A ^ 3
    + (10 / 9 : k) • (D0 * E0)
    + (3 / 8 * l : k) • D0 ^ 2
    + (3 / 4 * l : k) • (C0 * E0)
    + (4 / 9 * alpha : k) • (C0 * D0)
    + (7 / 72 * beta : k) • C0 ^ 2
    + (4 / 9 * alpha : k) • (B * E0)
    + (7 / 36 * beta : k) • (B * D0)
    - (5 / 72 * delta : k) • B ^ 2
    + (7 / 36 * beta : k) • (A * E0)
    - (5 / 36 * delta : k) • (A * C0)
    - (2 / 9 * epsilon : k) • (A * B)
    - (1 / 8 * zeta : k) • A ^ 2
    + (5 / 6 * delta : k) • E0
    + (2 / 3 * epsilon : k) • D0
    + (1 / 2 * zeta : k) • C0
    + (1 / 3 * eta : k) • B
    + (1 / 6 * theta : k) • A

/-- `κ` with unique `D₀ E₀` deleted. -/
def degreeZeroKappaNoD0E0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B)
    - (3 / 256 * l : k) • A ^ 5
    + (20 / 243 : k) • (A * B ^ 3)
    + (20 / 81 : k) • (A ^ 2 * B * C0)
    + (9 / 64 * l : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * D0)
    + (3 / 32 * l : k) • (A ^ 3 * C0)
    + (20 / 243 * alpha : k) • (A ^ 3 * B)
    + (385 / 31104 * beta : k) • A ^ 4
    - (5 / 27 : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * D0)
    - (3 / 16 * l : k) • (B ^ 2 * C0)
    - (4 / 81 * alpha : k) • B ^ 3
    - (10 / 27 : k) • (A * C0 * D0)
    - (3 / 16 * l : k) • (A * C0 ^ 2)
    - (10 / 27 : k) • (A * B * E0)
    - (3 / 8 * l : k) • (A * B * D0)
    - (8 / 27 * alpha : k) • (A * B * C0)
    - (35 / 432 * beta : k) • (A * B ^ 2)
    - (3 / 16 * l : k) • (A ^ 2 * E0)
    - (4 / 27 * alpha : k) • (A ^ 2 * D0)
    - (35 / 432 * beta : k) • (A ^ 2 * C0)
    + (35 / 1296 * delta : k) • A ^ 3
    + (3 / 8 * l : k) • D0 ^ 2
    + (3 / 4 * l : k) • (C0 * E0)
    + (4 / 9 * alpha : k) • (C0 * D0)
    + (7 / 72 * beta : k) • C0 ^ 2
    + (4 / 9 * alpha : k) • (B * E0)
    + (7 / 36 * beta : k) • (B * D0)
    - (5 / 72 * delta : k) • B ^ 2
    + (7 / 36 * beta : k) • (A * E0)
    - (5 / 36 * delta : k) • (A * C0)
    - (2 / 9 * epsilon : k) • (A * B)
    - (1 / 8 * zeta : k) • A ^ 2
    + (5 / 6 * delta : k) • E0
    + (2 / 3 * epsilon : k) • D0
    + (1 / 2 * zeta : k) • C0
    + (1 / 3 * eta : k) • B
    + (1 / 6 * theta : k) • A

/-- `κ` with unique `A C₀ D₀` deleted. -/
def degreeZeroKappaNoAC0D0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B)
    - (3 / 256 * l : k) • A ^ 5
    + (20 / 243 : k) • (A * B ^ 3)
    + (20 / 81 : k) • (A ^ 2 * B * C0)
    + (9 / 64 * l : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * D0)
    + (3 / 32 * l : k) • (A ^ 3 * C0)
    + (20 / 243 * alpha : k) • (A ^ 3 * B)
    + (385 / 31104 * beta : k) • A ^ 4
    - (5 / 27 : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * D0)
    - (3 / 16 * l : k) • (B ^ 2 * C0)
    - (4 / 81 * alpha : k) • B ^ 3
    - (3 / 16 * l : k) • (A * C0 ^ 2)
    - (10 / 27 : k) • (A * B * E0)
    - (3 / 8 * l : k) • (A * B * D0)
    - (8 / 27 * alpha : k) • (A * B * C0)
    - (35 / 432 * beta : k) • (A * B ^ 2)
    - (3 / 16 * l : k) • (A ^ 2 * E0)
    - (4 / 27 * alpha : k) • (A ^ 2 * D0)
    - (35 / 432 * beta : k) • (A ^ 2 * C0)
    + (35 / 1296 * delta : k) • A ^ 3
    + (10 / 9 : k) • (D0 * E0)
    + (3 / 8 * l : k) • D0 ^ 2
    + (3 / 4 * l : k) • (C0 * E0)
    + (4 / 9 * alpha : k) • (C0 * D0)
    + (7 / 72 * beta : k) • C0 ^ 2
    + (4 / 9 * alpha : k) • (B * E0)
    + (7 / 36 * beta : k) • (B * D0)
    - (5 / 72 * delta : k) • B ^ 2
    + (7 / 36 * beta : k) • (A * E0)
    - (5 / 36 * delta : k) • (A * C0)
    - (2 / 9 * epsilon : k) • (A * B)
    - (1 / 8 * zeta : k) • A ^ 2
    + (5 / 6 * delta : k) • E0
    + (2 / 3 * epsilon : k) • D0
    + (1 / 2 * zeta : k) • C0
    + (1 / 3 * eta : k) • B
    + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_ABC0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaABC0Combined610 A B C0 +
        degreeZeroLambdaNoABC0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaABC0Combined610,
    degreeZeroLambdaNoABC0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_ABE0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaABE0Combined610 A B E0 +
        degreeZeroLambdaNoABE0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaABE0Combined610,
    degreeZeroLambdaNoABE0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_AC0E0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaAC0E0Combined610 A C0 E0 +
        degreeZeroLambdaNoAC0E0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaAC0E0Combined610,
    degreeZeroLambdaNoAC0E0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_ABC0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaABC0Combined610 A B C0 +
        degreeZeroKappaNoABC0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaABC0Combined610,
    degreeZeroKappaNoABC0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_ABE0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaABE0Combined610 A B E0 +
        degreeZeroKappaNoABE0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaABE0Combined610,
    degreeZeroKappaNoABE0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_B2D0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaB2D0Face610 B D0 +
        degreeZeroKappaNoB2D0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaB2D0Face610,
    degreeZeroKappaNoB2D0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_D0E0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaD0E0Face610 D0 E0 +
        degreeZeroKappaNoD0E0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaD0E0Face610,
    degreeZeroKappaNoD0E0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoABC0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABC0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoABC0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoABC0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_tr, zero_pow_three_tr,
    zero_pow_four_tr, zero_pow_five_tr, zero_pow_six_tr]
  compute_degree
  have hE1 : 2 * E0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoABE0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoABE0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hE, hC, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoABE0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_tr, zero_pow_three_tr,
    zero_pow_four_tr, zero_pow_five_tr, zero_pow_six_tr]
  compute_degree
  have hC1 : 3 * C0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hC
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoAC0E0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AC0E0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoAC0E0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hC, hE, hB, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoAC0E0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_tr, zero_pow_three_tr,
    zero_pow_four_tr, zero_pow_five_tr, zero_pow_six_tr]
  compute_degree
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hB
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoABC0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABC0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoABC0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * A.natDegree + B.natDegree := by
  rcases hcone with ⟨hApos, htie, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroKappaNoABC0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_tr, zero_pow_three_tr,
    zero_pow_four_tr, zero_pow_five_tr]
  compute_degree
  have hE1 : 2 * E0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoABE0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoABE0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * A.natDegree + B.natDegree := by
  rcases hcone with ⟨hApos, htie, hE, hC, hD1, hD2, hD3⟩
  simp only [degreeZeroKappaNoABE0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_tr, zero_pow_three_tr,
    zero_pow_four_tr, zero_pow_five_tr]
  compute_degree
  have hC1 : 3 * C0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hC
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

/-- `μ` with the unique `B D₀²` face deleted. -/
def degreeZeroMuNoBD02Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (5 / 1024 * l : k) • A ^ 6
    + (35 / 1458 : k) • (A ^ 5 * B)
    - (77 / 15552 * beta : k) • A ^ 5
    - (10 / 243 * alpha : k) • (A ^ 4 * B)
    - (11 / 256 * l : k) • (A ^ 4 * C0)
    - (25 / 729 : k) • (A ^ 4 * D0)
    - (35 / 3456 * delta : k) • A ^ 4
    - (3 / 32 * l : k) • (A ^ 3 * B ^ 2)
    - (110 / 729 : k) • (A ^ 3 * B * C0)
    + (35 / 972 * beta : k) • (A ^ 3 * C0)
    + (14 / 243 * alpha : k) • (A ^ 3 * D0)
    + (1 / 16 * l : k) • (A ^ 3 * E0)
    + (1 / 24 * zeta : k) • A ^ 3
    - (20 / 243 : k) • (A ^ 2 * B ^ 3)
    + (35 / 576 * beta : k) • (A ^ 2 * B ^ 2)
    + (16 / 81 * alpha : k) • (A ^ 2 * B * C0)
    + (7 / 32 * l : k) • (A ^ 2 * B * D0)
    + (5 / 27 : k) • (A ^ 2 * B * E0)
    + (1 / 9 * epsilon : k) • (A ^ 2 * B)
    + (7 / 64 * l : k) • (A ^ 2 * C0 ^ 2)
    + (5 / 27 : k) • (A ^ 2 * C0 * D0)
    + (25 / 432 * delta : k) • (A ^ 2 * C0)
    - (7 / 144 * beta : k) • (A ^ 2 * E0)
    - (1 / 24 * theta : k) • A ^ 2
    + (2 / 27 * alpha : k) • (A * B ^ 3)
    + (1 / 4 * l : k) • (A * B ^ 2 * C0)
    + (35 / 162 : k) • (A * B ^ 2 * D0)
    + (5 / 72 * delta : k) • (A * B ^ 2)
    + (35 / 162 : k) • (A * B * C0 ^ 2)
    - (7 / 54 * beta : k) • (A * B * D0)
    - (2 / 9 * alpha : k) • (A * B * E0)
    - (1 / 6 * eta : k) • (A * B)
    - (7 / 108 * beta : k) • (A * C0 ^ 2)
    - (2 / 9 * alpha : k) • (A * C0 * D0)
    - (1 / 4 * l : k) • (A * C0 * E0)
    - (1 / 6 * zeta : k) • (A * C0)
    - (1 / 8 * l : k) • (A * D0 ^ 2)
    - (5 / 27 : k) • (A * D0 * E0)
    - (1 / 9 * epsilon : k) • (A * D0)
    + (3 / 128 * l : k) • B ^ 4
    + (20 / 243 : k) • (B ^ 3 * C0)
    - (35 / 432 * beta : k) • (B ^ 2 * C0)
    - (4 / 27 * alpha : k) • (B ^ 2 * D0)
    - (3 / 16 * l : k) • (B ^ 2 * E0)
    - (1 / 8 * zeta : k) • B ^ 2
    - (4 / 27 * alpha : k) • (B * C0 ^ 2)
    - (3 / 8 * l : k) • (B * C0 * D0)
    - (10 / 27 : k) • (B * C0 * E0)
    - (2 / 9 * epsilon : k) • (B * C0)
    - (5 / 36 * delta : k) • (B * D0)
    - (1 / 16 * l : k) • C0 ^ 3
    - (5 / 27 : k) • (C0 ^ 2 * D0)
    - (5 / 72 * delta : k) • C0 ^ 2
    + (7 / 36 * beta : k) • (C0 * E0)
    + (1 / 6 * theta : k) • C0
    + (7 / 72 * beta : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (D0 * E0)
    + (1 / 3 * eta : k) • D0
    + (3 / 8 * l : k) • E0 ^ 2
    + (1 / 2 * zeta : k) • E0

/-- `μ` with the unique `C₀² D₀` face deleted. -/
def degreeZeroMuNoC02D0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (5 / 1024 * l : k) • A ^ 6
    + (35 / 1458 : k) • (A ^ 5 * B)
    - (77 / 15552 * beta : k) • A ^ 5
    - (10 / 243 * alpha : k) • (A ^ 4 * B)
    - (11 / 256 * l : k) • (A ^ 4 * C0)
    - (25 / 729 : k) • (A ^ 4 * D0)
    - (35 / 3456 * delta : k) • A ^ 4
    - (3 / 32 * l : k) • (A ^ 3 * B ^ 2)
    - (110 / 729 : k) • (A ^ 3 * B * C0)
    + (35 / 972 * beta : k) • (A ^ 3 * C0)
    + (14 / 243 * alpha : k) • (A ^ 3 * D0)
    + (1 / 16 * l : k) • (A ^ 3 * E0)
    + (1 / 24 * zeta : k) • A ^ 3
    - (20 / 243 : k) • (A ^ 2 * B ^ 3)
    + (35 / 576 * beta : k) • (A ^ 2 * B ^ 2)
    + (16 / 81 * alpha : k) • (A ^ 2 * B * C0)
    + (7 / 32 * l : k) • (A ^ 2 * B * D0)
    + (5 / 27 : k) • (A ^ 2 * B * E0)
    + (1 / 9 * epsilon : k) • (A ^ 2 * B)
    + (7 / 64 * l : k) • (A ^ 2 * C0 ^ 2)
    + (5 / 27 : k) • (A ^ 2 * C0 * D0)
    + (25 / 432 * delta : k) • (A ^ 2 * C0)
    - (7 / 144 * beta : k) • (A ^ 2 * E0)
    - (1 / 24 * theta : k) • A ^ 2
    + (2 / 27 * alpha : k) • (A * B ^ 3)
    + (1 / 4 * l : k) • (A * B ^ 2 * C0)
    + (35 / 162 : k) • (A * B ^ 2 * D0)
    + (5 / 72 * delta : k) • (A * B ^ 2)
    + (35 / 162 : k) • (A * B * C0 ^ 2)
    - (7 / 54 * beta : k) • (A * B * D0)
    - (2 / 9 * alpha : k) • (A * B * E0)
    - (1 / 6 * eta : k) • (A * B)
    - (7 / 108 * beta : k) • (A * C0 ^ 2)
    - (2 / 9 * alpha : k) • (A * C0 * D0)
    - (1 / 4 * l : k) • (A * C0 * E0)
    - (1 / 6 * zeta : k) • (A * C0)
    - (1 / 8 * l : k) • (A * D0 ^ 2)
    - (5 / 27 : k) • (A * D0 * E0)
    - (1 / 9 * epsilon : k) • (A * D0)
    + (3 / 128 * l : k) • B ^ 4
    + (20 / 243 : k) • (B ^ 3 * C0)
    - (35 / 432 * beta : k) • (B ^ 2 * C0)
    - (4 / 27 * alpha : k) • (B ^ 2 * D0)
    - (3 / 16 * l : k) • (B ^ 2 * E0)
    - (1 / 8 * zeta : k) • B ^ 2
    - (4 / 27 * alpha : k) • (B * C0 ^ 2)
    - (3 / 8 * l : k) • (B * C0 * D0)
    - (10 / 27 : k) • (B * C0 * E0)
    - (2 / 9 * epsilon : k) • (B * C0)
    - (5 / 27 : k) • (B * D0 ^ 2)
    - (5 / 36 * delta : k) • (B * D0)
    - (1 / 16 * l : k) • C0 ^ 3
    - (5 / 72 * delta : k) • C0 ^ 2
    + (7 / 36 * beta : k) • (C0 * E0)
    + (1 / 6 * theta : k) • C0
    + (7 / 72 * beta : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (D0 * E0)
    + (1 / 3 * eta : k) • D0
    + (3 / 8 * l : k) • E0 ^ 2
    + (1 / 2 * zeta : k) • E0

/-- Raw tail with the `A`–`B`–`C₀` combination deleted. -/
def degreeZeroRawFourthTailNoABC0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  - (35 / 729 : k) • (A ^ 4 * E0)
    - (140 / 729 : k) • (A ^ 3 * B * D0)
    + (20 / 81 : k) • (A ^ 2 * C0 * E0)
    + (10 / 81 : k) • (A ^ 2 * D0 ^ 2)
    + (20 / 81 : k) • (A * B ^ 2 * E0)
    + (40 / 81 : k) • (A * B * C0 * D0)
    - (5 / 27 : k) • (A * E0 ^ 2)
    + (20 / 243 : k) • (B ^ 3 * D0)
    - (10 / 27 : k) • (B * D0 * E0)
    - (5 / 27 : k) • (C0 ^ 2 * E0)
    - (5 / 27 : k) • (C0 * D0 ^ 2)
    + (21 / 512 * l : k) • (A ^ 5 * B)
    - (15 / 256 * l : k) • (A ^ 4 * D0)
    - (15 / 64 * l : k) • (A ^ 3 * B * C0)
    - (15 / 128 * l : k) • (A ^ 2 * B ^ 3)
    + (9 / 32 * l : k) • (A ^ 2 * B * E0)
    + (9 / 32 * l : k) • (A ^ 2 * C0 * D0)
    + (9 / 32 * l : k) • (A * B ^ 2 * D0)
    + (9 / 32 * l : k) • (A * B * C0 ^ 2)
    - (3 / 8 * l : k) • (A * D0 * E0)
    + (3 / 32 * l : k) • (B ^ 3 * C0)
    - (3 / 8 * l : k) • (B * C0 * E0)
    - (3 / 16 * l : k) • (B * D0 ^ 2)
    - (3 / 16 * l : k) • (C0 ^ 2 * D0)
    + (44 / 6561 * alpha : k) • A ^ 6
    - (40 / 729 * alpha : k) • (A ^ 4 * C0)
    - (80 / 729 * alpha : k) • (A ^ 3 * B ^ 2)
    + (20 / 243 * alpha : k) • (A ^ 3 * E0)
    + (20 / 81 * alpha : k) • (A ^ 2 * B * D0)
    + (10 / 81 * alpha : k) • (A ^ 2 * C0 ^ 2)
    + (20 / 81 * alpha : k) • (A * B ^ 2 * C0)
    - (8 / 27 * alpha : k) • (A * C0 * E0)
    - (4 / 27 * alpha : k) • (A * D0 ^ 2)
    + (5 / 243 * alpha : k) • B ^ 4
    - (4 / 27 * alpha : k) • (B ^ 2 * E0)
    - (8 / 27 * alpha : k) • (B * C0 * D0)
    - (4 / 81 * alpha : k) • C0 ^ 3
    + (2 / 9 * alpha : k) • E0 ^ 2
    - (6545 / 186624 * beta : k) • (A ^ 4 * B)
    + (385 / 7776 * beta : k) • (A ^ 3 * D0)
    + (385 / 2592 * beta : k) • (A ^ 2 * B * C0)
    + (385 / 7776 * beta : k) • (A * B ^ 3)
    - (35 / 216 * beta : k) • (A * B * E0)
    - (35 / 216 * beta : k) • (A * C0 * D0)
    - (35 / 432 * beta : k) • (B ^ 2 * D0)
    - (35 / 432 * beta : k) • (B * C0 ^ 2)
    + (7 / 36 * beta : k) • (D0 * E0)
    - (455 / 7776 * delta : k) • (A ^ 3 * B)
    + (35 / 432 * delta : k) • (A ^ 2 * D0)
    + (35 / 216 * delta : k) • (A * B * C0)
    + (35 / 1296 * delta : k) • B ^ 3
    - (5 / 36 * delta : k) • (B * E0)
    - (5 / 36 * delta : k) • (C0 * D0)
    - (7 / 243 * epsilon : k) • A ^ 4
    + (4 / 27 * epsilon : k) • (A ^ 2 * C0)
    + (4 / 27 * epsilon : k) • (A * B ^ 2)
    - (2 / 9 * epsilon : k) • (A * E0)
    - (2 / 9 * epsilon : k) • (B * D0)
    - (1 / 9 * epsilon : k) • C0 ^ 2
    + (5 / 81 * eta : k) • A ^ 3
    - (2 / 9 * eta : k) • (A * C0)
    - (1 / 9 * eta : k) • B ^ 2
    + (1 / 3 * eta : k) • E0
    - (5 / 36 * theta : k) • (A * B)
    + (1 / 6 * theta : k) • D0
    + (3 / 16 * zeta : k) • (A ^ 2 * B)
    - (1 / 4 * zeta : k) • (A * D0)
    - (1 / 4 * zeta : k) • (B * C0)

/-- Raw tail with the `A`–`B`–`E₀` combination deleted. -/
def degreeZeroRawFourthTailNoABE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (70 / 2187 : k) • (A ^ 5 * C0)
    - (140 / 729 : k) • (A ^ 3 * B * D0)
    - (70 / 729 : k) • (A ^ 3 * C0 ^ 2)
    - (70 / 243 : k) • (A ^ 2 * B ^ 2 * C0)
    + (20 / 81 : k) • (A ^ 2 * C0 * E0)
    + (10 / 81 : k) • (A ^ 2 * D0 ^ 2)
    + (40 / 81 : k) • (A * B * C0 * D0)
    + (20 / 243 : k) • (A * C0 ^ 3)
    + (20 / 243 : k) • (B ^ 3 * D0)
    + (10 / 81 : k) • (B ^ 2 * C0 ^ 2)
    - (10 / 27 : k) • (B * D0 * E0)
    - (5 / 27 : k) • (C0 ^ 2 * E0)
    - (5 / 27 : k) • (C0 * D0 ^ 2)
    + (21 / 512 * l : k) • (A ^ 5 * B)
    - (15 / 256 * l : k) • (A ^ 4 * D0)
    - (15 / 64 * l : k) • (A ^ 3 * B * C0)
    - (15 / 128 * l : k) • (A ^ 2 * B ^ 3)
    + (9 / 32 * l : k) • (A ^ 2 * B * E0)
    + (9 / 32 * l : k) • (A ^ 2 * C0 * D0)
    + (9 / 32 * l : k) • (A * B ^ 2 * D0)
    + (9 / 32 * l : k) • (A * B * C0 ^ 2)
    - (3 / 8 * l : k) • (A * D0 * E0)
    + (3 / 32 * l : k) • (B ^ 3 * C0)
    - (3 / 8 * l : k) • (B * C0 * E0)
    - (3 / 16 * l : k) • (B * D0 ^ 2)
    - (3 / 16 * l : k) • (C0 ^ 2 * D0)
    + (44 / 6561 * alpha : k) • A ^ 6
    - (40 / 729 * alpha : k) • (A ^ 4 * C0)
    - (80 / 729 * alpha : k) • (A ^ 3 * B ^ 2)
    + (20 / 243 * alpha : k) • (A ^ 3 * E0)
    + (20 / 81 * alpha : k) • (A ^ 2 * B * D0)
    + (10 / 81 * alpha : k) • (A ^ 2 * C0 ^ 2)
    + (20 / 81 * alpha : k) • (A * B ^ 2 * C0)
    - (8 / 27 * alpha : k) • (A * C0 * E0)
    - (4 / 27 * alpha : k) • (A * D0 ^ 2)
    + (5 / 243 * alpha : k) • B ^ 4
    - (4 / 27 * alpha : k) • (B ^ 2 * E0)
    - (8 / 27 * alpha : k) • (B * C0 * D0)
    - (4 / 81 * alpha : k) • C0 ^ 3
    + (2 / 9 * alpha : k) • E0 ^ 2
    - (6545 / 186624 * beta : k) • (A ^ 4 * B)
    + (385 / 7776 * beta : k) • (A ^ 3 * D0)
    + (385 / 2592 * beta : k) • (A ^ 2 * B * C0)
    + (385 / 7776 * beta : k) • (A * B ^ 3)
    - (35 / 216 * beta : k) • (A * B * E0)
    - (35 / 216 * beta : k) • (A * C0 * D0)
    - (35 / 432 * beta : k) • (B ^ 2 * D0)
    - (35 / 432 * beta : k) • (B * C0 ^ 2)
    + (7 / 36 * beta : k) • (D0 * E0)
    - (455 / 7776 * delta : k) • (A ^ 3 * B)
    + (35 / 432 * delta : k) • (A ^ 2 * D0)
    + (35 / 216 * delta : k) • (A * B * C0)
    + (35 / 1296 * delta : k) • B ^ 3
    - (5 / 36 * delta : k) • (B * E0)
    - (5 / 36 * delta : k) • (C0 * D0)
    - (7 / 243 * epsilon : k) • A ^ 4
    + (4 / 27 * epsilon : k) • (A ^ 2 * C0)
    + (4 / 27 * epsilon : k) • (A * B ^ 2)
    - (2 / 9 * epsilon : k) • (A * E0)
    - (2 / 9 * epsilon : k) • (B * D0)
    - (1 / 9 * epsilon : k) • C0 ^ 2
    + (5 / 81 * eta : k) • A ^ 3
    - (2 / 9 * eta : k) • (A * C0)
    - (1 / 9 * eta : k) • B ^ 2
    + (1 / 3 * eta : k) • E0
    - (5 / 36 * theta : k) • (A * B)
    + (1 / 6 * theta : k) • D0
    + (3 / 16 * zeta : k) • (A ^ 2 * B)
    - (1 / 4 * zeta : k) • (A * D0)
    - (1 / 4 * zeta : k) • (B * C0)

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial610_eq_BD02_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0 =
      muBD02Face610 B D0 +
        degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0 := by
  simp only [degreeZeroMuPolynomial610, muBD02Face610, degreeZeroMuNoBD02Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial610_eq_C02D0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0 =
      muC02D0Face610 C0 D0 +
        degreeZeroMuNoC02D0Polynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0 := by
  simp only [degreeZeroMuPolynomial610, muC02D0Face610, degreeZeroMuNoC02D0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroRawFourthTailPolynomial610_eq_ABC0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 =
      rawABC0Combined610 A B C0 +
        degreeZeroRawFourthTailNoABC0Polynomial610 l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroRawFourthTailPolynomial610, rawABC0Combined610,
    degreeZeroRawFourthTailNoABC0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroRawFourthTailPolynomial610_eq_ABE0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 =
      rawABE0Combined610 A B E0 +
        degreeZeroRawFourthTailNoABE0Polynomial610 l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroRawFourthTailPolynomial610, rawABE0Combined610,
    degreeZeroRawFourthTailNoABE0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedADB
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBRatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htie, hA, hC, hE, hD2, hD3⟩
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hE
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedBBD
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBBDRatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htie, hA, hC, hE, hAD, hA2⟩
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hE
  have hAD1 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hAD
  have hA21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hA2
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedADBBD
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBBDRatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htieAD, htieBD, hA, hC, hE, hA2⟩
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hE
  have hA21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hA2
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedADBE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBERatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htieE, htieAD, hA, hC, hA2, hBD⟩
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hA21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hA2
  have hBD1 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hBD
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedBBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBBDERatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htieE, htieBD, hA, hC, hAD, hA2⟩
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hAD1 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hAD
  have hA21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hA2
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedADBBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBBDERatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htieE, htieAD, htieBD, hA, hC, hA2⟩
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hA21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hA2
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoC02D0_natDegree_lt_of_MixedADC
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADCRatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoC02D0Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      2 * C0.natDegree + D0.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, htie, hA, hB, hE, hA2, hBD⟩
  simp only [degreeZeroMuNoC02D0Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 3 * C0.natDegree := Nat.succ_le_of_lt hA
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C0.natDegree := Nat.succ_le_of_lt hB
  have hE1 : 2 * E0.natDegree + 1 ≤ 3 * C0.natDegree := Nat.succ_le_of_lt hE
  have hA21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      3 * C0.natDegree := Nat.succ_le_of_lt hA2
  have hBD1 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      3 * C0.natDegree := Nat.succ_le_of_lt hBD
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoC02D0_natDegree_lt_of_MixedADCE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADCERatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoC02D0Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      2 * C0.natDegree + D0.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, htieE, htieAD, hA, hB, hA2, hBD⟩
  simp only [degreeZeroMuNoC02D0Polynomial610, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_tr, zero_pow_three_tr, zero_pow_four_tr, zero_pow_five_tr,
    zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 3 * C0.natDegree := Nat.succ_le_of_lt hA
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C0.natDegree := Nat.succ_le_of_lt hB
  have hA21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      3 * C0.natDegree := Nat.succ_le_of_lt hA2
  have hBD1 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      3 * C0.natDegree := Nat.succ_le_of_lt hBD
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroRawFourthTailNoABC0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABC0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroRawFourthTailNoABC0Polynomial610 l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hC, hE, hD1, hD2, hD3⟩
  have hAB : 2 * B.natDegree = 3 * A.natDegree := htie.symm
  obtain ⟨m, hAm, hBm⟩ := exists_param_two_three hAB
  have hCeq : C0.natDegree = 2 * A.natDegree := by
    have : 3 * C0.natDegree = 3 * (2 * A.natDegree) := by
      rw [hC]
      omega
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) this
  simp only [hAm, hBm, hCeq] at hApos hE hD1 hD2 hD3
  simp only [degreeZeroRawFourthTailNoABC0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_tr, zero_pow_three_tr,
    zero_pow_four_tr, zero_pow_five_tr, zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  simp only [hAm, hBm, hCeq, max_lt_iff]
  have hE1 : 2 * E0.natDegree + 1 ≤ 12 * m := Nat.succ_le_of_lt (by omega)
  have hD11 : 2 * m + 2 * D0.natDegree + 1 ≤ 12 * m :=
    Nat.succ_le_of_lt (by omega)
  have hD21 : 4 * m + 3 * m + D0.natDegree + 1 ≤ 12 * m :=
    Nat.succ_le_of_lt (by omega)
  have hD31 : 3 * m + 4 * m + D0.natDegree + 1 ≤ 12 * m :=
    Nat.succ_le_of_lt (by omega)
  all_goals omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroRawFourthTailNoABE0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroRawFourthTailNoABE0Polynomial610 l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hE, hC, hD1, hD2, hD3⟩
  have hAB : 2 * B.natDegree = 3 * A.natDegree := htie.symm
  obtain ⟨m, hAm, hBm⟩ := exists_param_two_three hAB
  have hEeq : E0.natDegree = 3 * A.natDegree := by
    have : 2 * E0.natDegree = 2 * (3 * A.natDegree) := by
      rw [hE]
      omega
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this
  simp only [hAm, hBm, hEeq] at hApos hC hD1 hD2 hD3
  simp only [degreeZeroRawFourthTailNoABE0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_tr, zero_pow_three_tr,
    zero_pow_four_tr, zero_pow_five_tr, zero_pow_six_tr, zero_pow_seven_tr]
  compute_degree
  simp only [hAm, hBm, hEeq, max_lt_iff]
  have hC1 : 3 * C0.natDegree + 1 ≤ 12 * m := Nat.succ_le_of_lt (by omega)
  have hD11 : 2 * m + 2 * D0.natDegree + 1 ≤ 12 * m :=
    Nat.succ_le_of_lt (by omega)
  have hD21 : 4 * m + 3 * m + D0.natDegree + 1 ≤ 12 * m :=
    Nat.succ_le_of_lt (by omega)
  have hD31 : 3 * m + C0.natDegree + D0.natDegree + 1 ≤ 12 * m :=
    Nat.succ_le_of_lt (by omega)
  all_goals omega

end TripleRests610

/-! ## Scale identities for leftover triples -/

section TripleScale610

variable {k : Type*} [Field k] [CharZero k]


theorem lambdaABC0_scale (a b c : k) :
    (35 / 6561 : k) * a ^ 6 - (70 / 729 : k) * (a ^ 3 * b ^ 2) -
        (35 / 729 : k) * (a ^ 4 * c) + (5 / 243 : k) * b ^ 4 +
        (20 / 81 : k) * (a * b ^ 2 * c) + (10 / 81 : k) * (a ^ 2 * c ^ 2) -
        (5 / 81 : k) * c ^ 3 =
      (5 / 6561 : k) *
        (7 * a ^ 6 - 63 * a ^ 4 * c - 126 * a ^ 3 * b ^ 2 +
          162 * a ^ 2 * c ^ 2 + 324 * a * b ^ 2 * c + 27 * b ^ 4 -
          81 * c ^ 3) := by
  ring

theorem kappaABC0_scale (a b c : k) :
    (-(35 / 729 : k)) * (a ^ 4 * b) + (20 / 243 : k) * (a * b ^ 3) +
        (20 / 81 : k) * (a ^ 2 * b * c) - (5 / 27 : k) * (b * c ^ 2) =
      (-(5 / 729 : k)) * b *
        (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2) := by
  ring

theorem raw_abc0_of_lambda_kappa (a b c : k) :
    (-(65 / 19683 : k)) * a ^ 7 + (70 / 2187 : k) * (a ^ 5 * c) +
        (175 / 2187 : k) * (a ^ 4 * b ^ 2) - (70 / 729 : k) * (a ^ 3 * c ^ 2) -
        (70 / 243 : k) * (a ^ 2 * b ^ 2 * c) - (35 / 729 : k) * (a * b ^ 4) +
        (20 / 243 : k) * (a * c ^ 3) + (10 / 81 : k) * (b ^ 2 * c ^ 2) +
      (b / 6) *
          ((-(35 / 729 : k)) * (a ^ 4 * b) + (20 / 243 : k) * (a * b ^ 3) +
            (20 / 81 : k) * (a ^ 2 * b * c) - (5 / 27 : k) * (b * c ^ 2)) +
        (a / 3) *
          ((35 / 6561 : k) * a ^ 6 - (70 / 729 : k) * (a ^ 3 * b ^ 2) -
            (35 / 729 : k) * (a ^ 4 * c) + (5 / 243 : k) * b ^ 4 +
            (20 / 81 : k) * (a * b ^ 2 * c) +
            (10 / 81 : k) * (a ^ 2 * c ^ 2) - (5 / 81 : k) * c ^ 3) =
      (-(5 / 13122 : k)) *
        (4 * a ^ 7 - 42 * a ^ 5 * c - 105 * a ^ 4 * b ^ 2 +
          144 * a ^ 3 * c ^ 2 + 432 * a ^ 2 * b ^ 2 * c + 72 * a * b ^ 4 -
          162 * a * c ^ 3 - 243 * b ^ 2 * c ^ 2) := by
  ring

theorem lambdaABE0_scale (a b e : k) :
    (35 / 6561 : k) * a ^ 6 - (70 / 729 : k) * (a ^ 3 * b ^ 2) +
        (20 / 243 : k) * (a ^ 3 * e) + (5 / 243 : k) * b ^ 4 -
        (5 / 27 : k) * (b ^ 2 * e) + (5 / 9 : k) * e ^ 2 =
      (5 / 6561 : k) *
        (7 * a ^ 6 - 126 * a ^ 3 * b ^ 2 + 108 * a ^ 3 * e + 27 * b ^ 4 -
          243 * b ^ 2 * e + 729 * e ^ 2) := by
  ring

theorem kappaABE0_scale (a b e : k) :
    (-(35 / 729 : k)) * (a ^ 4 * b) + (20 / 243 : k) * (a * b ^ 3) -
        (10 / 27 : k) * (a * b * e) =
      (-(5 / 729 : k)) * (a * b) * (7 * a ^ 3 - 12 * b ^ 2 + 54 * e) := by
  ring

theorem raw_abe0_of_lambda_kappa (a b e : k) :
    (-(65 / 19683 : k)) * a ^ 7 + (175 / 2187 : k) * (a ^ 4 * b ^ 2) -
        (35 / 729 : k) * (a ^ 4 * e) - (35 / 729 : k) * (a * b ^ 4) +
        (20 / 81 : k) * (a * b ^ 2 * e) - (5 / 27 : k) * (a * e ^ 2) +
      (b / 6) *
          ((-(35 / 729 : k)) * (a ^ 4 * b) + (20 / 243 : k) * (a * b ^ 3) -
            (10 / 27 : k) * (a * b * e)) +
        (a / 3) *
          ((35 / 6561 : k) * a ^ 6 - (70 / 729 : k) * (a ^ 3 * b ^ 2) +
            (20 / 243 : k) * (a ^ 3 * e) + (5 / 243 : k) * b ^ 4 -
            (5 / 27 : k) * (b ^ 2 * e) + (5 / 9 : k) * e ^ 2) =
      (-(5 / 13122 : k)) * a *
        (4 * a ^ 6 - 105 * a ^ 3 * b ^ 2 + 54 * a ^ 3 * e + 72 * b ^ 4 -
          324 * b ^ 2 * e) := by
  ring

end TripleScale610

/-! ## Combined-face degrees -/

section TripleCombinedDegrees610

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 16000000 in
theorem lambdaABC0Combined610_natDegree_eq_of_coeff_ne
    {A B C0 : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C0 ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hCtie : 3 * C0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) -
            (35 / 729 : k) * (A.leadingCoeff ^ 4 * C0.leadingCoeff) +
              (5 / 243 : k) * B.leadingCoeff ^ 4 +
                (20 / 81 : k) *
                    (A.leadingCoeff * B.leadingCoeff ^ 2 * C0.leadingCoeff) +
                  (10 / 81 : k) *
                      (A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2) -
                    (5 / 81 : k) * C0.leadingCoeff ^ 3 ≠
        0) :
    (lambdaABC0Combined610 A B C0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hC3 : (C0 ^ 3).natDegree = 3 * C0.natDegree := natDegree_pow C0 3
  have hA3B2 :
      (A ^ 3 * B ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hB), natDegree_pow,
      natDegree_pow]
    omega
  have hA4C :
      (A ^ 4 * C0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hC, natDegree_pow]
    omega
  have hAB2C :
      (A * B ^ 2 * C0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hC, natDegree_mul hA
      (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hA2C2 :
      (A ^ 2 * C0 ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hC), natDegree_pow,
      natDegree_pow]
    omega
  have htop :
      (lambdaABC0Combined610 A B C0).coeff (6 * A.natDegree) ≠ 0 := by
    simp only [lambdaABC0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 3 * B ^ 2).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 := by
      rw [← hA3B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h3 : (A ^ 4 * C0).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 4 * C0.leadingCoeff := by
      rw [← hA4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h4 : (B ^ 4).coeff (6 * A.natDegree) = B.leadingCoeff ^ 4 := by
      have : 4 * B.natDegree = 6 * A.natDegree := by omega
      rw [← this, ← hB4, coeff_natDegree, leadingCoeff_pow]
    have h5 : (A * B ^ 2 * C0).coeff (6 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 2 * C0.leadingCoeff := by
      rw [← hAB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow]
    have h6 : (A ^ 2 * C0 ^ 2).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 := by
      rw [← hA2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h7 : (C0 ^ 3).coeff (6 * A.natDegree) = C0.leadingCoeff ^ 3 := by
      have : 3 * C0.natDegree = 6 * A.natDegree := hCtie
      rw [← this, ← hC3, coeff_natDegree, leadingCoeff_pow]
    simpa [h1, h2, h3, h4, h5, h6, h7] using hcoeff
  have hle :
      (lambdaABC0Combined610 A B C0).natDegree ≤ 6 * A.natDegree := by
    simp only [lambdaABC0Combined610]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
            · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
              · exact (natDegree_smul_le610 _ _).trans hA6.le
              · exact (natDegree_smul_le610 _ _).trans hA3B2.le
            · exact (natDegree_smul_le610 _ _).trans hA4C.le
          · exact (natDegree_smul_le610 _ _).trans (hB4.trans (by omega)).le
        · exact (natDegree_smul_le610 _ _).trans hAB2C.le
      · exact (natDegree_smul_le610 _ _).trans hA2C2.le
    · exact (natDegree_smul_le610 _ _).trans (hC3.trans hCtie).le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem kappaABC0Combined610_natDegree_eq_of_coeff_ne
    {A B C0 : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C0 ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hCtie : 3 * C0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (-(35 / 729 : k)) * (A.leadingCoeff ^ 4 * B.leadingCoeff) +
          (20 / 243 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) +
            (20 / 81 : k) *
                (A.leadingCoeff ^ 2 * B.leadingCoeff * C0.leadingCoeff) -
              (5 / 27 : k) * (B.leadingCoeff * C0.leadingCoeff ^ 2) ≠
        0) :
    (kappaABC0Combined610 A B C0).natDegree =
      4 * A.natDegree + B.natDegree := by
  have hA4B :
      (A ^ 4 * B).natDegree = 4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hB, natDegree_pow]
  have hAB3 :
      (A * B ^ 3).natDegree = 4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
    omega
  have hA2BC :
      (A ^ 2 * B * C0).natDegree = 4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) hC,
      natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
    omega
  have hBC2 :
      (B * C0 ^ 2).natDegree = 4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hC), natDegree_pow]
    omega
  have htop :
      (kappaABC0Combined610 A B C0).coeff
          (4 * A.natDegree + B.natDegree) ≠
        0 := by
    simp only [kappaABC0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 4 * B).coeff (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff ^ 4 * B.leadingCoeff := by
      rw [← hA4B, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2 : (A * B ^ 3).coeff (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 3 := by
      rw [← hAB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3 : (A ^ 2 * B * C0).coeff (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff ^ 2 * B.leadingCoeff * C0.leadingCoeff := by
      rw [← hA2BC, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow]
    have h4 : (B * C0 ^ 2).coeff (4 * A.natDegree + B.natDegree) =
        B.leadingCoeff * C0.leadingCoeff ^ 2 := by
      rw [← hBC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    simpa [h1, h2, h3, h4] using hcoeff
  have hle :
      (kappaABC0Combined610 A B C0).natDegree ≤
        4 * A.natDegree + B.natDegree := by
    simp only [kappaABC0Combined610]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact (natDegree_smul_le610 _ _).trans hA4B.le
        · exact (natDegree_smul_le610 _ _).trans hAB3.le
      · exact (natDegree_smul_le610 _ _).trans hA2BC.le
    · exact (natDegree_smul_le610 _ _).trans hBC2.le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem rawABC0Combined610_natDegree_eq_of_coeff_ne
    {A B C0 : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C0 ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hCtie : 3 * C0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (-(65 / 19683 : k)) * A.leadingCoeff ^ 7 +
          (70 / 2187 : k) * (A.leadingCoeff ^ 5 * C0.leadingCoeff) +
            (175 / 2187 : k) *
                (A.leadingCoeff ^ 4 * B.leadingCoeff ^ 2) -
              (70 / 729 : k) *
                  (A.leadingCoeff ^ 3 * C0.leadingCoeff ^ 2) -
                (70 / 243 : k) *
                    (A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 *
                      C0.leadingCoeff) -
                  (35 / 729 : k) *
                      (A.leadingCoeff * B.leadingCoeff ^ 4) +
                    (20 / 243 : k) *
                        (A.leadingCoeff * C0.leadingCoeff ^ 3) +
                      (10 / 81 : k) *
                          (B.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2) ≠
        0) :
    (rawABC0Combined610 A B C0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA5C :
      (A ^ 5 * C0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 5 hA) hC, natDegree_pow]
    omega
  have hA4B2 :
      (A ^ 4 * B ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) (pow_ne_zero 2 hB), natDegree_pow,
      natDegree_pow]
    omega
  have hA3C2 :
      (A ^ 3 * C0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hC), natDegree_pow,
      natDegree_pow]
    omega
  have hA2B2C :
      (A ^ 2 * B ^ 2 * C0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)) hC,
      natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hB), natDegree_pow,
      natDegree_pow]
    omega
  have hAB4 :
      (A * B ^ 4).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 4 hB), natDegree_pow]
    omega
  have hAC3 :
      (A * C0 ^ 3).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hC), natDegree_pow]
    omega
  have hB2C2 :
      (B ^ 2 * C0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hB) (pow_ne_zero 2 hC), natDegree_pow,
      natDegree_pow]
    omega
  have htop :
      (rawABC0Combined610 A B C0).coeff (7 * A.natDegree) ≠ 0 := by
    simp only [rawABC0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 5 * C0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 5 * C0.leadingCoeff := by
      rw [← hA5C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3 : (A ^ 4 * B ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * B.leadingCoeff ^ 2 := by
      rw [← hA4B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h4 : (A ^ 3 * C0 ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 3 * C0.leadingCoeff ^ 2 := by
      rw [← hA3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h5 : (A ^ 2 * B ^ 2 * C0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * C0.leadingCoeff := by
      rw [← hA2B2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow, leadingCoeff_pow]
    have h6 : (A * B ^ 4).coeff (7 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 4 := by
      rw [← hAB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h7 : (A * C0 ^ 3).coeff (7 * A.natDegree) =
        A.leadingCoeff * C0.leadingCoeff ^ 3 := by
      rw [← hAC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h8 : (B ^ 2 * C0 ^ 2).coeff (7 * A.natDegree) =
        B.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 := by
      rw [← hB2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    simpa [h1, h2, h3, h4, h5, h6, h7, h8] using hcoeff
  have hle :
      (rawABC0Combined610 A B C0).natDegree ≤ 7 * A.natDegree := by
    simp only [rawABC0Combined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
            · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
              · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
                · exact (natDegree_smul_le610 _ _).trans hA7.le
                · exact (natDegree_smul_le610 _ _).trans hA5C.le
              · exact (natDegree_smul_le610 _ _).trans hA4B2.le
            · exact (natDegree_smul_le610 _ _).trans hA3C2.le
          · exact (natDegree_smul_le610 _ _).trans hA2B2C.le
        · exact (natDegree_smul_le610 _ _).trans hAB4.le
      · exact (natDegree_smul_le610 _ _).trans hAC3.le
    · exact (natDegree_smul_le610 _ _).trans hB2C2.le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem lambdaABE0Combined610_natDegree_eq_of_coeff_ne
    {A B E0 : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hEtie : 2 * E0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            (20 / 243 : k) * (A.leadingCoeff ^ 3 * E0.leadingCoeff) +
              (5 / 243 : k) * B.leadingCoeff ^ 4 -
                (5 / 27 : k) * (B.leadingCoeff ^ 2 * E0.leadingCoeff) +
                  (5 / 9 : k) * E0.leadingCoeff ^ 2 ≠
        0) :
    (lambdaABE0Combined610 A B E0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hE2 : (E0 ^ 2).natDegree = 2 * E0.natDegree := natDegree_pow E0 2
  have hA3B2 :
      (A ^ 3 * B ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hB), natDegree_pow,
      natDegree_pow]
    omega
  have hA3E :
      (A ^ 3 * E0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) hE, natDegree_pow]
    omega
  have hB2E :
      (B ^ 2 * E0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hB) hE, natDegree_pow]
    omega
  have htop :
      (lambdaABE0Combined610 A B E0).coeff (6 * A.natDegree) ≠ 0 := by
    simp only [lambdaABE0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 3 * B ^ 2).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 := by
      rw [← hA3B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h3 : (A ^ 3 * E0).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [← hA3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h4 : (B ^ 4).coeff (6 * A.natDegree) = B.leadingCoeff ^ 4 := by
      have : 4 * B.natDegree = 6 * A.natDegree := by omega
      rw [← this, ← hB4, coeff_natDegree, leadingCoeff_pow]
    have h5 : (B ^ 2 * E0).coeff (6 * A.natDegree) =
        B.leadingCoeff ^ 2 * E0.leadingCoeff := by
      rw [← hB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h6 : (E0 ^ 2).coeff (6 * A.natDegree) = E0.leadingCoeff ^ 2 := by
      rw [← hEtie, ← hE2, coeff_natDegree, leadingCoeff_pow]
    simpa [h1, h2, h3, h4, h5, h6] using hcoeff
  have hle :
      (lambdaABE0Combined610 A B E0).natDegree ≤ 6 * A.natDegree := by
    simp only [lambdaABE0Combined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
            · exact (natDegree_smul_le610 _ _).trans hA6.le
            · exact (natDegree_smul_le610 _ _).trans hA3B2.le
          · exact (natDegree_smul_le610 _ _).trans hA3E.le
        · exact (natDegree_smul_le610 _ _).trans (hB4.trans (by omega)).le
      · exact (natDegree_smul_le610 _ _).trans hB2E.le
    · exact (natDegree_smul_le610 _ _).trans (hE2.trans hEtie).le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem kappaABE0Combined610_natDegree_eq_of_coeff_ne
    {A B E0 : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hEtie : 2 * E0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (-(35 / 729 : k)) * (A.leadingCoeff ^ 4 * B.leadingCoeff) +
          (20 / 243 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) -
            (10 / 27 : k) *
                (A.leadingCoeff * B.leadingCoeff * E0.leadingCoeff) ≠
        0) :
    (kappaABE0Combined610 A B E0).natDegree =
      4 * A.natDegree + B.natDegree := by
  have hA4B :
      (A ^ 4 * B).natDegree = 4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hB, natDegree_pow]
  have hAB3 :
      (A * B ^ 3).natDegree = 4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
    omega
  have hABE :
      (A * B * E0).natDegree = 4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) hE, natDegree_mul hA hB]
    omega
  have htop :
      (kappaABE0Combined610 A B E0).coeff
          (4 * A.natDegree + B.natDegree) ≠
        0 := by
    simp only [kappaABE0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 4 * B).coeff (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff ^ 4 * B.leadingCoeff := by
      rw [← hA4B, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2 : (A * B ^ 3).coeff (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 3 := by
      rw [← hAB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3 : (A * B * E0).coeff (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff * B.leadingCoeff * E0.leadingCoeff := by
      rw [← hABE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
    simpa [h1, h2, h3] using hcoeff
  have hle :
      (kappaABE0Combined610 A B E0).natDegree ≤
        4 * A.natDegree + B.natDegree := by
    simp only [kappaABE0Combined610]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_smul_le610 _ _).trans hA4B.le
      · exact (natDegree_smul_le610 _ _).trans hAB3.le
    · exact (natDegree_smul_le610 _ _).trans hABE.le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem rawABE0Combined610_natDegree_eq_of_coeff_ne
    {A B E0 : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hEtie : 2 * E0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (-(65 / 19683 : k)) * A.leadingCoeff ^ 7 +
          (175 / 2187 : k) * (A.leadingCoeff ^ 4 * B.leadingCoeff ^ 2) -
            (35 / 729 : k) * (A.leadingCoeff ^ 4 * E0.leadingCoeff) -
              (35 / 729 : k) * (A.leadingCoeff * B.leadingCoeff ^ 4) +
                (20 / 81 : k) *
                    (A.leadingCoeff * B.leadingCoeff ^ 2 * E0.leadingCoeff) -
                  (5 / 27 : k) * (A.leadingCoeff * E0.leadingCoeff ^ 2) ≠
        0) :
    (rawABE0Combined610 A B E0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA4B2 :
      (A ^ 4 * B ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) (pow_ne_zero 2 hB), natDegree_pow,
      natDegree_pow]
    omega
  have hA4E :
      (A ^ 4 * E0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hE, natDegree_pow]
    omega
  have hAB4 :
      (A * B ^ 4).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 4 hB), natDegree_pow]
    omega
  have hAB2E :
      (A * B ^ 2 * E0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hE,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hAE2 :
      (A * E0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hE), natDegree_pow]
    omega
  have htop :
      (rawABE0Combined610 A B E0).coeff (7 * A.natDegree) ≠ 0 := by
    simp only [rawABE0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 4 * B ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * B.leadingCoeff ^ 2 := by
      rw [← hA4B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h3 : (A ^ 4 * E0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * E0.leadingCoeff := by
      rw [← hA4E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h4 : (A * B ^ 4).coeff (7 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 4 := by
      rw [← hAB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h5 : (A * B ^ 2 * E0).coeff (7 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 2 * E0.leadingCoeff := by
      rw [← hAB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow]
    have h6 : (A * E0 ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [← hAE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    simpa [h1, h2, h3, h4, h5, h6] using hcoeff
  have hle :
      (rawABE0Combined610 A B E0).natDegree ≤ 7 * A.natDegree := by
    simp only [rawABE0Combined610]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
            · exact (natDegree_smul_le610 _ _).trans hA7.le
            · exact (natDegree_smul_le610 _ _).trans hA4B2.le
          · exact (natDegree_smul_le610 _ _).trans hA4E.le
        · exact (natDegree_smul_le610 _ _).trans hAB4.le
      · exact (natDegree_smul_le610 _ _).trans hAB2E.le
    · exact (natDegree_smul_le610 _ _).trans hAE2.le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

end TripleCombinedDegrees610

/-! ## Unique-`μ` mixed-`D₀` kills -/

section UniqueMuKills610

variable {k : Type*} [Field k] [CharZero k]

theorem mu_BD02_impossible_of_MixedADB
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBRatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedADB l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_BD02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, _⟩
  omega

theorem mu_BD02_impossible_of_MixedBBD
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBBDRatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedBBD l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_BD02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, _⟩
  omega

theorem mu_BD02_impossible_of_MixedADBBD
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBBDRatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedADBBD l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_BD02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, _⟩
  omega

theorem mu_BD02_impossible_of_MixedADBE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBERatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedADBE l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_BD02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, _⟩
  omega

theorem mu_BD02_impossible_of_MixedBBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBBDERatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedBBDE l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_BD02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, _⟩
  omega

theorem mu_BD02_impossible_of_MixedADBBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBBDERatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedADBBDE l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_BD02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, _⟩
  omega

theorem mu_C02D0_impossible_of_MixedADC
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADCRatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hCne : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muC02D0Face610 C0 D0).natDegree =
        2 * C0.natDegree + D0.natDegree := by
    simp only [muC02D0Face610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hDne,
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoC02D0_natDegree_lt_of_MixedADC l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_C02D0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, _⟩
  omega

theorem mu_C02D0_impossible_of_MixedADCE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADCERatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hCne : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muC02D0Face610 C0 D0).natDegree =
        2 * C0.natDegree + D0.natDegree := by
    simp only [muC02D0Face610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hDne,
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoC02D0_natDegree_lt_of_MixedADCE l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hcone
  rw [degreeZeroMuPolynomial610_eq_C02D0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, _⟩
  omega

end UniqueMuKills610

/-! ## Triple polynomial kills -/

section TriplePolyKills610

variable {k : Type*} [Field k] [CharZero k]


theorem lambda_ABC0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABC0RatioTieCone610 A B C0 D0 E0)
    (hkapDeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0)
    (hlamDeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0)
    (homiDeg :
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    have : B.natDegree = 0 := by simp [hB0]
    rcases hcone with ⟨hApos, htie, _⟩
    omega
  have hCne : C0 ≠ 0 := by
    intro hC0
    have : C0.natDegree = 0 := by simp [hC0]
    rcases hcone with ⟨hApos, htie, hC, _⟩
    omega
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2.1
  have hCtie : 3 * C0.natDegree = 6 * A.natDegree := hcone.2.2.1
  set a := A.leadingCoeff
  set b := B.leadingCoeff
  set c := C0.leadingCoeff
  have hb0 : b ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  by_cases hlamDrop :
      (35 / 6561 : k) * a ^ 6 - (70 / 729 : k) * (a ^ 3 * b ^ 2) -
          (35 / 729 : k) * (a ^ 4 * c) + (5 / 243 : k) * b ^ 4 +
            (20 / 81 : k) * (a * b ^ 2 * c) +
              (10 / 81 : k) * (a ^ 2 * c ^ 2) - (5 / 81 : k) * c ^ 3 =
        0
  · by_cases hkapDrop :
        (-(35 / 729 : k)) * (a ^ 4 * b) + (20 / 243 : k) * (a * b ^ 3) +
            (20 / 81 : k) * (a ^ 2 * b * c) - (5 / 27 : k) * (b * c ^ 2) =
          0
    · by_cases hrawDrop :
          (-(65 / 19683 : k)) * a ^ 7 + (70 / 2187 : k) * (a ^ 5 * c) +
              (175 / 2187 : k) * (a ^ 4 * b ^ 2) -
                (70 / 729 : k) * (a ^ 3 * c ^ 2) -
                  (70 / 243 : k) * (a ^ 2 * b ^ 2 * c) -
                    (35 / 729 : k) * (a * b ^ 4) +
                      (20 / 243 : k) * (a * c ^ 3) +
                        (10 / 81 : k) * (b ^ 2 * c ^ 2) =
            0
      · have hlamForm :
            (7 : k) * a ^ 6 - 63 * a ^ 4 * c - 126 * a ^ 3 * b ^ 2 +
                162 * a ^ 2 * c ^ 2 + 324 * a * b ^ 2 * c + 27 * b ^ 4 -
                81 * c ^ 3 =
              0 := by
          have hsc := lambdaABC0_scale a b c
          have h5 : (5 / 6561 : k) ≠ 0 :=
            div_ne_zero (by norm_num) (by norm_num)
          have : (5 / 6561 : k) *
              (7 * a ^ 6 - 63 * a ^ 4 * c - 126 * a ^ 3 * b ^ 2 +
                162 * a ^ 2 * c ^ 2 + 324 * a * b ^ 2 * c + 27 * b ^ 4 -
                81 * c ^ 3) =
              0 := by
            rw [← hsc]
            exact hlamDrop
          exact (mul_eq_zero.mp this).resolve_left h5
        have hkapInner :
            (7 : k) * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2 =
              0 := by
          have hsc := kappaABC0_scale a b c
          have hfac : (-(5 / 729 : k)) * b ≠ 0 :=
            mul_ne_zero
              (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))) hb0
          have : (-(5 / 729 : k)) * b *
              (7 * a ^ 4 - 36 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2) =
              0 := by
            rw [← hsc]
            exact hkapDrop
          exact (mul_eq_zero.mp this).resolve_left hfac
        have homiForm :
            (4 : k) * a ^ 7 - 42 * a ^ 5 * c - 105 * a ^ 4 * b ^ 2 +
                144 * a ^ 3 * c ^ 2 + 432 * a ^ 2 * b ^ 2 * c +
                72 * a * b ^ 4 - 162 * a * c ^ 3 - 243 * b ^ 2 * c ^ 2 =
              0 := by
          have hid := raw_abc0_of_lambda_kappa a b c
          have : (-(5 / 13122 : k)) *
              (4 * a ^ 7 - 42 * a ^ 5 * c - 105 * a ^ 4 * b ^ 2 +
                144 * a ^ 3 * c ^ 2 + 432 * a ^ 2 * b ^ 2 * c +
                72 * a * b ^ 4 - 162 * a * c ^ 3 - 243 * b ^ 2 * c ^ 2) =
              0 := by
            rw [← hid, hlamDrop, hkapDrop, hrawDrop]
            simp
          have hsc : (-(5 / 13122 : k)) ≠ 0 :=
            neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
          exact (mul_eq_zero.mp this).resolve_left hsc
        exact abc0_tied_leadings_impossible a b c hb0 hkapInner hlamForm
          homiForm
      · have hcomb :=
          rawABC0Combined610_natDegree_eq_of_coeff_ne hAne hBne hCne htie
            hCtie hrawDrop
        have hrawRest :=
          degreeZeroRawFourthTailNoABC0_natDegree_lt l alpha beta delta
            epsilon zeta eta theta A B C0 D0 E0 hcone
        have hAlam :
            ((1 / 3 : k) • (A *
                degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
                  zeta eta theta A B C0 D0 E0)).natDegree <
              7 * A.natDegree := by
          have hmul :=
            natDegree_mul_of_natDegree_eq_zero A
              (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
                eta theta A B C0 D0 E0) hlamDeg
          have hsm :=
            natDegree_smul_le610 (1 / 3 : k)
              (A * degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
                zeta eta theta A B C0 D0 E0)
          rcases hcone with ⟨hApos, _⟩
          omega
        have hBkap :
            ((1 / 6 : k) • (B *
                degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
                  eta theta A B C0 D0 E0)).natDegree <
              7 * A.natDegree := by
          have hmul :=
            natDegree_mul_of_natDegree_eq_zero B
              (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
                eta theta A B C0 D0 E0) hkapDeg
          have hsm :=
            natDegree_smul_le610 (1 / 6 : k)
              (B * degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                zeta eta theta A B C0 D0 E0)
          rcases hcone with ⟨hApos, htie', _⟩
          omega
        have homiEq :
            degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta
                eta theta A B C0 D0 E0 =
              rawABC0Combined610 A B C0 +
                (degreeZeroRawFourthTailNoABC0Polynomial610 l alpha beta
                    delta epsilon zeta eta theta A B C0 D0 E0 +
                  ((1 / 6 : k) • (B *
                      degreeZeroKappaPolynomial610 l alpha beta delta
                        epsilon zeta eta theta A B C0 D0 E0) +
                    (1 / 3 : k) • (A *
                        degreeZeroLambdaPolynomial610 l alpha beta delta
                          epsilon zeta eta theta A B C0 D0 E0))) := by
          simp only [degreeZeroOmicronPolynomial610]
          rw [degreeZeroRawFourthTailPolynomial610_eq_ABC0_add_rest]
          abel
        have hrestSum :=
          natDegree_add_lt610 hrawRest (natDegree_add_lt610 hBkap hAlam)
        rw [homiEq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
          hcomb] at homiDeg
        rcases hcone with ⟨hApos, _⟩
        omega
    · have hcomb :=
        kappaABC0Combined610_natDegree_eq_of_coeff_ne hAne hBne hCne htie
          hCtie hkapDrop
      have hrest :=
        degreeZeroKappaNoABC0_natDegree_lt l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 hcone
      rw [degreeZeroKappaPolynomial610_eq_ABC0_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
        hcomb] at hkapDeg
      rcases hcone with ⟨hApos, htie', _⟩
      omega
  · have hcomb :=
      lambdaABC0Combined610_natDegree_eq_of_coeff_ne hAne hBne hCne htie
        hCtie hlamDrop
    have hrest :=
      degreeZeroLambdaNoABC0_natDegree_lt l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 hcone
    rw [degreeZeroLambdaPolynomial610_eq_ABC0_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
      hcomb] at hlamDeg
    rcases hcone with ⟨hApos, _⟩
    omega

theorem lambda_ABE0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABE0RatioTieCone610 A B C0 D0 E0)
    (hkapDeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0)
    (hlamDeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0)
    (homiDeg :
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    have : B.natDegree = 0 := by simp [hB0]
    rcases hcone with ⟨hApos, htie, _⟩
    omega
  have hEne : E0 ≠ 0 := by
    intro hE0
    have : E0.natDegree = 0 := by simp [hE0]
    rcases hcone with ⟨hApos, htie, hE, _⟩
    omega
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2.1
  have hEtie : 2 * E0.natDegree = 6 * A.natDegree := hcone.2.2.1
  set a := A.leadingCoeff
  set b := B.leadingCoeff
  set e := E0.leadingCoeff
  have hb0 : b ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  by_cases hlamDrop :
      (35 / 6561 : k) * a ^ 6 - (70 / 729 : k) * (a ^ 3 * b ^ 2) +
          (20 / 243 : k) * (a ^ 3 * e) + (5 / 243 : k) * b ^ 4 -
            (5 / 27 : k) * (b ^ 2 * e) + (5 / 9 : k) * e ^ 2 =
        0
  · by_cases hkapDrop :
        (-(35 / 729 : k)) * (a ^ 4 * b) + (20 / 243 : k) * (a * b ^ 3) -
            (10 / 27 : k) * (a * b * e) =
          0
    · by_cases hrawDrop :
          (-(65 / 19683 : k)) * a ^ 7 +
              (175 / 2187 : k) * (a ^ 4 * b ^ 2) -
                (35 / 729 : k) * (a ^ 4 * e) -
                  (35 / 729 : k) * (a * b ^ 4) +
                    (20 / 81 : k) * (a * b ^ 2 * e) -
                      (5 / 27 : k) * (a * e ^ 2) =
            0
      · have hlamForm :
            (7 : k) * a ^ 6 - 126 * a ^ 3 * b ^ 2 + 108 * a ^ 3 * e +
                27 * b ^ 4 - 243 * b ^ 2 * e + 729 * e ^ 2 =
              0 := by
          have hsc := lambdaABE0_scale a b e
          have h5 : (5 / 6561 : k) ≠ 0 :=
            div_ne_zero (by norm_num) (by norm_num)
          have : (5 / 6561 : k) *
              (7 * a ^ 6 - 126 * a ^ 3 * b ^ 2 + 108 * a ^ 3 * e +
                27 * b ^ 4 - 243 * b ^ 2 * e + 729 * e ^ 2) =
              0 := by
            rw [← hsc]
            exact hlamDrop
          exact (mul_eq_zero.mp this).resolve_left h5
        have hkapInner :
            (7 : k) * a ^ 3 - 12 * b ^ 2 + 54 * e = 0 := by
          have hsc := kappaABE0_scale a b e
          have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hAne
          have hfac : (-(5 / 729 : k)) * (a * b) ≠ 0 :=
            mul_ne_zero
              (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num)))
              (mul_ne_zero ha0 hb0)
          have : (-(5 / 729 : k)) * (a * b) *
              (7 * a ^ 3 - 12 * b ^ 2 + 54 * e) =
              0 := by
            rw [← hsc]
            exact hkapDrop
          exact (mul_eq_zero.mp this).resolve_left hfac
        have homiForm :
            (4 : k) * a ^ 6 - 105 * a ^ 3 * b ^ 2 + 54 * a ^ 3 * e +
                72 * b ^ 4 - 324 * b ^ 2 * e =
              0 := by
          have hid := raw_abe0_of_lambda_kappa a b e
          have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hAne
          have : (-(5 / 13122 : k)) * a *
              (4 * a ^ 6 - 105 * a ^ 3 * b ^ 2 + 54 * a ^ 3 * e +
                72 * b ^ 4 - 324 * b ^ 2 * e) =
              0 := by
            rw [← hid, hlamDrop, hkapDrop, hrawDrop]
            simp
          have hsc : (-(5 / 13122 : k)) * a ≠ 0 :=
            mul_ne_zero
              (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))) ha0
          exact (mul_eq_zero.mp this).resolve_left hsc
        exact abe0_tied_leadings_impossible a b e hb0 hkapInner hlamForm
          homiForm
      · have hcomb :=
          rawABE0Combined610_natDegree_eq_of_coeff_ne hAne hBne hEne htie
            hEtie hrawDrop
        have hrawRest :=
          degreeZeroRawFourthTailNoABE0_natDegree_lt l alpha beta delta
            epsilon zeta eta theta A B C0 D0 E0 hcone
        have hAlam :
            ((1 / 3 : k) • (A *
                degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
                  zeta eta theta A B C0 D0 E0)).natDegree <
              7 * A.natDegree := by
          have hmul :=
            natDegree_mul_of_natDegree_eq_zero A
              (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
                eta theta A B C0 D0 E0) hlamDeg
          have hsm :=
            natDegree_smul_le610 (1 / 3 : k)
              (A * degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
                zeta eta theta A B C0 D0 E0)
          rcases hcone with ⟨hApos, _⟩
          omega
        have hBkap :
            ((1 / 6 : k) • (B *
                degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
                  eta theta A B C0 D0 E0)).natDegree <
              7 * A.natDegree := by
          have hmul :=
            natDegree_mul_of_natDegree_eq_zero B
              (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
                eta theta A B C0 D0 E0) hkapDeg
          have hsm :=
            natDegree_smul_le610 (1 / 6 : k)
              (B * degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                zeta eta theta A B C0 D0 E0)
          rcases hcone with ⟨hApos, htie', _⟩
          omega
        have homiEq :
            degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta
                eta theta A B C0 D0 E0 =
              rawABE0Combined610 A B E0 +
                (degreeZeroRawFourthTailNoABE0Polynomial610 l alpha beta
                    delta epsilon zeta eta theta A B C0 D0 E0 +
                  ((1 / 6 : k) • (B *
                      degreeZeroKappaPolynomial610 l alpha beta delta
                        epsilon zeta eta theta A B C0 D0 E0) +
                    (1 / 3 : k) • (A *
                        degreeZeroLambdaPolynomial610 l alpha beta delta
                          epsilon zeta eta theta A B C0 D0 E0))) := by
          simp only [degreeZeroOmicronPolynomial610]
          rw [degreeZeroRawFourthTailPolynomial610_eq_ABE0_add_rest]
          abel
        have hrestSum :=
          natDegree_add_lt610 hrawRest (natDegree_add_lt610 hBkap hAlam)
        rw [homiEq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
          hcomb] at homiDeg
        rcases hcone with ⟨hApos, _⟩
        omega
    · have hcomb :=
        kappaABE0Combined610_natDegree_eq_of_coeff_ne hAne hBne hEne htie
          hEtie hkapDrop
      have hrest :=
        degreeZeroKappaNoABE0_natDegree_lt l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 hcone
      rw [degreeZeroKappaPolynomial610_eq_ABE0_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
        hcomb] at hkapDeg
      rcases hcone with ⟨hApos, htie', _⟩
      omega
  · have hcomb :=
      lambdaABE0Combined610_natDegree_eq_of_coeff_ne hAne hBne hEne htie
        hEtie hlamDrop
    have hrest :=
      degreeZeroLambdaNoABE0_natDegree_lt l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 hcone
    rw [degreeZeroLambdaPolynomial610_eq_ABE0_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
      hcomb] at hlamDeg
    rcases hcone with ⟨hApos, _⟩
    omega

end TriplePolyKills610

/-! ## Source-facing residual -/

section Closed610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]


/-- Unique-`μ` mixed-`D₀` chambers with a single maximal monomial
(`B D₀²` or `C₀² D₀`) are empty, as are the triples `A`–`B`–`C₀` and
`A`–`B`–`E₀` (leading-coefficient identities `C₀⁶` / `E₀⁴` after extracting
tied `λ`/`κ`/`ο` forms).  Remaining: the triple `A`–`C₀`–`E₀` (cusp with
`l = 0`), the quadruple `T₂` branch, and mixed-`D₀` combination max-sets
whose companion `κ`/`μ` faces have more than one monomial. -/
theorem normalized610ScaleZero_coneTriplesResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      ¬ WeightedAD02LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedA2BD0LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedBC0D0LeadsCone610 A B C0 D0 E0 ∧
      ¬ A6AD02TieCone610 A B C0 D0 E0 ∧
      ¬ BC0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ BC0E0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ BE0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ ABRatioTieCone610 A B C0 D0 E0 ∧
      ¬ AE0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ AC0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ C0E0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ ABC0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ ABE0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedBBDRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBBDRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedBBDERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBBDERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADCRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADCERatioTieCone610 A B C0 D0 E0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hAD02,
      hA2BD, hBCD, hA6AD, hBC0, hBC0E0, hBE0, hAB, hAE0, hAC0, hC0E0⟩ :=
    normalized610ScaleZero_coneFinishResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht,
    hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hAD02, hA2BD,
    hBCD, hA6AD, hBC0, hBC0E0, hBE0, hAB, hAE0, hAC0, hC0E0, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hABC0
    exact lambda_ABC0_impossible l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hABC0 hkapDeg hlamDeg homiDeg
  · intro hABE0
    exact lambda_ABE0_impossible l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hABE0 hkapDeg hlamDeg homiDeg
  · intro hADB
    exact mu_BD02_impossible_of_MixedADB l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADB hmuDeg
  · intro hBBD
    exact mu_BD02_impossible_of_MixedBBD l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hBBD hmuDeg
  · intro hADBBD
    exact mu_BD02_impossible_of_MixedADBBD l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADBBD hmuDeg
  · intro hADBE
    exact mu_BD02_impossible_of_MixedADBE l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADBE hmuDeg
  · intro hBBDE
    exact mu_BD02_impossible_of_MixedBBDE l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hBBDE hmuDeg
  · intro hADBBDE
    exact mu_BD02_impossible_of_MixedADBBDE l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADBBDE hmuDeg
  · intro hADC
    exact mu_C02D0_impossible_of_MixedADC l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADC hmuDeg
  · intro hADCE
    exact mu_C02D0_impossible_of_MixedADCE l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADCE hmuDeg

end Closed610

#print axioms abc0_tied_leadings_impossible
#print axioms ac0e0_tied_leadings_impossible
#print axioms lambda_ABC0_impossible
#print axioms lambda_ABE0_impossible
#print axioms mu_BD02_impossible_of_MixedADB
#print axioms mu_C02D0_impossible_of_MixedADC
#print axioms normalized610ScaleZero_coneTriplesResidual

end Max11DegreeRoutes
