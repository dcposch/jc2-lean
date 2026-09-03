import Grok610ScaleZeroConeFinishScratch

/-! # Scale-zero cone triples for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeFinishScratch` on the constant core
`H = (C t)²`.  Untracked working note.  No tracked file was edited.

The parent residual `normalized610ScaleZero_coneFinishResidual` (green at
content SHA `014b69b2`, commit `35631da`) hands, for every
`Normalized610LeadingCoreSource P Q H 0`, the constant core `H = (C t)²`,
the derivative identity, `natDegree 0` for `λ/κ/μ/ο`, and the negation of
every pair-ratio and unique-`D₀` monomial cone.  Remaining chambers are
the triples `ABC0` / `ABE0` / `AC0E0`, the quadruple `ABCE0`, and mixed
`D₀` weights that are not a unique maximum.

CAS job `derive_610_scale_zero_cone_triples.py` (extending
`derive_610_scale_zero_cone_ratio_ties.py`).  Groebner certificates:
`C₀⁶` on `A`–`B`–`C₀` (`λ+κ+ο`), `E₀⁴` on `A`–`B`–`E₀` (parent
`abe0_tied_leadings_impossible`), and `b¹²` / `v⁵` after the `κ` drop
on the quadruple.  Mixed `D₀` chambers with a unique `κ` or `μ`
monomial are killed as `WeightedAD02LeadsCone610` was.  Combination
mixed-`D₀` max-sets that do not reduce to a unique companion monomial
are named and recorded if they resist.

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

end TripleRests610

/-! ## Source-facing residual -/

section Closed610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Field identities for the leftover triples (`C₀⁶` / Euclidean `b¹²`
on `A`–`B`–`C₀`, parent `E₀⁴` on `A`–`B`–`E₀`, cusp load on
`A`–`C₀`–`E₀` with `l ≠ 0`) and rest bounds for the corresponding
`λ`/`κ` faces.  Mixed-`D₀` max-sets are named.  Remaining after this
file: the drop chambers of the triples (leading forms vanish), the
quadruple `T₂` branch, `A`–`C₀`–`E₀` with `l = 0`, and mixed-`D₀`
combination max-sets. -/
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
      ¬ C0E0RatioTieCone610 A B C0 D0 E0 :=
  normalized610ScaleZero_coneFinishResidual hsource

end Closed610

#print axioms abc0_tied_leadings_impossible
#print axioms ac0e0_tied_leadings_impossible
#print axioms normalized610ScaleZero_coneTriplesResidual

end Max11DegreeRoutes
