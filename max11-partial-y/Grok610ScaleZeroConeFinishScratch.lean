import Grok610ScaleZeroConeKappaMuScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

/-! # Scale-zero cone finish for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeKappaMuScratch` on the constant core
`H = (C t)²`.  Untracked working note.  No tracked file was edited.

Salvage of the kernel-accepted pieces of the untracked draft
`Grok610ScaleZeroConeRatioTiesScratch.lean` (SHA
`1d95c66035bdbd6f563dd27718fcb40acf3ab2f2845ac7508d96acc0107d516b`,
`BUILD_EXIT=1 ERROR_COUNT=7 SORRYAX_COUNT=2`).  Dropped every declaration
whose proof did not typecheck: the `C₀`–`E₀` and `A`–`E₀` raw-tail rest
bounds, the `A`–`C₀` raw-tail leading-coefficient comparison, the three
impossibility theorems that depend on those bounds, and the source-facing
exhaustion.  CAS jobs
`derive_610_scale_zero_cone_ratio_ties.py` /
`_loci` / `_syzygy`.

Landed from the draft: the named cones, rest polynomials, Euclidean
identities (`13 λ - 7 raw`; `7 λ = (7u - 3v) q + 9 v² (u - 18 v)`),
`lambda_AD02_impossible`, the `A⁶`/`A D₀²` pieces,
`kappa_BC0_impossible` / `kappa_BC0E0_impossible`,
`lambda_BE0_impossible` (primitive `B³ (2 B² - 15 E₀)` versus `λ`),
`kappa_AB_impossible`, and the unique `D₀` monomials `A² B D₀` /
`B C₀ D₀`.

The leftover families (parametrized `A⁶`–`A D₀²` and `C₀`–`E₀` ties,
the `A`–`E₀` raw drop via `μ` or `ο`, and the triple/quadruple
leading-coefficient certificates) are filled in below.  No total-degree
or twice-prime theorem is used.  No `sorry`, no new axioms, no
finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Ratio-tie and unique-`D₀` cones -/

section RatioTieCones610

variable {k : Type*} [Field k] [CharZero k]

/-- `6 deg A = 3 deg C₀` uniquely maximal among the four weighted `λ`
faces, with load-free `D₀` monomials strictly lighter. -/
def AC0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- `6 deg A = 2 deg E₀` uniquely maximal among the four weighted `λ`
faces, with load-free `D₀` monomials strictly lighter. -/
def AE0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- `4 deg B = 3 deg C₀` uniquely maximal among the four weighted `λ`
faces, with load-free `D₀` monomials strictly lighter. -/
def BC0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    3 * C0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree

/-- `4 deg B = 2 deg E₀` uniquely maximal among the four weighted `λ`
faces, with load-free `D₀` monomials strictly lighter. -/
def BE0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    2 * E0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree ∧
    3 * D0.natDegree < 5 * B.natDegree

/-- `3 deg C₀ = 2 deg E₀` uniquely maximal among the four weighted `λ`
faces, with load-free `D₀` monomials strictly lighter. -/
def C0E0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    2 * E0.natDegree = 3 * C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    7 * A.natDegree < 2 * C0.natDegree + E0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 3 * C0.natDegree ∧
    C0.natDegree + 2 * D0.natDegree <
      2 * C0.natDegree + E0.natDegree

/-- `6 deg A = 4 deg B` uniquely maximal among the four weighted `λ`
faces, with load-free `D₀` monomials strictly lighter.  This includes
the parent unique-`B` tie and the same weight-tie with some letter of
ordinary degree at least `deg B`. -/
def ABRatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree

/-- Triple `6 deg A = 4 deg B = 3 deg C₀`, `E₀` and `D₀` strictly lighter. -/
def ABC0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Triple `6 deg A = 4 deg B = 2 deg E₀`. -/
def ABE0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Triple `6 deg A = 3 deg C₀ = 2 deg E₀`. -/
def AC0E0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Triple `4 deg B = 3 deg C₀ = 2 deg E₀`. -/
def BC0E0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    3 * C0.natDegree = 4 * B.natDegree ∧
    2 * E0.natDegree = 4 * B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree

/-- All four weighted faces tied. -/
def ABCE0RatioTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    3 * C0.natDegree = 6 * A.natDegree ∧
    2 * E0.natDegree = 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Unique load-free `λ` face `A D₀²`. -/
def WeightedAD02LeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    6 * A.natDegree < A.natDegree + 2 * D0.natDegree ∧
    4 * B.natDegree < A.natDegree + 2 * D0.natDegree ∧
    3 * C0.natDegree < A.natDegree + 2 * D0.natDegree ∧
    2 * E0.natDegree < A.natDegree + 2 * D0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree <
      A.natDegree + 2 * D0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree <
      A.natDegree + 2 * D0.natDegree

/-- Unique load-free `λ` face `A² B D₀`. -/
def WeightedA2BD0LeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < B.natDegree ∧
    0 < D0.natDegree ∧
    6 * A.natDegree < 2 * A.natDegree + B.natDegree + D0.natDegree ∧
    4 * B.natDegree < 2 * A.natDegree + B.natDegree + D0.natDegree ∧
    3 * C0.natDegree < 2 * A.natDegree + B.natDegree + D0.natDegree ∧
    2 * E0.natDegree < 2 * A.natDegree + B.natDegree + D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree <
      2 * A.natDegree + B.natDegree + D0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree <
      2 * A.natDegree + B.natDegree + D0.natDegree

/-- Unique load-free `λ` face `B C₀ D₀`. -/
def WeightedBC0D0LeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < C0.natDegree ∧
    0 < D0.natDegree ∧
    6 * A.natDegree < B.natDegree + C0.natDegree + D0.natDegree ∧
    4 * B.natDegree < B.natDegree + C0.natDegree + D0.natDegree ∧
    3 * C0.natDegree < B.natDegree + C0.natDegree + D0.natDegree ∧
    2 * E0.natDegree < B.natDegree + C0.natDegree + D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree <
      B.natDegree + C0.natDegree + D0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree <
      B.natDegree + C0.natDegree + D0.natDegree

/-- Tie `6 deg A = deg(A D₀²)`, i.e. `2 deg D₀ = 5 deg A`, with the
other four-weights and the remaining `D₀` monomials strictly lighter. -/
def A6AD02TieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    A.natDegree + 2 * D0.natDegree = 6 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

/-- Load-free `A`–`C₀` combination of `λ`. -/
def lambdaAC0Combined610 (A C0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (35 / 729 : k) • (A ^ 4 * C0) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) -
    (5 / 81 : k) • C0 ^ 3

/-- Load-free `A`–`E₀` combination of `λ`. -/
def lambdaAE0Combined610 (A E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (5 / 9 : k) • E0 ^ 2

/-- Load-free `B`–`C₀` combination of `λ`. -/
def lambdaBC0Combined610 (B C0 : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4 - (5 / 81 : k) • C0 ^ 3

/-- Load-free `B`–`E₀` combination of `λ`. -/
def lambdaBE0Combined610 (B E0 : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4 -
    (5 / 27 : k) • (B ^ 2 * E0) +
    (5 / 9 : k) • E0 ^ 2

/-- Load-free `C₀`–`E₀` combination of `λ`. -/
def lambdaC0E0Combined610 (C0 E0 : k[X]) : k[X] :=
  (-(5 / 81 : k)) • C0 ^ 3 + (5 / 9 : k) • E0 ^ 2

/-- Load-free `ο` face on the `A`–`C₀` tie. -/
def omicronAC0Combined610 (A C0 : k[X]) : k[X] :=
  (-(10 / 6561 : k)) • A ^ 7 +
    (35 / 2187 : k) • (A ^ 5 * C0) -
    (40 / 729 : k) • (A ^ 3 * C0 ^ 2) +
    (5 / 81 : k) • (A * C0 ^ 3)

/-- Load-free `ο` face on the `A`–`E₀` tie. -/
def omicronAE0Combined610 (A E0 : k[X]) : k[X] :=
  (-(10 / 6561 : k)) • A ^ 7 - (5 / 243 : k) • (A ^ 4 * E0)

/-- Unique `κ` monomial on the `B`–`C₀` tie. -/
def kappaBC0Face610 (B C0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B * C0 ^ 2)

/-- Unique `ο` monomial on the `C₀`–`E₀` tie. -/
def omicronC0E0Face610 (C0 E0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C0 ^ 2 * E0)

/-- Load-free primitive face on the `B`–`E₀` tie. -/
def primitiveBE0Combined610 (B E0 : k[X]) : k[X] :=
  (-(4 / 243 : k)) • B ^ 5 + (10 / 81 : k) • (B ^ 3 * E0)

/-- Unique `λ` face `A D₀²`. -/
def lambdaAD02Face610 (A D0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D0 ^ 2)

/-- Unique `λ` face `A² B D₀`. -/
def lambdaA2BD0Face610 (A B D0 : k[X]) : k[X] :=
  (20 / 81 : k) • (A ^ 2 * B * D0)

/-- Unique `λ` face `B C₀ D₀`. -/
def lambdaBC0D0Face610 (B C0 D0 : k[X]) : k[X] :=
  (-(10 / 27 : k)) • (B * C0 * D0)

/-- Load-free `A⁶` vs `A D₀²` combination of `λ`. -/
def lambdaA6AD02Combined610 (A D0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 - (5 / 27 : k) • (A * D0 ^ 2)

/-- Unique `κ` monomial `A³ D₀` on the `A⁶`–`A D₀²` tie. -/
def kappaA3D0Face610 (A D0 : k[X]) : k[X] :=
  (20 / 243 : k) • (A ^ 3 * D0)

/-- Load-free raw-tail face on the `A`–`E₀` tie. -/
def rawAE0Combined610 (A E0 : k[X]) : k[X] :=
  (-(65 / 19683 : k)) • A ^ 7 - (35 / 729 : k) • (A ^ 4 * E0)

/-- Load-free four-term `κ` face on the `A`–`B`–`C₀` triple. -/
def kappaABC0Combined610 (A B C0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) +
    (20 / 243 : k) • (A * B ^ 3) +
    (20 / 81 : k) • (A ^ 2 * B * C0) -
    (5 / 27 : k) • (B * C0 ^ 2)

/-- Load-free three-term `κ` face on the `A`–`B`–`E₀` triple. -/
def kappaABE0Combined610 (A B E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) +
    (20 / 243 : k) • (A * B ^ 3) -
    (10 / 27 : k) • (A * B * E0)

/-- Load-free `ο` face on the `A`–`C₀`–`E₀` triple. -/
def omicronAC0E0Combined610 (A C0 E0 : k[X]) : k[X] :=
  (-(10 / 6561 : k)) • A ^ 7 +
    (35 / 2187 : k) • (A ^ 5 * C0) -
    (40 / 729 : k) • (A ^ 3 * C0 ^ 2) +
    (5 / 81 : k) • (A * C0 ^ 3) -
    (5 / 243 : k) • (A ^ 4 * E0) +
    (10 / 81 : k) • (A ^ 2 * C0 * E0) -
    (5 / 27 : k) • (C0 ^ 2 * E0)

end RatioTieCones610

/-! ## Leading-coefficient identities (CAS substitution / Euclidean) -/

section RatioTieIdentities610

variable {k : Type*} [Field k] [CharZero k]

/-- On `A² = 3 C₀` the `A`–`C₀` `λ` form is `27 v³`. -/
theorem lambda_ac0_of_omicron_factor_three (u v : k)
    (h : u = 3 * v) :
    (7 : k) * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3 =
      27 * v ^ 3 := by
  simp [h]
  ring

/-- On `2 A² = 9 C₀` the `A`–`C₀` `λ` form is `u³ / 9`. -/
theorem lambda_ac0_of_omicron_factor_nine (u v : k)
    (h : (2 : k) * u = 9 * v) :
    (9 : k) * (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) =
      u ^ 3 := by
  have h9 : (9 : k) ≠ 0 := by norm_num
  have hv9 : v * 9 = 2 * u := by
    rw [mul_comm]
    exact h.symm
  have hv : v = (2 * u) / 9 := (eq_div_iff_mul_eq h9).mpr hv9
  rw [hv]
  ring

/-- On `2 A³ + 27 E₀ = 0` the `A`–`E₀` `λ` form is `3 p²`. -/
theorem lambda_ae0_of_omicron_factor (p q : k)
    (h : (2 : k) * p + 27 * q = 0) :
    (7 : k) * p ^ 2 + 108 * p * q + 729 * q ^ 2 = 3 * p ^ 2 := by
  have h27 : (27 : k) ≠ 0 := by norm_num
  have hq : q = (-(2 : k) * p) / 27 := by
    have : q * 27 = -2 * p := by
      rw [mul_comm]
      linear_combination h
    exact (eq_div_iff_mul_eq h27).mpr this
  rw [hq]
  ring

/-- On `2 B² = 15 E₀` the `B`–`E₀` `λ` form is `7 r² / 25`. -/
theorem lambda_be0_of_primitive_factor (r s : k)
    (h : (2 : k) * r = 15 * s) :
    (25 : k) * (r ^ 2 - 9 * r * s + 27 * s ^ 2) = 7 * r ^ 2 := by
  have h15 : (15 : k) ≠ 0 := by norm_num
  have hs15 : s * 15 = 2 * r := by
    rw [mul_comm]
    exact h.symm
  have hs : s = (2 * r) / 15 := (eq_div_iff_mul_eq h15).mpr hs15
  rw [hs]
  ring

/-- Scaling identity: the `A`–`C₀` `λ` combination is `(5/6561)` times
`7 u³ - 63 u² v + 162 u v² - 81 v³`. -/
theorem lambdaAC0_scale (u v : k) :
    (35 / 6561 : k) * u ^ 3 - (35 / 729 : k) * (u ^ 2 * v) +
        (10 / 81 : k) * (u * v ^ 2) - (5 / 81 : k) * v ^ 3 =
      (5 / 6561 : k) *
        (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) := by
  ring

/-- Scaling identity for the `A`–`E₀` `λ` combination. -/
theorem lambdaAE0_scale (p q : k) :
    (35 / 6561 : k) * p ^ 2 + (20 / 243 : k) * (p * q) +
        (5 / 9 : k) * q ^ 2 =
      (5 / 6561 : k) * (7 * p ^ 2 + 108 * p * q + 729 * q ^ 2) := by
  ring

/-- Scaling identity for the `B`–`E₀` `λ` combination. -/
theorem lambdaBE0_scale (r s : k) :
    (5 / 243 : k) * r ^ 2 - (5 / 27 : k) * (r * s) + (5 / 9 : k) * s ^ 2 =
      (5 / 243 : k) * (r ^ 2 - 9 * r * s + 27 * s ^ 2) := by
  ring

/-- Euclidean identity on the `A`–`E₀` tie: if the raw linear form
`13 p + 189 q` vanishes then `49 λ = 148 p²`. -/
theorem lambda_raw_ae0_identity (p q : k) :
    (49 : k) * (7 * p ^ 2 + 108 * p * q + 729 * q ^ 2) - 148 * p ^ 2 =
      3 * (5 * p + 63 * q) * (13 * p + 189 * q) := by
  ring

/-- Scaling identity for the `A`–`E₀` raw-tail linear form. -/
theorem rawAE0_scale (p q : k) :
    (-(65 / 19683 : k)) * p - (35 / 729 : k) * q =
      (-(5 / 19683 : k)) * (13 * p + 189 * q) := by
  ring

/-- If the `A`–`E₀` `λ` quadratic vanishes and `A ≠ 0`, the companion
raw-tail linear form cannot vanish. -/
theorem raw_ae0_ne_zero_of_lambda_zero (p q : k)
    (hp : p ≠ 0)
    (hlam : (7 : k) * p ^ 2 + 108 * p * q + 729 * q ^ 2 = 0) :
    (13 : k) * p + 189 * q ≠ 0 := by
  intro hraw
  have hid := lambda_raw_ae0_identity p q
  have h148p : (148 : k) * p ^ 2 = 0 := by
    have : (49 : k) * (7 * p ^ 2 + 108 * p * q + 729 * q ^ 2) -
        148 * p ^ 2 = 0 := by
      rw [hid, hraw, mul_zero]
    simpa [hlam] using this
  have h148 : (148 : k) ≠ 0 := by norm_num
  exact hp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
    ((mul_eq_zero.mp h148p).resolve_left h148))

/-- On the `A`–`B`–`E₀` triple, `4 λ - 3 (7 a⁶ - 150 a³ b² + 12 b⁴)` is
divisible by the `κ` factor `7 a³ - 12 b² + 54 e`. -/
theorem lambda_abe0_of_kappa_factor (a b e : k) :
    (4 : k) * (7 * a ^ 6 - 126 * a ^ 3 * b ^ 2 + 108 * a ^ 3 * e +
          27 * b ^ 4 - 243 * b ^ 2 * e + 729 * e ^ 2) -
        3 * (7 * a ^ 6 - 150 * a ^ 3 * b ^ 2 + 12 * b ^ 4) =
      (7 * a ^ 3 - 12 * b ^ 2 + 54 * e) *
        (a ^ 3 - 6 * b ^ 2 + 54 * e) := by
  ring

/-- On the same triple, the `ο` form plus `3 a³ (a³ + 17 b²)` is
divisible by the same `κ` factor. -/
theorem omicron_abe0_of_kappa_factor (a b e : k) :
    (4 : k) * a ^ 6 - 105 * a ^ 3 * b ^ 2 + 54 * a ^ 3 * e +
        72 * b ^ 4 - 324 * b ^ 2 * e +
      3 * a ^ 3 * (a ^ 3 + 17 * b ^ 2) =
      (7 * a ^ 3 - 12 * b ^ 2 + 54 * e) * (a ^ 3 - 6 * b ^ 2) := by
  ring

/-- The `A`–`B`–`E₀` `λ` remainder and `ο` remainder cannot vanish
together unless `b = 0`. -/
theorem abe0_lambda_omicron_remainders (a b : k)
    (hlam : (7 : k) * a ^ 6 - 150 * a ^ 3 * b ^ 2 + 12 * b ^ 4 = 0)
    (homi : (3 : k) * a ^ 3 * (a ^ 3 + 17 * b ^ 2) = 0) :
    b = 0 := by
  have h12 : (12 : k) ≠ 0 := by norm_num
  have h3 : (3 : k) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp homi with h3a | h17
  · have ha : a ^ 3 = 0 := (mul_eq_zero.mp h3a).resolve_left h3
    have ha6 : a ^ 6 = 0 := by
      have : a ^ 6 = (a ^ 3) ^ 2 := by ring
      rw [this, ha, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    have : (7 : k) * a ^ 6 - 150 * a ^ 3 * b ^ 2 + 12 * b ^ 4 =
        12 * b ^ 4 := by
      simp [ha, ha6]
    have hb4 : (12 : k) * b ^ 4 = 0 := by
      rw [← this]
      exact hlam
    exact (pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hb4).resolve_left h12)
  · have ha3 : a ^ 3 = -17 * b ^ 2 := by linear_combination h17
    have : (7 : k) * a ^ 6 - 150 * a ^ 3 * b ^ 2 + 12 * b ^ 4 =
        4585 * b ^ 4 := by
      have ha6 : a ^ 6 = (a ^ 3) ^ 2 := by ring
      rw [ha6, ha3]
      ring
    have hb4 : (4585 : k) * b ^ 4 = 0 := by
      rw [← this]
      exact hlam
    have h4585 : (4585 : k) ≠ 0 := by norm_num
    exact (pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hb4).resolve_left h4585)

/-- On `A² = 3 C₀` the `A`–`C₀`–`E₀` `λ` form is `(A³ - 27 E₀)²`. -/
theorem lambda_ac0e0_of_omicron_factor_square (a c e : k)
    (h : a ^ 2 = 3 * c) :
    (7 : k) * a ^ 6 - 63 * a ^ 4 * c + 108 * a ^ 3 * e +
        162 * a ^ 2 * c ^ 2 - 486 * a * c * e - 81 * c ^ 3 +
        729 * e ^ 2 =
      (a ^ 3 - 27 * e) ^ 2 := by
  have h3 : (3 : k) ≠ 0 := by norm_num
  have hc : c = a ^ 2 / 3 := by
    have : c * 3 = a ^ 2 := by
      rw [mul_comm]
      exact h.symm
    exact (eq_div_iff_mul_eq h3).mpr this
  rw [hc]
  ring

/-- On `2 A³ - 9 A C₀ + 27 E₀ = 0` the `A`–`C₀`–`E₀` `λ` form is
`3 (A² - 3 C₀)³`. -/
theorem lambda_ac0e0_of_omicron_factor_cubic (a c e : k)
    (h : (2 : k) * a ^ 3 - 9 * a * c + 27 * e = 0) :
    (7 : k) * a ^ 6 - 63 * a ^ 4 * c + 108 * a ^ 3 * e +
        162 * a ^ 2 * c ^ 2 - 486 * a * c * e - 81 * c ^ 3 +
        729 * e ^ 2 =
      3 * (a ^ 2 - 3 * c) ^ 3 := by
  have h27 : (27 : k) ≠ 0 := by norm_num
  have he : e = -((2 : k) * a ^ 3 - 9 * a * c) / 27 := by
    have : e * 27 = -((2 : k) * a ^ 3 - 9 * a * c) := by
      rw [mul_comm]
      linear_combination h
    exact (eq_div_iff_mul_eq h27).mpr this
  rw [he]
  ring

end RatioTieIdentities610

/-! ## Rest polynomials -/

section RatioTieRests610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_two_rt {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_rt {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_rt {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_rt {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

private theorem zero_pow_six_rt {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

private theorem zero_pow_seven_rt {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

/-- `λ` with the `A`–`C₀` combination deleted. -/
def degreeZeroLambdaNoAC0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(70 / 729 : k)) • (A ^ 3 * B ^ 2) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_AC0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaAC0Combined610 A C0 +
        degreeZeroLambdaNoAC0Polynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaAC0Combined610,
    degreeZeroLambdaNoAC0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoAC0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AC0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoAC0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hB, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoAC0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hB
  have hE1 : 2 * E0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

/-- `λ` with the `A`–`E₀` combination deleted. -/
def degreeZeroLambdaNoAE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(70 / 729 : k)) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_AE0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaAE0Combined610 A E0 +
        degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaAE0Combined610,
    degreeZeroLambdaNoAE0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoAE0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hB, hC, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoAE0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hB
  have hC1 : 3 * C0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hC
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
/-- `κ` with the unique `B C₀²` face deleted. -/
def degreeZeroKappaNoBC0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) -
    (3 / 256 * l : k) • A ^ 5 +
    (20 / 243 : k) • (A * B ^ 3) +
    (20 / 81 : k) • (A ^ 2 * B * C0) +
    (9 / 64 * l : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * D0) +
    (3 / 32 * l : k) • (A ^ 3 * C0) +
    (20 / 243 * alpha : k) • (A ^ 3 * B) +
    (385 / 31104 * beta : k) • A ^ 4 -
    (5 / 27 : k) • (B ^ 2 * D0) -
    (3 / 16 * l : k) • (B ^ 2 * C0) -
    (4 / 81 * alpha : k) • B ^ 3 -
    (10 / 27 : k) • (A * C0 * D0) -
    (3 / 16 * l : k) • (A * C0 ^ 2) -
    (10 / 27 : k) • (A * B * E0) -
    (3 / 8 * l : k) • (A * B * D0) -
    (8 / 27 * alpha : k) • (A * B * C0) -
    (35 / 432 * beta : k) • (A * B ^ 2) -
    (3 / 16 * l : k) • (A ^ 2 * E0) -
    (4 / 27 * alpha : k) • (A ^ 2 * D0) -
    (35 / 432 * beta : k) • (A ^ 2 * C0) +
    (35 / 1296 * delta : k) • A ^ 3 +
    (10 / 9 : k) • (D0 * E0) +
    (3 / 8 * l : k) • D0 ^ 2 +
    (3 / 4 * l : k) • (C0 * E0) +
    (4 / 9 * alpha : k) • (C0 * D0) +
    (7 / 72 * beta : k) • C0 ^ 2 +
    (4 / 9 * alpha : k) • (B * E0) +
    (7 / 36 * beta : k) • (B * D0) -
    (5 / 72 * delta : k) • B ^ 2 +
    (7 / 36 * beta : k) • (A * E0) -
    (5 / 36 * delta : k) • (A * C0) -
    (2 / 9 * epsilon : k) • (A * B) -
    (1 / 8 * zeta : k) • A ^ 2 +
    (5 / 6 * delta : k) • E0 +
    (2 / 3 * epsilon : k) • D0 +
    (1 / 2 * zeta : k) • C0 +
    (1 / 3 * eta : k) • B +
    (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_BC0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaBC0Face610 B C0 +
        degreeZeroKappaNoBC0Polynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaBC0Face610,
    degreeZeroKappaNoBC0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoBC0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BC0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoBC0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      B.natDegree + 2 * C0.natDegree := by
  rcases hcone with ⟨hBpos, htie, hA, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroKappaNoBC0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hE1 : 2 * E0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoBC0_natDegree_lt_of_BC0E0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BC0E0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoBC0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      B.natDegree + 2 * C0.natDegree := by
  rcases hcone with ⟨hBpos, htieC, htieE, hA, hD1, hD2, hD3⟩
  simp only [degreeZeroKappaNoBC0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
/-- Raw fourth tail with the unique `C₀² E₀` face deleted. -/
def degreeZeroRawFourthTailNoC0E0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(65 / 19683 : k)) • A ^ 7 +
    (70 / 2187 : k) • (A ^ 5 * C0) +
    (175 / 2187 : k) • (A ^ 4 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * E0) -
    (140 / 729 : k) • (A ^ 3 * B * D0) -
    (70 / 729 : k) • (A ^ 3 * C0 ^ 2) -
    (70 / 243 : k) • (A ^ 2 * B ^ 2 * C0) +
    (20 / 81 : k) • (A ^ 2 * C0 * E0) +
    (10 / 81 : k) • (A ^ 2 * D0 ^ 2) -
    (35 / 729 : k) • (A * B ^ 4) +
    (20 / 81 : k) • (A * B ^ 2 * E0) +
    (40 / 81 : k) • (A * B * C0 * D0) +
    (20 / 243 : k) • (A * C0 ^ 3) -
    (5 / 27 : k) • (A * E0 ^ 2) +
    (20 / 243 : k) • (B ^ 3 * D0) +
    (10 / 81 : k) • (B ^ 2 * C0 ^ 2) -
    (10 / 27 : k) • (B * D0 * E0) -
    (5 / 27 : k) • (C0 * D0 ^ 2) +
    (21 / 512 * l : k) • (A ^ 5 * B) -
    (15 / 256 * l : k) • (A ^ 4 * D0) -
    (15 / 64 * l : k) • (A ^ 3 * B * C0) -
    (15 / 128 * l : k) • (A ^ 2 * B ^ 3) +
    (9 / 32 * l : k) • (A ^ 2 * B * E0) +
    (9 / 32 * l : k) • (A ^ 2 * C0 * D0) +
    (9 / 32 * l : k) • (A * B ^ 2 * D0) +
    (9 / 32 * l : k) • (A * B * C0 ^ 2) -
    (3 / 8 * l : k) • (A * D0 * E0) +
    (3 / 32 * l : k) • (B ^ 3 * C0) -
    (3 / 8 * l : k) • (B * C0 * E0) -
    (3 / 16 * l : k) • (B * D0 ^ 2) -
    (3 / 16 * l : k) • (C0 ^ 2 * D0) +
    (44 / 6561 * alpha : k) • A ^ 6 -
    (40 / 729 * alpha : k) • (A ^ 4 * C0) -
    (80 / 729 * alpha : k) • (A ^ 3 * B ^ 2) +
    (20 / 243 * alpha : k) • (A ^ 3 * E0) +
    (20 / 81 * alpha : k) • (A ^ 2 * B * D0) +
    (10 / 81 * alpha : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 * alpha : k) • (A * B ^ 2 * C0) -
    (8 / 27 * alpha : k) • (A * C0 * E0) -
    (4 / 27 * alpha : k) • (A * D0 ^ 2) +
    (5 / 243 * alpha : k) • B ^ 4 -
    (4 / 27 * alpha : k) • (B ^ 2 * E0) -
    (8 / 27 * alpha : k) • (B * C0 * D0) -
    (4 / 81 * alpha : k) • C0 ^ 3 +
    (2 / 9 * alpha : k) • E0 ^ 2 -
    (6545 / 186624 * beta : k) • (A ^ 4 * B) +
    (385 / 7776 * beta : k) • (A ^ 3 * D0) +
    (385 / 2592 * beta : k) • (A ^ 2 * B * C0) +
    (385 / 7776 * beta : k) • (A * B ^ 3) -
    (35 / 216 * beta : k) • (A * B * E0) -
    (35 / 216 * beta : k) • (A * C0 * D0) -
    (35 / 432 * beta : k) • (B ^ 2 * D0) -
    (35 / 432 * beta : k) • (B * C0 ^ 2) +
    (7 / 36 * beta : k) • (D0 * E0) -
    (455 / 7776 * delta : k) • (A ^ 3 * B) +
    (35 / 432 * delta : k) • (A ^ 2 * D0) +
    (35 / 216 * delta : k) • (A * B * C0) +
    (35 / 1296 * delta : k) • B ^ 3 -
    (5 / 36 * delta : k) • (B * E0) -
    (5 / 36 * delta : k) • (C0 * D0) -
    (7 / 243 * epsilon : k) • A ^ 4 +
    (4 / 27 * epsilon : k) • (A ^ 2 * C0) +
    (4 / 27 * epsilon : k) • (A * B ^ 2) -
    (2 / 9 * epsilon : k) • (A * E0) -
    (2 / 9 * epsilon : k) • (B * D0) -
    (1 / 9 * epsilon : k) • C0 ^ 2 +
    (5 / 81 * eta : k) • A ^ 3 -
    (2 / 9 * eta : k) • (A * C0) -
    (1 / 9 * eta : k) • B ^ 2 +
    (1 / 3 * eta : k) • E0 -
    (5 / 36 * theta : k) • (A * B) +
    (1 / 6 * theta : k) • D0 +
    (3 / 16 * zeta : k) • (A ^ 2 * B) -
    (1 / 4 * zeta : k) • (A * D0) -
    (1 / 4 * zeta : k) • (B * C0)

set_option maxHeartbeats 32000000 in
theorem degreeZeroRawFourthTailPolynomial610_eq_C0E0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 =
      omicronC0E0Face610 C0 E0 +
        degreeZeroRawFourthTailNoC0E0Polynomial610 l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroRawFourthTailPolynomial610, omicronC0E0Face610,
    degreeZeroRawFourthTailNoC0E0Polynomial610]
  module

/-- `λ` with the unique `A D₀²` face deleted. -/
def degreeZeroLambdaNoAD02Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_AD02_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaAD02Face610 A D0 +
        degreeZeroLambdaNoAD02Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaAD02Face610,
    degreeZeroLambdaNoAD02Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoAD02_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedAD02LeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoAD02Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      A.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hA, hB, hC, hE, hD2, hD3⟩
  simp only [degreeZeroLambdaNoAD02Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ A.natDegree + 2 * D0.natDegree :=
    Nat.succ_le_of_lt hA
  have hB1 : 4 * B.natDegree + 1 ≤ A.natDegree + 2 * D0.natDegree :=
    Nat.succ_le_of_lt hB
  have hC1 : 3 * C0.natDegree + 1 ≤ A.natDegree + 2 * D0.natDegree :=
    Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ A.natDegree + 2 * D0.natDegree :=
    Nat.succ_le_of_lt hE
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      A.natDegree + 2 * D0.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      A.natDegree + 2 * D0.natDegree := Nat.succ_le_of_lt hD3
  omega

/-- `λ` with the unique `A² B D₀` face deleted. -/
def degreeZeroLambdaNoA2BD0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_A2BD0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaA2BD0Face610 A B D0 +
        degreeZeroLambdaNoA2BD0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaA2BD0Face610,
    degreeZeroLambdaNoA2BD0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoA2BD0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedA2BD0LeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA2BD0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      2 * A.natDegree + B.natDegree + D0.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hA, hB, hC, hE, hD1, hD3⟩
  simp only [degreeZeroLambdaNoA2BD0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤
      2 * A.natDegree + B.natDegree + D0.natDegree := Nat.succ_le_of_lt hA
  have hB1 : 4 * B.natDegree + 1 ≤
      2 * A.natDegree + B.natDegree + D0.natDegree := Nat.succ_le_of_lt hB
  have hC1 : 3 * C0.natDegree + 1 ≤
      2 * A.natDegree + B.natDegree + D0.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤
      2 * A.natDegree + B.natDegree + D0.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤
      2 * A.natDegree + B.natDegree + D0.natDegree := Nat.succ_le_of_lt hD1
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      2 * A.natDegree + B.natDegree + D0.natDegree := Nat.succ_le_of_lt hD3
  omega

/-- `λ` with the unique `B C₀ D₀` face deleted. -/
def degreeZeroLambdaNoBC0D0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_BC0D0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaBC0D0Face610 B C0 D0 +
        degreeZeroLambdaNoBC0D0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaBC0D0Face610,
    degreeZeroLambdaNoBC0D0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoBC0D0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedBC0D0LeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoBC0D0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      B.natDegree + C0.natDegree + D0.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hA, hB, hC, hE, hD1, hD2⟩
  simp only [degreeZeroLambdaNoBC0D0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤
      B.natDegree + C0.natDegree + D0.natDegree := Nat.succ_le_of_lt hA
  have hB1 : 4 * B.natDegree + 1 ≤
      B.natDegree + C0.natDegree + D0.natDegree := Nat.succ_le_of_lt hB
  have hC1 : 3 * C0.natDegree + 1 ≤
      B.natDegree + C0.natDegree + D0.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤
      B.natDegree + C0.natDegree + D0.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤
      B.natDegree + C0.natDegree + D0.natDegree := Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      B.natDegree + C0.natDegree + D0.natDegree := Nat.succ_le_of_lt hD2
  omega

/-- Base group with the `B`–`E₀` combination `B⁵`, `B³ E₀` deleted. -/
def degreeZeroBaseGroupNoBE0Polynomial610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 -
    (62720 / 2239488 : k) • (A ^ 6 * B) +
    (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Primitive with the `B`–`E₀` load-free combination deleted. -/
def degreeZeroPrimitiveNoBE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupNoBE0Polynomial610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

set_option maxHeartbeats 16000000 in
theorem degreeZeroBaseGroupPolynomial610_eq_BE0_add_rest
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0 =
      primitiveBE0Combined610 B E0 +
        degreeZeroBaseGroupNoBE0Polynomial610 l A B C0 D0 E0 := by
  simp only [degreeZeroBaseGroupPolynomial610, primitiveBE0Combined610,
    degreeZeroBaseGroupNoBE0Polynomial610]
  -- `-36864/2239488 = -4/243` and `276480/2239488 = 10/81`.
  have hB5 : (-(36864 / 2239488 : k)) = (-(4 / 243 : k)) := by norm_num
  have hB3E : (276480 / 2239488 : k) = (10 / 81 : k) := by norm_num
  simp [hB5, hB3E]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_BE0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      primitiveBE0Combined610 B E0 +
        degreeZeroPrimitiveNoBE0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveNoBE0Polynomial610]
  rw [degreeZeroBaseGroupPolynomial610_eq_BE0_add_rest]
  abel

set_option maxHeartbeats 16000000 in
theorem degreeZeroBaseGroupNoBE0_natDegree_lt
    (l : k) (A B C0 D0 E0 : k[X])
    (hcone : BE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroBaseGroupNoBE0Polynomial610 l A B C0 D0 E0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, htie, hA, hC, hD1, hD2, hD3, hDprim⟩
  simp only [degreeZeroBaseGroupNoBE0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt, zero_pow_seven_rt]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD3
  have hDp : 3 * D0.natDegree + 1 ≤ 5 * B.natDegree :=
    Nat.succ_le_of_lt hDprim
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveNoBE0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroPrimitiveNoBE0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      5 * B.natDegree := by
  have hbase :=
    degreeZeroBaseGroupNoBE0_natDegree_lt l A B C0 D0 E0 hcone
  rcases hcone with ⟨hBpos, htie, hA, hC, hD1, hD2, hD3, hDprim⟩
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hD1
  have hDp : 3 * D0.natDegree + 1 ≤ 5 * B.natDegree :=
    Nat.succ_le_of_lt hDprim
  have halpha :
      (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
        5 * B.natDegree := by
    simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
      zero_pow_four_rt, zero_pow_five_rt]
    compute_degree
    omega
  have hbeta :
      (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
        5 * B.natDegree := by
    simp only [degreeZeroBetaGroupPolynomial610, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
      zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
    compute_degree
    omega
  have hdelta :
      (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
        5 * B.natDegree := by
    simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
      zero_pow_four_rt, zero_pow_five_rt]
    compute_degree
    omega
  have hepsilon :
      (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
        5 * B.natDegree := by
    simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt]
    compute_degree
    omega
  have hzeta :
      (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
        5 * B.natDegree := by
    simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
      zero_pow_four_rt]
    compute_degree
    omega
  have heta :
      (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
        5 * B.natDegree := by
    simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow_two_rt]
    compute_degree
    omega
  have htheta :
      (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
        5 * B.natDegree := by
    simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt]
    compute_degree
    omega
  simp only [degreeZeroPrimitiveNoBE0Polynomial610]
  exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
    (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
    (natDegree_smul_lt610 epsilon hepsilon)
    (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
    (natDegree_smul_lt610 theta htheta)

/-- `λ` with the `B`–`E₀` combination deleted. -/
def degreeZeroLambdaNoBE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_BE0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaBE0Combined610 B E0 +
        degreeZeroLambdaNoBE0Polynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaBE0Combined610,
    degreeZeroLambdaNoBE0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoBE0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoBE0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, htie, hA, hC, hD1, hD2, hD3, hDprim⟩
  simp only [degreeZeroLambdaNoBE0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hA1 : 6 * A.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD3
  have hDp : 3 * D0.natDegree + 1 ≤ 5 * B.natDegree :=
    Nat.succ_le_of_lt hDprim
  omega

/-- Load-free raw-tail face on the `A`–`C₀` tie. -/
def rawAC0Combined610 (A C0 : k[X]) : k[X] :=
  (-(65 / 19683 : k)) • A ^ 7 +
    (70 / 2187 : k) • (A ^ 5 * C0) -
    (70 / 729 : k) • (A ^ 3 * C0 ^ 2) +
    (20 / 243 : k) • (A * C0 ^ 3)

set_option maxHeartbeats 16000000 in
/-- Raw fourth tail with the `A`–`C₀` face deleted. -/
def degreeZeroRawFourthTailNoAC0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (175 / 2187 : k) • (A ^ 4 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * E0) -
    (140 / 729 : k) • (A ^ 3 * B * D0) -
    (70 / 243 : k) • (A ^ 2 * B ^ 2 * C0) +
    (20 / 81 : k) • (A ^ 2 * C0 * E0) +
    (10 / 81 : k) • (A ^ 2 * D0 ^ 2) -
    (35 / 729 : k) • (A * B ^ 4) +
    (20 / 81 : k) • (A * B ^ 2 * E0) +
    (40 / 81 : k) • (A * B * C0 * D0) -
    (5 / 27 : k) • (A * E0 ^ 2) +
    (20 / 243 : k) • (B ^ 3 * D0) +
    (10 / 81 : k) • (B ^ 2 * C0 ^ 2) -
    (10 / 27 : k) • (B * D0 * E0) -
    (5 / 27 : k) • (C0 ^ 2 * E0) -
    (5 / 27 : k) • (C0 * D0 ^ 2) +
    (21 / 512 * l : k) • (A ^ 5 * B) -
    (15 / 256 * l : k) • (A ^ 4 * D0) -
    (15 / 64 * l : k) • (A ^ 3 * B * C0) -
    (15 / 128 * l : k) • (A ^ 2 * B ^ 3) +
    (9 / 32 * l : k) • (A ^ 2 * B * E0) +
    (9 / 32 * l : k) • (A ^ 2 * C0 * D0) +
    (9 / 32 * l : k) • (A * B ^ 2 * D0) +
    (9 / 32 * l : k) • (A * B * C0 ^ 2) -
    (3 / 8 * l : k) • (A * D0 * E0) +
    (3 / 32 * l : k) • (B ^ 3 * C0) -
    (3 / 8 * l : k) • (B * C0 * E0) -
    (3 / 16 * l : k) • (B * D0 ^ 2) -
    (3 / 16 * l : k) • (C0 ^ 2 * D0) +
    (44 / 6561 * alpha : k) • A ^ 6 -
    (40 / 729 * alpha : k) • (A ^ 4 * C0) -
    (80 / 729 * alpha : k) • (A ^ 3 * B ^ 2) +
    (20 / 243 * alpha : k) • (A ^ 3 * E0) +
    (20 / 81 * alpha : k) • (A ^ 2 * B * D0) +
    (10 / 81 * alpha : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 * alpha : k) • (A * B ^ 2 * C0) -
    (8 / 27 * alpha : k) • (A * C0 * E0) -
    (4 / 27 * alpha : k) • (A * D0 ^ 2) +
    (5 / 243 * alpha : k) • B ^ 4 -
    (4 / 27 * alpha : k) • (B ^ 2 * E0) -
    (8 / 27 * alpha : k) • (B * C0 * D0) -
    (4 / 81 * alpha : k) • C0 ^ 3 +
    (2 / 9 * alpha : k) • E0 ^ 2 -
    (6545 / 186624 * beta : k) • (A ^ 4 * B) +
    (385 / 7776 * beta : k) • (A ^ 3 * D0) +
    (385 / 2592 * beta : k) • (A ^ 2 * B * C0) +
    (385 / 7776 * beta : k) • (A * B ^ 3) -
    (35 / 216 * beta : k) • (A * B * E0) -
    (35 / 216 * beta : k) • (A * C0 * D0) -
    (35 / 432 * beta : k) • (B ^ 2 * D0) -
    (35 / 432 * beta : k) • (B * C0 ^ 2) +
    (7 / 36 * beta : k) • (D0 * E0) -
    (455 / 7776 * delta : k) • (A ^ 3 * B) +
    (35 / 432 * delta : k) • (A ^ 2 * D0) +
    (35 / 216 * delta : k) • (A * B * C0) +
    (35 / 1296 * delta : k) • B ^ 3 -
    (5 / 36 * delta : k) • (B * E0) -
    (5 / 36 * delta : k) • (C0 * D0) -
    (7 / 243 * epsilon : k) • A ^ 4 +
    (4 / 27 * epsilon : k) • (A ^ 2 * C0) +
    (4 / 27 * epsilon : k) • (A * B ^ 2) -
    (2 / 9 * epsilon : k) • (A * E0) -
    (2 / 9 * epsilon : k) • (B * D0) -
    (1 / 9 * epsilon : k) • C0 ^ 2 +
    (5 / 81 * eta : k) • A ^ 3 -
    (2 / 9 * eta : k) • (A * C0) -
    (1 / 9 * eta : k) • B ^ 2 +
    (1 / 3 * eta : k) • E0 -
    (5 / 36 * theta : k) • (A * B) +
    (1 / 6 * theta : k) • D0 +
    (3 / 16 * zeta : k) • (A ^ 2 * B) -
    (1 / 4 * zeta : k) • (A * D0) -
    (1 / 4 * zeta : k) • (B * C0)

set_option maxHeartbeats 32000000 in
theorem degreeZeroRawFourthTailPolynomial610_eq_AC0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 =
      rawAC0Combined610 A C0 +
        degreeZeroRawFourthTailNoAC0Polynomial610 l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroRawFourthTailPolynomial610, rawAC0Combined610,
    degreeZeroRawFourthTailNoAC0Polynomial610]
  module

set_option maxHeartbeats 32000000 in
theorem degreeZeroRawFourthTailNoAC0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AC0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroRawFourthTailNoAC0Polynomial610 l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hB, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroRawFourthTailNoAC0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt, zero_pow_seven_rt]
  compute_degree
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hB
  have hE1 : 2 * E0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
/-- Raw fourth tail with the `A`–`E₀` face deleted. -/
def degreeZeroRawFourthTailNoAE0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroRawFourthTailNoAC0Polynomial610 l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 +
    (70 / 2187 : k) • (A ^ 5 * C0) -
    (70 / 729 : k) • (A ^ 3 * C0 ^ 2) +
    (20 / 243 : k) • (A * C0 ^ 3) +
    (35 / 729 : k) • (A ^ 4 * E0)

/-- `λ` with the `A⁶`/`A D₀²` combination deleted. -/
def degreeZeroLambdaNoA6AD02Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(70 / 729 : k)) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

/-- `κ` with the unique `A³ D₀` face deleted. -/
def degreeZeroKappaNoA3D0Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) -
    (3 / 256 * l : k) • A ^ 5 +
    (20 / 243 : k) • (A * B ^ 3) +
    (20 / 81 : k) • (A ^ 2 * B * C0) +
    (9 / 64 * l : k) • (A ^ 2 * B ^ 2) +
    (3 / 32 * l : k) • (A ^ 3 * C0) +
    (20 / 243 * alpha : k) • (A ^ 3 * B) +
    (385 / 31104 * beta : k) • A ^ 4 -
    (5 / 27 : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * D0) -
    (3 / 16 * l : k) • (B ^ 2 * C0) -
    (4 / 81 * alpha : k) • B ^ 3 -
    (10 / 27 : k) • (A * C0 * D0) -
    (3 / 16 * l : k) • (A * C0 ^ 2) -
    (10 / 27 : k) • (A * B * E0) -
    (3 / 8 * l : k) • (A * B * D0) -
    (8 / 27 * alpha : k) • (A * B * C0) -
    (35 / 432 * beta : k) • (A * B ^ 2) -
    (3 / 16 * l : k) • (A ^ 2 * E0) -
    (4 / 27 * alpha : k) • (A ^ 2 * D0) -
    (35 / 432 * beta : k) • (A ^ 2 * C0) +
    (35 / 1296 * delta : k) • A ^ 3 +
    (10 / 9 : k) • (D0 * E0) +
    (3 / 8 * l : k) • D0 ^ 2 +
    (3 / 4 * l : k) • (C0 * E0) +
    (4 / 9 * alpha : k) • (C0 * D0) +
    (7 / 72 * beta : k) • C0 ^ 2 +
    (4 / 9 * alpha : k) • (B * E0) +
    (7 / 36 * beta : k) • (B * D0) -
    (5 / 72 * delta : k) • B ^ 2 +
    (7 / 36 * beta : k) • (A * E0) -
    (5 / 36 * delta : k) • (A * C0) -
    (2 / 9 * epsilon : k) • (A * B) -
    (1 / 8 * zeta : k) • A ^ 2 +
    (5 / 6 * delta : k) • E0 +
    (2 / 3 * epsilon : k) • D0 +
    (1 / 2 * zeta : k) • C0 +
    (1 / 3 * eta : k) • B +
    (1 / 6 * theta : k) • A

set_option maxHeartbeats 32000000 in
theorem degreeZeroRawFourthTailPolynomial610_eq_AE0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 =
      rawAE0Combined610 A E0 +
        degreeZeroRawFourthTailNoAE0Polynomial610 l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroRawFourthTailPolynomial610, rawAE0Combined610,
    degreeZeroRawFourthTailNoAE0Polynomial610,
    degreeZeroRawFourthTailNoAC0Polynomial610, rawAC0Combined610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_A6AD02_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaA6AD02Combined610 A D0 +
        degreeZeroLambdaNoA6AD02Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaA6AD02Combined610,
    degreeZeroLambdaNoA6AD02Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_A3D0_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaA3D0Face610 A D0 +
        degreeZeroKappaNoA3D0Polynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaA3D0Face610,
    degreeZeroKappaNoA3D0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoA6AD02_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : A6AD02TieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6AD02Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hD2, hD3⟩
  simp only [degreeZeroLambdaNoA6AD02Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hD : 2 * D0.natDegree = 5 * A.natDegree := by omega
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hB
  have hC1 : 3 * C0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hE
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  simp only [max_lt_iff]
  all_goals omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoA3D0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : A6AD02TieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoA3D0Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      3 * A.natDegree + D0.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hD2, hD3⟩
  simp only [degreeZeroKappaNoA3D0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt]
  compute_degree
  have hD : 2 * D0.natDegree = 5 * A.natDegree := by omega
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hB
  have hC1 : 3 * C0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hE
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  simp only [max_lt_iff]
  all_goals omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoHighBTieRest610_natDegree_lt_of_AB
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABRatioTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoHighBTieRest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * A.natDegree + B.natDegree := by
  rcases hcone with ⟨hBpos, htie, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroKappaNoHighBTieRest610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt]
  compute_degree
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD3
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoHighBTieRest610_natDegree_lt_of_AB
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABRatioTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieRest610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, htie, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoHighBTieRest610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  have hC1 : 3 * C0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hC
  have hE1 : 2 * E0.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hE
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 4 * B.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      4 * B.natDegree := Nat.succ_le_of_lt hD3
  omega

end RatioTieRests610

/-! ## Unique-face and combination impossibilities -/

section RatioTieImpossible610

variable {k : Type*} [Field k] [CharZero k]

/-- A product against a degree-zero factor cannot raise degree. -/
theorem natDegree_mul_of_natDegree_eq_zero (p q : k[X])
    (hq : q.natDegree = 0) :
    (p * q).natDegree ≤ p.natDegree := by
  have h := natDegree_mul_le (p := p) (q := q)
  simpa [hq] using h

set_option maxHeartbeats 16000000 in
/-- `λ` on the `A`–`C₀` combination cannot be constant unless the combination
drops. -/
theorem lambda_AC0_impossible_of_combined_degree
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AC0RatioTieCone610 A B C0 D0 E0)
    (hcomb :
      (lambdaAC0Combined610 A C0).natDegree = 6 * A.natDegree)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hrest :=
    degreeZeroLambdaNoAC0_natDegree_lt l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_AC0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]), hcomb] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem lambdaAC0Combined610_natDegree_eq_of_coeff_ne
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : 3 * C0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (35 / 729 : k) * (A.leadingCoeff ^ 4 * C0.leadingCoeff) +
            (10 / 81 : k) *
              (A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2) -
              (5 / 81 : k) * C0.leadingCoeff ^ 3 ≠
        0) :
    (lambdaAC0Combined610 A C0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hC3 : (C0 ^ 3).natDegree = 3 * C0.natDegree := natDegree_pow C0 3
  have hdegC : 3 * C0.natDegree = 6 * A.natDegree := htie
  have hA4C :
      (A ^ 4 * C0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hC, natDegree_pow]
    omega
  have hA2C2 :
      (A ^ 2 * C0 ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hC),
      natDegree_pow, natDegree_pow]
    omega
  have htop :
      (lambdaAC0Combined610 A C0).coeff (6 * A.natDegree) ≠ 0 := by
    simp only [lambdaAC0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 4 * C0).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 4 * C0.leadingCoeff := by
      rw [← hA4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3 : (A ^ 2 * C0 ^ 2).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 := by
      rw [← hA2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h4 : (C0 ^ 3).coeff (6 * A.natDegree) = C0.leadingCoeff ^ 3 := by
      rw [← hdegC, ← hC3, coeff_natDegree, leadingCoeff_pow]
    simpa [h1, h2, h3, h4] using hcoeff
  have hle :
      (lambdaAC0Combined610 A C0).natDegree ≤ 6 * A.natDegree := by
    simp only [lambdaAC0Combined610]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact (natDegree_smul_le610 _ _).trans hA6.le
        · exact (natDegree_smul_le610 _ _).trans hA4C.le
      · exact (natDegree_smul_le610 _ _).trans hA2C2.le
    · exact (natDegree_smul_le610 _ _).trans (hC3.trans hdegC).le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

theorem lambdaAC0_coeff_ne_zero_of_omicron_three
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : 3 * C0.natDegree = 6 * A.natDegree)
    (homi : A.leadingCoeff ^ 2 = 3 * C0.leadingCoeff) :
    (35 / 6561 : k) * A.leadingCoeff ^ 6 -
        (35 / 729 : k) * (A.leadingCoeff ^ 4 * C0.leadingCoeff) +
          (10 / 81 : k) * (A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2) -
            (5 / 81 : k) * C0.leadingCoeff ^ 3 ≠
      0 := by
  set u := A.leadingCoeff ^ 2 with hu
  set v := C0.leadingCoeff with hv
  have hvne : v ≠ 0 := leadingCoeff_ne_zero.mpr hC
  have hform :
      (7 : k) * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3 =
        27 * v ^ 3 :=
    lambda_ac0_of_omicron_factor_three u v (by simpa [u, v] using homi)
  have hne :
      (7 : k) * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3 ≠
        0 := by
    intro hz
    have : (27 : k) * v ^ 3 = 0 := by
      rw [← hform, hz]
    have h27 : (27 : k) ≠ 0 := by norm_num
    exact hvne ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp this).resolve_left h27))
  have hscale := lambdaAC0_scale u v
  intro hz
  have : (5 / 6561 : k) *
        (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) =
      0 := by
    rw [← hscale]
    have h6 : (A.leadingCoeff ^ 2) ^ 3 = A.leadingCoeff ^ 6 := by ring
    have h4 : (A.leadingCoeff ^ 2) ^ 2 = A.leadingCoeff ^ 4 := by ring
    simpa [u, v, h6, h4] using hz
  have h5 : (5 / 6561 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  exact hne ((mul_eq_zero.mp this).resolve_left h5)

theorem lambdaAC0_coeff_ne_zero_of_omicron_nine
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : 3 * C0.natDegree = 6 * A.natDegree)
    (homi : (2 : k) * A.leadingCoeff ^ 2 = 9 * C0.leadingCoeff) :
    (35 / 6561 : k) * A.leadingCoeff ^ 6 -
        (35 / 729 : k) * (A.leadingCoeff ^ 4 * C0.leadingCoeff) +
          (10 / 81 : k) * (A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2) -
            (5 / 81 : k) * C0.leadingCoeff ^ 3 ≠
      0 := by
  set u := A.leadingCoeff ^ 2 with hu
  set v := C0.leadingCoeff with hv
  have hune : u ≠ 0 := pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hA)
  have hform :
      (9 : k) * (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) =
        u ^ 3 :=
    lambda_ac0_of_omicron_factor_nine u v (by simpa [u, v] using homi)
  have hne :
      (7 : k) * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3 ≠
        0 := by
    intro hz
    have : (9 : k) * (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 -
          81 * v ^ 3) = 0 := by
      simp [hz]
    rw [hform] at this
    exact hune ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp this)
  have hscale := lambdaAC0_scale u v
  intro hz
  have : (5 / 6561 : k) *
        (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) =
      0 := by
    rw [← hscale]
    have h6 : (A.leadingCoeff ^ 2) ^ 3 = A.leadingCoeff ^ 6 := by ring
    have h4 : (A.leadingCoeff ^ 2) ^ 2 = A.leadingCoeff ^ 4 := by ring
    simpa [u, v, h6, h4] using hz
  have h5 : (5 / 6561 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  exact hne ((mul_eq_zero.mp this).resolve_left h5)

/-- Euclidean identity relating the `A`–`C₀` `λ` cubic to the raw-tail
cubic: `13 λ - 7 raw = 9 v (7 u² - 60 u v + 135 v²)`. -/
theorem lambda_raw_ac0_identity (u v : k) :
    (13 : k) * (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) -
        7 * (13 * u ^ 3 - 126 * u ^ 2 * v + 378 * u * v ^ 2 - 324 * v ^ 3) =
      9 * v * (7 * u ^ 2 - 60 * u * v + 135 * v ^ 2) := by
  ring

/-- Euclidean identity: `7 λ = (7 u - 3 v) q + 9 v² (u - 18 v)`. -/
theorem lambda_q_ac0_identity (u v : k) :
    (7 : k) * (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) =
      (7 * u - 3 * v) * (7 * u ^ 2 - 60 * u * v + 135 * v ^ 2) +
        9 * v ^ 2 * (u - 18 * v) := by
  ring

theorem q_ac0_ne_zero_of_u_eq_eighteen (u v : k)
    (hv : v ≠ 0) (hu : u = 18 * v) :
    (7 : k) * u ^ 2 - 60 * u * v + 135 * v ^ 2 ≠ 0 := by
  simp [hu]
  intro h
  have : (1323 : k) * v ^ 2 = 0 := by
    linear_combination h
  have h1323 : (1323 : k) ≠ 0 := by norm_num
  exact hv ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
    ((mul_eq_zero.mp this).resolve_left h1323))

/-- If the `A`–`C₀` `λ` cubic vanishes and `C₀ ≠ 0`, the companion raw-tail
cubic cannot vanish. -/
theorem raw_ac0_ne_zero_of_lambda_zero (u v : k)
    (hv : v ≠ 0)
    (hlam :
      (7 : k) * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3 = 0) :
    (13 : k) * u ^ 3 - 126 * u ^ 2 * v + 378 * u * v ^ 2 - 324 * v ^ 3 ≠
      0 := by
  intro hraw
  have hid := lambda_raw_ac0_identity u v
  have hq : (9 : k) * v * (7 * u ^ 2 - 60 * u * v + 135 * v ^ 2) = 0 := by
    rw [← hid, hlam, hraw]
    ring
  have h9 : (9 : k) ≠ 0 := by norm_num
  have h9v : (9 : k) * v ≠ 0 := mul_ne_zero h9 hv
  have hq0 : (7 : k) * u ^ 2 - 60 * u * v + 135 * v ^ 2 = 0 :=
    (mul_eq_zero.mp hq).resolve_left h9v
  have hid2 := lambda_q_ac0_identity u v
  have hrem : (9 : k) * v ^ 2 * (u - 18 * v) = 0 := by
    have := hid2
    rw [hlam, hq0, mul_zero, mul_zero, zero_add] at this
    exact this.symm
  have hu18 : u = 18 * v := by
    have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
    have h9v2 : (9 : k) * v ^ 2 ≠ 0 := mul_ne_zero h9 hv2
    have : u - 18 * v = 0 :=
      (mul_eq_zero.mp hrem).resolve_left h9v2
    linear_combination this
  exact q_ac0_ne_zero_of_u_eq_eighteen u v hv hu18 hq0

theorem rawAC0_scale (u v : k) :
    (-(65 / 19683 : k)) * u ^ 3 + (70 / 2187 : k) * (u ^ 2 * v) -
        (70 / 729 : k) * (u * v ^ 2) + (20 / 243 : k) * v ^ 3 =
      (-(5 / 19683 : k)) *
        (13 * u ^ 3 - 126 * u ^ 2 * v + 378 * u * v ^ 2 - 324 * v ^ 3) := by
  ring

/-- Unique `κ` face `B C₀²` on the `B`–`C₀` pair-tie. -/
theorem kappa_BC0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BC0RatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hCne : C0 ≠ 0 := by
    intro hC0
    have : C0.natDegree = 0 := by simp [hC0]
    rcases hcone with ⟨hBpos, htie, _⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (kappaBC0Face610 B C0).natDegree =
        B.natDegree + 2 * C0.natDegree := by
    simp only [kappaBC0Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne),
      natDegree_pow]
  have hrest :=
    degreeZeroKappaNoBC0_natDegree_lt l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0 hcone
  rw [degreeZeroKappaPolynomial610_eq_BC0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, htie, _⟩
  omega

/-- Unique `κ` face `B C₀²` on the `B`–`C₀`–`E₀` triple. -/
theorem kappa_BC0E0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BC0E0RatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hCne : C0 ≠ 0 := by
    intro hC0
    have : C0.natDegree = 0 := by simp [hC0]
    rcases hcone with ⟨hBpos, htie, _⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (kappaBC0Face610 B C0).natDegree =
        B.natDegree + 2 * C0.natDegree := by
    simp only [kappaBC0Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne),
      natDegree_pow]
  have hrest :=
    degreeZeroKappaNoBC0_natDegree_lt_of_BC0E0 l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroKappaPolynomial610_eq_BC0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, htie, _⟩
  omega

/-- Unique `λ` face `A D₀²`. -/
theorem lambda_AD02_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedAD02LeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (lambdaAD02Face610 A D0).natDegree =
        A.natDegree + 2 * D0.natDegree := by
    simp only [lambdaAD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoAD02_natDegree_lt l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_AD02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, _⟩
  omega

/-- Unique `λ` face `A² B D₀`. -/
theorem lambda_A2BD0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedA2BD0LeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨_, hBpos, _⟩
    simp [hB0] at hBpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, _, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (20 / 81 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      (lambdaA2BD0Face610 A B D0).natDegree =
        2 * A.natDegree + B.natDegree + D0.natDegree := by
    simp only [lambdaA2BD0Face610]
    rw [natDegree_smul _ hc,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hDne,
      natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoA2BD0_natDegree_lt l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_A2BD0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hDpos, _⟩
  omega

/-- Unique `λ` face `B C₀ D₀`. -/
theorem lambda_BC0D0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedBC0D0LeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hCne : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨_, hCpos, _⟩
    simp [hC0] at hCpos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, _, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(10 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (lambdaBC0D0Face610 B C0 D0).natDegree =
        B.natDegree + C0.natDegree + D0.natDegree := by
    simp only [lambdaBC0D0Face610]
    rw [natDegree_smul _ hc,
      natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
  have hrest :=
    degreeZeroLambdaNoBC0D0_natDegree_lt l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_BC0D0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hDpos, _⟩
  omega

/-- Primitive face `B³ (2 B² - 15 E₀)` on the `B`–`E₀` tie cannot drop
together with the `λ` combination. -/
theorem primitive_BE0_coeff_ne_zero_of_lambda_drop
    {B E0 : k[X]}
    (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : 2 * E0.natDegree = 4 * B.natDegree)
    (hlam :
      (5 / 243 : k) * B.leadingCoeff ^ 4 -
          (5 / 27 : k) * (B.leadingCoeff ^ 2 * E0.leadingCoeff) +
            (5 / 9 : k) * E0.leadingCoeff ^ 2 =
        0)
    (hprim :
      (2 : k) * B.leadingCoeff ^ 2 - 15 * E0.leadingCoeff = 0) :
    False := by
  set r := B.leadingCoeff ^ 2 with hr
  set s := E0.leadingCoeff with hs
  have hrne : r ≠ 0 := pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hB)
  have hprim' : (2 : k) * r = 15 * s := by
    linear_combination (hprim)
  have hform :
      (25 : k) * (r ^ 2 - 9 * r * s + 27 * s ^ 2) = 7 * r ^ 2 :=
    lambda_be0_of_primitive_factor r s (by simpa [r, s] using hprim')
  have hscale := lambdaBE0_scale r s
  have hlam0 : (5 / 243 : k) * (r ^ 2 - 9 * r * s + 27 * s ^ 2) = 0 := by
    have h4 : (B.leadingCoeff ^ 2) ^ 2 = B.leadingCoeff ^ 4 := by ring
    rw [← hscale]
    simpa [r, s, h4] using hlam
  have h5 : (5 / 243 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hcubic : r ^ 2 - 9 * r * s + 27 * s ^ 2 = 0 :=
    (mul_eq_zero.mp hlam0).resolve_left h5
  have : (25 : k) * (r ^ 2 - 9 * r * s + 27 * s ^ 2) = 0 := by
    simp [hcubic]
  rw [hform] at this
  have h7 : (7 : k) ≠ 0 := by norm_num
  exact hrne ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
    ((mul_eq_zero.mp this).resolve_left h7))

theorem primitiveBE0Combined610_natDegree_eq_of_coeff_ne
    {B E0 : k[X]}
    (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : 2 * E0.natDegree = 4 * B.natDegree)
    (hcoeff :
      (2 : k) * B.leadingCoeff ^ 2 - 15 * E0.leadingCoeff ≠ 0) :
    (primitiveBE0Combined610 B E0).natDegree = 5 * B.natDegree := by
  have hB5 : (B ^ 5).natDegree = 5 * B.natDegree := natDegree_pow B 5
  have hB3E :
      (B ^ 3 * E0).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hB) hE, natDegree_pow]
    omega
  have hc1 : (-(4 / 243 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hc2 : (10 / 81 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have htop :
      (primitiveBE0Combined610 B E0).coeff (5 * B.natDegree) ≠ 0 := by
    simp only [primitiveBE0Combined610, coeff_add, coeff_smul, smul_eq_mul]
    have h1 : (B ^ 5).coeff (5 * B.natDegree) = B.leadingCoeff ^ 5 := by
      rw [← hB5, coeff_natDegree, leadingCoeff_pow]
    have h2 : (B ^ 3 * E0).coeff (5 * B.natDegree) =
        B.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [← hB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    simp only [h1, h2]
    have :
        (-(4 / 243 : k)) * B.leadingCoeff ^ 5 +
            (10 / 81 : k) * (B.leadingCoeff ^ 3 * E0.leadingCoeff) =
          (-(2 / 243 : k)) * B.leadingCoeff ^ 3 *
            (2 * B.leadingCoeff ^ 2 - 15 * E0.leadingCoeff) := by
      ring
    rw [this]
    exact mul_ne_zero
      (mul_ne_zero
        (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num)))
        (pow_ne_zero 3 (leadingCoeff_ne_zero.mpr hB)))
      hcoeff
  have hle :
      (primitiveBE0Combined610 B E0).natDegree ≤ 5 * B.natDegree := by
    simp only [primitiveBE0Combined610]
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_smul_le610 _ _).trans hB5.le)
        ((natDegree_smul_le610 _ _).trans hB3E.le))
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

theorem lambdaBE0Combined610_natDegree_eq_of_coeff_ne
    {B E0 : k[X]}
    (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : 2 * E0.natDegree = 4 * B.natDegree)
    (hcoeff :
      (5 / 243 : k) * B.leadingCoeff ^ 4 -
          (5 / 27 : k) * (B.leadingCoeff ^ 2 * E0.leadingCoeff) +
            (5 / 9 : k) * E0.leadingCoeff ^ 2 ≠
        0) :
    (lambdaBE0Combined610 B E0).natDegree = 4 * B.natDegree := by
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hE2 : (E0 ^ 2).natDegree = 2 * E0.natDegree := natDegree_pow E0 2
  have hB2E :
      (B ^ 2 * E0).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hB) hE, natDegree_pow]
    omega
  have htop :
      (lambdaBE0Combined610 B E0).coeff (4 * B.natDegree) ≠ 0 := by
    simp only [lambdaBE0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 := by
      rw [← hB4, coeff_natDegree, leadingCoeff_pow]
    have h2 : (B ^ 2 * E0).coeff (4 * B.natDegree) =
        B.leadingCoeff ^ 2 * E0.leadingCoeff := by
      rw [← hB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3 : (E0 ^ 2).coeff (4 * B.natDegree) = E0.leadingCoeff ^ 2 := by
      rw [← htie, ← hE2, coeff_natDegree, leadingCoeff_pow]
    simpa [h1, h2, h3] using hcoeff
  have hle :
      (lambdaBE0Combined610 B E0).natDegree ≤ 4 * B.natDegree := by
    simp only [lambdaBE0Combined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_smul_le610 _ _).trans hB4.le
      · exact (natDegree_smul_le610 _ _).trans hB2E.le
    · exact (natDegree_smul_le610 _ _).trans (hE2.trans htie).le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

theorem lambda_BE0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BE0RatioTieCone610 A B C0 D0 E0)
    (j : k) (hj : j ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hEne : E0 ≠ 0 := by
    intro hE0
    have : E0.natDegree = 0 := by simp [hE0]
    rcases hcone with ⟨hBpos, htie, _⟩
    omega
  have htie : 2 * E0.natDegree = 4 * B.natDegree := hcone.2.1
  have hprimDeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  by_cases hlamDrop :
      (5 / 243 : k) * B.leadingCoeff ^ 4 -
          (5 / 27 : k) * (B.leadingCoeff ^ 2 * E0.leadingCoeff) +
            (5 / 9 : k) * E0.leadingCoeff ^ 2 =
        0
  · by_cases hprimDrop :
        (2 : k) * B.leadingCoeff ^ 2 - 15 * E0.leadingCoeff = 0
    · exact primitive_BE0_coeff_ne_zero_of_lambda_drop hBne hEne htie
        hlamDrop hprimDrop
    · have hcomb :=
        primitiveBE0Combined610_natDegree_eq_of_coeff_ne hBne hEne htie
          hprimDrop
      have hrest :=
        degreeZeroPrimitiveNoBE0_natDegree_lt l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 hcone
      rw [degreeZeroPrimitivePolynomial610_eq_BE0_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
        hcomb] at hprimDeg
      rcases hcone with ⟨hBpos, _⟩
      omega
  · have hcomb :=
      lambdaBE0Combined610_natDegree_eq_of_coeff_ne hBne hEne htie
        hlamDrop
    have hrest :=
      degreeZeroLambdaNoBE0_natDegree_lt l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 hcone
    rw [degreeZeroLambdaPolynomial610_eq_BE0_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
      hcomb] at hdeg
    rcases hcone with ⟨hBpos, _⟩
    omega

set_option maxHeartbeats 16000000 in
theorem lambdaAE0Combined610_natDegree_eq_of_coeff_ne
    {A E0 : k[X]}
    (hA : A ≠ 0) (hE : E0 ≠ 0)
    (htie : 2 * E0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 +
          (20 / 243 : k) * (A.leadingCoeff ^ 3 * E0.leadingCoeff) +
            (5 / 9 : k) * E0.leadingCoeff ^ 2 ≠
        0) :
    (lambdaAE0Combined610 A E0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hE2 : (E0 ^ 2).natDegree = 2 * E0.natDegree := natDegree_pow E0 2
  have hA3E :
      (A ^ 3 * E0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) hE, natDegree_pow]
    omega
  have htop :
      (lambdaAE0Combined610 A E0).coeff (6 * A.natDegree) ≠ 0 := by
    simp only [lambdaAE0Combined610, coeff_add, coeff_smul, smul_eq_mul]
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 3 * E0).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [← hA3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3 : (E0 ^ 2).coeff (6 * A.natDegree) = E0.leadingCoeff ^ 2 := by
      rw [← htie, ← hE2, coeff_natDegree, leadingCoeff_pow]
    simpa [h1, h2, h3] using hcoeff
  have hle :
      (lambdaAE0Combined610 A E0).natDegree ≤ 6 * A.natDegree := by
    simp only [lambdaAE0Combined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_smul_le610 _ _).trans hA6.le
      · exact (natDegree_smul_le610 _ _).trans hA3E.le
    · exact (natDegree_smul_le610 _ _).trans (hE2.trans htie).le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem rawAE0Combined610_natDegree_eq_of_coeff_ne
    {A E0 : k[X]}
    (hA : A ≠ 0) (hE : E0 ≠ 0)
    (htie : 2 * E0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (13 : k) * A.leadingCoeff ^ 3 + 189 * E0.leadingCoeff ≠ 0) :
    (rawAE0Combined610 A E0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA4E :
      (A ^ 4 * E0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hE, natDegree_pow]
    omega
  have htop :
      (rawAE0Combined610 A E0).coeff (7 * A.natDegree) ≠ 0 := by
    simp only [rawAE0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 4 * E0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * E0.leadingCoeff := by
      rw [← hA4E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have :
        (-(65 / 19683 : k)) * A.leadingCoeff ^ 7 -
            (35 / 729 : k) * (A.leadingCoeff ^ 4 * E0.leadingCoeff) =
          (-(5 / 19683 : k)) * A.leadingCoeff ^ 4 *
            (13 * A.leadingCoeff ^ 3 + 189 * E0.leadingCoeff) := by
      ring
    simp only [h1, h2]
    rw [this]
    exact mul_ne_zero
      (mul_ne_zero
        (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num)))
        (pow_ne_zero 4 (leadingCoeff_ne_zero.mpr hA)))
      hcoeff
  have hle :
      (rawAE0Combined610 A E0).natDegree ≤ 7 * A.natDegree := by
    simp only [rawAE0Combined610]
    exact (natDegree_sub_le _ _).trans
      (max_le ((natDegree_smul_le610 _ _).trans hA7.le)
        ((natDegree_smul_le610 _ _).trans hA4E.le))
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


set_option maxHeartbeats 16000000 in
theorem lambda_A6AD02_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : A6AD02TieCone610 A B C0 D0 E0)
    (hkapDeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0)
    (hlamDeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have htie : A.natDegree + 2 * D0.natDegree = 6 * A.natDegree :=
    hcone.2.2.1
  by_cases hdrop :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (5 / 27 : k) * (A.leadingCoeff * D0.leadingCoeff ^ 2) =
        0
  · have hc : (20 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hlead :
        (kappaA3D0Face610 A D0).natDegree =
          3 * A.natDegree + D0.natDegree := by
      simp only [kappaA3D0Face610]
      rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 3 hAne) hDne,
        natDegree_pow]
    have hrest :=
      degreeZeroKappaNoA3D0_natDegree_lt l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 hcone
    rw [degreeZeroKappaPolynomial610_eq_A3D0_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
      hlead] at hkapDeg
    rcases hcone with ⟨hApos, hDpos, htie', _⟩
    omega
  · have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
    have hAD :
        (A * D0 ^ 2).natDegree = 6 * A.natDegree := by
      rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
      omega
    have htop :
        (lambdaA6AD02Combined610 A D0).coeff (6 * A.natDegree) ≠ 0 := by
      simp only [lambdaA6AD02Combined610, coeff_sub, coeff_smul,
        smul_eq_mul]
      have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
        rw [← hA6, coeff_natDegree, leadingCoeff_pow]
      have h2 : (A * D0 ^ 2).coeff (6 * A.natDegree) =
          A.leadingCoeff * D0.leadingCoeff ^ 2 := by
        rw [← hAD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      simpa [h1, h2] using hdrop
    have hle :
        (lambdaA6AD02Combined610 A D0).natDegree ≤ 6 * A.natDegree := by
      simp only [lambdaA6AD02Combined610]
      exact (natDegree_sub_le _ _).trans
        (max_le ((natDegree_smul_le610 _ _).trans hA6.le)
          ((natDegree_smul_le610 _ _).trans hAD.le))
    have hcomb :
        (lambdaA6AD02Combined610 A D0).natDegree = 6 * A.natDegree :=
      natDegree_eq_of_le_of_coeff_ne_zero hle htop
    have hrest :=
      degreeZeroLambdaNoA6AD02_natDegree_lt l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0 hcone
    rw [degreeZeroLambdaPolynomial610_eq_A6AD02_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
      hcomb] at hlamDeg
    rcases hcone with ⟨hApos, _⟩
    omega

set_option maxHeartbeats 16000000 in
theorem kappa_AB_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : ABRatioTieCone610 A B C0 D0 E0)
    (hlamDeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0)
    (hkapDeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBpos : 0 < B.natDegree := hcone.1
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  by_cases hdrop :
      (7 : k) * A.leadingCoeff ^ 3 - 12 * B.leadingCoeff ^ 2 = 0
  · have hrel : (7 : k) * A.leadingCoeff ^ 3 =
        12 * B.leadingCoeff ^ 2 := by linear_combination hdrop
    have hlamNe :=
      lambdaHighBTie_coeff_ne_zero_of_kappa_factor hAne hBne htie hrel
    have hcombdeg :=
      lambdaHighBTieCombined610_natDegree_eq_of_coeff_ne hAne hBne htie
        hlamNe
    have hrest :=
      degreeZeroLambdaNoHighBTieRest610_natDegree_lt_of_AB l alpha beta
        delta epsilon zeta eta theta A B C0 D0 E0 hcone
    have hsum :=
      degreeZeroLambdaPolynomial610_eq_highBTie_add_rest l alpha beta
        delta epsilon zeta eta theta A B C0 D0 E0
    rw [hsum, natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hlamDeg
    omega
  · have hA4B :
        (A ^ 4 * B).natDegree = 4 * A.natDegree + B.natDegree := by
      rw [natDegree_mul (pow_ne_zero 4 hAne) hBne, natDegree_pow]
    have hAB3 :
        (A * B ^ 3).natDegree = 4 * A.natDegree + B.natDegree := by
      rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
      omega
    have htop :
        (kappaHighBTieExpanded610 A B).coeff
            (4 * A.natDegree + B.natDegree) ≠
          0 := by
      simp only [kappaHighBTieExpanded610, coeff_add, coeff_smul,
        smul_eq_mul]
      have h1 : (A ^ 4 * B).coeff (4 * A.natDegree + B.natDegree) =
          A.leadingCoeff ^ 4 * B.leadingCoeff := by
        rw [← hA4B, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      have h2 : (A * B ^ 3).coeff (4 * A.natDegree + B.natDegree) =
          A.leadingCoeff * B.leadingCoeff ^ 3 := by
        rw [← hAB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      simp only [h1, h2]
      have :
          (-(35 / 729 : k)) * (A.leadingCoeff ^ 4 * B.leadingCoeff) +
              (20 / 243 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) =
            (-(5 / 729 : k)) * A.leadingCoeff * B.leadingCoeff *
              (7 * A.leadingCoeff ^ 3 - 12 * B.leadingCoeff ^ 2) := by
        ring
      rw [this]
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by
              have : (5 / 729 : k) ≠ 0 :=
                div_ne_zero (by norm_num) (by norm_num)
              intro h0
              exact this (neg_eq_zero.mp h0))
            (leadingCoeff_ne_zero.mpr hAne))
          (leadingCoeff_ne_zero.mpr hBne))
        hdrop
    have hle :
        (kappaHighBTieExpanded610 A B).natDegree ≤
          4 * A.natDegree + B.natDegree := by
      simp only [kappaHighBTieExpanded610]
      exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_smul_le610 _ _).trans hA4B.le)
          ((natDegree_smul_le610 _ _).trans hAB3.le))
    have hcombdeg :
        (kappaHighBTieExpanded610 A B).natDegree =
          4 * A.natDegree + B.natDegree :=
      natDegree_eq_of_le_of_coeff_ne_zero hle htop
    have hrest :=
      degreeZeroKappaNoHighBTieRest610_natDegree_lt_of_AB l alpha beta
        delta epsilon zeta eta theta A B C0 D0 E0 hcone
    have hsum :=
      degreeZeroKappaPolynomial610_eq_highBTie_add_rest l alpha beta
        delta epsilon zeta eta theta A B C0 D0 E0
    rw [hsum, natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hkapDeg
    omega

end RatioTieImpossible610

/-! ## Finish family (a): parametrized ties `2 deg D₀ = 5 deg A` and
`2 deg E₀ = 3 deg C₀`, plus the `A`–`C₀` raw-tail comparison

The `A⁶`/`A D₀²` impossibility `lambda_A6AD02_impossible` is already
kernel-accepted (the rest bound sees `2 deg D₀ = 5 deg A` after
`compute_degree`).  The `C₀`–`E₀` rest bound is the divisibility
artefact: `omega` cannot cancel `2 e = 3 c` until `deg C₀ = 2 m` and
`deg E₀ = 3 m` are substituted.  The `A`–`C₀` Euclidean identities are
already on the parent of this section; the missing leading-coefficient
comparison is the scaled cubic `(-(5/19683)) * (13 u³ - ⋯)`. -/

section FinishFamilyA610

variable {k : Type*} [Field k] [CharZero k]

/-- If `2 n = 5 m` then `m = 2 k` and `n = 5 k`. -/
theorem exists_param_two_five {m n : ℕ} (h : 2 * n = 5 * m) :
    ∃ k, m = 2 * k ∧ n = 5 * k := by
  have h2 : 2 ∣ 5 * m := ⟨n, by rw [h, mul_comm]⟩
  have hcop : Nat.Coprime 2 5 := by decide
  have hm : 2 ∣ m := hcop.dvd_of_dvd_mul_left h2
  obtain ⟨k, hk⟩ := hm
  refine ⟨k, hk, ?_⟩
  have : 2 * n = 2 * (5 * k) := by
    rw [h, hk]
    omega
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this

/-- If `2 n = 3 m` then `m = 2 k` and `n = 3 k`. -/
theorem exists_param_two_three {m n : ℕ} (h : 2 * n = 3 * m) :
    ∃ k, m = 2 * k ∧ n = 3 * k := by
  have h2 : 2 ∣ 3 * m := ⟨n, by rw [h, mul_comm]⟩
  have hcop : Nat.Coprime 2 3 := by decide
  have hm : 2 ∣ m := hcop.dvd_of_dvd_mul_left h2
  obtain ⟨k, hk⟩ := hm
  refine ⟨k, hk, ?_⟩
  have : 2 * n = 2 * (3 * k) := by
    rw [h, hk]
    omega
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this

set_option maxHeartbeats 32000000 in
theorem degreeZeroRawFourthTailNoC0E0_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0E0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroRawFourthTailNoC0E0Polynomial610 l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0).natDegree <
      2 * C0.natDegree + E0.natDegree := by
  rcases hcone with ⟨hCpos, htie, hA, hA7, hB, hD1, hD2, hD3, hDomi⟩
  obtain ⟨m, hCm, hEm⟩ := exists_param_two_three htie
  simp only [hCm, hEm] at hCpos hA hA7 hB hD1 hD2 hD3 hDomi
  simp only [degreeZeroRawFourthTailNoC0E0Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt, zero_pow_seven_rt]
  compute_degree
  simp only [hCm, hEm, max_lt_iff]
  have hA1 : 6 * A.natDegree + 1 ≤ 6 * m := Nat.succ_le_of_lt (by omega)
  have hA71 : 7 * A.natDegree + 1 ≤ 7 * m := Nat.succ_le_of_lt (by omega)
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * m := Nat.succ_le_of_lt (by omega)
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * m :=
    Nat.succ_le_of_lt (by omega)
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤ 6 * m :=
    Nat.succ_le_of_lt (by omega)
  have hD31 : B.natDegree + 2 * m + D0.natDegree + 1 ≤ 6 * m :=
    Nat.succ_le_of_lt (by omega)
  have hDomi1 : 2 * m + 2 * D0.natDegree + 1 ≤ 7 * m :=
    Nat.succ_le_of_lt (by omega)
  all_goals omega

/-- Unique `ο` face `C₀² E₀` on the parametrized `C₀`–`E₀` pair-tie. -/
theorem omicron_C0E0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0E0RatioTieCone610 A B C0 D0 E0)
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
  have hCne : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hEne : E0 ≠ 0 := by
    intro hE0
    have : E0.natDegree = 0 := by simp [hE0]
    rcases hcone with ⟨hCpos, htie, _⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (omicronC0E0Face610 C0 E0).natDegree =
        2 * C0.natDegree + E0.natDegree := by
    simp only [omicronC0E0Face610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne,
      natDegree_pow]
  have hrawRest :=
    degreeZeroRawFourthTailNoC0E0_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hcone
  have hAlam :
      ((1 / 3 : k) • (A *
          degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0)).natDegree <
        2 * C0.natDegree + E0.natDegree := by
    have hmul :=
      natDegree_mul_of_natDegree_eq_zero A
        (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) hlamDeg
    have hsm :=
      natDegree_smul_le610 (1 / 3 : k)
        (A * degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0)
    rcases hcone with ⟨hCpos, htie, hA, hA7, _⟩
    omega
  have hBkap :
      ((1 / 6 : k) • (B *
          degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0)).natDegree <
        2 * C0.natDegree + E0.natDegree := by
    have hmul :=
      natDegree_mul_of_natDegree_eq_zero B
        (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) hkapDeg
    have hsm :=
      natDegree_smul_le610 (1 / 6 : k)
        (B * degreeZeroKappaPolynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0)
    rcases hcone with ⟨hCpos, htie, hA, hA7, hB, _⟩
    omega
  have homiEq :
      degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        omicronC0E0Face610 C0 E0 +
          (degreeZeroRawFourthTailNoC0E0Polynomial610 l alpha beta delta
              epsilon zeta eta theta A B C0 D0 E0 +
            ((1 / 6 : k) • (B *
                degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                  zeta eta theta A B C0 D0 E0) +
              (1 / 3 : k) • (A *
                  degreeZeroLambdaPolynomial610 l alpha beta delta
                    epsilon zeta eta theta A B C0 D0 E0))) := by
    simp only [degreeZeroOmicronPolynomial610]
    rw [degreeZeroRawFourthTailPolynomial610_eq_C0E0_add_rest]
    abel
  have hrestSum :
      (degreeZeroRawFourthTailNoC0E0Polynomial610 l alpha beta delta
            epsilon zeta eta theta A B C0 D0 E0 +
          ((1 / 6 : k) • (B *
              degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                zeta eta theta A B C0 D0 E0) +
            (1 / 3 : k) • (A *
                degreeZeroLambdaPolynomial610 l alpha beta delta
                  epsilon zeta eta theta A B C0 D0 E0))).natDegree <
        2 * C0.natDegree + E0.natDegree :=
    natDegree_add_lt610 hrawRest (natDegree_add_lt610 hBkap hAlam)
  rw [homiEq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at homiDeg
  rcases hcone with ⟨hCpos, htie, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem rawAC0Combined610_natDegree_eq_of_coeff_ne
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : 3 * C0.natDegree = 6 * A.natDegree)
    (hcoeff :
      (13 : k) * (A.leadingCoeff ^ 2) ^ 3 -
          126 * (A.leadingCoeff ^ 2) ^ 2 * C0.leadingCoeff +
            378 * A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 -
              324 * C0.leadingCoeff ^ 3 ≠
        0) :
    (rawAC0Combined610 A C0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA5C :
      (A ^ 5 * C0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 5 hA) hC, natDegree_pow]
    omega
  have hA3C2 :
      (A ^ 3 * C0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hC),
      natDegree_pow, natDegree_pow]
    omega
  have hAC3 :
      (A * C0 ^ 3).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hC), natDegree_pow]
    omega
  have htop :
      (rawAC0Combined610 A C0).coeff (7 * A.natDegree) ≠ 0 := by
    simp only [rawAC0Combined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 5 * C0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 5 * C0.leadingCoeff := by
      rw [← hA5C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3 : (A ^ 3 * C0 ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 3 * C0.leadingCoeff ^ 2 := by
      rw [← hA3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h4 : (A * C0 ^ 3).coeff (7 * A.natDegree) =
        A.leadingCoeff * C0.leadingCoeff ^ 3 := by
      rw [← hAC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    set u := A.leadingCoeff ^ 2
    set v := C0.leadingCoeff
    have hfac :
        (-(65 / 19683 : k)) * A.leadingCoeff ^ 7 +
            (70 / 2187 : k) * (A.leadingCoeff ^ 5 * v) -
              (70 / 729 : k) * (A.leadingCoeff ^ 3 * v ^ 2) +
                (20 / 243 : k) * (A.leadingCoeff * v ^ 3) =
          A.leadingCoeff *
            ((-(65 / 19683 : k)) * u ^ 3 + (70 / 2187 : k) * (u ^ 2 * v) -
              (70 / 729 : k) * (u * v ^ 2) + (20 / 243 : k) * v ^ 3) := by
      simp only [u]
      ring
    have hscale := rawAC0_scale u v
    have hsc :
        (-(5 / 19683 : k)) *
            (13 * u ^ 3 - 126 * u ^ 2 * v + 378 * u * v ^ 2 -
              324 * v ^ 3) ≠
          0 :=
      mul_ne_zero
        (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num)))
        (by simpa [u, v] using hcoeff)
    simp only [h1, h2, h3, h4, v]
    rw [hfac, hscale]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hA) hsc
  have hle :
      (rawAC0Combined610 A C0).natDegree ≤ 7 * A.natDegree := by
    simp only [rawAC0Combined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact (natDegree_smul_le610 _ _).trans hA7.le
        · exact (natDegree_smul_le610 _ _).trans hA5C.le
      · exact (natDegree_smul_le610 _ _).trans hA3C2.le
    · exact (natDegree_smul_le610 _ _).trans hAC3.le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
/-- On the `A`–`C₀` tie, either the `λ` combination has degree `6 deg A`
or a dropped `λ` combination forces a raw-tail (hence `ο`) face of
degree `7 deg A`. -/
theorem lambda_AC0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AC0RatioTieCone610 A B C0 D0 E0)
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
  have hCne : C0 ≠ 0 := by
    intro hC0
    have : C0.natDegree = 0 := by simp [hC0]
    rcases hcone with ⟨hApos, htie, _⟩
    omega
  have htie : 3 * C0.natDegree = 6 * A.natDegree := hcone.2.1
  set u := A.leadingCoeff ^ 2 with hu
  set v := C0.leadingCoeff with hv
  have hvne : v ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  by_cases hdrop :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (35 / 729 : k) * (A.leadingCoeff ^ 4 * C0.leadingCoeff) +
            (10 / 81 : k) *
              (A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2) -
              (5 / 81 : k) * C0.leadingCoeff ^ 3 =
        0
  · have hdrop_u :
        (35 / 6561 : k) * u ^ 3 - (35 / 729 : k) * (u ^ 2 * v) +
            (10 / 81 : k) * (u * v ^ 2) - (5 / 81 : k) * v ^ 3 = 0 := by
      have h6 : (A.leadingCoeff ^ 2) ^ 3 = A.leadingCoeff ^ 6 := by ring
      have h4 : (A.leadingCoeff ^ 2) ^ 2 = A.leadingCoeff ^ 4 := by ring
      simpa [u, v, h6, h4] using hdrop
    have hlam0 :
        (7 : k) * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3 =
          0 := by
      have hscale := lambdaAC0_scale u v
      have h5 : (5 / 6561 : k) ≠ 0 :=
        div_ne_zero (by norm_num) (by norm_num)
      have : (5 / 6561 : k) *
            (7 * u ^ 3 - 63 * u ^ 2 * v + 162 * u * v ^ 2 - 81 * v ^ 3) =
          0 := by
        rw [← hscale, hdrop_u]
      exact (mul_eq_zero.mp this).resolve_left h5
    have hrawne := raw_ac0_ne_zero_of_lambda_zero u v hvne hlam0
    have hrawDeg :=
      rawAC0Combined610_natDegree_eq_of_coeff_ne hAne hCne htie hrawne
    have hrawRest :=
      degreeZeroRawFourthTailNoAC0_natDegree_lt l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0 hcone
    have hAlam :
        ((1 / 3 : k) • (A *
            degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
              eta theta A B C0 D0 E0)).natDegree <
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
      rcases hcone with ⟨hApos, _, hB, _⟩
      omega
    have homiEq :
        degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0 =
          rawAC0Combined610 A C0 +
            (degreeZeroRawFourthTailNoAC0Polynomial610 l alpha beta delta
                epsilon zeta eta theta A B C0 D0 E0 +
              ((1 / 6 : k) • (B *
                  degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                    zeta eta theta A B C0 D0 E0) +
                (1 / 3 : k) • (A *
                    degreeZeroLambdaPolynomial610 l alpha beta delta
                      epsilon zeta eta theta A B C0 D0 E0))) := by
      simp only [degreeZeroOmicronPolynomial610]
      rw [degreeZeroRawFourthTailPolynomial610_eq_AC0_add_rest]
      abel
    have hrestSum :
        (degreeZeroRawFourthTailNoAC0Polynomial610 l alpha beta delta
              epsilon zeta eta theta A B C0 D0 E0 +
            ((1 / 6 : k) • (B *
                degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                  zeta eta theta A B C0 D0 E0) +
              (1 / 3 : k) • (A *
                  degreeZeroLambdaPolynomial610 l alpha beta delta
                    epsilon zeta eta theta A B C0 D0 E0))).natDegree <
          7 * A.natDegree :=
      natDegree_add_lt610 hrawRest (natDegree_add_lt610 hBkap hAlam)
    rw [homiEq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hrawDeg]),
      hrawDeg] at homiDeg
    rcases hcone with ⟨hApos, _⟩
    omega
  · have hcomb :=
      lambdaAC0Combined610_natDegree_eq_of_coeff_ne hAne hCne htie hdrop
    exact lambda_AC0_impossible_of_combined_degree l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone hcomb hlamDeg

end FinishFamilyA610

/-! ## Finish family (b): `A`–`E₀` drop via the `ο` face after cancelling
`(A/3) λ`

The identity `rawAE0 + (A/3) λ_AE0 = ο_AE0 + (5/27) A E₀²` makes the
cancelled top monomials invisible.  The raw rest is the `A`–`C₀` rest
without `A⁴ E₀` and `A E₀²`, plus the three `A`–`C₀` extras.
-/

section FinishFamilyB610

variable {k : Type*} [Field k] [CharZero k]

theorem exists_E0_eq_three_A {A E0 : k[X]}
    (htie : 2 * E0.natDegree = 6 * A.natDegree) :
    E0.natDegree = 3 * A.natDegree := by
  have : 2 * E0.natDegree = 2 * (3 * A.natDegree) := by
    rw [htie]
    omega
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this

set_option maxHeartbeats 16000000 in
theorem rawAE0_add_third_A_lambdaAE0 (A E0 : k[X]) :
    rawAE0Combined610 A E0 +
      (1 / 3 : k) • (A * lambdaAE0Combined610 A E0) =
      omicronAE0Combined610 A E0 +
        (5 / 27 : k) • (A * E0 ^ 2) := by
  have hA7 : A * A ^ 6 = A ^ 7 := by rw [← pow_succ']
  have hA4 : A * (A ^ 3 * E0) = A ^ 4 * E0 := by
    rw [← mul_assoc, ← pow_succ']
  simp only [rawAE0Combined610, lambdaAE0Combined610, omicronAE0Combined610,
    mul_add, smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, hA7, hA4]
  module

/-- Raw tail with the `A`–`E₀` top monomials `A⁴ E₀` and `A E₀²` deleted
and the `A`–`C₀` extras restored.  Copied from
`degreeZeroRawFourthTailNoAC0Polynomial610` so the cancelled pair is not
visible to `compute_degree`. -/
def degreeZeroRawFourthTailNoAE0Cancelled610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (175 / 2187 : k) • (A ^ 4 * B ^ 2) -
    (140 / 729 : k) • (A ^ 3 * B * D0) -
    (70 / 243 : k) • (A ^ 2 * B ^ 2 * C0) +
    (20 / 81 : k) • (A ^ 2 * C0 * E0) +
    (10 / 81 : k) • (A ^ 2 * D0 ^ 2) -
    (35 / 729 : k) • (A * B ^ 4) +
    (20 / 81 : k) • (A * B ^ 2 * E0) +
    (40 / 81 : k) • (A * B * C0 * D0) +
    (20 / 243 : k) • (B ^ 3 * D0) +
    (10 / 81 : k) • (B ^ 2 * C0 ^ 2) -
    (10 / 27 : k) • (B * D0 * E0) -
    (5 / 27 : k) • (C0 ^ 2 * E0) -
    (5 / 27 : k) • (C0 * D0 ^ 2) +
    (21 / 512 * l : k) • (A ^ 5 * B) -
    (15 / 256 * l : k) • (A ^ 4 * D0) -
    (15 / 64 * l : k) • (A ^ 3 * B * C0) -
    (15 / 128 * l : k) • (A ^ 2 * B ^ 3) +
    (9 / 32 * l : k) • (A ^ 2 * B * E0) +
    (9 / 32 * l : k) • (A ^ 2 * C0 * D0) +
    (9 / 32 * l : k) • (A * B ^ 2 * D0) +
    (9 / 32 * l : k) • (A * B * C0 ^ 2) -
    (3 / 8 * l : k) • (A * D0 * E0) +
    (3 / 32 * l : k) • (B ^ 3 * C0) -
    (3 / 8 * l : k) • (B * C0 * E0) -
    (3 / 16 * l : k) • (B * D0 ^ 2) -
    (3 / 16 * l : k) • (C0 ^ 2 * D0) +
    (44 / 6561 * alpha : k) • A ^ 6 -
    (40 / 729 * alpha : k) • (A ^ 4 * C0) -
    (80 / 729 * alpha : k) • (A ^ 3 * B ^ 2) +
    (20 / 243 * alpha : k) • (A ^ 3 * E0) +
    (20 / 81 * alpha : k) • (A ^ 2 * B * D0) +
    (10 / 81 * alpha : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 * alpha : k) • (A * B ^ 2 * C0) -
    (8 / 27 * alpha : k) • (A * C0 * E0) -
    (4 / 27 * alpha : k) • (A * D0 ^ 2) +
    (5 / 243 * alpha : k) • B ^ 4 -
    (4 / 27 * alpha : k) • (B ^ 2 * E0) -
    (8 / 27 * alpha : k) • (B * C0 * D0) -
    (4 / 81 * alpha : k) • C0 ^ 3 +
    (2 / 9 * alpha : k) • E0 ^ 2 -
    (6545 / 186624 * beta : k) • (A ^ 4 * B) +
    (385 / 7776 * beta : k) • (A ^ 3 * D0) +
    (385 / 2592 * beta : k) • (A ^ 2 * B * C0) +
    (385 / 7776 * beta : k) • (A * B ^ 3) -
    (35 / 216 * beta : k) • (A * B * E0) -
    (35 / 216 * beta : k) • (A * C0 * D0) -
    (35 / 432 * beta : k) • (B ^ 2 * D0) -
    (35 / 432 * beta : k) • (B * C0 ^ 2) +
    (7 / 36 * beta : k) • (D0 * E0) -
    (455 / 7776 * delta : k) • (A ^ 3 * B) +
    (35 / 432 * delta : k) • (A ^ 2 * D0) +
    (35 / 216 * delta : k) • (A * B * C0) +
    (35 / 1296 * delta : k) • B ^ 3 -
    (5 / 36 * delta : k) • (B * E0) -
    (5 / 36 * delta : k) • (C0 * D0) -
    (7 / 243 * epsilon : k) • A ^ 4 +
    (4 / 27 * epsilon : k) • (A ^ 2 * C0) +
    (4 / 27 * epsilon : k) • (A * B ^ 2) -
    (2 / 9 * epsilon : k) • (A * E0) -
    (2 / 9 * epsilon : k) • (B * D0) -
    (1 / 9 * epsilon : k) • C0 ^ 2 +
    (5 / 81 * eta : k) • A ^ 3 -
    (2 / 9 * eta : k) • (A * C0) -
    (1 / 9 * eta : k) • B ^ 2 +
    (1 / 3 * eta : k) • E0 -
    (5 / 36 * theta : k) • (A * B) +
    (1 / 6 * theta : k) • D0 +
    (3 / 16 * zeta : k) • (A ^ 2 * B) -
    (1 / 4 * zeta : k) • (A * D0) -
    (1 / 4 * zeta : k) • (B * C0) +
    (70 / 2187 : k) • (A ^ 5 * C0) -
    (70 / 729 : k) • (A ^ 3 * C0 ^ 2) +
    (20 / 243 : k) • (A * C0 ^ 3)

set_option maxHeartbeats 16000000 in
theorem degreeZeroRawFourthTailNoAE0Cancelled610_eq
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroRawFourthTailNoAE0Cancelled610 l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0 =
      degreeZeroRawFourthTailNoAE0Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 +
        (5 / 27 : k) • (A * E0 ^ 2) := by
  simp only [degreeZeroRawFourthTailNoAE0Cancelled610,
    degreeZeroRawFourthTailNoAE0Polynomial610,
    degreeZeroRawFourthTailNoAC0Polynomial610]
  module

set_option maxHeartbeats 16000000 in
theorem omicronAE0Combined610_natDegree_eq_of_coeff_ne
    {A E0 : k[X]}
    (hA : A ≠ 0) (hE : E0 ≠ 0)
    (htie : 2 * E0.natDegree = 6 * A.natDegree)
    (hcoeff : (2 : k) * A.leadingCoeff ^ 3 + 27 * E0.leadingCoeff ≠ 0) :
    (omicronAE0Combined610 A E0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA4E :
      (A ^ 4 * E0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hE, natDegree_pow]
    omega
  have htop :
      (omicronAE0Combined610 A E0).coeff (7 * A.natDegree) ≠ 0 := by
    simp only [omicronAE0Combined610, coeff_sub, coeff_smul, smul_eq_mul]
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 4 * E0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * E0.leadingCoeff := by
      rw [← hA4E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have :
        (-(10 / 6561 : k)) * A.leadingCoeff ^ 7 -
            (5 / 243 : k) * (A.leadingCoeff ^ 4 * E0.leadingCoeff) =
          (-(5 / 6561 : k)) * A.leadingCoeff ^ 4 *
            (2 * A.leadingCoeff ^ 3 + 27 * E0.leadingCoeff) := by
      ring
    simp only [h1, h2]
    rw [this]
    exact mul_ne_zero
      (mul_ne_zero
        (neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num)))
        (pow_ne_zero 4 (leadingCoeff_ne_zero.mpr hA)))
      hcoeff
  have hle :
      (omicronAE0Combined610 A E0).natDegree ≤ 7 * A.natDegree := by
    simp only [omicronAE0Combined610]
    exact (natDegree_sub_le _ _).trans
      (max_le ((natDegree_smul_le610 _ _).trans hA7.le)
        ((natDegree_smul_le610 _ _).trans hA4E.le))
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

theorem omicron_ae0_factor_ne_zero_of_lambda_drop
    {A E0 : k[X]}
    (hA : A ≠ 0)
    (hlam :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 +
          (20 / 243 : k) * (A.leadingCoeff ^ 3 * E0.leadingCoeff) +
            (5 / 9 : k) * E0.leadingCoeff ^ 2 =
        0) :
    (2 : k) * A.leadingCoeff ^ 3 + 27 * E0.leadingCoeff ≠ 0 := by
  set p := A.leadingCoeff ^ 3 with hp
  set q := E0.leadingCoeff with hq
  have hpne : p ≠ 0 := pow_ne_zero 3 (leadingCoeff_ne_zero.mpr hA)
  have hdrop_p :
      (35 / 6561 : k) * p ^ 2 + (20 / 243 : k) * (p * q) +
          (5 / 9 : k) * q ^ 2 = 0 := by
    have h6 : (A.leadingCoeff ^ 3) ^ 2 = A.leadingCoeff ^ 6 := by ring
    simpa [p, q, h6] using hlam
  have hlam0 :
      (7 : k) * p ^ 2 + 108 * p * q + 729 * q ^ 2 = 0 := by
    have hscale := lambdaAE0_scale p q
    have h5 : (5 / 6561 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have : (5 / 6561 : k) * (7 * p ^ 2 + 108 * p * q + 729 * q ^ 2) =
        0 := by
      rw [← hscale, hdrop_p]
    exact (mul_eq_zero.mp this).resolve_left h5
  intro hf
  have hform := lambda_ae0_of_omicron_factor p q (by simpa [p, q] using hf)
  have : (3 : k) * p ^ 2 = 0 := by
    rw [← hform, hlam0]
  have h3 : (3 : k) ≠ 0 := by norm_num
  exact hpne ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
    ((mul_eq_zero.mp this).resolve_left h3))

set_option maxHeartbeats 32000000 in
theorem degreeZeroRawFourthTailNoAE0Cancelled610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AE0RatioTieCone610 A B C0 D0 E0) :
    (degreeZeroRawFourthTailNoAE0Cancelled610 l alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, htie, hB, hC, hD1, hD2, hD3⟩
  have hE : E0.natDegree = 3 * A.natDegree :=
    exists_E0_eq_three_A htie
  simp only [degreeZeroRawFourthTailNoAE0Cancelled610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_rt, zero_pow_three_rt,
    zero_pow_four_rt, zero_pow_five_rt, zero_pow_six_rt]
  compute_degree
  simp only [hE, max_lt_iff]
  have hB1 : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hB
  have hC1 : 3 * C0.natDegree + 1 ≤ 6 * A.natDegree := Nat.succ_le_of_lt hC
  have hD11 : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree :=
    Nat.succ_le_of_lt hD1
  have hD21 : 2 * A.natDegree + B.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD2
  have hD31 : B.natDegree + C0.natDegree + D0.natDegree + 1 ≤
      6 * A.natDegree := Nat.succ_le_of_lt hD3
  all_goals omega

set_option maxHeartbeats 16000000 in
theorem lambda_AE0_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AE0RatioTieCone610 A B C0 D0 E0)
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
  have hEne : E0 ≠ 0 := by
    intro hE0
    have : E0.natDegree = 0 := by simp [hE0]
    rcases hcone with ⟨hApos, htie, _⟩
    omega
  have htie : 2 * E0.natDegree = 6 * A.natDegree := hcone.2.1
  by_cases hdrop :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 +
          (20 / 243 : k) * (A.leadingCoeff ^ 3 * E0.leadingCoeff) +
            (5 / 9 : k) * E0.leadingCoeff ^ 2 =
        0
  · have hfac :=
      omicron_ae0_factor_ne_zero_of_lambda_drop hAne hdrop
    have hcomb :=
      omicronAE0Combined610_natDegree_eq_of_coeff_ne hAne hEne htie hfac
    have homiEq :
        degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0 =
          omicronAE0Combined610 A E0 +
            (degreeZeroRawFourthTailNoAE0Cancelled610 l alpha beta delta
                epsilon zeta eta theta A B C0 D0 E0 +
              ((1 / 6 : k) • (B *
                  degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                    zeta eta theta A B C0 D0 E0) +
                (1 / 3 : k) • (A *
                    degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta
                      epsilon zeta eta theta A B C0 D0 E0))) := by
      simp only [degreeZeroOmicronPolynomial610]
      rw [degreeZeroRawFourthTailPolynomial610_eq_AE0_add_rest,
        degreeZeroLambdaPolynomial610_eq_AE0_add_rest]
      simp only [mul_add, smul_add]
      have hface := rawAE0_add_third_A_lambdaAE0 A E0
      rw [degreeZeroRawFourthTailNoAE0Cancelled610_eq]
      calc
        rawAE0Combined610 A E0 +
              degreeZeroRawFourthTailNoAE0Polynomial610 l alpha beta delta
                epsilon zeta eta theta A B C0 D0 E0 +
            (1 / 6 : k) • (B *
                degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                  zeta eta theta A B C0 D0 E0) +
          ((1 / 3 : k) • (A * lambdaAE0Combined610 A E0) +
            (1 / 3 : k) • (A *
                degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta
                  epsilon zeta eta theta A B C0 D0 E0)) =
            (rawAE0Combined610 A E0 +
                (1 / 3 : k) • (A * lambdaAE0Combined610 A E0)) +
              degreeZeroRawFourthTailNoAE0Polynomial610 l alpha beta delta
                epsilon zeta eta theta A B C0 D0 E0 +
            (1 / 6 : k) • (B *
                degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                  zeta eta theta A B C0 D0 E0) +
              (1 / 3 : k) • (A *
                  degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta
                    epsilon zeta eta theta A B C0 D0 E0) := by
          abel
        _ =
            (omicronAE0Combined610 A E0 +
                (5 / 27 : k) • (A * E0 ^ 2)) +
              degreeZeroRawFourthTailNoAE0Polynomial610 l alpha beta delta
                epsilon zeta eta theta A B C0 D0 E0 +
            (1 / 6 : k) • (B *
                degreeZeroKappaPolynomial610 l alpha beta delta epsilon
                  zeta eta theta A B C0 D0 E0) +
              (1 / 3 : k) • (A *
                  degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta
                    epsilon zeta eta theta A B C0 D0 E0) := by
          rw [hface]
        _ =
            omicronAE0Combined610 A E0 +
              (degreeZeroRawFourthTailNoAE0Polynomial610 l alpha beta delta
                    epsilon zeta eta theta A B C0 D0 E0 +
                  (5 / 27 : k) • (A * E0 ^ 2) +
                ((1 / 6 : k) • (B *
                    degreeZeroKappaPolynomial610 l alpha beta delta
                      epsilon zeta eta theta A B C0 D0 E0) +
                  (1 / 3 : k) • (A *
                      degreeZeroLambdaNoAE0Polynomial610 l alpha beta
                        delta epsilon zeta eta theta A B C0 D0 E0))) := by
          abel
    have hrawRest :=
      degreeZeroRawFourthTailNoAE0Cancelled610_natDegree_lt l alpha beta
        delta epsilon zeta eta theta A B C0 D0 E0 hcone
    have hAlam :
        ((1 / 3 : k) • (A *
            degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)).natDegree <
          7 * A.natDegree := by
      have hlt :=
        degreeZeroLambdaNoAE0_natDegree_lt l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 hcone
      have hmul :=
        natDegree_mul_le
          (p := A)
          (q := degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta
            epsilon zeta eta theta A B C0 D0 E0)
      have hsm :=
        natDegree_smul_le610 (1 / 3 : k)
          (A * degreeZeroLambdaNoAE0Polynomial610 l alpha beta delta
            epsilon zeta eta theta A B C0 D0 E0)
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
      rcases hcone with ⟨hApos, _, hB, _⟩
      omega
    have hrestSum :=
      natDegree_add_lt610 hrawRest (natDegree_add_lt610 hBkap hAlam)
    rw [homiEq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
      hcomb] at homiDeg
    rcases hcone with ⟨hApos, _⟩
    omega
  · have hcomb :=
      lambdaAE0Combined610_natDegree_eq_of_coeff_ne hAne hEne htie hdrop
    have hrest :=
      degreeZeroLambdaNoAE0_natDegree_lt l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0 hcone
    rw [degreeZeroLambdaPolynomial610_eq_AE0_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]),
      hcomb] at hlamDeg
    rcases hcone with ⟨hApos, _⟩
    omega

end FinishFamilyB610

/-! ## Finish family (c) and source-facing closure

Pair-ties `A`–`C₀`, `A`–`E₀`, `B`–`C₀`, `B`–`E₀`, `C₀`–`E₀`, `A`–`B`,
the unique `D₀` monomials, and `A⁶`/`A D₀²` are empty.  Triple and
quadruple leading-coefficient certificates (`C₀⁶`, `E₀⁴`, `B¹⁶` in the
CAS Groebner bases) are applied below as vanishing of a power of a
tied leading coefficient.  The scale-zero leaf is then assembled from
`normalized610ScaleZero_kappaMuFaces_closed`.
-/

section FinishFamilyCAndClosed610

variable {k : Type*} [Field k] [CharZero k]

/-- On the `A`–`B`–`E₀` triple, the `κ` factor `7 a³ - 12 b² + 54 e`
cannot vanish together with both `λ` and `ο` remainders unless `b = 0`.
CAS: Groebner basis of the load-free forms contains `E₀⁴`. -/
theorem abe0_tied_leadings_impossible (a b e : k)
    (hb : b ≠ 0)
    (hkap : (7 : k) * a ^ 3 - 12 * b ^ 2 + 54 * e = 0)
    (hlam :
      (7 : k) * a ^ 6 - 126 * a ^ 3 * b ^ 2 + 108 * a ^ 3 * e +
          27 * b ^ 4 - 243 * b ^ 2 * e + 729 * e ^ 2 =
        0)
    (homi :
      (4 : k) * a ^ 6 - 105 * a ^ 3 * b ^ 2 + 54 * a ^ 3 * e +
          72 * b ^ 4 - 324 * b ^ 2 * e =
        0) :
    False := by
  have hlamRem :
      (7 : k) * a ^ 6 - 150 * a ^ 3 * b ^ 2 + 12 * b ^ 4 = 0 := by
    have hid := lambda_abe0_of_kappa_factor a b e
    rw [hkap, zero_mul, hlam, mul_zero, zero_sub] at hid
    have h3 : (3 : k) ≠ 0 := by norm_num
    have : (3 : k) * (7 * a ^ 6 - 150 * a ^ 3 * b ^ 2 + 12 * b ^ 4) =
        0 :=
      neg_eq_zero.mp hid
    exact (mul_eq_zero.mp this).resolve_left h3
  have homiRem :
      (3 : k) * a ^ 3 * (a ^ 3 + 17 * b ^ 2) = 0 := by
    have hid := omicron_abe0_of_kappa_factor a b e
    rw [hkap, zero_mul, homi, zero_add] at hid
    exact hid
  exact hb (abe0_lambda_omicron_remainders a b hlamRem homiRem)

end FinishFamilyCAndClosed610

/-! ## Source-facing assembly -/

section Closed610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Pair-ties, unique `D₀` monomials, and `A⁶`/`A D₀²` are empty.
Remaining chambers are the triples `A`–`B`–`C₀`, `A`–`B`–`E₀`,
`A`–`C₀`–`E₀` and the quadruple (CAS Groebner certificates `C₀⁶`,
`E₀⁴`, `B¹⁶` as field identities on leading coefficients, of which
`abe0_tied_leadings_impossible` is landed). Mixed `D₀` weights that
are not a unique maximum are also unnamed here. -/
theorem normalized610ScaleZero_coneFinishResidual
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
      ¬ C0E0RatioTieCone610 A B C0 D0 E0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hdeg1, hcLam, hlamDeg, hcKap, hkapDeg,
      hcMu, hmuDeg, hcOmi, homiDeg, hAmax, hBleads, hCleads, hEleads,
      hBtie, hWA, hWB, hWC, hWE, hExt, hA6B, hDonly, hBonly,
      hconst⟩ :=
    normalized610ScaleZero_kappaMuFaces_closed hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht,
    hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hAD02
    exact lambda_AD02_impossible l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0 hAD02 hlamDeg
  · intro hA2BD
    exact lambda_A2BD0_impossible l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0 hA2BD hlamDeg
  · intro hBCD
    exact lambda_BC0D0_impossible l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0 hBCD hlamDeg
  · intro hA6AD
    exact lambda_A6AD02_impossible l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0 hA6AD hkapDeg hlamDeg
  · intro hBC0
    exact kappa_BC0_impossible l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hBC0 hkapDeg
  · intro hBC0E0
    exact kappa_BC0E0_impossible l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0 hBC0E0 hkapDeg
  · intro hBE0
    exact lambda_BE0_impossible l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hBE0 (j / t) hjdiv hder hlamDeg
  · intro hAB
    exact kappa_AB_impossible l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hAB hlamDeg hkapDeg
  · intro hAE0
    exact lambda_AE0_impossible l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hAE0 hkapDeg hlamDeg homiDeg
  · intro hAC0
    exact lambda_AC0_impossible l alpha beta delta epsilon zeta eta theta
      A B C0 D0 E0 hAC0 hkapDeg hlamDeg homiDeg
  · intro hC0E0
    exact omicron_C0E0_impossible l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0 hC0E0 hkapDeg hlamDeg homiDeg

end Closed610



#print axioms exists_param_two_five
#print axioms lambda_ac0_of_omicron_factor_three
#print axioms lambda_raw_ac0_identity
#print axioms kappa_BC0_impossible
#print axioms lambda_AD02_impossible
#print axioms lambda_BE0_impossible
#print axioms lambda_A6AD02_impossible
#print axioms kappa_AB_impossible
#print axioms omicron_C0E0_impossible
#print axioms lambda_AC0_impossible
#print axioms lambda_AE0_impossible
#print axioms abe0_tied_leadings_impossible
#print axioms normalized610ScaleZero_coneFinishResidual

end Max11DegreeRoutes

