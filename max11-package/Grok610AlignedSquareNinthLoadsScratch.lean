import Grok610AlignedSquareEndgameScratch

/-! # Ninth loads closing the next cancellation on the aligned-square `(6,10)` chamber

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareEndgameScratch` reduced the square chamber at the
unique root `a` of the forced linear scale to the 410-style branch
`w₁(a) = 0` (with global `h₀ ∣ w₁`) or `(μ = 0 ∧ e₁(a) = 0)`, and on
the complementary limb killed through `u₂(a) = 81 p₂(a)` and `ν = 0`.
The two missing exact objects named there are constructed here, in the
same clearing/residual style as the committed `μ = 0` ninth load.

* `alignedSquareMuZeroNuZeroNinthLoad610` is the ninth quotient after
  the further substitution `ν = 0` (and `u₂ = 81 p₂ + h₀ v`).  Its
  `h₀`-free head is exactly
  `-5120 (4374 p₂ e₁n² w₁ - 1458 p₂ e₁n e₃ - 54 e₁n³ w₁³ + e₃³
  + 9 v² w₁)`.  The matching eighth quotient after the same `μ = 0`
  upgrades has head `1280 (81 p₂ - w₁ (e₃ - 3 e₁n w₁))²`, which is
  `1280 h₀² v²` on the product identity, and after two more `h₀`
  cancellations contributes the monomial `1280 v²` together with a
  remaining `(p₀, q₂, p₁, κ)` jet.
* `alignedSquareW1ZeroNinthLoad610` is the ninth quotient after
  `w₁ = h₀ w₁n` and the product upgrade of `u₂`.  Its `h₀²`-free head
  is exactly
  `-46080 (6561 p₂² w₁n - 972 p₂ e₁² w₁n + 162 p₂ e₁ e₃
  + 21 e₁⁴ w₁n - 4 e₁³ e₃)`.

Neither limb is claimed empty.  On `μ = 0` the ninth head plus the
product identity is the cube residual
`(e₃(a) - 6 e₁n(a) w₁(a))³ + 9 v(a)² w₁(a) = 0`; the eighth `v²`
monomial does not by itself kill `v(a)` against the leftover jet.
On `w₁(a) = 0` the ninth head vanishes at `a`, and the matching
eighth quotient forces the `(p₂, e₁)` residual
`e₁(a)⁴ - 81 e₁(a)² p₂(a) + 2187 p₂(a)² = 0`.  The last Keller row
still separates the cross-products.  No `sorry`, no new axioms, no
finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000

/-! ## Exact ninth quotient after `ν = 0` on the `μ = 0` limb -/

/-- Exact quotient of the committed `μ = 0` ninth load after
`u₂ = 81 p₂ + h₀ v` and `ν = 0`, cancelling two further literal `h₀`.
Its `h₀`-free head is
`-5120 (4374 p₂ e₁n² w₁ - 1458 p₂ e₁n e₃ - 54 e₁n³ w₁³ + e₃³
+ 9 v² w₁)`. -/
def alignedSquareMuZeroNuZeroNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n e3 v a0 a1 a2 b1 : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ : K) : K[X] :=
  -((5120 : K[X]) *
      ((4374 : K[X]) * a2 * e1n ^ 2 * w1 -
        (1458 : K[X]) * a2 * e1n * e3 -
        (54 : K[X]) * e1n ^ 3 * w1 ^ 3 + e3 ^ 3 +
        (9 : K[X]) * v ^ 2 * w1)) +
    h0 *
      (Polynomial.C κ * ((221184 : K[X]) * e1n * v * w1) -
        Polynomial.C κ * ((36864 : K[X]) * e3 * v) -
        Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) -
        (829440 : K[X]) * e1n ^ 2 * v * w1 +
        (184320 : K[X]) * e1n * e3 * v -
        (22394880 : K[X]) * v * a1) +
    h0 ^ 2 *
      (Polynomial.C κ * ((552960 : K[X]) * e1n ^ 3 * w1) -
        Polynomial.C κ * ((110592 : K[X]) * e1n ^ 2 * e3) +
        Polynomial.C κ * ((26873856 : K[X]) * e1n * a1) +
        Polynomial.C κ * ((80621568 : K[X]) * w1 * a0) -
        Polynomial.C κ₃ * ((3359232 : K[X]) * a1) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1n * w1) -
        Polynomial.C κ₅ * ((384 : K[X]) * e3) -
        Polynomial.C κ₇ * ((36 : K[X]) * w1) -
        (967680 : K[X]) * e1n ^ 4 * w1 +
        (184320 : K[X]) * e1n ^ 3 * e3 -
        (33592320 : K[X]) * e1n ^ 2 * a1 -
        (201553920 : K[X]) * e1n * w1 * a0 +
        (67184640 : K[X]) * e3 * a0 -
        (1632586752 : K[X]) * b1) +
    h0 ^ 3 * (-(Polynomial.C ν₂ * ((108 : K[X]) * e1n)))

/-- Matching eighth quotient after the `μ = 0` upgrades `e₁ = h₀ e₁n`,
`e₂ = h₀ e₃` and `ν = 0`, cancelling two literal `h₀`.  Its `h₀`-free
head is `1280 (81 p₂ - w₁ (e₃ - 3 e₁n w₁))²`.  On the product identity
this is `1280 h₀² v²`. -/
def alignedSquareMuZeroNuZeroEighthLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n e3 a0 a1 a2 b2 : K[X])
    (κ κ₃ κ₅ ν₂ : K) : K[X] :=
  (1280 : K[X]) *
      ((81 : K[X]) * a2 + (3 : K[X]) * e1n * w1 ^ 2 - e3 * w1) ^ 2 +
    h0 ^ 2 *
      (Polynomial.C κ * ((13824 : K[X]) * e1n ^ 2 * w1 ^ 2) -
        Polynomial.C κ * ((6144 : K[X]) * e1n * e3 * w1) +
        Polynomial.C κ * ((248832 : K[X]) * e1n * a2) +
        Polynomial.C κ * ((512 : K[X]) * e3 ^ 2) +
        Polynomial.C κ * ((746496 : K[X]) * w1 * a1) -
        Polynomial.C κ₃ * ((31104 : K[X]) * a2) -
        Polynomial.C κ₅ * ((16 : K[X]) * w1 ^ 2) -
        (38400 : K[X]) * e1n ^ 3 * w1 ^ 2 +
        (15360 : K[X]) * e1n ^ 2 * e3 * w1 -
        (311040 : K[X]) * e1n ^ 2 * a2 -
        (1280 : K[X]) * e1n * e3 ^ 2 -
        (1866240 : K[X]) * e1n * w1 * a1 +
        (622080 : K[X]) * e3 * a1 +
        (2799360 : K[X]) * w1 ^ 2 * a0 -
        (15116544 : K[X]) * b2) +
    h0 ^ 3 * (-(Polynomial.C ν₂ * ((3 : K[X]) * w1))) +
    h0 ^ 4 *
      (-(Polynomial.C κ * ((3072 : K[X]) * e1n ^ 3)) +
        Polynomial.C κ * ((2239488 : K[X]) * a0) -
        Polynomial.C κ₅ * ((32 : K[X]) * e1n) +
        (3840 : K[X]) * e1n ^ 4 +
        (5598720 : K[X]) * e1n * a0)

/-- Eighth quotient after the further product substitution
`81 p₂ = w₁ (e₃ - 3 e₁n w₁) - h₀ v`, cancelling two more `h₀`.  The
`h₀`-free part contains the matching monomial `1280 v²` together with
the remaining `(p₀, q₂, p₁, κ)` jet. -/
def alignedSquareMuZeroNuZeroEighthVLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n e3 v a0 a1 b2 : K[X])
    (κ κ₃ κ₅ ν₂ : K) : K[X] :=
  (1280 : K[X]) * v ^ 2 + (2799360 : K[X]) * w1 ^ 2 * a0 -
    (15116544 : K[X]) * b2 -
    (1866240 : K[X]) * e1n * w1 * a1 + (622080 : K[X]) * e3 * a1 +
    Polynomial.C κ * ((746496 : K[X]) * w1 * a1) +
    Polynomial.C κ * ((4608 : K[X]) * e1n ^ 2 * w1 ^ 2) -
    Polynomial.C κ * ((3072 : K[X]) * e1n * e3 * w1) +
    Polynomial.C κ * ((512 : K[X]) * e3 ^ 2) +
    Polynomial.C κ₃ * ((1152 : K[X]) * e1n * w1 ^ 2) -
    Polynomial.C κ₃ * ((384 : K[X]) * e3 * w1) -
    Polynomial.C κ₅ * ((16 : K[X]) * w1 ^ 2) -
    (26880 : K[X]) * e1n ^ 3 * w1 ^ 2 +
    (11520 : K[X]) * e1n ^ 2 * e3 * w1 -
    (1280 : K[X]) * e1n * e3 ^ 2 +
    h0 *
      ((3840 : K[X]) * e1n ^ 2 * v -
        Polynomial.C κ * ((3072 : K[X]) * e1n * v) +
        Polynomial.C κ₃ * ((384 : K[X]) * v) -
        Polynomial.C ν₂ * ((3 : K[X]) * w1)) +
    h0 ^ 2 *
      ((3840 : K[X]) * e1n ^ 4 + (5598720 : K[X]) * e1n * a0 -
        Polynomial.C κ * ((3072 : K[X]) * e1n ^ 3) +
        Polynomial.C κ * ((2239488 : K[X]) * a0) -
        Polynomial.C κ₅ * ((32 : K[X]) * e1n))

/-! ## Exact ninth quotient after `w₁ = h₀ w₁n` -/

/-- Exact quotient of the ninth peeled row after `w₁ = h₀ w₁n`,
`e₂ = h₀ e₃`, and the product upgrade `u₂ = h₀ w₁n (e₃ - 3 e₁ w₁n)`,
cancelling two literal `h₀`.  Its `h₀²`-free head is
`-46080 (6561 p₂² w₁n - 972 p₂ e₁² w₁n + 162 p₂ e₁ e₃
+ 21 e₁⁴ w₁n - 4 e₁³ e₃)`. -/
def alignedSquareW1ZeroNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1 e3 a0 a1 a2 b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) : K[X] :=
  -((46080 : K[X]) *
      ((6561 : K[X]) * a2 ^ 2 * w1n -
        (972 : K[X]) * a2 * e1 ^ 2 * w1n +
        (162 : K[X]) * a2 * e1 * e3 +
        (21 : K[X]) * e1 ^ 4 * w1n -
        (4 : K[X]) * e1 ^ 3 * e3)) +
    h0 *
      (Polynomial.C κ * ((552960 : K[X]) * e1 ^ 3 * w1n) -
        Polynomial.C κ * ((110592 : K[X]) * e1 ^ 2 * e3) -
        Polynomial.C κ * ((17915904 : K[X]) * e1 * w1n * a2) +
        Polynomial.C κ * ((2985984 : K[X]) * e3 * a2) +
        Polynomial.C μ * ((20160 : K[X]) * e1 ^ 3) -
        Polynomial.C μ * ((1306368 : K[X]) * e1 * a2) +
        (2764800 : K[X]) * e1 ^ 3 * w1n ^ 3 -
        (1382400 : K[X]) * e1 ^ 2 * e3 * w1n ^ 2 -
        (33592320 : K[X]) * e1 ^ 2 * a1 +
        (184320 : K[X]) * e1 * e3 ^ 2 * w1n -
        (22394880 : K[X]) * e1 * w1n ^ 3 * a2 -
        (5120 : K[X]) * e3 ^ 3 +
        (7464960 : K[X]) * e3 * w1n ^ 2 * a2 +
        (1813985280 : K[X]) * a1 * a2) +
    h0 ^ 2 *
      (-(Polynomial.C κ * ((663552 : K[X]) * e1 ^ 2 * w1n ^ 3)) +
        Polynomial.C κ * ((331776 : K[X]) * e1 * e3 * w1n ^ 2) +
        Polynomial.C κ * ((26873856 : K[X]) * e1 * a1) -
        Polynomial.C κ * ((36864 : K[X]) * e3 ^ 2 * w1n) -
        Polynomial.C μ * ((105840 : K[X]) * e1 ^ 2 * w1n ^ 2) +
        Polynomial.C μ * ((40320 : K[X]) * e1 * e3 * w1n) -
        Polynomial.C μ * ((2688 : K[X]) * e3 ^ 2) +
        Polynomial.C μ * ((326592 : K[X]) * w1n ^ 2 * a2) +
        Polynomial.C ν * ((2160 : K[X]) * e1 ^ 2) -
        Polynomial.C ν * ((233280 : K[X]) * a2) -
        (414720 : K[X]) * e1 ^ 2 * w1n ^ 5 +
        (276480 : K[X]) * e1 * e3 * w1n ^ 4 +
        (67184640 : K[X]) * e1 * w1n ^ 2 * a1 -
        (46080 : K[X]) * e3 ^ 2 * w1n ^ 3 -
        (22394880 : K[X]) * e3 * w1n * a1) +
    h0 ^ 3 *
      (Polynomial.C μ * ((3780 : K[X]) * e1 * w1n ^ 4) -
        Polynomial.C μ * ((2016 : K[X]) * e3 * w1n ^ 3) -
        Polynomial.C μ * ((3919104 : K[X]) * w1n * a1) -
        Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
        Polynomial.C ν * ((3240 : K[X]) * e1 * w1n ^ 2) +
        Polynomial.C ν * ((1440 : K[X]) * e3 * w1n) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1 * w1n) -
        Polynomial.C κ₅ * ((384 : K[X]) * e3) -
        Polynomial.C ν₂ * ((108 : K[X]) * e1) -
        (201553920 : K[X]) * e1 * w1n * a0 +
        (67184640 : K[X]) * e3 * a0 -
        (1632586752 : K[X]) * b1) +
    h0 ^ 4 *
      (Polynomial.C κ * ((80621568 : K[X]) * w1n * a0) -
        Polynomial.C μ * ((189 : K[X]) * w1n ^ 6) -
        Polynomial.C μ * ((23514624 : K[X]) * a0) +
        Polynomial.C ν * ((135 : K[X]) * w1n ^ 4) -
        Polynomial.C ν₂ * ((27 : K[X]) * w1n ^ 2) -
        Polynomial.C κ₇ * ((36 : K[X]) * w1n))

/-- Matching eighth quotient after `w₁ = h₀ w₁n` and `e₂ = h₀ e₃`,
cancelling two literal `h₀`.  Its `h₀`-free head is
`3840 (e₁⁴ - 81 e₁² p₂ + 2187 p₂²)`. -/
def alignedSquareW1ZeroEighthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1 e3 a0 a1 a2 b2 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ : K) : K[X] :=
  (3840 : K[X]) *
      (e1 ^ 4 - (81 : K[X]) * e1 ^ 2 * a2 + (2187 : K[X]) * a2 ^ 2) +
    h0 *
      (-(Polynomial.C κ * ((3072 : K[X]) * e1 ^ 3)) +
        Polynomial.C κ * ((248832 : K[X]) * e1 * a2) -
        (38400 : K[X]) * e1 ^ 3 * w1n ^ 2 +
        (15360 : K[X]) * e1 ^ 2 * e3 * w1n -
        (1280 : K[X]) * e1 * e3 ^ 2 +
        (622080 : K[X]) * e1 * w1n ^ 2 * a2 -
        (207360 : K[X]) * e3 * w1n * a2) +
    h0 ^ 2 *
      (Polynomial.C κ * ((13824 : K[X]) * e1 ^ 2 * w1n ^ 2) -
        Polynomial.C κ * ((6144 : K[X]) * e1 * e3 * w1n) +
        Polynomial.C κ * ((512 : K[X]) * e3 ^ 2) +
        Polynomial.C μ * ((1680 : K[X]) * e1 ^ 2 * w1n) -
        Polynomial.C μ * ((448 : K[X]) * e1 * e3) -
        Polynomial.C μ * ((36288 : K[X]) * w1n * a2) -
        Polynomial.C κ₃ * ((31104 : K[X]) * a2) +
        (11520 : K[X]) * e1 ^ 2 * w1n ^ 4 -
        (7680 : K[X]) * e1 * e3 * w1n ^ 3 -
        (1866240 : K[X]) * e1 * w1n * a1 +
        (1280 : K[X]) * e3 ^ 2 * w1n ^ 2 +
        (622080 : K[X]) * e3 * a1 -
        (15116544 : K[X]) * b2) +
    h0 ^ 3 *
      (Polynomial.C κ * ((746496 : K[X]) * w1n * a1) -
        Polynomial.C μ * ((168 : K[X]) * e1 * w1n ^ 3) +
        Polynomial.C μ * ((112 : K[X]) * e3 * w1n ^ 2) -
        Polynomial.C μ * ((217728 : K[X]) * a1) +
        Polynomial.C ν * ((120 : K[X]) * e1 * w1n) -
        Polynomial.C ν * ((80 : K[X]) * e3) -
        Polynomial.C κ₅ * ((32 : K[X]) * e1) +
        (5598720 : K[X]) * e1 * a0) +
    h0 ^ 4 *
      (Polynomial.C κ * ((2239488 : K[X]) * a0) +
        Polynomial.C μ * ((21 : K[X]) * w1n ^ 5) -
        Polynomial.C ν * ((30 : K[X]) * w1n ^ 3) -
        Polynomial.C κ₅ * ((16 : K[X]) * w1n ^ 2) -
        Polynomial.C ν₂ * ((3 : K[X]) * w1n) +
        (2799360 : K[X]) * w1n ^ 2 * a0)

variable {K : Type*} [Field K] [CharZero K]

/-! ## Factor identities and head kills, `μ = 0` limb -/

set_option maxHeartbeats 16000000 in
/-- After `u₂ = 81 p₂ + h₀ v` and `ν = 0`, the committed `μ = 0` ninth
load is `h₀²` times `alignedSquareMuZeroNuZeroNinthLoad610`. -/
theorem alignedSquareMuZeroNuZero_ninthFactor610
    (h0 w1 e1n e3 v a0 a1 a2 b1 : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ : K) :
    alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
        (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ κ₃ 0 κ₅ ν₂ κ₇ =
      h0 ^ 2 *
        alignedSquareMuZeroNuZeroNinthLoad610 h0 w1 e1n e3 v a0 a1 a2
          b1 κ κ₃ κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareMuZeroNinthLoad610,
    alignedSquareMuZeroNuZeroNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 16000000 in
/-- The ninth peeled row on the `μ = 0`, `ν = 0` upgrades with
`u₂ = 81 p₂ + h₀ v` is `h₀³` times the new ninth load. -/
theorem alignedSquareMuZeroNuZero_ninthPeeledFactor610
    (h0 w1 e1n e3 v a0 a1 a2 b1 : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ : K) :
    alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3)
        (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
      h0 ^ 3 *
        alignedSquareMuZeroNuZeroNinthLoad610 h0 w1 e1n e3 v a0 a1 a2
          b1 κ κ₃ κ₅ ν₂ κ₇ := by
  have hμ :=
    alignedSquareMuZero_ninthFactor610 h0 w1 e1n e3
      (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ κ₃ 0 κ₅ ν₂ κ₇
  have hν :=
    alignedSquareMuZeroNuZero_ninthFactor610 h0 w1 e1n e3 v a0 a1 a2 b1
      κ κ₃ κ₅ ν₂ κ₇
  calc
    alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3)
          (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
        h0 *
          alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
            (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ κ₃ 0 κ₅ ν₂
            κ₇ := hμ
    _ = h0 *
          (h0 ^ 2 *
            alignedSquareMuZeroNuZeroNinthLoad610 h0 w1 e1n e3 v a0 a1
              a2 b1 κ κ₃ κ₅ ν₂ κ₇) := by rw [hν]
    _ = h0 ^ 3 *
          alignedSquareMuZeroNuZeroNinthLoad610 h0 w1 e1n e3 v a0 a1 a2
            b1 κ κ₃ κ₅ ν₂ κ₇ := by ring

set_option maxHeartbeats 8000000 in
/-- At the unique root the `ν = 0` ninth head is the named certificate. -/
theorem alignedSquareMuZeroNuZero_ninthHeadKill610
    (h0 w1 e1n e3 v a0 a1 a2 b1 : K[X])
    (κ μ₃ κ₃ κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3)
          (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    (4374 : K) * a2.eval x * e1n.eval x ^ 2 * w1.eval x -
        (1458 : K) * a2.eval x * e1n.eval x * e3.eval x -
        (54 : K) * e1n.eval x ^ 3 * w1.eval x ^ 3 +
          e3.eval x ^ 3 +
            (9 : K) * v.eval x ^ 2 * w1.eval x =
      0 := by
  have hfactor :=
    alignedSquareMuZeroNuZero_ninthPeeledFactor610 h0 w1 e1n e3 v a0 a1
      a2 b1 κ κ₃ κ₅ ν₂ κ₇
  rw [hfactor] at hrow
  have hload :
      alignedSquareMuZeroNuZeroNinthLoad610 h0 w1 e1n e3 v a0 a1 a2 b1
          κ κ₃ κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 3 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 3 * (Polynomial.C μ₃ * h0 ^ 3) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 3 hh0) (hrow.trans hpow)
  have hloadx :=
    congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareMuZeroNuZeroNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

/-- Algebraic identity rewriting the named ninth head against the cube
`(e₃ - 6 e₁n w₁)³` and the product factor
`81 p₂ - w₁ (e₃ - 3 e₁n w₁)`. -/
theorem alignedSquareMuZeroNuZero_ninthHeadCube610
    (e1n e3 a2 w1 : K) :
    (4374 : K) * a2 * e1n ^ 2 * w1 -
        (1458 : K) * a2 * e1n * e3 -
        (54 : K) * e1n ^ 3 * w1 ^ 3 + e3 ^ 3 =
      (e3 - (6 : K) * e1n * w1) ^ 3 +
        (18 : K) * e1n * ((3 : K) * e1n * w1 - e3) *
          ((81 : K) * a2 + (3 : K) * e1n * w1 ^ 2 - e3 * w1) := by
  ring

set_option maxHeartbeats 16000000 in
/-- The eighth peeled row on the `μ = 0`, `ν = 0` upgrades is `h₀²`
times `alignedSquareMuZeroNuZeroEighthLoad610`. -/
theorem alignedSquareMuZeroNuZero_eighthFactor610
    (h0 w1 e1n e3 a0 a1 a2 b2 : K[X])
    (κ κ₃ κ₅ ν₂ : K) :
    alignedEighthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3) a0 a1 a2
        b2 κ 0 κ₃ 0 κ₅ ν₂ =
      h0 ^ 2 *
        alignedSquareMuZeroNuZeroEighthLoad610 h0 w1 e1n e3 a0 a1 a2 b2
          κ κ₃ κ₅ ν₂ := by
  apply Polynomial.funext
  intro z
  simp only [alignedEighthSquarePeeledRow610,
    alignedSquareMuZeroNuZeroEighthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

/-- On the product identity the eighth head is `1280 h₀² v²`. -/
theorem alignedSquareMuZeroNuZero_eighthHeadV610
    (h0 w1 e1n e3 v a2 : K[X])
    (hprod :
      w1 * (e3 - (3 : K[X]) * e1n * w1) =
        h0 * v + (81 : K[X]) * a2) :
    (81 : K[X]) * a2 + (3 : K[X]) * e1n * w1 ^ 2 - e3 * w1 =
      -h0 * v := by
  calc
    (81 : K[X]) * a2 + (3 : K[X]) * e1n * w1 ^ 2 - e3 * w1 =
        (81 : K[X]) * a2 -
          w1 * (e3 - (3 : K[X]) * e1n * w1) := by
      ring
    _ = (81 : K[X]) * a2 - (h0 * v + (81 : K[X]) * a2) := by
      rw [hprod]
    _ = -h0 * v := by
      ring

set_option maxHeartbeats 16000000 in
/-- After rewriting `p₂` from the product identity, the eighth peeled
row is `h₀⁴` times `alignedSquareMuZeroNuZeroEighthVLoad610`.  The
`h₀`-free part of that quotient is `1280 v²` plus the remaining jet. -/
theorem alignedSquareMuZeroNuZero_eighthVFactor610
    (h0 w1 e1n e3 v a0 a1 b2 : K[X])
    (κ κ₃ κ₅ ν₂ : K) :
    alignedEighthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3) a0 a1
        ((w1 * (e3 - (3 : K[X]) * e1n * w1) - h0 * v) *
          Polynomial.C (81 : K)⁻¹)
        b2 κ 0 κ₃ 0 κ₅ ν₂ =
      h0 ^ 4 *
        alignedSquareMuZeroNuZeroEighthVLoad610 h0 w1 e1n e3 v a0 a1 b2
          κ κ₃ κ₅ ν₂ := by
  apply Polynomial.funext
  intro z
  simp only [alignedEighthSquarePeeledRow610,
    alignedSquareMuZeroNuZeroEighthVLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0,
    zero_mul, mul_zero, add_zero, sub_zero, zero_add]
  ring

set_option maxHeartbeats 8000000 in
/-- At the unique root the eighth `v`-load forces the residual
`1280 v(a)²` plus the leftover `(p₀, q₂, p₁, κ)` jet. -/
theorem alignedSquareMuZeroNuZero_eighthVHeadKill610
    (h0 w1 e1n e3 v a0 a1 b2 : K[X])
    (κ κ₇ κ₃ κ₅ ν₂ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedEighthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3) a0 a1
          ((w1 * (e3 - (3 : K[X]) * e1n * w1) - h0 * v) *
            Polynomial.C (81 : K)⁻¹)
          b2 κ 0 κ₃ 0 κ₅ ν₂ =
        Polynomial.C κ₇ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    (1280 : K) * v.eval x ^ 2 +
        (2799360 : K) * w1.eval x ^ 2 * a0.eval x -
          (15116544 : K) * b2.eval x -
            (1866240 : K) * e1n.eval x * w1.eval x * a1.eval x +
              (622080 : K) * e3.eval x * a1.eval x +
                κ * ((746496 : K) * w1.eval x * a1.eval x) +
                  κ * ((4608 : K) * e1n.eval x ^ 2 * w1.eval x ^ 2) -
                    κ * ((3072 : K) * e1n.eval x * e3.eval x *
                      w1.eval x) +
                      κ * ((512 : K) * e3.eval x ^ 2) +
                        κ₃ * ((1152 : K) * e1n.eval x *
                          w1.eval x ^ 2) -
                          κ₃ * ((384 : K) * e3.eval x * w1.eval x) -
                            κ₅ * ((16 : K) * w1.eval x ^ 2) -
                              (26880 : K) * e1n.eval x ^ 3 *
                                w1.eval x ^ 2 +
                                (11520 : K) * e1n.eval x ^ 2 *
                                  e3.eval x * w1.eval x -
                                  (1280 : K) * e1n.eval x *
                                    e3.eval x ^ 2 =
      0 := by
  have hfactor :=
    alignedSquareMuZeroNuZero_eighthVFactor610 h0 w1 e1n e3 v a0 a1 b2
      κ κ₃ κ₅ ν₂
  rw [hfactor] at hrow
  have hload :
      alignedSquareMuZeroNuZeroEighthVLoad610 h0 w1 e1n e3 v a0 a1 b2
          κ κ₃ κ₅ ν₂ =
        Polynomial.C κ₇ * h0 ^ 2 := by
    have hpow : Polynomial.C κ₇ * h0 ^ 6 =
        h0 ^ 4 * (Polynomial.C κ₇ * h0 ^ 2) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 4 hh0) (hrow.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareMuZeroNuZeroEighthVLoad610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  linear_combination hloadx

/-! ## Factor identities and head kills, `w₁(a) = 0` limb -/

set_option maxHeartbeats 16000000 in
/-- The ninth peeled row after `w₁ = h₀ w₁n`, `e₂ = h₀ e₃`, and the
product upgrade of `u₂` is `h₀²` times
`alignedSquareW1ZeroNinthLoad610`. -/
theorem alignedSquareW1Zero_ninthFactor610
    (h0 w1n e1 e3 a0 a1 a2 b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) :
    alignedNinthSquarePeeledRow610 h0 (h0 * w1n) e1 (h0 * e3)
        (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n)) a0 a1 a2 b1 κ μ κ₃ ν
        κ₅ ν₂ κ₇ =
      h0 ^ 2 *
        alignedSquareW1ZeroNinthLoad610 h0 w1n e1 e3 a0 a1 a2 b1 κ μ κ₃
          ν κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedNinthSquarePeeledRow610,
    alignedSquareW1ZeroNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 8000000 in
/-- At the unique root the `w₁ = 0` ninth head is the named certificate. -/
theorem alignedSquareW1Zero_ninthHeadKill610
    (h0 w1n e1 e3 a0 a1 a2 b1 : K[X])
    (κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 (h0 * w1n) e1 (h0 * e3)
          (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n)) a0 a1 a2 b1 κ μ κ₃
          ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    (6561 : K) * a2.eval x ^ 2 * w1n.eval x -
        (972 : K) * a2.eval x * e1.eval x ^ 2 * w1n.eval x +
          (162 : K) * a2.eval x * e1.eval x * e3.eval x +
            (21 : K) * e1.eval x ^ 4 * w1n.eval x -
              (4 : K) * e1.eval x ^ 3 * e3.eval x =
      0 := by
  have hfactor :=
    alignedSquareW1Zero_ninthFactor610 h0 w1n e1 e3 a0 a1 a2 b1 κ μ κ₃
      ν κ₅ ν₂ κ₇
  rw [hfactor] at hrow
  have hload :
      alignedSquareW1ZeroNinthLoad610 h0 w1n e1 e3 a0 a1 a2 b1 κ μ κ₃ ν
          κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 4 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 2 * (Polynomial.C μ₃ * h0 ^ 4) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hh0) (hrow.trans hpow)
  have hloadx :=
    congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

set_option maxHeartbeats 16000000 in
/-- The eighth peeled row after `w₁ = h₀ w₁n` and `e₂ = h₀ e₃` is
`h₀²` times `alignedSquareW1ZeroEighthLoad610`. -/
theorem alignedSquareW1Zero_eighthFactor610
    (h0 w1n e1 e3 a0 a1 a2 b2 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ : K) :
    alignedEighthSquarePeeledRow610 h0 (h0 * w1n) e1 (h0 * e3) a0 a1 a2
        b2 κ μ κ₃ ν κ₅ ν₂ =
      h0 ^ 2 *
        alignedSquareW1ZeroEighthLoad610 h0 w1n e1 e3 a0 a1 a2 b2 κ μ
          κ₃ ν κ₅ ν₂ := by
  apply Polynomial.funext
  intro z
  simp only [alignedEighthSquarePeeledRow610,
    alignedSquareW1ZeroEighthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 8000000 in
/-- At the unique root the `w₁ = 0` eighth head is the `(p₂, e₁)`
residual `e₁⁴ - 81 e₁² p₂ + 2187 p₂²`. -/
theorem alignedSquareW1Zero_eighthHeadKill610
    (h0 w1n e1 e3 a0 a1 a2 b2 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedEighthSquarePeeledRow610 h0 (h0 * w1n) e1 (h0 * e3) a0 a1
          a2 b2 κ μ κ₃ ν κ₅ ν₂ =
        Polynomial.C κ₇ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    e1.eval x ^ 4 - (81 : K) * e1.eval x ^ 2 * a2.eval x +
        (2187 : K) * a2.eval x ^ 2 =
      0 := by
  have hfactor :=
    alignedSquareW1Zero_eighthFactor610 h0 w1n e1 e3 a0 a1 a2 b2 κ μ κ₃
      ν κ₅ ν₂
  rw [hfactor] at hrow
  have hload :
      alignedSquareW1ZeroEighthLoad610 h0 w1n e1 e3 a0 a1 a2 b2 κ μ κ₃
          ν κ₅ ν₂ =
        Polynomial.C κ₇ * h0 ^ 4 := by
    have hpow : Polynomial.C κ₇ * h0 ^ 6 =
        h0 ^ 2 * (Polynomial.C κ₇ * h0 ^ 4) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hh0) (hrow.trans hpow)
  have hloadx :=
    congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroEighthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

/-! ## Source-facing application per limb -/

set_option maxHeartbeats 16000000 in
/-- Product identity on the `μ = 0` upgrades: after cancelling the
recorded `h₀`, one has `w₁ (e₃ - 3 e₁n w₁) = 81 p₂ + h₀ v`. -/
theorem alignedSquareMuZero_productReduce610
    (h0 w1 e1n e3 v a2 u2 : K[X])
    (hh0 : h0 ≠ 0)
    (hu2 : w1 * (h0 * e3 - (3 : K[X]) * (h0 * e1n) * w1) = h0 * u2)
    (hu : u2 = h0 * v + (81 : K[X]) * a2) :
    w1 * (e3 - (3 : K[X]) * e1n * w1) =
      h0 * v + (81 : K[X]) * a2 := by
  have hcancel :
      h0 * (w1 * (e3 - (3 : K[X]) * e1n * w1)) =
        h0 * (h0 * v + (81 : K[X]) * a2) := by
    calc
      h0 * (w1 * (e3 - (3 : K[X]) * e1n * w1)) =
          w1 * (h0 * e3 - (3 : K[X]) * (h0 * e1n) * w1) := by ring
      _ = h0 * u2 := hu2
      _ = h0 * (h0 * v + (81 : K[X]) * a2) := by rw [hu]
  exact mul_left_cancel₀ hh0 hcancel

set_option maxHeartbeats 16000000 in
/-- Cube residual on the `μ = 0` limb: the named ninth head together
with the product identity is
`(e₃(a) - 6 e₁n(a) w₁(a))³ + 9 v(a)² w₁(a) = 0`. -/
theorem alignedSquareMuZeroNuZero_cubeResidual610
    (h0 w1 e1n e3 v a0 a1 a2 b1 : K[X])
    (κ μ₃ κ₃ κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3)
          (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (hprod :
      w1 * (e3 - (3 : K[X]) * e1n * w1) =
        h0 * v + (81 : K[X]) * a2)
    (x : K) (hx : h0.eval x = 0) :
    (e3.eval x - (6 : K) * e1n.eval x * w1.eval x) ^ 3 +
        (9 : K) * v.eval x ^ 2 * w1.eval x =
      0 := by
  have hhead :=
    alignedSquareMuZeroNuZero_ninthHeadKill610 h0 w1 e1n e3 v a0 a1 a2
      b1 κ μ₃ κ₃ κ₅ ν₂ κ₇ hh0 hrow x hx
  have hcube :=
    alignedSquareMuZeroNuZero_ninthHeadCube610 (e1n.eval x) (e3.eval x)
      (a2.eval x) (w1.eval x)
  have hprod_x := congrArg (fun w : K[X] => w.eval x) hprod
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]
    at hprod_x
  rw [hx, zero_mul, zero_add] at hprod_x
  have hdelta :
      (81 : K) * a2.eval x + (3 : K) * e1n.eval x * w1.eval x ^ 2 -
          e3.eval x * w1.eval x =
        0 := by
    calc
      (81 : K) * a2.eval x + (3 : K) * e1n.eval x * w1.eval x ^ 2 -
            e3.eval x * w1.eval x =
          (81 : K) * a2.eval x -
            w1.eval x *
              (e3.eval x - (3 : K) * e1n.eval x * w1.eval x) := by
        ring
      _ = (81 : K) * a2.eval x - (81 : K) * a2.eval x := by
        rw [hprod_x]
      _ = 0 := by
        ring
  rw [hcube, hdelta, mul_zero, add_zero] at hhead
  exact hhead

set_option maxHeartbeats 16000000 in
/-- Square-chamber ninth-load reduction.  Both missing exact objects
are applied at the unique root.  On `μ = 0` the ninth head is the cube
residual against `v(a)`, and the matching eighth `v`-load leaves
`1280 v(a)²` plus the leftover jet; on `w₁(a) = 0` the ninth head is
the named quintic and the matching eighth head is the `(p₂, e₁)`
quadratic.  The Keller row still separates the cross-products.  Neither
limb is closed. -/
theorem normalized610ScaleTwo_alignedSquare_ninthLoadReduction
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a j : K) (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K)
      (w1 f2 e1 e2 u2 e3 : K[X]),
      h0.natDegree = 1 ∧ h0.eval a = 0 ∧ j ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
            (p.coeff 1).eval a *
              ((q.coeff 0).derivative).eval a = j ∧
        p.coeff 5 = h0 ^ 4 * w1 ∧
        p.coeff 4 = h0 ^ 2 * f2 ∧
        (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
        e2 = h0 * e3 ∧
        w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
        alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 ∧
        (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0)) ∧
        (w1.eval a = 0 →
          ∃ w1n : K[X],
            w1 = h0 * w1n ∧
              u2 =
                  h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n) ∧
                alignedNinthSquarePeeledRow610 h0 (h0 * w1n) e1
                    (h0 * e3)
                    (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n))
                    (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ
                    μ κ₃ ν κ₅ ν₂ κ₇ =
                  h0 ^ 2 *
                    alignedSquareW1ZeroNinthLoad610 h0 w1n e1 e3
                      (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1)
                      κ μ κ₃ ν κ₅ ν₂ κ₇ ∧
                  (6561 : K) * (p.coeff 2).eval a ^ 2 * w1n.eval a -
                        (972 : K) * (p.coeff 2).eval a *
                          e1.eval a ^ 2 * w1n.eval a +
                          (162 : K) * (p.coeff 2).eval a * e1.eval a *
                            e3.eval a +
                            (21 : K) * e1.eval a ^ 4 * w1n.eval a -
                              (4 : K) * e1.eval a ^ 3 * e3.eval a =
                    0) ∧
        (w1.eval a ≠ 0 →
          μ = 0 ∧ ν = 0 ∧
            ∃ e1n v : K[X],
              e1 = h0 * e1n ∧
                u2 = h0 * v + (81 : K[X]) * p.coeff 2 ∧
                  w1 * (e3 - (3 : K[X]) * e1n * w1) =
                    h0 * v + (81 : K[X]) * p.coeff 2 ∧
                    alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n)
                        (h0 * e3)
                        (h0 * v + (81 : K[X]) * p.coeff 2)
                        (p.coeff 0) (p.coeff 1) (p.coeff 2)
                        (q.coeff 1) κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
                      h0 ^ 3 *
                        alignedSquareMuZeroNuZeroNinthLoad610 h0 w1
                          e1n e3 v (p.coeff 0) (p.coeff 1)
                          (p.coeff 2) (q.coeff 1) κ κ₃ κ₅ ν₂ κ₇ ∧
                      (e3.eval a - (6 : K) * e1n.eval a * w1.eval a)
                            ^ 3 +
                          (9 : K) * v.eval a ^ 2 * w1.eval a =
                        0) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, w1, f2, e1, e2, u2, e3,
    hdeg1, hroot, hj, hrow, hroweval, hp5, hp4, he1, he2, he3, hu2, hM,
    hD, hF, hR9, hbranch, hA, hB⟩ :=
    normalized610ScaleTwo_alignedSquare_endgameReduction hsource hh0
      hHsq haligned
  refine ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, w1, f2, e1, e2, u2, e3,
    hdeg1, hroot, hj, hrow, hroweval, hp5, hp4, he1, he2, he3, hu2, hR9,
    hbranch, ?limbA, ?limbB⟩
  · intro hw1a
    obtain ⟨w1n, hw1⟩ := hA hw1a
    have hu2' :
        u2 = h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n) := by
      have hprod := hu2
      rw [hw1, he3] at hprod
      have hcancel :
          h0 * u2 =
            h0 * (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n)) := by
        calc
          h0 * u2 =
              (h0 * w1n) *
                (h0 * e3 - (3 : K[X]) * e1 * (h0 * w1n)) :=
            hprod.symm
          _ = h0 * (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n)) := by
            ring
      exact mul_left_cancel₀ hh0 hcancel
    have hR9' :
        alignedNinthSquarePeeledRow610 h0 (h0 * w1n) e1 (h0 * e3)
            (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n)) (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 := by
      simpa [hw1, he3, hu2'] using hR9
    have hfac :=
      alignedSquareW1Zero_ninthFactor610 h0 w1n e1 e3 (p.coeff 0)
        (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇
    have hkill :=
      alignedSquareW1Zero_ninthHeadKill610 h0 w1n e1 e3 (p.coeff 0)
        (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇ hh0
        hR9' a hroot
    exact ⟨w1n, hw1, hu2', hfac, hkill⟩
  · intro hw1x
    obtain ⟨hμ, hν, hu2a, _hD0, _hF0, e1n, v, he1n, hu⟩ := hB hw1x
    have hprod :=
      alignedSquareMuZero_productReduce610 h0 w1 e1n e3 v (p.coeff 2)
        u2 hh0 (by simpa [he1n, he3] using hu2) hu
    have hR9μ :
        alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3)
            (h0 * v + (81 : K[X]) * p.coeff 2) (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (q.coeff 1) κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 := by
      simpa [hμ, hν, he1n, he3, hu] using hR9
    have hfac :=
      alignedSquareMuZeroNuZero_ninthPeeledFactor610 h0 w1 e1n e3 v
        (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ κ₅ ν₂ κ₇
    have hcube :=
      alignedSquareMuZeroNuZero_cubeResidual610 h0 w1 e1n e3 v
        (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ₃ κ₃ κ₅ ν₂
        κ₇ hh0 hR9μ hprod a hroot
    exact ⟨hμ, hν, e1n, v, he1n, hu, hprod, hfac, hcube⟩

#print axioms alignedSquareMuZeroNuZero_ninthFactor610
#print axioms alignedSquareMuZeroNuZero_ninthPeeledFactor610
#print axioms alignedSquareMuZeroNuZero_ninthHeadKill610
#print axioms alignedSquareMuZeroNuZero_ninthHeadCube610
#print axioms alignedSquareMuZeroNuZero_eighthFactor610
#print axioms alignedSquareMuZeroNuZero_eighthHeadV610
#print axioms alignedSquareMuZeroNuZero_eighthVFactor610
#print axioms alignedSquareMuZeroNuZero_eighthVHeadKill610
#print axioms alignedSquareW1Zero_ninthFactor610
#print axioms alignedSquareW1Zero_ninthHeadKill610
#print axioms alignedSquareW1Zero_eighthFactor610
#print axioms alignedSquareW1Zero_eighthHeadKill610
#print axioms alignedSquareMuZero_productReduce610
#print axioms alignedSquareMuZeroNuZero_cubeResidual610
#print axioms normalized610ScaleTwo_alignedSquare_ninthLoadReduction

end Max11DegreeRoutes
