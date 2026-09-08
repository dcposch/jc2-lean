import Grok610AlignedSquareNinthLoadsScratch

/-! # Mixed `(p₁, q₁)` ninth/tenth pair on the aligned-square `(6,10)` limbs

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareNinthLoadsScratch` landed both ninth loads with
residuals: on `μ = 0` the cube
`(e₃(a) - 6 e₁n(a) w₁(a))³ + 9 v(a)² w₁(a) = 0` (`v(a) = 0` not forced),
and on `w₁(a) = 0` the `(p₂, e₁)` quadratic (not field-independent).
The Keller row `p₀'(a) q₁(a) - p₁(a) q₀'(a) = j`, `j ≠ 0`, was
untouched.

This file extracts the next quotient orders that mix the Keller-row
letters `p₁, q₁` (and `q₀` on the tenth), then drives each limb.

* On `μ = 0`, the cube residual is an `h₀`-divisor.  Cancelling it
  produces a mixed ninth/tenth pair whose heads are linear in `p₁`.
  Their `h₀`-free combination is `30720 v y² - 45 ν₂ w₁³`.  On
  `w₁(a) ≠ 0` this is `2048 v(a) y(a)² = 3 ν₂ w₁(a)³`.  The branch
  `v(a) = 0` forces `y(a) = 0` from the cube and then `ν₂ = 0`; the
  deepened pair has tenth head `92160 (243 p₁ + v₁ w₁)²` and ninth
  head linear in `p₁` and `q₁`.  Neither branch forces both Keller
  cross-products to vanish.
* On `w₁(a) = 0`, the eighth quadratic together with the tenth
  remainder forces `e₁(a) = p₂(a) = 0` over any characteristic-zero
  field.  The next ninth head is `-5120 e₃(a)³`, so `e₃(a) = 0`.  The
  mixed pair after that is
  `a₂b (6 p₁ - a₂b w₁n) = 0` and
  `45 p₁² - 30 p₁ a₂b w₁n + a₂b² (2 κ - 5 e₁b + 5 w₁n²) = 0`.
  The child `a₂b(a) = 0` forces `p₁(a) = 0` and then `q₁(a) = 0`,
  contradicting `j ≠ 0` (410-style collision).  The complementary
  child remains, with residual `6 p₁(a) = a₂b(a) w₁n(a)` and
  `20 e₁b(a) = 8 κ + 5 w₁n(a)²`.

No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim of the square chamber.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000

/-! ## `μ = 0` mixed pair after the cube divisor -/

/-- Ninth quotient after the product upgrade, the rewrite
`e₃ = y + 6 e₁n w₁`, and *before* the cube identity.  Its `h₀`-free
head is `-5120 (y³ + 9 v² w₁)`. -/
def alignedSquareMuZeroMixedNinthPreLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n y v a0 a1 b1 : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ : K) : K[X] :=
  -((5120 : K[X]) * (y ^ 3 + (9 : K[X]) * v ^ 2 * w1)) +
    h0 *
      (-(Polynomial.C κ * ((36864 : K[X]) * y * v)) -
        Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) +
        (92160 : K[X]) * e1n * y * v -
        (22394880 : K[X]) * v * a1) +
    h0 ^ 2 *
      (-(Polynomial.C κ * ((110592 : K[X]) * e1n ^ 3 * w1)) -
        Polynomial.C κ * ((110592 : K[X]) * e1n ^ 2 * y) +
        Polynomial.C κ * ((26873856 : K[X]) * e1n * a1) +
        Polynomial.C κ * ((80621568 : K[X]) * w1 * a0) -
        Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
        Polynomial.C κ₅ * ((1152 : K[X]) * e1n * w1) -
        Polynomial.C κ₅ * ((384 : K[X]) * y) -
        Polynomial.C κ₇ * ((36 : K[X]) * w1) +
        (138240 : K[X]) * e1n ^ 4 * w1 +
        (184320 : K[X]) * e1n ^ 3 * y -
        (33592320 : K[X]) * e1n ^ 2 * a1 +
        (201553920 : K[X]) * e1n * w1 * a0 +
        (67184640 : K[X]) * y * a0 -
        (1632586752 : K[X]) * b1) +
    h0 ^ 3 * (-(Polynomial.C ν₂ * ((108 : K[X]) * e1n)))

/-- Ninth mixed load after `y³ + 9 v² w₁ = h₀ ρ`.  The `h₀`-free head
is linear in `p₁`.  The letter `q₁` sits at `h₀¹`. -/
def alignedSquareMuZeroMixedNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n y v a0 a1 b1 rho : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ : K) : K[X] :=
  -(Polynomial.C κ * ((36864 : K[X]) * y * v)) -
    Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) +
    (92160 : K[X]) * e1n * y * v -
    (22394880 : K[X]) * v * a1 -
    (5120 : K[X]) * rho +
    h0 *
      (-(Polynomial.C κ * ((110592 : K[X]) * e1n ^ 3 * w1)) -
        Polynomial.C κ * ((110592 : K[X]) * e1n ^ 2 * y) +
        Polynomial.C κ * ((26873856 : K[X]) * e1n * a1) +
        Polynomial.C κ * ((80621568 : K[X]) * w1 * a0) -
        Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
        Polynomial.C κ₅ * ((1152 : K[X]) * e1n * w1) -
        Polynomial.C κ₅ * ((384 : K[X]) * y) -
        Polynomial.C κ₇ * ((36 : K[X]) * w1) +
        (138240 : K[X]) * e1n ^ 4 * w1 +
        (184320 : K[X]) * e1n ^ 3 * y -
        (33592320 : K[X]) * e1n ^ 2 * a1 +
        (201553920 : K[X]) * e1n * w1 * a0 +
        (67184640 : K[X]) * y * a0 -
        (1632586752 : K[X]) * b1) +
    h0 ^ 2 * (-(Polynomial.C ν₂ * ((108 : K[X]) * e1n)))

/-- Tenth quotient after the same product/`y` rewrite and before the
cube identity.  Head `10240 w₁ (y³ + 9 v² w₁)`. -/
def alignedSquareMuZeroMixedTenthPreLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n y v a0 a1 b0 : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  (10240 : K[X]) * w1 * (y ^ 3 + (9 : K[X]) * v ^ 2 * w1) +
    h0 *
      (Polynomial.C κ * ((73728 : K[X]) * y * v * w1) +
        Polynomial.C ν₂ * ((9 : K[X]) * w1 ^ 3) -
        (184320 : K[X]) * e1n * y * v * w1 +
        (30720 : K[X]) * y ^ 2 * v +
        (44789760 : K[X]) * v * w1 * a1) +
    h0 ^ 2 *
      (-(Polynomial.C κ * ((73728 : K[X]) * e1n * y ^ 2)) +
        Polynomial.C κ * ((17915904 : K[X]) * y * a1) +
        Polynomial.C κ * ((36864 : K[X]) * v ^ 2) +
        (184320 : K[X]) * e1n ^ 2 * y ^ 2 -
        (44789760 : K[X]) * e1n * y * a1 -
        (92160 : K[X]) * e1n * v ^ 2 +
        (5441955840 : K[X]) * a1 ^ 2) +
    h0 ^ 3 *
      (Polynomial.C κ * ((221184 : K[X]) * e1n ^ 2 * v) +
        Polynomial.C κ₅ * ((768 : K[X]) * v) -
        Polynomial.C ν₂ * ((108 : K[X]) * e1n * w1) -
        Polynomial.C ν₂ * ((72 : K[X]) * y) -
        Polynomial.C μ₃ * w1 -
        (368640 : K[X]) * e1n ^ 3 * v -
        (134369280 : K[X]) * v * a0) +
    h0 ^ 4 *
      (Polynomial.C κ * ((276480 : K[X]) * e1n ^ 4) +
        Polynomial.C κ * ((161243136 : K[X]) * e1n * a0) -
        Polynomial.C κ₃ * ((20155392 : K[X]) * a0) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1n ^ 2) -
        Polynomial.C κ₇ * ((72 : K[X]) * e1n) -
        (387072 : K[X]) * e1n ^ 5 -
        (201553920 : K[X]) * e1n ^ 2 * a0 -
        (9795520512 : K[X]) * b0)

/-- Tenth mixed load after `y³ + 9 v² w₁ = h₀ ρ`.  Head linear in `p₁`.
The letter `q₀` sits at `h₀³`. -/
def alignedSquareMuZeroMixedTenthLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n y v a0 a1 b0 rho : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  Polynomial.C κ * ((73728 : K[X]) * y * v * w1) +
    Polynomial.C ν₂ * ((9 : K[X]) * w1 ^ 3) -
    (184320 : K[X]) * e1n * y * v * w1 +
    (30720 : K[X]) * y ^ 2 * v +
    (44789760 : K[X]) * v * w1 * a1 +
    (10240 : K[X]) * w1 * rho +
    h0 *
      (-(Polynomial.C κ * ((73728 : K[X]) * e1n * y ^ 2)) +
        Polynomial.C κ * ((17915904 : K[X]) * y * a1) +
        Polynomial.C κ * ((36864 : K[X]) * v ^ 2) +
        (184320 : K[X]) * e1n ^ 2 * y ^ 2 -
        (44789760 : K[X]) * e1n * y * a1 -
        (92160 : K[X]) * e1n * v ^ 2 +
        (5441955840 : K[X]) * a1 ^ 2) +
    h0 ^ 2 *
      (Polynomial.C κ * ((221184 : K[X]) * e1n ^ 2 * v) +
        Polynomial.C κ₅ * ((768 : K[X]) * v) -
        Polynomial.C ν₂ * ((108 : K[X]) * e1n * w1) -
        Polynomial.C ν₂ * ((72 : K[X]) * y) -
        Polynomial.C μ₃ * w1 -
        (368640 : K[X]) * e1n ^ 3 * v -
        (134369280 : K[X]) * v * a0) +
    h0 ^ 3 *
      (Polynomial.C κ * ((276480 : K[X]) * e1n ^ 4) +
        Polynomial.C κ * ((161243136 : K[X]) * e1n * a0) -
        Polynomial.C κ₃ * ((20155392 : K[X]) * a0) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1n ^ 2) -
        Polynomial.C κ₇ * ((72 : K[X]) * e1n) -
        (387072 : K[X]) * e1n ^ 5 -
        (201553920 : K[X]) * e1n ^ 2 * a0 -
        (9795520512 : K[X]) * b0)

/-- Deep ninth mixed load after `v = h₀ v₁`, `y = h₀ y₁`, `ν₂ = 0`.
Head linear in `p₁` and `q₁`. -/
def alignedSquareMuZeroDeepMixedNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n a0 a1 b1 y1 v1 : K[X])
    (κ κ₃ κ₅ κ₇ : K) : K[X] :=
  -(Polynomial.C κ * ((110592 : K[X]) * e1n ^ 3 * w1)) +
    Polynomial.C κ * ((26873856 : K[X]) * e1n * a1) +
    Polynomial.C κ * ((80621568 : K[X]) * w1 * a0) -
    Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
    Polynomial.C κ₅ * ((1152 : K[X]) * e1n * w1) -
    Polynomial.C κ₇ * ((36 : K[X]) * w1) +
    (138240 : K[X]) * e1n ^ 4 * w1 -
    (33592320 : K[X]) * e1n ^ 2 * a1 +
    (201553920 : K[X]) * e1n * w1 * a0 -
    (46080 : K[X]) * w1 * v1 ^ 2 -
    (22394880 : K[X]) * a1 * v1 -
    (1632586752 : K[X]) * b1 +
    h0 *
      (-(Polynomial.C κ * ((110592 : K[X]) * e1n ^ 2 * y1)) -
        Polynomial.C κ * ((36864 : K[X]) * y1 * v1) -
        Polynomial.C κ₅ * ((384 : K[X]) * y1) +
        (184320 : K[X]) * e1n ^ 3 * y1 +
        (92160 : K[X]) * e1n * y1 * v1 +
        (67184640 : K[X]) * a0 * y1 -
        (5120 : K[X]) * y1 ^ 3)

/-- Deep tenth mixed load after the same upgrades.  Head
`92160 (243 p₁ + v₁ w₁)²`. -/
def alignedSquareMuZeroDeepMixedTenthLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n a0 a1 b0 y1 v1 : K[X])
    (κ κ₃ κ₅ κ₇ μ₃ : K) : K[X] :=
  (92160 : K[X]) * w1 ^ 2 * v1 ^ 2 +
    (44789760 : K[X]) * w1 * a1 * v1 +
    (5441955840 : K[X]) * a1 ^ 2 +
    h0 *
      (Polynomial.C κ * ((73728 : K[X]) * w1 * y1 * v1) +
        Polynomial.C κ * ((17915904 : K[X]) * a1 * y1) -
        Polynomial.C μ₃ * w1 -
        (184320 : K[X]) * e1n * w1 * y1 * v1 -
        (44789760 : K[X]) * e1n * a1 * y1 +
        (10240 : K[X]) * w1 * y1 ^ 3) +
    h0 ^ 2 *
      (Polynomial.C κ * ((276480 : K[X]) * e1n ^ 4) +
        Polynomial.C κ * ((221184 : K[X]) * e1n ^ 2 * v1) +
        Polynomial.C κ * ((161243136 : K[X]) * e1n * a0) -
        Polynomial.C κ * ((73728 : K[X]) * e1n * y1 ^ 2) +
        Polynomial.C κ * ((36864 : K[X]) * v1 ^ 2) -
        Polynomial.C κ₃ * ((20155392 : K[X]) * a0) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1n ^ 2) +
        Polynomial.C κ₅ * ((768 : K[X]) * v1) -
        Polynomial.C κ₇ * ((72 : K[X]) * e1n) -
        (387072 : K[X]) * e1n ^ 5 -
        (368640 : K[X]) * e1n ^ 3 * v1 -
        (201553920 : K[X]) * e1n ^ 2 * a0 +
        (184320 : K[X]) * e1n ^ 2 * y1 ^ 2 -
        (92160 : K[X]) * e1n * v1 ^ 2 -
        (134369280 : K[X]) * a0 * v1 -
        (9795520512 : K[X]) * b0 +
        (30720 : K[X]) * y1 ^ 2 * v1)

/-! ## `w₁ = 0` mixed pair after `e₁(a) = p₂(a) = e₃(a) = 0` -/

set_option maxHeartbeats 16000000 in
/-- Tenth quotient after `w₁ = h₀ w₁n`, `e₂ = h₀ e₃`, and the product
upgrade of `u₂`.  Head `-55296 e₁ (10935 p₂² - 540 p₂ e₁² + 7 e₁⁴)`. -/
def alignedSquareW1ZeroTenthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1 e3 a0 a1 a2 b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  -((387072 : K[X]) * e1 ^ 5) + (29859840 : K[X]) * e1 ^ 3 * a2 -
    (604661760 : K[X]) * e1 * a2 ^ 2 +
    h0 *
      (Polynomial.C κ * ((276480 : K[X]) * e1 ^ 4) -
        Polynomial.C κ * ((17915904 : K[X]) * e1 ^ 2 * a2) +
        Polynomial.C κ * ((241864704 : K[X]) * a2 ^ 2) +
        (7741440 : K[X]) * e1 ^ 4 * w1n ^ 2 -
        (2580480 : K[X]) * e1 ^ 3 * e3 * w1n +
        (184320 : K[X]) * e1 ^ 2 * e3 ^ 2 -
        (223948800 : K[X]) * e1 ^ 2 * w1n ^ 2 * a2 +
        (59719680 : K[X]) * e1 * e3 * w1n * a2 -
        (2488320 : K[X]) * e3 ^ 2 * a2 +
        (604661760 : K[X]) * w1n ^ 2 * a2 ^ 2) +
    h0 ^ 2 *
      (-(Polynomial.C κ * ((3317760 : K[X]) * e1 ^ 3 * w1n ^ 2)) +
        Polynomial.C κ * ((1105920 : K[X]) * e1 ^ 2 * e3 * w1n) -
        Polynomial.C κ * ((73728 : K[X]) * e1 * e3 ^ 2) +
        Polynomial.C κ * ((53747712 : K[X]) * e1 * w1n ^ 2 * a2) -
        Polynomial.C κ * ((11943936 : K[X]) * e3 * w1n * a2) -
        Polynomial.C μ * ((221760 : K[X]) * e1 ^ 3 * w1n) +
        Polynomial.C μ * ((40320 : K[X]) * e1 ^ 2 * e3) +
        Polynomial.C μ * ((6531840 : K[X]) * e1 * w1n * a2) -
        Polynomial.C μ * ((870912 : K[X]) * e3 * a2) -
        (9676800 : K[X]) * e1 ^ 3 * w1n ^ 4 +
        (5529600 : K[X]) * e1 ^ 2 * e3 * w1n ^ 3 +
        (268738560 : K[X]) * e1 ^ 2 * w1n * a1 -
        (921600 : K[X]) * e1 * e3 ^ 2 * w1n ^ 2 -
        (44789760 : K[X]) * e1 * e3 * a1 +
        (44789760 : K[X]) * e1 * w1n ^ 4 * a2 +
        (40960 : K[X]) * e3 ^ 3 * w1n -
        (14929920 : K[X]) * e3 * w1n ^ 3 * a2 -
        (3627970560 : K[X]) * w1n * a1 * a2) +
    h0 ^ 3 *
      (Polynomial.C κ * ((1658880 : K[X]) * e1 ^ 2 * w1n ^ 4) -
        Polynomial.C κ * ((884736 : K[X]) * e1 * e3 * w1n ^ 3) -
        Polynomial.C κ * ((107495424 : K[X]) * e1 * w1n * a1) +
        Polynomial.C κ * ((110592 : K[X]) * e3 ^ 2 * w1n ^ 2) +
        Polynomial.C κ * ((17915904 : K[X]) * e3 * a1) +
        Polynomial.C μ * ((317520 : K[X]) * e1 ^ 2 * w1n ^ 3) -
        Polynomial.C μ * ((141120 : K[X]) * e1 * e3 * w1n ^ 2) -
        Polynomial.C μ * ((7838208 : K[X]) * e1 * a1) +
        Polynomial.C μ * ((13440 : K[X]) * e3 ^ 2 * w1n) -
        Polynomial.C μ * ((326592 : K[X]) * w1n ^ 3 * a2) -
        Polynomial.C ν * ((15120 : K[X]) * e1 ^ 2 * w1n) +
        Polynomial.C ν * ((2880 : K[X]) * e1 * e3) +
        Polynomial.C ν * ((233280 : K[X]) * w1n * a2) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1 ^ 2) -
        Polynomial.C κ₅ * ((62208 : K[X]) * a2) +
        (829440 : K[X]) * e1 ^ 2 * w1n ^ 6 -
        (201553920 : K[X]) * e1 ^ 2 * a0 -
        (552960 : K[X]) * e1 * e3 * w1n ^ 5 -
        (134369280 : K[X]) * e1 * w1n ^ 3 * a1 +
        (92160 : K[X]) * e3 ^ 2 * w1n ^ 4 +
        (44789760 : K[X]) * e3 * w1n ^ 2 * a1 +
        (10883911680 : K[X]) * a0 * a2 +
        (5441955840 : K[X]) * a1 ^ 2) +
    h0 ^ 4 *
      (Polynomial.C κ * ((161243136 : K[X]) * e1 * a0) -
        Polynomial.C μ * ((5292 : K[X]) * e1 * w1n ^ 5) +
        Polynomial.C μ * ((2520 : K[X]) * e3 * w1n ^ 4) +
        Polynomial.C μ * ((1959552 : K[X]) * w1n ^ 2 * a1) +
        Polynomial.C ν * ((5400 : K[X]) * e1 * w1n ^ 3) -
        Polynomial.C ν * ((2160 : K[X]) * e3 * w1n ^ 2) -
        Polynomial.C ν * ((1399680 : K[X]) * a1) -
        Polynomial.C κ₅ * ((2304 : K[X]) * e1 * w1n ^ 2) +
        Polynomial.C κ₅ * ((768 : K[X]) * e3 * w1n) +
        Polynomial.C ν₂ * ((324 : K[X]) * e1 * w1n) -
        Polynomial.C ν₂ * ((72 : K[X]) * e3) -
        Polynomial.C κ₇ * ((72 : K[X]) * e1) +
        (403107840 : K[X]) * e1 * w1n ^ 2 * a0 -
        (134369280 : K[X]) * e3 * w1n * a0) +
    h0 ^ 5 *
      (Polynomial.C μ * ((135 : K[X]) * w1n ^ 7) -
        Polynomial.C μ * ((23514624 : K[X]) * w1n * a0) -
        Polynomial.C κ₃ * ((20155392 : K[X]) * a0) -
        Polynomial.C ν * ((81 : K[X]) * w1n ^ 5) +
        Polynomial.C ν₂ * ((9 : K[X]) * w1n ^ 3) -
        Polynomial.C μ₃ * w1n -
        (9795520512 : K[X]) * b0)

/-- Ninth quotient after the further upgrades `e₁ = h₀ e₁b`,
`p₂ = h₀ a₂b`.  Head `-5120 e₃³`. -/
def alignedSquareW1ZeroE1A2NinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1b e3 a0 a1 a2b b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) : K[X] :=
  -((5120 : K[X]) * e3 ^ 3) +
    h0 *
      (-(Polynomial.C κ * ((36864 : K[X]) * e3 ^ 2 * w1n)) +
        Polynomial.C κ * ((2985984 : K[X]) * e3 * a2b) -
        Polynomial.C μ * ((2688 : K[X]) * e3 ^ 2) +
        (184320 : K[X]) * e1b * e3 ^ 2 * w1n -
        (7464960 : K[X]) * e1b * e3 * a2b -
        (46080 : K[X]) * e3 ^ 2 * w1n ^ 3 +
        (7464960 : K[X]) * e3 * w1n ^ 2 * a2b -
        (22394880 : K[X]) * e3 * w1n * a1 -
        (302330880 : K[X]) * w1n * a2b ^ 2 +
        (1813985280 : K[X]) * a1 * a2b) +
    h0 ^ 2 *
      (-(Polynomial.C κ * ((110592 : K[X]) * e1b ^ 2 * e3)) +
        Polynomial.C κ * ((331776 : K[X]) * e1b * e3 * w1n ^ 2) -
        Polynomial.C κ * ((17915904 : K[X]) * e1b * w1n * a2b) +
        Polynomial.C κ * ((26873856 : K[X]) * e1b * a1) +
        Polynomial.C μ * ((40320 : K[X]) * e1b * e3 * w1n) -
        Polynomial.C μ * ((1306368 : K[X]) * e1b * a2b) -
        Polynomial.C μ * ((2016 : K[X]) * e3 * w1n ^ 3) +
        Polynomial.C μ * ((326592 : K[X]) * w1n ^ 2 * a2b) -
        Polynomial.C μ * ((3919104 : K[X]) * w1n * a1) -
        Polynomial.C κ₃ * ((3359232 : K[X]) * a1) +
        Polynomial.C ν * ((1440 : K[X]) * e3 * w1n) -
        Polynomial.C ν * ((233280 : K[X]) * a2b) -
        Polynomial.C κ₅ * ((384 : K[X]) * e3) +
        (184320 : K[X]) * e1b ^ 3 * e3 -
        (1382400 : K[X]) * e1b ^ 2 * e3 * w1n ^ 2 +
        (44789760 : K[X]) * e1b ^ 2 * w1n * a2b -
        (33592320 : K[X]) * e1b ^ 2 * a1 +
        (276480 : K[X]) * e1b * e3 * w1n ^ 4 -
        (22394880 : K[X]) * e1b * w1n ^ 3 * a2b +
        (67184640 : K[X]) * e1b * w1n ^ 2 * a1 +
        (67184640 : K[X]) * e3 * a0 -
        (1632586752 : K[X]) * b1) +
    h0 ^ 3 *
      (Polynomial.C κ * ((552960 : K[X]) * e1b ^ 3 * w1n) -
        Polynomial.C κ * ((663552 : K[X]) * e1b ^ 2 * w1n ^ 3) +
        Polynomial.C κ * ((80621568 : K[X]) * w1n * a0) +
        Polynomial.C μ * ((20160 : K[X]) * e1b ^ 3) -
        Polynomial.C μ * ((105840 : K[X]) * e1b ^ 2 * w1n ^ 2) +
        Polynomial.C μ * ((3780 : K[X]) * e1b * w1n ^ 4) -
        Polynomial.C μ * ((189 : K[X]) * w1n ^ 6) -
        Polynomial.C μ * ((23514624 : K[X]) * a0) +
        Polynomial.C ν * ((2160 : K[X]) * e1b ^ 2) -
        Polynomial.C ν * ((3240 : K[X]) * e1b * w1n ^ 2) +
        Polynomial.C ν * ((135 : K[X]) * w1n ^ 4) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1b * w1n) -
        Polynomial.C ν₂ * ((108 : K[X]) * e1b) -
        Polynomial.C ν₂ * ((27 : K[X]) * w1n ^ 2) -
        Polynomial.C κ₇ * ((36 : K[X]) * w1n) -
        (967680 : K[X]) * e1b ^ 4 * w1n +
        (2764800 : K[X]) * e1b ^ 3 * w1n ^ 3 -
        (414720 : K[X]) * e1b ^ 2 * w1n ^ 5 -
        (201553920 : K[X]) * e1b * w1n * a0)

/-- Mixed ninth after `e₃ = h₀ e₃b`.  Head `302330880 a₂b (6 p₁ - a₂b w₁n)`. -/
def alignedSquareW1ZeroMixedNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1b e3b a0 a1 a2b b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) : K[X] :=
  -((302330880 : K[X]) * w1n * a2b ^ 2) +
    (1813985280 : K[X]) * a1 * a2b +
    h0 *
      (-(Polynomial.C κ * ((17915904 : K[X]) * e1b * w1n * a2b)) +
        Polynomial.C κ * ((26873856 : K[X]) * e1b * a1) +
        Polynomial.C κ * ((2985984 : K[X]) * e3b * a2b) -
        Polynomial.C μ * ((1306368 : K[X]) * e1b * a2b) +
        Polynomial.C μ * ((326592 : K[X]) * w1n ^ 2 * a2b) -
        Polynomial.C μ * ((3919104 : K[X]) * w1n * a1) -
        Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
        Polynomial.C ν * ((233280 : K[X]) * a2b) +
        (44789760 : K[X]) * e1b ^ 2 * w1n * a2b -
        (33592320 : K[X]) * e1b ^ 2 * a1 -
        (7464960 : K[X]) * e1b * e3b * a2b -
        (22394880 : K[X]) * e1b * w1n ^ 3 * a2b +
        (67184640 : K[X]) * e1b * w1n ^ 2 * a1 +
        (7464960 : K[X]) * e3b * w1n ^ 2 * a2b -
        (22394880 : K[X]) * e3b * w1n * a1 -
        (1632586752 : K[X]) * b1) +
    h0 ^ 2 *
      (Polynomial.C κ * ((552960 : K[X]) * e1b ^ 3 * w1n) -
        Polynomial.C κ * ((110592 : K[X]) * e1b ^ 2 * e3b) -
        Polynomial.C κ * ((663552 : K[X]) * e1b ^ 2 * w1n ^ 3) +
        Polynomial.C κ * ((331776 : K[X]) * e1b * e3b * w1n ^ 2) -
        Polynomial.C κ * ((36864 : K[X]) * e3b ^ 2 * w1n) +
        Polynomial.C κ * ((80621568 : K[X]) * w1n * a0) +
        Polynomial.C μ * ((20160 : K[X]) * e1b ^ 3) -
        Polynomial.C μ * ((105840 : K[X]) * e1b ^ 2 * w1n ^ 2) +
        Polynomial.C μ * ((40320 : K[X]) * e1b * e3b * w1n) +
        Polynomial.C μ * ((3780 : K[X]) * e1b * w1n ^ 4) -
        Polynomial.C μ * ((2688 : K[X]) * e3b ^ 2) -
        Polynomial.C μ * ((2016 : K[X]) * e3b * w1n ^ 3) -
        Polynomial.C μ * ((189 : K[X]) * w1n ^ 6) -
        Polynomial.C μ * ((23514624 : K[X]) * a0) +
        Polynomial.C ν * ((2160 : K[X]) * e1b ^ 2) -
        Polynomial.C ν * ((3240 : K[X]) * e1b * w1n ^ 2) +
        Polynomial.C ν * ((1440 : K[X]) * e3b * w1n) +
        Polynomial.C ν * ((135 : K[X]) * w1n ^ 4) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1b * w1n) -
        Polynomial.C κ₅ * ((384 : K[X]) * e3b) -
        Polynomial.C ν₂ * ((108 : K[X]) * e1b) -
        Polynomial.C ν₂ * ((27 : K[X]) * w1n ^ 2) -
        Polynomial.C κ₇ * ((36 : K[X]) * w1n) -
        (967680 : K[X]) * e1b ^ 4 * w1n +
        (184320 : K[X]) * e1b ^ 3 * e3b +
        (2764800 : K[X]) * e1b ^ 3 * w1n ^ 3 -
        (1382400 : K[X]) * e1b ^ 2 * e3b * w1n ^ 2 -
        (414720 : K[X]) * e1b ^ 2 * w1n ^ 5 +
        (184320 : K[X]) * e1b * e3b ^ 2 * w1n +
        (276480 : K[X]) * e1b * e3b * w1n ^ 4 -
        (201553920 : K[X]) * e1b * w1n * a0 -
        (5120 : K[X]) * e3b ^ 3 -
        (46080 : K[X]) * e3b ^ 2 * w1n ^ 3 +
        (67184640 : K[X]) * e3b * a0)

set_option maxHeartbeats 16000000 in
/-- Mixed tenth after `e₃ = h₀ e₃b`.  Head
`120932352 (45 p₁² - 30 p₁ a₂b w₁n - 5 a₂b² e₁b + 2 a₂b² κ + 5 a₂b² w₁n²)`. -/
def alignedSquareW1ZeroMixedTenthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1b e3b a0 a1 a2b b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  Polynomial.C κ * ((241864704 : K[X]) * a2b ^ 2) -
    (604661760 : K[X]) * e1b * a2b ^ 2 +
    (604661760 : K[X]) * w1n ^ 2 * a2b ^ 2 -
    (3627970560 : K[X]) * w1n * a1 * a2b +
    (5441955840 : K[X]) * a1 ^ 2 +
    h0 *
      (-(Polynomial.C κ * ((17915904 : K[X]) * e1b ^ 2 * a2b)) +
        Polynomial.C κ * ((53747712 : K[X]) * e1b * w1n ^ 2 * a2b) -
        Polynomial.C κ * ((107495424 : K[X]) * e1b * w1n * a1) -
        Polynomial.C κ * ((11943936 : K[X]) * e3b * w1n * a2b) +
        Polynomial.C κ * ((17915904 : K[X]) * e3b * a1) +
        Polynomial.C μ * ((6531840 : K[X]) * e1b * w1n * a2b) -
        Polynomial.C μ * ((7838208 : K[X]) * e1b * a1) -
        Polynomial.C μ * ((870912 : K[X]) * e3b * a2b) -
        Polynomial.C μ * ((326592 : K[X]) * w1n ^ 3 * a2b) +
        Polynomial.C μ * ((1959552 : K[X]) * w1n ^ 2 * a1) +
        Polynomial.C ν * ((233280 : K[X]) * w1n * a2b) -
        Polynomial.C ν * ((1399680 : K[X]) * a1) -
        Polynomial.C κ₅ * ((62208 : K[X]) * a2b) +
        (29859840 : K[X]) * e1b ^ 3 * a2b -
        (223948800 : K[X]) * e1b ^ 2 * w1n ^ 2 * a2b +
        (268738560 : K[X]) * e1b ^ 2 * w1n * a1 +
        (59719680 : K[X]) * e1b * e3b * w1n * a2b -
        (44789760 : K[X]) * e1b * e3b * a1 +
        (44789760 : K[X]) * e1b * w1n ^ 4 * a2b -
        (134369280 : K[X]) * e1b * w1n ^ 3 * a1 -
        (2488320 : K[X]) * e3b ^ 2 * a2b -
        (14929920 : K[X]) * e3b * w1n ^ 3 * a2b +
        (44789760 : K[X]) * e3b * w1n ^ 2 * a1 +
        (10883911680 : K[X]) * a0 * a2b) +
    h0 ^ 2 *
      (Polynomial.C κ * ((276480 : K[X]) * e1b ^ 4) -
        Polynomial.C κ * ((3317760 : K[X]) * e1b ^ 3 * w1n ^ 2) +
        Polynomial.C κ * ((1105920 : K[X]) * e1b ^ 2 * e3b * w1n) +
        Polynomial.C κ * ((1658880 : K[X]) * e1b ^ 2 * w1n ^ 4) -
        Polynomial.C κ * ((73728 : K[X]) * e1b * e3b ^ 2) -
        Polynomial.C κ * ((884736 : K[X]) * e1b * e3b * w1n ^ 3) +
        Polynomial.C κ * ((161243136 : K[X]) * e1b * a0) +
        Polynomial.C κ * ((110592 : K[X]) * e3b ^ 2 * w1n ^ 2) -
        Polynomial.C μ * ((221760 : K[X]) * e1b ^ 3 * w1n) +
        Polynomial.C μ * ((40320 : K[X]) * e1b ^ 2 * e3b) +
        Polynomial.C μ * ((317520 : K[X]) * e1b ^ 2 * w1n ^ 3) -
        Polynomial.C μ * ((141120 : K[X]) * e1b * e3b * w1n ^ 2) -
        Polynomial.C μ * ((5292 : K[X]) * e1b * w1n ^ 5) +
        Polynomial.C μ * ((13440 : K[X]) * e3b ^ 2 * w1n) +
        Polynomial.C μ * ((2520 : K[X]) * e3b * w1n ^ 4) +
        Polynomial.C μ * ((135 : K[X]) * w1n ^ 7) -
        Polynomial.C μ * ((23514624 : K[X]) * w1n * a0) -
        Polynomial.C κ₃ * ((20155392 : K[X]) * a0) -
        Polynomial.C ν * ((15120 : K[X]) * e1b ^ 2 * w1n) +
        Polynomial.C ν * ((2880 : K[X]) * e1b * e3b) +
        Polynomial.C ν * ((5400 : K[X]) * e1b * w1n ^ 3) -
        Polynomial.C ν * ((2160 : K[X]) * e3b * w1n ^ 2) -
        Polynomial.C ν * ((81 : K[X]) * w1n ^ 5) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1b ^ 2) -
        Polynomial.C κ₅ * ((2304 : K[X]) * e1b * w1n ^ 2) +
        Polynomial.C κ₅ * ((768 : K[X]) * e3b * w1n) +
        Polynomial.C ν₂ * ((324 : K[X]) * e1b * w1n) -
        Polynomial.C ν₂ * ((72 : K[X]) * e3b) +
        Polynomial.C ν₂ * ((9 : K[X]) * w1n ^ 3) -
        Polynomial.C κ₇ * ((72 : K[X]) * e1b) -
        Polynomial.C μ₃ * w1n -
        (387072 : K[X]) * e1b ^ 5 +
        (7741440 : K[X]) * e1b ^ 4 * w1n ^ 2 -
        (2580480 : K[X]) * e1b ^ 3 * e3b * w1n -
        (9676800 : K[X]) * e1b ^ 3 * w1n ^ 4 +
        (184320 : K[X]) * e1b ^ 2 * e3b ^ 2 +
        (5529600 : K[X]) * e1b ^ 2 * e3b * w1n ^ 3 +
        (829440 : K[X]) * e1b ^ 2 * w1n ^ 6 -
        (201553920 : K[X]) * e1b ^ 2 * a0 -
        (921600 : K[X]) * e1b * e3b ^ 2 * w1n ^ 2 -
        (552960 : K[X]) * e1b * e3b * w1n ^ 5 +
        (403107840 : K[X]) * e1b * w1n ^ 2 * a0 +
        (40960 : K[X]) * e3b ^ 3 * w1n +
        (92160 : K[X]) * e3b ^ 2 * w1n ^ 4 -
        (134369280 : K[X]) * e3b * w1n * a0 -
        (9795520512 : K[X]) * b0)

/-- Ninth quotient on the `a₂b = h₀ a₂c` child.  At `p₁(a) = 0` the
head is `-1632586752 q₁`. -/
def alignedSquareW1ZeroA2cNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1b e3b a0 a1 a2c b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) : K[X] :=
  Polynomial.C κ * ((26873856 : K[X]) * e1b * a1) -
    Polynomial.C μ * ((3919104 : K[X]) * w1n * a1) -
    Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
    (33592320 : K[X]) * e1b ^ 2 * a1 +
    (67184640 : K[X]) * e1b * w1n ^ 2 * a1 -
    (22394880 : K[X]) * e3b * w1n * a1 +
    (1813985280 : K[X]) * a1 * a2c -
    (1632586752 : K[X]) * b1 +
    h0 *
      (Polynomial.C κ * ((552960 : K[X]) * e1b ^ 3 * w1n) -
        Polynomial.C κ * ((110592 : K[X]) * e1b ^ 2 * e3b) -
        Polynomial.C κ * ((663552 : K[X]) * e1b ^ 2 * w1n ^ 3) +
        Polynomial.C κ * ((331776 : K[X]) * e1b * e3b * w1n ^ 2) -
        Polynomial.C κ * ((17915904 : K[X]) * e1b * w1n * a2c) -
        Polynomial.C κ * ((36864 : K[X]) * e3b ^ 2 * w1n) +
        Polynomial.C κ * ((2985984 : K[X]) * e3b * a2c) +
        Polynomial.C κ * ((80621568 : K[X]) * w1n * a0) +
        Polynomial.C μ * ((20160 : K[X]) * e1b ^ 3) -
        Polynomial.C μ * ((105840 : K[X]) * e1b ^ 2 * w1n ^ 2) +
        Polynomial.C μ * ((40320 : K[X]) * e1b * e3b * w1n) +
        Polynomial.C μ * ((3780 : K[X]) * e1b * w1n ^ 4) -
        Polynomial.C μ * ((1306368 : K[X]) * e1b * a2c) -
        Polynomial.C μ * ((2688 : K[X]) * e3b ^ 2) -
        Polynomial.C μ * ((2016 : K[X]) * e3b * w1n ^ 3) -
        Polynomial.C μ * ((189 : K[X]) * w1n ^ 6) +
        Polynomial.C μ * ((326592 : K[X]) * w1n ^ 2 * a2c) -
        Polynomial.C μ * ((23514624 : K[X]) * a0) +
        Polynomial.C ν * ((2160 : K[X]) * e1b ^ 2) -
        Polynomial.C ν * ((3240 : K[X]) * e1b * w1n ^ 2) +
        Polynomial.C ν * ((1440 : K[X]) * e3b * w1n) +
        Polynomial.C ν * ((135 : K[X]) * w1n ^ 4) -
        Polynomial.C ν * ((233280 : K[X]) * a2c) +
        Polynomial.C κ₅ * ((1152 : K[X]) * e1b * w1n) -
        Polynomial.C κ₅ * ((384 : K[X]) * e3b) -
        Polynomial.C ν₂ * ((108 : K[X]) * e1b) -
        Polynomial.C ν₂ * ((27 : K[X]) * w1n ^ 2) -
        Polynomial.C κ₇ * ((36 : K[X]) * w1n) -
        (967680 : K[X]) * e1b ^ 4 * w1n +
        (184320 : K[X]) * e1b ^ 3 * e3b +
        (2764800 : K[X]) * e1b ^ 3 * w1n ^ 3 -
        (1382400 : K[X]) * e1b ^ 2 * e3b * w1n ^ 2 -
        (414720 : K[X]) * e1b ^ 2 * w1n ^ 5 +
        (44789760 : K[X]) * e1b ^ 2 * w1n * a2c +
        (184320 : K[X]) * e1b * e3b ^ 2 * w1n +
        (276480 : K[X]) * e1b * e3b * w1n ^ 4 -
        (7464960 : K[X]) * e1b * e3b * a2c -
        (22394880 : K[X]) * e1b * w1n ^ 3 * a2c -
        (201553920 : K[X]) * e1b * w1n * a0 -
        (5120 : K[X]) * e3b ^ 3 -
        (46080 : K[X]) * e3b ^ 2 * w1n ^ 3 +
        (7464960 : K[X]) * e3b * w1n ^ 2 * a2c +
        (67184640 : K[X]) * e3b * a0 -
        (302330880 : K[X]) * w1n * a2c ^ 2)

variable {K : Type*} [Field K] [CharZero K]

/-! ## Scalar identities -/

/-- Cube-order mixed heads: `2 w₁ N + T = 30720 v y² - 45 ν₂ w₁³`. -/
theorem alignedSquareMuZeroMixed_headCombo610
    (w1 e1n y v a1 rho : K) (κ ν₂ : K) :
    (2 : K) * w1 *
          (-(κ * ((36864 : K) * y * v)) - ν₂ * ((27 : K) * w1 ^ 2) +
            (92160 : K) * e1n * y * v - (22394880 : K) * v * a1 -
              (5120 : K) * rho) +
        (κ * ((73728 : K) * y * v * w1) + ν₂ * ((9 : K) * w1 ^ 3) -
          (184320 : K) * e1n * y * v * w1 + (30720 : K) * y ^ 2 * v +
            (44789760 : K) * v * w1 * a1 + (10240 : K) * w1 * rho) =
      (30720 : K) * v * y ^ 2 - (45 : K) * ν₂ * w1 ^ 3 := by
  ring

/-- Deep tenth head is `92160 (243 p₁ + v₁ w₁)²`. -/
theorem alignedSquareMuZeroDeepMixed_tenthHeadSquare610
    (w1 a1 v1 : K) :
    (92160 : K) * w1 ^ 2 * v1 ^ 2 + (44789760 : K) * w1 * a1 * v1 +
        (5441955840 : K) * a1 ^ 2 =
      (92160 : K) * ((243 : K) * a1 + v1 * w1) ^ 2 := by
  ring

/-- Tenth `w₁ = 0` head modulo the eighth quadratic. -/
theorem alignedSquareW1Zero_tenthHeadRemQ8610 (e1 a2 : K) :
    -((55296 : K) * e1 *
          ((10935 : K) * a2 ^ 2 - (540 : K) * a2 * e1 ^ 2 +
            (7 : K) * e1 ^ 4)) =
      -((276480 : K) * e1 *
            (e1 ^ 4 - (81 : K) * e1 ^ 2 * a2 + (2187 : K) * a2 ^ 2)) +
        (55296 : K) * e1 ^ 3 * ((135 : K) * a2 - (2 : K) * e1 ^ 2) := by
  ring

/-- On the ray `135 p₂ = 2 e₁²` the eighth quadratic is `(7/25) e₁⁴`. -/
theorem alignedSquareW1Zero_Q8_on_tenthRay610
    (e1 a2 : K) (h : (135 : K) * a2 = (2 : K) * e1 ^ 2) :
    (25 : K) * (e1 ^ 4 - (81 : K) * e1 ^ 2 * a2 + (2187 : K) * a2 ^ 2) =
      (7 : K) * e1 ^ 4 := by
  have h2025 :
      (2025 : K) * e1 ^ 2 * a2 = (30 : K) * e1 ^ 4 := by
    calc
      (2025 : K) * e1 ^ 2 * a2 =
          (15 : K) * e1 ^ 2 * ((135 : K) * a2) := by ring
      _ = (15 : K) * e1 ^ 2 * ((2 : K) * e1 ^ 2) := by rw [h]
      _ = (30 : K) * e1 ^ 4 := by ring
  have h54675 :
      (54675 : K) * a2 ^ 2 = (12 : K) * e1 ^ 4 := by
    have hsq : ((135 : K) * a2) ^ 2 = (4 : K) * e1 ^ 4 := by
      rw [h]; ring
    have h18225 : (18225 : K) * a2 ^ 2 = (4 : K) * e1 ^ 4 := by
      linear_combination hsq
    calc
      (54675 : K) * a2 ^ 2 = (3 : K) * ((18225 : K) * a2 ^ 2) := by ring
      _ = (3 : K) * ((4 : K) * e1 ^ 4) := by rw [h18225]
      _ = (12 : K) * e1 ^ 4 := by ring
  calc
    (25 : K) * (e1 ^ 4 - (81 : K) * e1 ^ 2 * a2 + (2187 : K) * a2 ^ 2) =
        (25 : K) * e1 ^ 4 - (2025 : K) * e1 ^ 2 * a2 +
          (54675 : K) * a2 ^ 2 := by
      ring
    _ = (25 : K) * e1 ^ 4 - (30 : K) * e1 ^ 4 + (12 : K) * e1 ^ 4 := by
      rw [h2025, h54675]
    _ = (7 : K) * e1 ^ 4 := by
      ring

/-- Mixed ninth `w₁ = 0` head after `e₃ = 0`. -/
theorem alignedSquareW1ZeroMixed_ninthHead610 (w1n a1 a2b : K) :
    -((302330880 : K) * w1n * a2b ^ 2) + (1813985280 : K) * a1 * a2b =
      (302330880 : K) * a2b * ((6 : K) * a1 - a2b * w1n) := by
  ring

/-- Mixed tenth `w₁ = 0` head after `e₃ = 0`. -/
theorem alignedSquareW1ZeroMixed_tenthHead610
    (w1n e1b a1 a2b : K) (κ : K) :
    κ * ((241864704 : K) * a2b ^ 2) - (604661760 : K) * e1b * a2b ^ 2 +
        (604661760 : K) * w1n ^ 2 * a2b ^ 2 -
          (3627970560 : K) * w1n * a1 * a2b +
            (5441955840 : K) * a1 ^ 2 =
      (120932352 : K) *
        ((45 : K) * a1 ^ 2 - (30 : K) * a1 * a2b * w1n -
          (5 : K) * a2b ^ 2 * e1b + (2 : K) * a2b ^ 2 * κ +
            (5 : K) * a2b ^ 2 * w1n ^ 2) := by
  ring

/-! ## Factor identities, `μ = 0` mixed pair -/

set_option maxHeartbeats 16000000 in
/-- After the product substitution and `e₃ = y + 6 e₁n w₁`, the
`ν = 0` ninth load is the mixed pre-load. -/
theorem alignedSquareMuZeroMixed_ninthPreFactor610
    (h0 w1 e1n y v a0 a1 b1 : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ : K) :
    alignedSquareMuZeroNuZeroNinthLoad610 h0 w1 e1n
        (y + (6 : K[X]) * e1n * w1) v a0 a1
        ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
          Polynomial.C (81 : K)⁻¹)
        b1 κ κ₃ κ₅ ν₂ κ₇ =
      alignedSquareMuZeroMixedNinthPreLoad610 h0 w1 e1n y v a0 a1 b1
        κ κ₃ κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareMuZeroNuZeroNinthLoad610,
    alignedSquareMuZeroMixedNinthPreLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

/-- The cube identity `y³ + 9 v² w₁ = h₀ ρ` cancels one more `h₀`. -/
theorem alignedSquareMuZeroMixed_ninthCubeFactor610
    (h0 w1 e1n y v a0 a1 b1 rho : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ : K)
    (hrho :
      y ^ 3 + (9 : K[X]) * v ^ 2 * w1 = h0 * rho) :
    alignedSquareMuZeroMixedNinthPreLoad610 h0 w1 e1n y v a0 a1 b1
        κ κ₃ κ₅ ν₂ κ₇ =
      h0 *
        alignedSquareMuZeroMixedNinthLoad610 h0 w1 e1n y v a0 a1 b1 rho
          κ κ₃ κ₅ ν₂ κ₇ := by
  simp only [alignedSquareMuZeroMixedNinthPreLoad610,
    alignedSquareMuZeroMixedNinthLoad610]
  rw [hrho]
  ring

set_option maxHeartbeats 16000000 in
/-- After the product substitution and `e₃ = y + 6 e₁n w₁`, the
tenth peeled row is `h₀²` times the mixed tenth pre-load. -/
theorem alignedSquareMuZeroMixed_tenthPreFactor610
    (h0 w1 e1n y v a0 a1 b0 : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ μ₃ : K) :
    alignedTenthSquarePeeledRow610 h0 w1 (h0 * e1n)
        (h0 * (y + (6 : K[X]) * e1n * w1))
        (h0 * v +
          (81 : K[X]) *
            ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
              Polynomial.C (81 : K)⁻¹))
        ((2048 : K[X]) * h0 ^ 2 * e1n ^ 3 * w1 ^ 4) a0 a1
        ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
          Polynomial.C (81 : K)⁻¹)
        b0 κ 0 κ₃ 0 κ₅ ν₂ κ₇ μ₃ =
      h0 ^ 2 *
        alignedSquareMuZeroMixedTenthPreLoad610 h0 w1 e1n y v a0 a1 b0
          κ κ₃ κ₅ ν₂ κ₇ μ₃ := by
  apply Polynomial.funext
  intro z
  simp only [alignedTenthSquarePeeledRow610,
    alignedSquareMuZeroMixedTenthPreLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

/-- Cube identity on the tenth pre-load. -/
theorem alignedSquareMuZeroMixed_tenthCubeFactor610
    (h0 w1 e1n y v a0 a1 b0 rho : K[X])
    (κ κ₃ κ₅ ν₂ κ₇ μ₃ : K)
    (hrho :
      y ^ 3 + (9 : K[X]) * v ^ 2 * w1 = h0 * rho) :
    alignedSquareMuZeroMixedTenthPreLoad610 h0 w1 e1n y v a0 a1 b0
        κ κ₃ κ₅ ν₂ κ₇ μ₃ =
      h0 *
        alignedSquareMuZeroMixedTenthLoad610 h0 w1 e1n y v a0 a1 b0 rho
          κ κ₃ κ₅ ν₂ κ₇ μ₃ := by
  simp only [alignedSquareMuZeroMixedTenthPreLoad610,
    alignedSquareMuZeroMixedTenthLoad610]
  rw [hrho]
  ring

set_option maxHeartbeats 16000000 in
/-- Deep ninth mixed load after `v = h₀ v₁`, `y = h₀ y₁`, `ν₂ = 0`. -/
theorem alignedSquareMuZeroDeepMixed_ninthFactor610
    (h0 w1 e1n a0 a1 b1 y1 v1 : K[X])
    (κ κ₃ κ₅ κ₇ : K) :
    alignedSquareMuZeroMixedNinthLoad610 h0 w1 e1n (h0 * y1)
        (h0 * v1) a0 a1 b1
        (h0 ^ 2 * y1 ^ 3 + (9 : K[X]) * h0 * v1 ^ 2 * w1)
        κ κ₃ κ₅ 0 κ₇ =
      h0 *
        alignedSquareMuZeroDeepMixedNinthLoad610 h0 w1 e1n a0 a1 b1 y1
          v1 κ κ₃ κ₅ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareMuZeroMixedNinthLoad610,
    alignedSquareMuZeroDeepMixedNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 16000000 in
/-- Deep tenth mixed load after the same upgrades. -/
theorem alignedSquareMuZeroDeepMixed_tenthFactor610
    (h0 w1 e1n a0 a1 b0 y1 v1 : K[X])
    (κ κ₃ κ₅ κ₇ μ₃ : K) :
    alignedSquareMuZeroMixedTenthLoad610 h0 w1 e1n (h0 * y1)
        (h0 * v1) a0 a1 b0
        (h0 ^ 2 * y1 ^ 3 + (9 : K[X]) * h0 * v1 ^ 2 * w1)
        κ κ₃ κ₅ 0 κ₇ μ₃ =
      h0 *
        alignedSquareMuZeroDeepMixedTenthLoad610 h0 w1 e1n a0 a1 b0 y1
          v1 κ κ₃ κ₅ κ₇ μ₃ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareMuZeroMixedTenthLoad610,
    alignedSquareMuZeroDeepMixedTenthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

/-! ## Factor identities, `w₁ = 0` mixed pair -/

set_option maxHeartbeats 16000000 in
/-- Tenth peeled row after `w₁ = h₀ w₁n` and the product upgrade. -/
theorem alignedSquareW1Zero_tenthFactor610
    (h0 w1n e1 e3 a0 a1 a2 b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K) :
    alignedTenthSquarePeeledRow610 h0 (h0 * w1n) e1 (h0 * e3)
        (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n))
        ((2048 : K[X]) * e1 ^ 3 * h0 ^ 3 * w1n ^ 4 -
          Polynomial.C μ * h0 ^ 6 * w1n ^ 7) a0 a1 a2 b0
        κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
      h0 *
        alignedSquareW1ZeroTenthLoad610 h0 w1n e1 e3 a0 a1 a2 b0 κ μ
          κ₃ ν κ₅ ν₂ κ₇ μ₃ := by
  apply Polynomial.funext
  intro z
  simp only [alignedTenthSquarePeeledRow610,
    alignedSquareW1ZeroTenthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 16000000 in
/-- Ninth load after `e₁ = h₀ e₁b`, `p₂ = h₀ a₂b`. -/
theorem alignedSquareW1ZeroE1A2_ninthFactor610
    (h0 w1n e1b e3 a0 a1 a2b b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) :
    alignedSquareW1ZeroNinthLoad610 h0 w1n (h0 * e1b) e3 a0 a1
        (h0 * a2b) b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
      h0 *
        alignedSquareW1ZeroE1A2NinthLoad610 h0 w1n e1b e3 a0 a1 a2b b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareW1ZeroNinthLoad610,
    alignedSquareW1ZeroE1A2NinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 16000000 in
/-- Mixed ninth after `e₃ = h₀ e₃b`. -/
theorem alignedSquareW1ZeroMixed_ninthFactor610
    (h0 w1n e1b e3b a0 a1 a2b b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) :
    alignedSquareW1ZeroE1A2NinthLoad610 h0 w1n e1b (h0 * e3b) a0 a1
        a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
      h0 *
        alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1 a2b
          b1 κ μ κ₃ ν κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareW1ZeroE1A2NinthLoad610,
    alignedSquareW1ZeroMixedNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 16000000 in
/-- Mixed tenth after `e₁ = h₀ e₁b`, `p₂ = h₀ a₂b`, `e₃ = h₀ e₃b`. -/
theorem alignedSquareW1ZeroMixed_tenthFactor610
    (h0 w1n e1b e3b a0 a1 a2b b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K) :
    alignedSquareW1ZeroTenthLoad610 h0 w1n (h0 * e1b) (h0 * e3b) a0
        a1 (h0 * a2b) b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
      h0 ^ 3 *
        alignedSquareW1ZeroMixedTenthLoad610 h0 w1n e1b e3b a0 a1 a2b
          b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareW1ZeroTenthLoad610,
    alignedSquareW1ZeroMixedTenthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 16000000 in
/-- Ninth load on the `a₂b = h₀ a₂c` child. -/
theorem alignedSquareW1ZeroA2c_ninthFactor610
    (h0 w1n e1b e3b a0 a1 a2c b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) :
    alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1
        (h0 * a2c) b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
      h0 *
        alignedSquareW1ZeroA2cNinthLoad610 h0 w1n e1b e3b a0 a1 a2c b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareW1ZeroMixedNinthLoad610,
    alignedSquareW1ZeroA2cNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

/-! ## Head kills, `μ = 0` limb -/

set_option maxHeartbeats 16000000 in
/-- At the unique root the mixed ninth head is the named certificate. -/
theorem alignedSquareMuZeroMixed_ninthHeadKill610
    (h0 w1 e1n y v a0 a1 b1 rho : K[X])
    (κ μ₃ κ₃ κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrho :
      y ^ 3 + (9 : K[X]) * v ^ 2 * w1 = h0 * rho)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n)
          (h0 * (y + (6 : K[X]) * e1n * w1))
          (h0 * v +
            (81 : K[X]) *
              ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
                Polynomial.C (81 : K)⁻¹))
          a0 a1
          ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
            Polynomial.C (81 : K)⁻¹)
          b1 κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    -(κ * ((36864 : K) * y.eval x * v.eval x)) -
        ν₂ * ((27 : K) * w1.eval x ^ 2) +
          (92160 : K) * e1n.eval x * y.eval x * v.eval x -
            (22394880 : K) * v.eval x * a1.eval x -
              (5120 : K) * rho.eval x =
      0 := by
  have hν :=
    alignedSquareMuZeroNuZero_ninthPeeledFactor610 h0 w1 e1n
      (y + (6 : K[X]) * e1n * w1) v a0 a1
      ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
        Polynomial.C (81 : K)⁻¹)
      b1 κ κ₃ κ₅ ν₂ κ₇
  have hpre :=
    alignedSquareMuZeroMixed_ninthPreFactor610 h0 w1 e1n y v a0 a1 b1
      κ κ₃ κ₅ ν₂ κ₇
  have hcube :=
    alignedSquareMuZeroMixed_ninthCubeFactor610 h0 w1 e1n y v a0 a1 b1
      rho κ κ₃ κ₅ ν₂ κ₇ hrho
  rw [hν, hpre, hcube] at hrow
  have hrow' :
      h0 ^ 4 *
          alignedSquareMuZeroMixedNinthLoad610 h0 w1 e1n y v a0 a1 b1
            rho κ κ₃ κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6 := by
    calc
      h0 ^ 4 *
            alignedSquareMuZeroMixedNinthLoad610 h0 w1 e1n y v a0 a1
              b1 rho κ κ₃ κ₅ ν₂ κ₇ =
          h0 ^ 3 *
            (h0 *
              alignedSquareMuZeroMixedNinthLoad610 h0 w1 e1n y v a0 a1
                b1 rho κ κ₃ κ₅ ν₂ κ₇) := by
        ring
      _ = Polynomial.C μ₃ * h0 ^ 6 := hrow
  have hload :
      alignedSquareMuZeroMixedNinthLoad610 h0 w1 e1n y v a0 a1 b1 rho
          κ κ₃ κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 2 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 4 * (Polynomial.C μ₃ * h0 ^ 2) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 4 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareMuZeroMixedNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

set_option maxHeartbeats 16000000 in
/-- At the unique root the mixed tenth head is the named certificate. -/
theorem alignedSquareMuZeroMixed_tenthHeadKill610
    (h0 w1 e1n y v a0 a1 b0 rho : K[X])
    (κ κ₉ κ₃ κ₅ ν₂ κ₇ μ₃ : K)
    (hh0 : h0 ≠ 0)
    (hrho :
      y ^ 3 + (9 : K[X]) * v ^ 2 * w1 = h0 * rho)
    (hrow :
      alignedTenthSquarePeeledRow610 h0 w1 (h0 * e1n)
          (h0 * (y + (6 : K[X]) * e1n * w1))
          (h0 * v +
            (81 : K[X]) *
              ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
                Polynomial.C (81 : K)⁻¹))
          ((2048 : K[X]) * h0 ^ 2 * e1n ^ 3 * w1 ^ 4) a0 a1
          ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
            Polynomial.C (81 : K)⁻¹)
          b0 κ 0 κ₃ 0 κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    κ * ((73728 : K) * y.eval x * v.eval x * w1.eval x) +
        ν₂ * ((9 : K) * w1.eval x ^ 3) -
          (184320 : K) * e1n.eval x * y.eval x * v.eval x *
            w1.eval x +
            (30720 : K) * y.eval x ^ 2 * v.eval x +
              (44789760 : K) * v.eval x * w1.eval x * a1.eval x +
                (10240 : K) * w1.eval x * rho.eval x =
      0 := by
  have hpre :=
    alignedSquareMuZeroMixed_tenthPreFactor610 h0 w1 e1n y v a0 a1 b0
      κ κ₃ κ₅ ν₂ κ₇ μ₃
  have hcube :=
    alignedSquareMuZeroMixed_tenthCubeFactor610 h0 w1 e1n y v a0 a1 b0
      rho κ κ₃ κ₅ ν₂ κ₇ μ₃ hrho
  rw [hpre, hcube] at hrow
  have hrow' :
      h0 ^ 3 *
          alignedSquareMuZeroMixedTenthLoad610 h0 w1 e1n y v a0 a1 b0
            rho κ κ₃ κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 6 := by
    calc
      h0 ^ 3 *
            alignedSquareMuZeroMixedTenthLoad610 h0 w1 e1n y v a0 a1
              b0 rho κ κ₃ κ₅ ν₂ κ₇ μ₃ =
          h0 ^ 2 *
            (h0 *
              alignedSquareMuZeroMixedTenthLoad610 h0 w1 e1n y v a0 a1
                b0 rho κ κ₃ κ₅ ν₂ κ₇ μ₃) := by
        ring
      _ = Polynomial.C κ₉ * h0 ^ 6 := hrow
  have hload :
      alignedSquareMuZeroMixedTenthLoad610 h0 w1 e1n y v a0 a1 b0 rho
          κ κ₃ κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 3 := by
    have hpow : Polynomial.C κ₉ * h0 ^ 6 =
        h0 ^ 3 * (Polynomial.C κ₉ * h0 ^ 3) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 3 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareMuZeroMixedTenthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  linear_combination hloadx

/-- Mixed-pair residual: both heads vanish iff
`2048 v(a) y(a)² = 3 ν₂ w₁(a)³`. -/
theorem alignedSquareMuZeroMixed_comboResidual610
    (w1 e1n y v a1 rho : K) (κ ν₂ : K)
    (hN :
      -(κ * ((36864 : K) * y * v)) - ν₂ * ((27 : K) * w1 ^ 2) +
          (92160 : K) * e1n * y * v - (22394880 : K) * v * a1 -
            (5120 : K) * rho =
        0)
    (hT :
      κ * ((73728 : K) * y * v * w1) + ν₂ * ((9 : K) * w1 ^ 3) -
          (184320 : K) * e1n * y * v * w1 +
            (30720 : K) * y ^ 2 * v +
              (44789760 : K) * v * w1 * a1 +
                (10240 : K) * w1 * rho =
        0) :
    (2048 : K) * v * y ^ 2 = (3 : K) * ν₂ * w1 ^ 3 := by
  have hcombo :=
    alignedSquareMuZeroMixed_headCombo610 w1 e1n y v a1 rho κ ν₂
  rw [hN, hT] at hcombo
  simp only [mul_zero, add_zero, sub_zero, zero_mul] at hcombo
  have hsum :
      (30720 : K) * v * y ^ 2 - (45 : K) * ν₂ * w1 ^ 3 = 0 :=
    hcombo.symm
  have h15 : (15 : K) ≠ 0 := by norm_num
  have : (15 : K) * ((2048 : K) * v * y ^ 2 - (3 : K) * ν₂ * w1 ^ 3) =
      0 := by
    linear_combination hsum
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp this).resolve_left h15)

/-- Cube residual plus `v(a) = 0` and `w₁(a) ≠ 0` forces `y(a) = 0`. -/
theorem alignedSquareMuZeroMixed_vZero_yZero610
    (y v w1 : K)
    (hcube : y ^ 3 + (9 : K) * v ^ 2 * w1 = 0)
    (hv : v = 0) (hw1 : w1 ≠ 0) : y = 0 := by
  subst hv
  have : y ^ 3 = 0 := by linear_combination hcube
  exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this

set_option maxHeartbeats 16000000 in
/-- After `v(a) = y(a) = 0`, the mixed ninth head forces `ν₂ = 0`
because `ρ(a) = 0` as well. -/
theorem alignedSquareMuZeroMixed_vZero_nuTwoZero610
    (h0 w1 e1n y v a0 a1 b1 rho : K[X])
    (κ μ₃ κ₃ κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1)
    (hrho :
      y ^ 3 + (9 : K[X]) * v ^ 2 * w1 = h0 * rho)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n)
          (h0 * (y + (6 : K[X]) * e1n * w1))
          (h0 * v +
            (81 : K[X]) *
              ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
                Polynomial.C (81 : K)⁻¹))
          a0 a1
          ((w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
            Polynomial.C (81 : K)⁻¹)
          b1 κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0)
    (hv : v.eval x = 0) (hy : y.eval x = 0)
    (hw1 : w1.eval x ≠ 0) : ν₂ = 0 := by
  obtain ⟨y1, hy1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 y x hdeg1 hx hy
  obtain ⟨v1, hv1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 v x hdeg1 hx hv
  have hrho_eq :
      rho = h0 ^ 2 * y1 ^ 3 + (9 : K[X]) * h0 * v1 ^ 2 * w1 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * rho = y ^ 3 + (9 : K[X]) * v ^ 2 * w1 := hrho.symm
      _ = (h0 * y1) ^ 3 + (9 : K[X]) * (h0 * v1) ^ 2 * w1 := by
        rw [hy1, hv1]
      _ = h0 *
            (h0 ^ 2 * y1 ^ 3 + (9 : K[X]) * h0 * v1 ^ 2 * w1) := by
        ring
  have hrhox : rho.eval x = 0 := by
    have h := congrArg (fun w : K[X] => w.eval x) hrho_eq
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at h
    rw [h, hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    simp only [zero_mul, mul_zero, add_zero]
  have hhead :=
    alignedSquareMuZeroMixed_ninthHeadKill610 h0 w1 e1n y v a0 a1 b1
      rho κ μ₃ κ₃ κ₅ ν₂ κ₇ hh0 hrho hrow x hx
  rw [hv, hy, hrhox] at hhead
  simp only [mul_zero, zero_mul, add_zero, sub_zero, zero_add,
    zero_sub] at hhead
  have h27 : (27 : K) * w1.eval x ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hw1)
  have : ν₂ * ((27 : K) * w1.eval x ^ 2) = 0 := by
    linear_combination -hhead
  exact (mul_eq_zero.mp this).resolve_right h27

set_option maxHeartbeats 16000000 in
/-- Deep tenth head at the unique root is `(243 p₁ + v₁ w₁)²`. -/
theorem alignedSquareMuZeroDeepMixed_tenthHeadKill610
    (h0 w1 e1n a0 a1 b0 y1 v1 : K[X])
    (κ κ₉ κ₃ κ₅ κ₇ μ₃ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedTenthSquarePeeledRow610 h0 w1 (h0 * e1n)
          (h0 * (h0 * y1 + (6 : K[X]) * e1n * w1))
          (h0 * (h0 * v1) +
            (81 : K[X]) *
              ((w1 * (h0 * y1 + (3 : K[X]) * e1n * w1) -
                  h0 * (h0 * v1)) *
                Polynomial.C (81 : K)⁻¹))
          ((2048 : K[X]) * h0 ^ 2 * e1n ^ 3 * w1 ^ 4) a0 a1
          ((w1 * (h0 * y1 + (3 : K[X]) * e1n * w1) -
              h0 * (h0 * v1)) *
            Polynomial.C (81 : K)⁻¹)
          b0 κ 0 κ₃ 0 κ₅ 0 κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    (243 : K) * a1.eval x + v1.eval x * w1.eval x = 0 := by
  have hrho :
      (h0 * y1) ^ 3 + (9 : K[X]) * (h0 * v1) ^ 2 * w1 =
        h0 *
          (h0 ^ 2 * y1 ^ 3 + (9 : K[X]) * h0 * v1 ^ 2 * w1) := by
    ring
  have hpre :=
    alignedSquareMuZeroMixed_tenthPreFactor610 h0 w1 e1n (h0 * y1)
      (h0 * v1) a0 a1 b0 κ κ₃ κ₅ 0 κ₇ μ₃
  have hcube :=
    alignedSquareMuZeroMixed_tenthCubeFactor610 h0 w1 e1n (h0 * y1)
      (h0 * v1) a0 a1 b0
      (h0 ^ 2 * y1 ^ 3 + (9 : K[X]) * h0 * v1 ^ 2 * w1)
      κ κ₃ κ₅ 0 κ₇ μ₃ hrho
  have hdeep :=
    alignedSquareMuZeroDeepMixed_tenthFactor610 h0 w1 e1n a0 a1 b0 y1
      v1 κ κ₃ κ₅ κ₇ μ₃
  rw [hpre, hcube, hdeep] at hrow
  have hrow' :
      h0 ^ 4 *
          alignedSquareMuZeroDeepMixedTenthLoad610 h0 w1 e1n a0 a1 b0
            y1 v1 κ κ₃ κ₅ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 6 := by
    calc
      h0 ^ 4 *
            alignedSquareMuZeroDeepMixedTenthLoad610 h0 w1 e1n a0 a1
              b0 y1 v1 κ κ₃ κ₅ κ₇ μ₃ =
          h0 ^ 2 *
            (h0 *
              (h0 *
                alignedSquareMuZeroDeepMixedTenthLoad610 h0 w1 e1n a0
                  a1 b0 y1 v1 κ κ₃ κ₅ κ₇ μ₃)) := by
        ring
      _ = Polynomial.C κ₉ * h0 ^ 6 := hrow
  have hload :
      alignedSquareMuZeroDeepMixedTenthLoad610 h0 w1 e1n a0 a1 b0 y1
          v1 κ κ₃ κ₅ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 2 := by
    have hpow : Polynomial.C κ₉ * h0 ^ 6 =
        h0 ^ 4 * (Polynomial.C κ₉ * h0 ^ 2) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 4 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareMuZeroDeepMixedTenthLoad610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  have hsq :=
    alignedSquareMuZeroDeepMixed_tenthHeadSquare610 (w1.eval x)
      (a1.eval x) (v1.eval x)
  have : (92160 : K) *
        ((243 : K) * a1.eval x + v1.eval x * w1.eval x) ^ 2 = 0 := by
    linear_combination hloadx + hsq
  have h92160 : (92160 : K) ≠ 0 := by norm_num
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
    ((mul_eq_zero.mp this).resolve_left h92160)

/-! ## Head kills, `w₁ = 0` limb -/

set_option maxHeartbeats 16000000 in
/-- At the unique root the `w₁ = 0` tenth head is the named certificate. -/
theorem alignedSquareW1Zero_tenthHeadKill610
    (h0 w1n e1 e3 a0 a1 a2 b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ κ₉ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedTenthSquarePeeledRow610 h0 (h0 * w1n) e1 (h0 * e3)
          (h0 * w1n * (e3 - (3 : K[X]) * e1 * w1n))
          ((2048 : K[X]) * e1 ^ 3 * h0 ^ 3 * w1n ^ 4 -
            Polynomial.C μ * h0 ^ 6 * w1n ^ 7)
          a0 a1 a2 b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    -((55296 : K) * e1.eval x *
          ((10935 : K) * a2.eval x ^ 2 -
            (540 : K) * a2.eval x * e1.eval x ^ 2 +
              (7 : K) * e1.eval x ^ 4)) =
      0 := by
  have hfactor :=
    alignedSquareW1Zero_tenthFactor610 h0 w1n e1 e3 a0 a1 a2 b0 κ μ
      κ₃ ν κ₅ ν₂ κ₇ μ₃
  rw [hfactor] at hrow
  have hload :
      alignedSquareW1ZeroTenthLoad610 h0 w1n e1 e3 a0 a1 a2 b0 κ μ κ₃
          ν κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 5 := by
    have hpow : Polynomial.C κ₉ * h0 ^ 6 =
        h0 * (Polynomial.C κ₉ * h0 ^ 5) := by ring
    exact mul_left_cancel₀ hh0 (hrow.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroTenthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  have : -((387072 : K) * e1.eval x ^ 5) +
        (29859840 : K) * e1.eval x ^ 3 * a2.eval x -
          (604661760 : K) * e1.eval x * a2.eval x ^ 2 =
      0 := hloadx
  linear_combination this

/-- Eighth quadratic plus tenth remainder force `e₁(a) = p₂(a) = 0`. -/
theorem alignedSquareW1Zero_e1_a2_zero610
    (e1 a2 : K)
    (hQ8 :
      e1 ^ 4 - (81 : K) * e1 ^ 2 * a2 + (2187 : K) * a2 ^ 2 = 0)
    (hT :
      -((55296 : K) * e1 *
            ((10935 : K) * a2 ^ 2 - (540 : K) * a2 * e1 ^ 2 +
              (7 : K) * e1 ^ 4)) =
        0) :
    e1 = 0 ∧ a2 = 0 := by
  have hrem := alignedSquareW1Zero_tenthHeadRemQ8610 e1 a2
  have hT' := hT
  rw [hrem] at hT'
  have : (55296 : K) * e1 ^ 3 * ((135 : K) * a2 - (2 : K) * e1 ^ 2) =
      0 := by
    linear_combination hT' + (276480 : K) * e1 * hQ8
  have h55296 : (55296 : K) ≠ 0 := by norm_num
  have hprod :
      (55296 : K) *
          (e1 ^ 3 * ((135 : K) * a2 - (2 : K) * e1 ^ 2)) = 0 := by
    linear_combination this
  have hsplit :
      e1 ^ 3 = 0 ∨ (135 : K) * a2 - (2 : K) * e1 ^ 2 = 0 :=
    mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left h55296)
  cases' hsplit with he1 hray
  · have he1' : e1 = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp he1
    subst he1'
    have : (2187 : K) * a2 ^ 2 = 0 := by linear_combination hQ8
    have h2187 : (2187 : K) ≠ 0 := by norm_num
    exact ⟨rfl, (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp this).resolve_left h2187)⟩
  · have hray' : (135 : K) * a2 = (2 : K) * e1 ^ 2 := by
      linear_combination hray
    have h25 := alignedSquareW1Zero_Q8_on_tenthRay610 e1 a2 hray'
    have : (7 : K) * e1 ^ 4 = 0 := by
      rw [hQ8, mul_zero] at h25
      exact h25.symm
    have h7 : (7 : K) ≠ 0 := by norm_num
    have he1 : e1 = 0 :=
      (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp
        ((mul_eq_zero.mp this).resolve_left h7)
    subst he1
    have : (2187 : K) * a2 ^ 2 = 0 := by linear_combination hQ8
    have h2187 : (2187 : K) ≠ 0 := by norm_num
    exact ⟨rfl, (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp this).resolve_left h2187)⟩

set_option maxHeartbeats 16000000 in
/-- After `e₁ = h₀ e₁b` and `p₂ = h₀ a₂b`, the ninth head is `e₃(a)³`. -/
theorem alignedSquareW1ZeroE1A2_ninthHeadKill610
    (h0 w1n e1b e3 a0 a1 a2b b1 : K[X])
    (κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 (h0 * w1n) (h0 * e1b)
          (h0 * e3)
          (h0 * w1n * (e3 - (3 : K[X]) * (h0 * e1b) * w1n))
          a0 a1 (h0 * a2b) b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) : e3.eval x = 0 := by
  have hw1 :=
    alignedSquareW1Zero_ninthFactor610 h0 w1n (h0 * e1b) e3 a0 a1
      (h0 * a2b) b1 κ μ κ₃ ν κ₅ ν₂ κ₇
  have he1a2 :=
    alignedSquareW1ZeroE1A2_ninthFactor610 h0 w1n e1b e3 a0 a1 a2b b1
      κ μ κ₃ ν κ₅ ν₂ κ₇
  rw [hw1, he1a2] at hrow
  have hrow' :
      h0 ^ 3 *
          alignedSquareW1ZeroE1A2NinthLoad610 h0 w1n e1b e3 a0 a1 a2b
            b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6 := by
    calc
      h0 ^ 3 *
            alignedSquareW1ZeroE1A2NinthLoad610 h0 w1n e1b e3 a0 a1
              a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
          h0 ^ 2 *
            (h0 *
              alignedSquareW1ZeroE1A2NinthLoad610 h0 w1n e1b e3 a0 a1
                a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇) := by
        ring
      _ = Polynomial.C μ₃ * h0 ^ 6 := hrow
  have hload :
      alignedSquareW1ZeroE1A2NinthLoad610 h0 w1n e1b e3 a0 a1 a2b b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 3 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 3 * (Polynomial.C μ₃ * h0 ^ 3) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 3 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroE1A2NinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

set_option maxHeartbeats 16000000 in
/-- Mixed ninth head after `e₃ = h₀ e₃b`. -/
theorem alignedSquareW1ZeroMixed_ninthHeadKill610
    (h0 w1n e1b e3b a0 a1 a2b b1 : K[X])
    (κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 (h0 * w1n) (h0 * e1b)
          (h0 * (h0 * e3b))
          (h0 * w1n *
            (h0 * e3b - (3 : K[X]) * (h0 * e1b) * w1n))
          a0 a1 (h0 * a2b) b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    a2b.eval x *
        ((6 : K) * a1.eval x - a2b.eval x * w1n.eval x) =
      0 := by
  have hw1 :=
    alignedSquareW1Zero_ninthFactor610 h0 w1n (h0 * e1b) (h0 * e3b)
      a0 a1 (h0 * a2b) b1 κ μ κ₃ ν κ₅ ν₂ κ₇
  have he1a2 :=
    alignedSquareW1ZeroE1A2_ninthFactor610 h0 w1n e1b (h0 * e3b) a0
      a1 a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇
  have hmix :=
    alignedSquareW1ZeroMixed_ninthFactor610 h0 w1n e1b e3b a0 a1 a2b
      b1 κ μ κ₃ ν κ₅ ν₂ κ₇
  rw [hw1, he1a2, hmix] at hrow
  have hrow' :
      h0 ^ 4 *
          alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1
            a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6 := by
    calc
      h0 ^ 4 *
            alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1
              a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
          h0 ^ 2 *
            (h0 *
              (h0 *
                alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0
                  a1 a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇)) := by
        ring
      _ = Polynomial.C μ₃ * h0 ^ 6 := hrow
  have hload :
      alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1 a2b b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 2 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 4 * (Polynomial.C μ₃ * h0 ^ 2) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 4 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroMixedNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  have hhead :=
    alignedSquareW1ZeroMixed_ninthHead610 (w1n.eval x) (a1.eval x)
      (a2b.eval x)
  have : (302330880 : K) * a2b.eval x *
        ((6 : K) * a1.eval x - a2b.eval x * w1n.eval x) = 0 := by
    linear_combination hloadx + hhead
  have hconst : (302330880 : K) ≠ 0 := by norm_num
  have hprod :
      (302330880 : K) *
          (a2b.eval x *
            ((6 : K) * a1.eval x - a2b.eval x * w1n.eval x)) = 0 := by
    linear_combination this
  exact (mul_eq_zero.mp hprod).resolve_left hconst

set_option maxHeartbeats 16000000 in
/-- Mixed tenth head after `e₃ = h₀ e₃b`. -/
theorem alignedSquareW1ZeroMixed_tenthHeadKill610
    (h0 w1n e1b e3b a0 a1 a2b b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ κ₉ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedTenthSquarePeeledRow610 h0 (h0 * w1n) (h0 * e1b)
          (h0 * (h0 * e3b))
          (h0 * w1n *
            (h0 * e3b - (3 : K[X]) * (h0 * e1b) * w1n))
          ((2048 : K[X]) * (h0 * e1b) ^ 3 * h0 ^ 3 * w1n ^ 4 -
            Polynomial.C μ * h0 ^ 6 * w1n ^ 7)
          a0 a1 (h0 * a2b) b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    (45 : K) * a1.eval x ^ 2 -
        (30 : K) * a1.eval x * a2b.eval x * w1n.eval x -
          (5 : K) * a2b.eval x ^ 2 * e1b.eval x +
            (2 : K) * a2b.eval x ^ 2 * κ +
              (5 : K) * a2b.eval x ^ 2 * w1n.eval x ^ 2 =
      0 := by
  have hw1 :=
    alignedSquareW1Zero_tenthFactor610 h0 w1n (h0 * e1b) (h0 * e3b)
      a0 a1 (h0 * a2b) b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃
  have hmix :=
    alignedSquareW1ZeroMixed_tenthFactor610 h0 w1n e1b e3b a0 a1 a2b
      b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃
  rw [hw1, hmix] at hrow
  have hrow' :
      h0 ^ 4 *
          alignedSquareW1ZeroMixedTenthLoad610 h0 w1n e1b e3b a0 a1
            a2b b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 6 := by
    calc
      h0 ^ 4 *
            alignedSquareW1ZeroMixedTenthLoad610 h0 w1n e1b e3b a0 a1
              a2b b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
          h0 *
            (h0 ^ 3 *
              alignedSquareW1ZeroMixedTenthLoad610 h0 w1n e1b e3b a0
                a1 a2b b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃) := by
        ring
      _ = Polynomial.C κ₉ * h0 ^ 6 := hrow
  have hload :
      alignedSquareW1ZeroMixedTenthLoad610 h0 w1n e1b e3b a0 a1 a2b b0
          κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
        Polynomial.C κ₉ * h0 ^ 2 := by
    have hpow : Polynomial.C κ₉ * h0 ^ 6 =
        h0 ^ 4 * (Polynomial.C κ₉ * h0 ^ 2) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 4 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroMixedTenthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  have hhead :=
    alignedSquareW1ZeroMixed_tenthHead610 (w1n.eval x) (e1b.eval x)
      (a1.eval x) (a2b.eval x) κ
  have : (120932352 : K) *
        ((45 : K) * a1.eval x ^ 2 -
          (30 : K) * a1.eval x * a2b.eval x * w1n.eval x -
            (5 : K) * a2b.eval x ^ 2 * e1b.eval x +
              (2 : K) * a2b.eval x ^ 2 * κ +
                (5 : K) * a2b.eval x ^ 2 * w1n.eval x ^ 2) =
      0 := by
    linear_combination hloadx + hhead
  have hconst : (120932352 : K) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp this).resolve_left hconst

/-- On `a₂b(a) = 0` the mixed tenth forces `p₁(a) = 0`. -/
theorem alignedSquareW1ZeroMixed_a2bZero_p1Zero610
    (w1n e1b a1 : K) (κ : K)
    (hT :
      (45 : K) * a1 ^ 2 - (30 : K) * a1 * (0 : K) * w1n -
          (5 : K) * (0 : K) ^ 2 * e1b +
            (2 : K) * (0 : K) ^ 2 * κ +
              (5 : K) * (0 : K) ^ 2 * w1n ^ 2 =
        0) :
    a1 = 0 := by
  have : (45 : K) * a1 ^ 2 = 0 := by
    linear_combination hT
  have h45 : (45 : K) ≠ 0 := by norm_num
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
    ((mul_eq_zero.mp this).resolve_left h45)

set_option maxHeartbeats 16000000 in
/-- On `a₂b = h₀ a₂c` and `p₁(a) = 0` the ninth head is `-1632586752 q₁`. -/
theorem alignedSquareW1ZeroA2c_ninthHeadKill610
    (h0 w1n e1b e3b a0 a1 a2c b1 : K[X])
    (κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 (h0 * w1n) (h0 * e1b)
          (h0 * (h0 * e3b))
          (h0 * w1n *
            (h0 * e3b - (3 : K[X]) * (h0 * e1b) * w1n))
          a0 a1 (h0 * (h0 * a2c)) b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) (hp1 : a1.eval x = 0) :
    b1.eval x = 0 := by
  have hw1 :=
    alignedSquareW1Zero_ninthFactor610 h0 w1n (h0 * e1b) (h0 * e3b)
      a0 a1 (h0 * (h0 * a2c)) b1 κ μ κ₃ ν κ₅ ν₂ κ₇
  have he1a2 :=
    alignedSquareW1ZeroE1A2_ninthFactor610 h0 w1n e1b (h0 * e3b) a0
      a1 (h0 * a2c) b1 κ μ κ₃ ν κ₅ ν₂ κ₇
  have hmix :=
    alignedSquareW1ZeroMixed_ninthFactor610 h0 w1n e1b e3b a0 a1
      (h0 * a2c) b1 κ μ κ₃ ν κ₅ ν₂ κ₇
  have ha2c :=
    alignedSquareW1ZeroA2c_ninthFactor610 h0 w1n e1b e3b a0 a1 a2c b1
      κ μ κ₃ ν κ₅ ν₂ κ₇
  rw [hw1, he1a2, hmix, ha2c] at hrow
  have hrow' :
      h0 ^ 5 *
          alignedSquareW1ZeroA2cNinthLoad610 h0 w1n e1b e3b a0 a1 a2c
            b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6 := by
    calc
      h0 ^ 5 *
            alignedSquareW1ZeroA2cNinthLoad610 h0 w1n e1b e3b a0 a1
              a2c b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
          h0 ^ 2 *
            (h0 *
              (h0 *
                (h0 *
                  alignedSquareW1ZeroA2cNinthLoad610 h0 w1n e1b e3b a0
                    a1 a2c b1 κ μ κ₃ ν κ₅ ν₂ κ₇))) := by
        ring
      _ = Polynomial.C μ₃ * h0 ^ 6 := hrow
  have hload :
      alignedSquareW1ZeroA2cNinthLoad610 h0 w1n e1b e3b a0 a1 a2c b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 5 * (Polynomial.C μ₃ * h0) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 5 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroA2cNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx, hp1] at hloadx
  norm_num at hloadx
  exact hloadx

/-- 410-style collision: `p₁(a) = q₁(a) = 0` contradicts `j ≠ 0`. -/
theorem alignedSquareMixed_kellerCollision610
    (p0 p1 q0 q1 : K[X]) (j a : K)
    (hj : j ≠ 0)
    (hrow :
      p0.derivative * q1 - p1 * q0.derivative = Polynomial.C j)
    (hp1 : p1.eval a = 0) (hq1 : q1.eval a = 0) : False := by
  have hx := congrArg (fun w : K[X] => w.eval a) hrow
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C] at hx
  rw [hp1, hq1] at hx
  simp only [mul_zero, zero_mul, sub_zero] at hx
  exact hj hx.symm

/-- Complementary mixed residual on `a₂b(a) ≠ 0`:
`6 p₁ = a₂b w₁n` and `20 e₁b = 8 κ + 5 w₁n²`. -/
theorem alignedSquareW1ZeroMixed_complementResidual610
    (w1n e1b a1 a2b : K) (κ : K)
    (ha2b : a2b ≠ 0)
    (hN : a2b * ((6 : K) * a1 - a2b * w1n) = 0)
    (hT :
      (45 : K) * a1 ^ 2 - (30 : K) * a1 * a2b * w1n -
          (5 : K) * a2b ^ 2 * e1b + (2 : K) * a2b ^ 2 * κ +
            (5 : K) * a2b ^ 2 * w1n ^ 2 =
        0) :
    (6 : K) * a1 = a2b * w1n ∧
      (20 : K) * e1b = (8 : K) * κ + (5 : K) * w1n ^ 2 := by
  have hp1 : (6 : K) * a1 - a2b * w1n = 0 :=
    (mul_eq_zero.mp hN).resolve_left ha2b
  have hp1' : (6 : K) * a1 = a2b * w1n := by linear_combination hp1
  have hexp :
      (180 : K) * a1 ^ 2 - (120 : K) * a1 * a2b * w1n -
          (20 : K) * a2b ^ 2 * e1b + (8 : K) * a2b ^ 2 * κ +
            (20 : K) * a2b ^ 2 * w1n ^ 2 =
        0 := by
    linear_combination 4 * hT
  have ha1sq : (36 : K) * a1 ^ 2 = a2b ^ 2 * w1n ^ 2 := by
    have := congrArg (fun t : K => t * t) hp1'
    linear_combination this
  have ha1w : (6 : K) * a1 * a2b * w1n = a2b ^ 2 * w1n ^ 2 := by
    linear_combination a2b * w1n * hp1'
  have : a2b ^ 2 * ((5 : K) * w1n ^ 2 - (20 : K) * e1b + (8 : K) * κ) =
      0 := by
    linear_combination hexp - 5 * ha1sq + 20 * ha1w
  have ha2b2 : a2b ^ 2 ≠ 0 := pow_ne_zero 2 ha2b
  have hlin :
      (5 : K) * w1n ^ 2 - (20 : K) * e1b + (8 : K) * κ = 0 :=
    (mul_eq_zero.mp this).resolve_left ha2b2
  exact ⟨hp1', by linear_combination -hlin⟩

/-! ## Source rewrites: product `p₂` and the tenth `s₂` witnesses -/

/-- On the product identity, `p₂` is the named `81⁻¹` expression. -/
theorem alignedSquareMuZero_coeffTwo_of_product610
    (h0 w1 e1n e3 v a2 : K[X])
    (hprod :
      w1 * (e3 - (3 : K[X]) * e1n * w1) =
        h0 * v + (81 : K[X]) * a2) :
    a2 =
      (w1 * (e3 - (3 : K[X]) * e1n * w1) - h0 * v) *
        Polynomial.C (81 : K)⁻¹ := by
  have h81 : (81 : K) ≠ 0 := by norm_num
  have hC : (81 : K[X]) = Polynomial.C (81 : K) :=
    (Polynomial.C_eq_natCast 81).symm
  have hdiff :
      w1 * (e3 - (3 : K[X]) * e1n * w1) - h0 * v =
        (81 : K[X]) * a2 := by
    linear_combination hprod
  calc
    a2 = a2 * 1 := by ring
    _ = a2 *
          (Polynomial.C (81 : K) * Polynomial.C (81 : K)⁻¹) := by
      rw [← map_mul, mul_inv_cancel₀ h81, map_one]
    _ = (Polynomial.C (81 : K) * a2) * Polynomial.C (81 : K)⁻¹ := by
      ring
    _ = ((81 : K[X]) * a2) * Polynomial.C (81 : K)⁻¹ := by
      rw [hC]
    _ = (w1 * (e3 - (3 : K[X]) * e1n * w1) - h0 * v) *
          Polynomial.C (81 : K)⁻¹ := by
      rw [hdiff]

/-- On `μ = 0` and `e₁ = h₀ e₁n`, the tenth witness is
`2048 h₀² e₁n³ w₁⁴`. -/
theorem alignedSquareMuZero_s2_eq610
    (h0 w1 e1n s2 : K[X]) (μ : K)
    (hh0 : h0 ≠ 0) (hμ : μ = 0)
    (hs2 :
      (2048 : K[X]) * (h0 * e1n) ^ 3 * w1 ^ 4 -
          Polynomial.C μ * w1 ^ 7 = h0 * s2) :
    s2 = (2048 : K[X]) * h0 ^ 2 * e1n ^ 3 * w1 ^ 4 := by
  subst hμ
  simp only [Polynomial.C_0, zero_mul, sub_zero] at hs2
  apply mul_left_cancel₀ hh0
  calc
    h0 * s2 = (2048 : K[X]) * (h0 * e1n) ^ 3 * w1 ^ 4 := hs2.symm
    _ = h0 * ((2048 : K[X]) * h0 ^ 2 * e1n ^ 3 * w1 ^ 4) := by
      ring

/-- On `w₁ = h₀ w₁n`, the tenth witness is the named cubic/sextic
expression. -/
theorem alignedSquareW1Zero_s2_eq610
    (h0 w1n e1 s2 : K[X]) (μ : K)
    (hh0 : h0 ≠ 0)
    (hs2 :
      (2048 : K[X]) * e1 ^ 3 * (h0 * w1n) ^ 4 -
          Polynomial.C μ * (h0 * w1n) ^ 7 = h0 * s2) :
    s2 =
      (2048 : K[X]) * e1 ^ 3 * h0 ^ 3 * w1n ^ 4 -
        Polynomial.C μ * h0 ^ 6 * w1n ^ 7 := by
  apply mul_left_cancel₀ hh0
  calc
    h0 * s2 =
        (2048 : K[X]) * e1 ^ 3 * (h0 * w1n) ^ 4 -
          Polynomial.C μ * (h0 * w1n) ^ 7 := hs2.symm
    _ = h0 *
          ((2048 : K[X]) * e1 ^ 3 * h0 ^ 3 * w1n ^ 4 -
            Polynomial.C μ * h0 ^ 6 * w1n ^ 7) := by
      ring

/-! ## Source-facing mixed-pair reduction -/

set_option maxHeartbeats 32000000 in
/-- Mixed `(p₁, q₁)` reduction of the aligned-square chamber.

On `w₁(a) = 0` the eighth quadratic and tenth remainder force
`e₁(a) = p₂(a) = 0`, the next ninth head forces `e₃(a) = 0`, and the
child `a₂b(a) = 0` collides with the Keller row (`p₁(a) = q₁(a) = 0`
against `j ≠ 0`).  The complementary child is the residual
`6 p₁(a) = a₂b(a) w₁n(a)` and `20 e₁b(a) = 8 κ + 5 w₁n(a)²` with
`a₂b(a) ≠ 0`.

On `μ = 0` the cube residual is an `h₀`-divisor; the mixed ninth/tenth
heads combine to `2048 v(a) y(a)² = 3 ν₂ w₁(a)³`.  The branch
`v(a) = 0` forces `y(a) = 0` and `ν₂ = 0`, after which the deepened
tenth head is `(243 p₁(a) + v₁(a) w₁(a))²`.  Neither `μ = 0` branch
kills both Keller cross-products.  The square chamber is not claimed
empty. -/
theorem normalized610ScaleTwo_alignedSquare_mixedPairReduction
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a j : K) (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ κ₉ : K)
      (w1 f2 e1 e2 u2 e3 s2 : K[X]),
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
        (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
          h0 * s2 ∧
        alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 ∧
        alignedEighthSquarePeeledRow610 h0 w1 e1 e2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 2) κ μ κ₃ ν κ₅ ν₂ =
          Polynomial.C κ₇ * h0 ^ 6 ∧
        alignedTenthSquarePeeledRow610 h0 w1 e1 e2 u2 s2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 0) κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
          Polynomial.C κ₉ * h0 ^ 6 ∧
        (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0)) ∧
        (w1.eval a = 0 →
          ∃ w1n e1b a2b e3b : K[X],
            w1 = h0 * w1n ∧
              e1 = h0 * e1b ∧
                p.coeff 2 = h0 * a2b ∧
                  e3 = h0 * e3b ∧
                    a2b.eval a ≠ 0 ∧
                      (6 : K) * (p.coeff 1).eval a =
                          a2b.eval a * w1n.eval a ∧
                        (20 : K) * e1b.eval a =
                          (8 : K) * κ + (5 : K) * w1n.eval a ^ 2) ∧
        (w1.eval a ≠ 0 →
          μ = 0 ∧ ν = 0 ∧
            ∃ e1n v y rho : K[X],
              e1 = h0 * e1n ∧
                u2 = h0 * v + (81 : K[X]) * p.coeff 2 ∧
                  y = e3 - (6 : K[X]) * e1n * w1 ∧
                    y ^ 3 + (9 : K[X]) * v ^ 2 * w1 = h0 * rho ∧
                      (y.eval a) ^ 3 +
                          (9 : K) * v.eval a ^ 2 * w1.eval a = 0 ∧
                        (2048 : K) * v.eval a * y.eval a ^ 2 =
                          (3 : K) * ν₂ * w1.eval a ^ 3 ∧
                        (v.eval a = 0 →
                          y.eval a = 0 ∧ ν₂ = 0 ∧
                            ∃ y1 v1 : K[X],
                              y = h0 * y1 ∧ v = h0 * v1 ∧
                                (243 : K) * (p.coeff 1).eval a +
                                    v1.eval a * w1.eval a = 0)) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hdeg1 := alignedSquare610_h0_natDegree_eq_one hsource hh0 hHsq
  obtain ⟨a, hroot⟩ := alignedSquare610_exists_root h0 hdeg1
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleTwo_alignedFinalKellerRow hsource haligned
  have hroweval : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
    have h := congrArg (Polynomial.eval a) hrow
    simpa only [p, q, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] using h
  have hpacket :=
    normalized610ScaleTwo_alignedEleventhFace_squareChamber_packet
      hsource hh0 hHsq haligned
  dsimp only at hpacket
  obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, _κ₈, μ₃, κ₉, _κ₁₀, _μ₄, w1, f2, e1,
    e2, u2, e3, s2, _s4, _s5, _hμ₃, _hμ₄, _hM, hp5w1, hp4f2, he1, he2,
    hu2, hR8, he3, _h27, hR9, hs2, hR10, _hs4, _hR11x, _hs5, _hmu8,
    hQ9, _hD, _hE, _hF, _hG, _hI, _hJ, _hL, _hO, _hΛ, _hΛ2⟩ := hpacket
  have hev1 := congrArg (fun t : K[X] => t.eval a) hu2
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_ofNat] at hev1
  rw [hroot, zero_mul] at hev1
  have h1 : w1.eval a *
      (e2.eval a - 3 * e1.eval a * w1.eval a) = 0 := by
    linear_combination hev1
  have hevQ9 := congrArg (fun t : K[X] => t.eval a) hQ9
  simp only [alignedEighthSquareCombinedRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevQ9
  rw [hroot] at hevQ9
  have h2 : 1280 * e1.eval a *
      (3 * e1.eval a * w1.eval a - e2.eval a) *
      (6 * e1.eval a * w1.eval a - e2.eval a) +
      189 * μ * w1.eval a ^ 5 = 0 := by
    linear_combination -hevQ9
  have hevR9 := congrArg (fun t : K[X] => t.eval a) hR9
  simp only [alignedNinthSquarePeeledRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevR9
  rw [hroot] at hevR9
  have h9 : 276480 * e1.eval a ^ 3 * w1.eval a ^ 3 -
      5120 * e2.eval a ^ 3 - 189 * μ * w1.eval a ^ 6 = 0 := by
    linear_combination hevR9
  obtain ⟨_he2a, hbranch⟩ := alignedNinthSquareResolve_610 h1 h2 h9
  refine ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, κ₉, w1, f2, e1, e2, u2,
    e3, s2, hdeg1, hroot, hj, hrow, hroweval, hp5w1, hp4f2, he1, he2,
    he3, hu2, hs2, hR9, hR8, hR10, hbranch, ?limbA, ?limbB⟩
  · intro hw1a
    obtain ⟨w1n, hw1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w1 a hdeg1 hroot hw1a
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
    have hR8' := hR8
    rw [hw1, he3] at hR8'
    have hQ8 :=
      alignedSquareW1Zero_eighthHeadKill610 h0 w1n e1 e3 (p.coeff 0)
        (p.coeff 1) (p.coeff 2) (q.coeff 2) κ μ κ₃ ν κ₅ ν₂ κ₇ hh0 hR8'
        a hroot
    have hs2arg :
        (2048 : K[X]) * e1 ^ 3 * (h0 * w1n) ^ 4 -
            Polynomial.C μ * (h0 * w1n) ^ 7 = h0 * s2 := by
      simpa [hw1] using hs2
    have hs2eq :=
      alignedSquareW1Zero_s2_eq610 h0 w1n e1 s2 μ hh0 hs2arg
    have hR10' := hR10
    rw [hw1, he3, hu2', hs2eq] at hR10'
    have hT10 :=
      alignedSquareW1Zero_tenthHeadKill610 h0 w1n e1 e3 (p.coeff 0)
        (p.coeff 1) (p.coeff 2) (q.coeff 0) κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ κ₉
        hh0 hR10' a hroot
    obtain ⟨he1a, ha2a⟩ :=
      alignedSquareW1Zero_e1_a2_zero610 (e1.eval a) ((p.coeff 2).eval a)
        hQ8 hT10
    obtain ⟨e1b, he1b⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 e1 a hdeg1 hroot he1a
    obtain ⟨a2b, ha2b⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 2) a hdeg1
        hroot ha2a
    have hR9e := hR9
    rw [hw1, he3, hu2', he1b, ha2b] at hR9e
    have he3a :=
      alignedSquareW1ZeroE1A2_ninthHeadKill610 h0 w1n e1b e3
        (p.coeff 0) (p.coeff 1) a2b (q.coeff 1) κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇
        hh0 hR9e a hroot
    obtain ⟨e3b, he3b⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 e3 a hdeg1 hroot he3a
    have hR9m := hR9e
    rw [he3b] at hR9m
    have hNm :=
      alignedSquareW1ZeroMixed_ninthHeadKill610 h0 w1n e1b e3b
        (p.coeff 0) (p.coeff 1) a2b (q.coeff 1) κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇
        hh0 hR9m a hroot
    have hR10m := hR10'
    rw [he1b, he3b, ha2b] at hR10m
    have hTm :=
      alignedSquareW1ZeroMixed_tenthHeadKill610 h0 w1n e1b e3b
        (p.coeff 0) (p.coeff 1) a2b (q.coeff 0) κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃
        κ₉ hh0 hR10m a hroot
    by_cases ha2b0 : a2b.eval a = 0
    · have hT0 := hTm
      rw [ha2b0] at hT0
      have hp1 :=
        alignedSquareW1ZeroMixed_a2bZero_p1Zero610 (w1n.eval a)
          (e1b.eval a) ((p.coeff 1).eval a) κ hT0
      obtain ⟨a2c, ha2c⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 a2b a hdeg1 hroot
          ha2b0
      have hR9c := hR9m
      rw [ha2c] at hR9c
      have hq1 :=
        alignedSquareW1ZeroA2c_ninthHeadKill610 h0 w1n e1b e3b
          (p.coeff 0) (p.coeff 1) a2c (q.coeff 1) κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇
          hh0 hR9c a hroot hp1
      exact (alignedSquareMixed_kellerCollision610 (p.coeff 0)
        (p.coeff 1) (q.coeff 0) (q.coeff 1) j a hj hrow hp1 hq1).elim
    · obtain ⟨hp1eq, he1beq⟩ :=
        alignedSquareW1ZeroMixed_complementResidual610 (w1n.eval a)
          (e1b.eval a) ((p.coeff 1).eval a) (a2b.eval a) κ ha2b0 hNm hTm
      exact ⟨w1n, e1b, a2b, e3b, hw1, he1b, ha2b, he3b, ha2b0, hp1eq,
        he1beq⟩
  · intro hw1x
    have hμe1 : μ = 0 ∧ e1.eval a = 0 := hbranch.resolve_left hw1x
    obtain ⟨hμ, he1a⟩ := hμe1
    obtain ⟨e1n, he1n⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 e1 a hdeg1 hroot he1a
    have hR9μ :
        alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3) u2
            (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ 0 κ₃ ν
            κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 := by
      simpa [hμ, he1n, he3] using hR9
    have hu2a :=
      alignedSquareMuZero_ninthHeadKill610 h0 w1 e1n e3 u2
        (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ₃ κ₃ ν κ₅
        ν₂ κ₇ hh0 hR9μ a hroot hw1x
    have hua :
        (u2 - (81 : K[X]) * p.coeff 2).eval a = 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      linear_combination hu2a
    obtain ⟨v, hv⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        (u2 - (81 : K[X]) * p.coeff 2) a hdeg1 hroot hua
    have hu : u2 = h0 * v + (81 : K[X]) * p.coeff 2 := by
      linear_combination hv
    have hload :
        alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
            (h0 * v + (81 : K[X]) * p.coeff 2) (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 5 := by
      have hfactor :=
        alignedSquareMuZero_ninthFactor610 h0 w1 e1n e3 u2
          (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν κ₅
          ν₂ κ₇
      apply mul_left_cancel₀ hh0
      calc
        h0 * alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
              (h0 * v + (81 : K[X]) * p.coeff 2) (p.coeff 0)
              (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν κ₅ ν₂ κ₇ =
            h0 * alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3 u2
              (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν
              κ₅ ν₂ κ₇ := by rw [hu]
        _ = alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n)
              (h0 * e3) u2 (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (q.coeff 1) κ 0 κ₃ ν κ₅ ν₂ κ₇ := hfactor.symm
        _ = Polynomial.C μ₃ * h0 ^ 6 := hR9μ
        _ = h0 * (Polynomial.C μ₃ * h0 ^ 5) := by ring
    have hν : ν = 0 :=
      alignedSquareMuZero_uFactor_nuKill610 h0 w1 e1n e3 v
        (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ₃ κ₃ ν κ₅
        ν₂ κ₇ hh0 hload a hroot hw1x
    have hprod :=
      alignedSquareMuZero_productReduce610 h0 w1 e1n e3 v (p.coeff 2)
        u2 hh0 (by simpa [he1n, he3] using hu2) hu
    have hR9ν :
        alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3)
            (h0 * v + (81 : K[X]) * p.coeff 2) (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (q.coeff 1) κ 0 κ₃ 0 κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 := by
      simpa [hμ, hν, he1n, he3, hu] using hR9
    have hcube :=
      alignedSquareMuZeroNuZero_cubeResidual610 h0 w1 e1n e3 v
        (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ₃ κ₃ κ₅ ν₂
        κ₇ hh0 hR9ν hprod a hroot
    let y : K[X] := e3 - (6 : K[X]) * e1n * w1
    have hy : e3 = y + (6 : K[X]) * e1n * w1 := by
      simp only [y]; ring
    have hyeval :
        y.eval a = e3.eval a - (6 : K) * e1n.eval a * w1.eval a := by
      simp only [y, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
    have hcube' :
        y.eval a ^ 3 + (9 : K) * v.eval a ^ 2 * w1.eval a = 0 := by
      rwa [hyeval]
    have hcube_poly :
        (y ^ 3 + (9 : K[X]) * v ^ 2 * w1).eval a = 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat]
      exact hcube'
    obtain ⟨rho, hrho⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        (y ^ 3 + (9 : K[X]) * v ^ 2 * w1) a hdeg1 hroot hcube_poly
    have ha2 :=
      alignedSquareMuZero_coeffTwo_of_product610 h0 w1 e1n e3 v
        (p.coeff 2) hprod
    have hdelta :
        e3 - (3 : K[X]) * e1n * w1 =
          y + (3 : K[X]) * e1n * w1 := by
      simp only [y]; ring
    have ha2y := ha2
    rw [hdelta] at ha2y
    have hs2arg :
        (2048 : K[X]) * (h0 * e1n) ^ 3 * w1 ^ 4 -
            Polynomial.C μ * w1 ^ 7 = h0 * s2 := by
      simpa [he1n] using hs2
    have hs2eq :=
      alignedSquareMuZero_s2_eq610 h0 w1 e1n s2 μ hh0 hμ hs2arg
    have hR9m := hR9ν
    rw [hy, ha2y] at hR9m
    have hNm :=
      alignedSquareMuZeroMixed_ninthHeadKill610 h0 w1 e1n y v
        (p.coeff 0) (p.coeff 1) (q.coeff 1) rho κ μ₃ κ₃ κ₅ ν₂ κ₇ hh0
        hrho hR9m a hroot
    have hR10m := hR10
    rw [he1n, he3, hμ, hν, hu, hy, ha2y, hs2eq] at hR10m
    have hTm :=
      alignedSquareMuZeroMixed_tenthHeadKill610 h0 w1 e1n y v
        (p.coeff 0) (p.coeff 1) (q.coeff 0) rho κ κ₉ κ₃ κ₅ ν₂ κ₇ μ₃
        hh0 hrho hR10m a hroot
    have hcombo :=
      alignedSquareMuZeroMixed_comboResidual610 (w1.eval a)
        (e1n.eval a) (y.eval a) (v.eval a) ((p.coeff 1).eval a)
        (rho.eval a) κ ν₂ hNm hTm
    refine ⟨hμ, hν, e1n, v, y, rho, he1n, hu, rfl, hrho, hcube',
      hcombo, ?_⟩
    intro hv0
    have hy0 :=
      alignedSquareMuZeroMixed_vZero_yZero610 (y.eval a) (v.eval a)
        (w1.eval a) hcube' hv0 hw1x
    have hν₂ :=
      alignedSquareMuZeroMixed_vZero_nuTwoZero610 h0 w1 e1n y v
        (p.coeff 0) (p.coeff 1) (q.coeff 1) rho κ μ₃ κ₃ κ₅ ν₂ κ₇ hh0
        hdeg1 hrho hR9m a hroot hv0 hy0 hw1x
    obtain ⟨y1, hy1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 y a hdeg1 hroot hy0
    obtain ⟨v1, hv1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 v a hdeg1 hroot hv0
    have hR10d := hR10m
    rw [hy1, hv1, hν₂] at hR10d
    have hdeep :=
      alignedSquareMuZeroDeepMixed_tenthHeadKill610 h0 w1 e1n
        (p.coeff 0) (p.coeff 1) (q.coeff 0) y1 v1 κ κ₉ κ₃ κ₅ κ₇ μ₃
        hh0 hR10d a hroot
    exact ⟨hy0, hν₂, y1, v1, hy1, hv1, hdeep⟩

#print axioms alignedSquareMuZeroMixed_headCombo610
#print axioms alignedSquareMuZeroMixed_ninthPreFactor610
#print axioms alignedSquareMuZeroMixed_ninthCubeFactor610
#print axioms alignedSquareMuZeroMixed_tenthPreFactor610
#print axioms alignedSquareMuZeroMixed_tenthCubeFactor610
#print axioms alignedSquareMuZeroDeepMixed_ninthFactor610
#print axioms alignedSquareMuZeroDeepMixed_tenthFactor610
#print axioms alignedSquareW1Zero_tenthFactor610
#print axioms alignedSquareW1ZeroE1A2_ninthFactor610
#print axioms alignedSquareW1ZeroMixed_ninthFactor610
#print axioms alignedSquareW1ZeroMixed_tenthFactor610
#print axioms alignedSquareW1ZeroA2c_ninthFactor610
#print axioms alignedSquareMuZeroMixed_ninthHeadKill610
#print axioms alignedSquareMuZeroMixed_tenthHeadKill610
#print axioms alignedSquareMuZeroMixed_comboResidual610
#print axioms alignedSquareW1Zero_e1_a2_zero610
#print axioms alignedSquareW1ZeroE1A2_ninthHeadKill610
#print axioms alignedSquareW1ZeroMixed_ninthHeadKill610
#print axioms alignedSquareW1ZeroMixed_tenthHeadKill610
#print axioms alignedSquareW1ZeroA2c_ninthHeadKill610
#print axioms alignedSquareMixed_kellerCollision610
#print axioms alignedSquareW1ZeroMixed_complementResidual610
#print axioms alignedSquareMuZeroMixed_vZero_yZero610
#print axioms alignedSquareMuZeroMixed_vZero_nuTwoZero610
#print axioms alignedSquareMuZeroDeepMixed_tenthHeadKill610
#print axioms alignedSquareMuZero_coeffTwo_of_product610
#print axioms alignedSquareMuZero_s2_eq610
#print axioms alignedSquareW1Zero_s2_eq610
#print axioms normalized610ScaleTwo_alignedSquare_mixedPairReduction

end Max11DegreeRoutes

