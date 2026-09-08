import Grok610AlignedSquareMixedPairScratch

/-! # M1/M2 next orders on the aligned-square `(6,10)` mixed-pair limbs

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareMixedPairScratch` lands the two-limb packet
`normalized610ScaleTwo_alignedSquare_mixedPairReduction`.  On
`w₁(a)=0` the child `a₂b(a)=0` is already empty; the live complement
is `6 p₁(a)=a₂b(a) w₁n(a)` and `20 e₁b(a)=8 κ + 5 w₁n(a)²`.  On
`μ=0` the mixed ninth/tenth combo is `2048 v(a) y(a)² = 3 ν₂ w₁(a)³`
and does not force `v(a)=0`.

This file executes the two named missing objects.

* **M1.** Substitute `6 p₁ = a₂b w₁n` into
  `alignedSquareW1ZeroMixedNinthLoad610` and cancel the remaining
  `h₀`.  The `h₀¹` coefficient is linear in `q₁` with unit
  coefficient `-1632586752`, plus a genuine jet in
  `(e₁b,e₃b,κ,μ,κ₃,ν,w₁n,a₂b)`.  It is not a unit times `q₁` plus
  units, so it does not force `q₁(a)=0`.  The honest source upgrade
  of the evaluation identity is `6 p₁ - a₂b w₁n = h₀ τ`; the residual
  at `a` retains the extra monomial `302330880 a₂b(a) τ(a)`.  The
  next tenth order after both complement residuals is linear in
  `p₀` and does not force `w₁n(a)=0`.  Collision `p₁(a)=q₁(a)=0` is
  not reached; the `w₁=0` child is **not** `False`.
* **M2.** The valuation-`4` integer eighth head after the product
  identity is the already-constructed
  `alignedSquareMuZeroNuZeroEighthVLoad610` (CAS-checked equal to
  the session-`01a05a10` form, primitive
  `174960 p₀ w₁² - 116640 p₁ e₁n w₁ + 38880 p₁ e₃ + 46656 p₁ κ w₁
  - 944784 q₂ + 80 v² + ⋯`).  Combined with the mixed combo (no
  `ν₂` in the eighth head) and the degree-`1` row (derivatives, not
  values) it does not force `v(a)=0`.

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

/-! ## M1: mixed-ninth split and the complement `h₀¹` form -/

/-- `h₀`-free head of `alignedSquareW1ZeroMixedNinthLoad610`. -/
def alignedSquareW1ZeroMixedNinthHeadPoly610
    {K : Type*} [CommRing K] (w1n a1 a2b : K[X]) : K[X] :=
  -((302330880 : K[X]) * w1n * a2b ^ 2) +
    (1813985280 : K[X]) * a1 * a2b

/-- `h₀¹` coefficient of `alignedSquareW1ZeroMixedNinthLoad610`. -/
def alignedSquareW1ZeroMixedNinthC1Poly610
    {K : Type*} [CommRing K]
    (w1n e1b e3b a1 a2b b1 : K[X]) (κ μ κ₃ ν : K) : K[X] :=
  -(Polynomial.C κ * ((17915904 : K[X]) * e1b * w1n * a2b)) +
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
    (1632586752 : K[X]) * b1

set_option maxHeartbeats 16000000 in
/-- `h₀²` coefficient of `alignedSquareW1ZeroMixedNinthLoad610`. -/
def alignedSquareW1ZeroMixedNinthC2Poly610
    {K : Type*} [CommRing K]
    (w1n e1b e3b a0 : K[X]) (κ μ ν κ₅ ν₂ κ₇ : K) : K[X] :=
  Polynomial.C κ * ((552960 : K[X]) * e1b ^ 3 * w1n) -
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
    (67184640 : K[X]) * e3b * a0

/-- Exact `h₀¹` linear form after the polynomial substitution
`6 p₁ = a₂b w₁n`.  Unit coefficient `-1632586752` on `q₁`. -/
def alignedSquareW1ZeroComplementNinthC1Form610
    {K : Type*} [CommRing K]
    (w1n e1b e3b a2b b1 : K[X]) (κ μ κ₃ ν : K) : K[X] :=
  -(Polynomial.C κ * ((13436928 : K[X]) * e1b * w1n * a2b)) +
    Polynomial.C κ * ((2985984 : K[X]) * e3b * a2b) -
    Polynomial.C μ * ((1306368 : K[X]) * e1b * a2b) -
    Polynomial.C μ * ((326592 : K[X]) * w1n ^ 2 * a2b) -
    Polynomial.C κ₃ * ((559872 : K[X]) * w1n * a2b) -
    Polynomial.C ν * ((233280 : K[X]) * a2b) +
    (39191040 : K[X]) * e1b ^ 2 * w1n * a2b -
    (7464960 : K[X]) * e1b * e3b * a2b -
    (11197440 : K[X]) * e1b * w1n ^ 3 * a2b +
    (3732480 : K[X]) * e3b * w1n ^ 2 * a2b -
    (1632586752 : K[X]) * b1

/-- Complement ninth load after `6 p₁ = a₂b w₁n`. -/
def alignedSquareW1ZeroComplementNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1n e1b e3b a0 a2b b1 : K[X]) (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) : K[X] :=
  alignedSquareW1ZeroComplementNinthC1Form610 w1n e1b e3b a2b b1 κ μ
      κ₃ ν +
    h0 *
      alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b a0 κ μ ν κ₅
        ν₂ κ₇

variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial form of the mixed ninth head identity. -/
theorem alignedSquareW1ZeroMixed_ninthHead_poly610
    (w1n a1 a2b : K[X]) :
    alignedSquareW1ZeroMixedNinthHeadPoly610 w1n a1 a2b =
      (302330880 : K[X]) * a2b *
        ((6 : K[X]) * a1 - a2b * w1n) := by
  simp only [alignedSquareW1ZeroMixedNinthHeadPoly610]
  ring

set_option maxHeartbeats 16000000 in
/-- The mixed ninth load is head plus `h₀ C₁` plus `h₀² C₂`. -/
theorem alignedSquareW1ZeroMixed_ninthSplit610
    (h0 w1n e1b e3b a0 a1 a2b b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) :
    alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1 a2b b1
        κ μ κ₃ ν κ₅ ν₂ κ₇ =
      alignedSquareW1ZeroMixedNinthHeadPoly610 w1n a1 a2b +
        h0 *
          alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1 a2b
            b1 κ μ κ₃ ν +
          h0 ^ 2 *
            alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b a0 κ μ
              ν κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareW1ZeroMixedNinthLoad610,
    alignedSquareW1ZeroMixedNinthHeadPoly610,
    alignedSquareW1ZeroMixedNinthC1Poly610,
    alignedSquareW1ZeroMixedNinthC2Poly610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  try ring

/-- Clearing identity: `6 (C₁ - C₁Form) = (∂C₁/∂a₁) (6 a₁ - a₂b w₁n)`. -/
theorem alignedSquareW1ZeroComplement_c1Clear610
    (w1n e1b e3b a1 a2b b1 : K) (κ μ κ₃ ν : K) :
    (6 : K) *
        (-(κ * ((17915904 : K) * e1b * w1n * a2b)) +
            κ * ((26873856 : K) * e1b * a1) +
              κ * ((2985984 : K) * e3b * a2b) -
                μ * ((1306368 : K) * e1b * a2b) +
                  μ * ((326592 : K) * w1n ^ 2 * a2b) -
                    μ * ((3919104 : K) * w1n * a1) -
                      κ₃ * ((3359232 : K) * a1) -
                        ν * ((233280 : K) * a2b) +
                          (44789760 : K) * e1b ^ 2 * w1n * a2b -
                            (33592320 : K) * e1b ^ 2 * a1 -
                              (7464960 : K) * e1b * e3b * a2b -
                                (22394880 : K) * e1b * w1n ^ 3 *
                                    a2b +
                                  (67184640 : K) * e1b * w1n ^ 2 *
                                      a1 +
                                    (7464960 : K) * e3b * w1n ^ 2 *
                                        a2b -
                                      (22394880 : K) * e3b * w1n *
                                          a1 -
                                        (1632586752 : K) * b1 -
          (-(κ * ((13436928 : K) * e1b * w1n * a2b)) +
              κ * ((2985984 : K) * e3b * a2b) -
                μ * ((1306368 : K) * e1b * a2b) -
                  μ * ((326592 : K) * w1n ^ 2 * a2b) -
                    κ₃ * ((559872 : K) * w1n * a2b) -
                      ν * ((233280 : K) * a2b) +
                        (39191040 : K) * e1b ^ 2 * w1n * a2b -
                          (7464960 : K) * e1b * e3b * a2b -
                            (11197440 : K) * e1b * w1n ^ 3 * a2b +
                              (3732480 : K) * e3b * w1n ^ 2 * a2b -
                                (1632586752 : K) * b1)) =
      ((26873856 : K) * κ * e1b - (3919104 : K) * μ * w1n -
          (3359232 : K) * κ₃ - (33592320 : K) * e1b ^ 2 +
            (67184640 : K) * e1b * w1n ^ 2 -
              (22394880 : K) * e3b * w1n) *
        ((6 : K) * a1 - a2b * w1n) := by
  ring

set_option maxHeartbeats 8000000 in
/-- Polynomial clearing of `C₁` against the complement form. -/
theorem alignedSquareW1ZeroComplement_c1Clear_poly610
    (w1n e1b e3b a1 a2b b1 : K[X]) (κ μ κ₃ ν : K) :
    (6 : K[X]) *
        (alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1 a2b b1
              κ μ κ₃ ν -
          alignedSquareW1ZeroComplementNinthC1Form610 w1n e1b e3b a2b
            b1 κ μ κ₃ ν) =
      (Polynomial.C κ * ((26873856 : K[X]) * e1b) -
          Polynomial.C μ * ((3919104 : K[X]) * w1n) -
            Polynomial.C κ₃ * ((3359232 : K[X]) ) -
              (33592320 : K[X]) * e1b ^ 2 +
                (67184640 : K[X]) * e1b * w1n ^ 2 -
                  (22394880 : K[X]) * e3b * w1n) *
        ((6 : K[X]) * a1 - a2b * w1n) := by
  apply Polynomial.funext
  intro z
  simp only [alignedSquareW1ZeroMixedNinthC1Poly610,
    alignedSquareW1ZeroComplementNinthC1Form610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
  ring

/-- On `6 p₁ = a₂b w₁n` the mixed-ninth `C₁` polynomial is the named
linear form. -/
theorem alignedSquareW1ZeroComplement_c1EqForm_poly610
    (w1n e1b e3b a1 a2b b1 : K[X]) (κ μ κ₃ ν : K)
    (hp1 : (6 : K[X]) * a1 = a2b * w1n) :
    alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1 a2b b1 κ μ
        κ₃ ν =
      alignedSquareW1ZeroComplementNinthC1Form610 w1n e1b e3b a2b b1
        κ μ κ₃ ν := by
  have h6 : (6 : K[X]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by norm_num : (6 : ℕ) ≠ 0)
  have hclear :=
    alignedSquareW1ZeroComplement_c1Clear_poly610 w1n e1b e3b a1 a2b
      b1 κ μ κ₃ ν
  have hdiff : (6 : K[X]) * a1 - a2b * w1n = 0 := by
    linear_combination hp1
  rw [hdiff, mul_zero] at hclear
  exact
    sub_eq_zero.mp ((mul_eq_zero.mp hclear).resolve_left h6)

/-- On `6 p₁ = a₂b w₁n` the mixed-ninth `C₁` is the named linear form. -/
theorem alignedSquareW1ZeroComplement_c1EqForm610
    (w1n e1b e3b a1 a2b b1 : K) (κ μ κ₃ ν : K)
    (hp1 : (6 : K) * a1 = a2b * w1n) :
    -(κ * ((17915904 : K) * e1b * w1n * a2b)) +
        κ * ((26873856 : K) * e1b * a1) +
          κ * ((2985984 : K) * e3b * a2b) -
            μ * ((1306368 : K) * e1b * a2b) +
              μ * ((326592 : K) * w1n ^ 2 * a2b) -
                μ * ((3919104 : K) * w1n * a1) -
                  κ₃ * ((3359232 : K) * a1) -
                    ν * ((233280 : K) * a2b) +
                      (44789760 : K) * e1b ^ 2 * w1n * a2b -
                        (33592320 : K) * e1b ^ 2 * a1 -
                          (7464960 : K) * e1b * e3b * a2b -
                            (22394880 : K) * e1b * w1n ^ 3 * a2b +
                              (67184640 : K) * e1b * w1n ^ 2 * a1 +
                                (7464960 : K) * e3b * w1n ^ 2 * a2b -
                                  (22394880 : K) * e3b * w1n * a1 -
                                    (1632586752 : K) * b1 =
      -(κ * ((13436928 : K) * e1b * w1n * a2b)) +
        κ * ((2985984 : K) * e3b * a2b) -
          μ * ((1306368 : K) * e1b * a2b) -
            μ * ((326592 : K) * w1n ^ 2 * a2b) -
              κ₃ * ((559872 : K) * w1n * a2b) -
                ν * ((233280 : K) * a2b) +
                  (39191040 : K) * e1b ^ 2 * w1n * a2b -
                    (7464960 : K) * e1b * e3b * a2b -
                      (11197440 : K) * e1b * w1n ^ 3 * a2b +
                        (3732480 : K) * e3b * w1n ^ 2 * a2b -
                          (1632586752 : K) * b1 := by
  have h6 : (6 : K) ≠ 0 := by norm_num
  have hclear :=
    alignedSquareW1ZeroComplement_c1Clear610 w1n e1b e3b a1 a2b b1 κ μ
      κ₃ ν
  have hdiff : (6 : K) * a1 - a2b * w1n = 0 := by
    linear_combination hp1
  rw [hdiff, mul_zero] at hclear
  exact
    sub_eq_zero.mp ((mul_eq_zero.mp hclear).resolve_left h6)

/-- The linear form is not a unit times `q₁`: its `q₁`-free jet is
`a₂b` times a nonzero-looking form in the remaining letters. -/
theorem alignedSquareW1ZeroComplement_c1Form_q1Coeff610
    (w1n e1b e3b a2b b1 : K) (κ μ κ₃ ν : K) :
    (-(κ * ((13436928 : K) * e1b * w1n * a2b)) +
          κ * ((2985984 : K) * e3b * a2b) -
            μ * ((1306368 : K) * e1b * a2b) -
              μ * ((326592 : K) * w1n ^ 2 * a2b) -
                κ₃ * ((559872 : K) * w1n * a2b) -
                  ν * ((233280 : K) * a2b) +
                    (39191040 : K) * e1b ^ 2 * w1n * a2b -
                      (7464960 : K) * e1b * e3b * a2b -
                        (11197440 : K) * e1b * w1n ^ 3 * a2b +
                          (3732480 : K) * e3b * w1n ^ 2 * a2b -
                            (1632586752 : K) * b1) -
        (-(1632586752 : K) * b1) =
      a2b *
        (-(κ * ((13436928 : K) * e1b * w1n)) +
            κ * ((2985984 : K) * e3b) -
              μ * ((1306368 : K) * e1b) -
                μ * ((326592 : K) * w1n ^ 2) -
                  κ₃ * ((559872 : K) * w1n) - ν * ((233280 : K)) +
                    (39191040 : K) * e1b ^ 2 * w1n -
                      (7464960 : K) * e1b * e3b -
                        (11197440 : K) * e1b * w1n ^ 3 +
                          (3732480 : K) * e3b * w1n ^ 2) := by
  ring

set_option maxHeartbeats 16000000 in
/-- Polynomial substitution `6 p₁ = a₂b w₁n` realises the complement
ninth load after cancelling one `h₀`. -/
theorem alignedSquareW1ZeroComplement_ninthFactor610
    (h0 w1n e1b e3b a0 a1 a2b b1 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hp1 : (6 : K[X]) * a1 = a2b * w1n) :
    alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1 a2b b1
        κ μ κ₃ ν κ₅ ν₂ κ₇ =
      h0 *
        alignedSquareW1ZeroComplementNinthLoad610 h0 w1n e1b e3b a0
          a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ := by
  have hsplit :=
    alignedSquareW1ZeroMixed_ninthSplit610 h0 w1n e1b e3b a0 a1 a2b b1
      κ μ κ₃ ν κ₅ ν₂ κ₇
  have hhead :=
    alignedSquareW1ZeroMixed_ninthHead_poly610 w1n a1 a2b
  have hdiff : (6 : K[X]) * a1 - a2b * w1n = 0 := by
    linear_combination hp1
  have hH0 :
      alignedSquareW1ZeroMixedNinthHeadPoly610 w1n a1 a2b = 0 := by
    calc
      alignedSquareW1ZeroMixedNinthHeadPoly610 w1n a1 a2b =
          (302330880 : K[X]) * a2b *
            ((6 : K[X]) * a1 - a2b * w1n) := hhead
      _ = (302330880 : K[X]) * a2b * 0 := by rw [hdiff]
      _ = 0 := by ring
  have hc1 :=
    alignedSquareW1ZeroComplement_c1EqForm_poly610 w1n e1b e3b a1 a2b
      b1 κ μ κ₃ ν hp1
  calc
    alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1 a2b b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ =
        alignedSquareW1ZeroMixedNinthHeadPoly610 w1n a1 a2b +
          h0 *
            alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1 a2b
              b1 κ μ κ₃ ν +
            h0 ^ 2 *
              alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b a0 κ
                μ ν κ₅ ν₂ κ₇ := hsplit
    _ =
        0 +
          h0 *
            alignedSquareW1ZeroComplementNinthC1Form610 w1n e1b e3b
              a2b b1 κ μ κ₃ ν +
            h0 ^ 2 *
              alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b a0 κ
                μ ν κ₅ ν₂ κ₇ := by
      rw [hH0, hc1]
    _ =
        h0 *
          alignedSquareW1ZeroComplementNinthLoad610 h0 w1n e1b e3b a0
            a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ := by
      simp only [alignedSquareW1ZeroComplementNinthLoad610]
      ring

set_option maxHeartbeats 16000000 in
/-- On the polynomial complement `6 p₁ = a₂b w₁n`, the next ninth head
at the unique root is the named linear form. -/
theorem alignedSquareW1ZeroComplement_ninthHeadKill610
    (h0 w1n e1b e3b a0 a1 a2b b1 : K[X])
    (κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hp1 : (6 : K[X]) * a1 = a2b * w1n)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 (h0 * w1n) (h0 * e1b)
          (h0 * (h0 * e3b))
          (h0 * w1n *
            (h0 * e3b - (3 : K[X]) * (h0 * e1b) * w1n))
          a0 a1 (h0 * a2b) b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    -(κ * ((13436928 : K) * e1b.eval x * w1n.eval x * a2b.eval x)) +
        κ * ((2985984 : K) * e3b.eval x * a2b.eval x) -
          μ * ((1306368 : K) * e1b.eval x * a2b.eval x) -
            μ * ((326592 : K) * w1n.eval x ^ 2 * a2b.eval x) -
              κ₃ * ((559872 : K) * w1n.eval x * a2b.eval x) -
                ν * ((233280 : K) * a2b.eval x) +
                  (39191040 : K) * e1b.eval x ^ 2 * w1n.eval x *
                      a2b.eval x -
                    (7464960 : K) * e1b.eval x * e3b.eval x *
                        a2b.eval x -
                      (11197440 : K) * e1b.eval x * w1n.eval x ^ 3 *
                          a2b.eval x +
                        (3732480 : K) * e3b.eval x *
                            w1n.eval x ^ 2 * a2b.eval x -
                          (1632586752 : K) * b1.eval x =
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
  have hcomp :=
    alignedSquareW1ZeroComplement_ninthFactor610 h0 w1n e1b e3b a0 a1
      a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ hp1
  rw [hw1, he1a2, hmix, hcomp] at hrow
  have hrow' :
      h0 ^ 5 *
          alignedSquareW1ZeroComplementNinthLoad610 h0 w1n e1b e3b a0
            a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6 := by
    convert hrow using 1
    ring
  have hload :
      alignedSquareW1ZeroComplementNinthLoad610 h0 w1n e1b e3b a0 a2b
          b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 5 * (Polynomial.C μ₃ * h0) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 5 hh0) (hrow'.trans hpow)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareW1ZeroComplementNinthLoad610,
    alignedSquareW1ZeroComplementNinthC1Form610,
    alignedSquareW1ZeroMixedNinthC2Poly610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  simpa using hloadx

set_option maxHeartbeats 16000000 in
/-- Honest remainder upgrade: `6 p₁ - a₂b w₁n = h₀ τ` leaves the extra
monomial `302330880 a₂b τ` in the cancelled head. -/
theorem alignedSquareW1ZeroComplement_ninthTauHeadKill610
    (h0 w1n e1b e3b a0 a1 a2b b1 tau : K[X])
    (κ μ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (htau :
      (6 : K[X]) * a1 - a2b * w1n = h0 * tau)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 (h0 * w1n) (h0 * e1b)
          (h0 * (h0 * e3b))
          (h0 * w1n *
            (h0 * e3b - (3 : K[X]) * (h0 * e1b) * w1n))
          a0 a1 (h0 * a2b) b1 κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    -(κ * ((13436928 : K) * e1b.eval x * w1n.eval x * a2b.eval x)) +
        κ * ((2985984 : K) * e3b.eval x * a2b.eval x) -
          μ * ((1306368 : K) * e1b.eval x * a2b.eval x) -
            μ * ((326592 : K) * w1n.eval x ^ 2 * a2b.eval x) -
              κ₃ * ((559872 : K) * w1n.eval x * a2b.eval x) -
                ν * ((233280 : K) * a2b.eval x) +
                  (39191040 : K) * e1b.eval x ^ 2 * w1n.eval x *
                      a2b.eval x -
                    (7464960 : K) * e1b.eval x * e3b.eval x *
                        a2b.eval x -
                      (11197440 : K) * e1b.eval x * w1n.eval x ^ 3 *
                          a2b.eval x +
                        (3732480 : K) * e3b.eval x *
                            w1n.eval x ^ 2 * a2b.eval x -
                          (1632586752 : K) * b1.eval x +
                            (302330880 : K) * a2b.eval x *
                              tau.eval x =
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
                alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b
                  a0 a1 a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇)) := by
        ring
      _ = Polynomial.C μ₃ * h0 ^ 6 := hrow
  have hload :
      alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1 a2b b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 2 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 6 =
        h0 ^ 4 * (Polynomial.C μ₃ * h0 ^ 2) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 4 hh0) (hrow'.trans hpow)
  have hsplit :=
    alignedSquareW1ZeroMixed_ninthSplit610 h0 w1n e1b e3b a0 a1 a2b b1
      κ μ κ₃ ν κ₅ ν₂ κ₇
  have hhead :=
    alignedSquareW1ZeroMixed_ninthHead_poly610 w1n a1 a2b
  have hcancel :
      (302330880 : K[X]) * a2b * tau +
          alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1 a2b
            b1 κ μ κ₃ ν +
            h0 *
              alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b a0 κ
                μ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 := by
    have hsum :
        h0 *
            ((302330880 : K[X]) * a2b * tau +
              alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1
                a2b b1 κ μ κ₃ ν +
                h0 *
                  alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b
                    a0 κ μ ν κ₅ ν₂ κ₇) =
          Polynomial.C μ₃ * h0 ^ 2 := by
      calc
        h0 *
              ((302330880 : K[X]) * a2b * tau +
                alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1
                  a2b b1 κ μ κ₃ ν +
                  h0 *
                    alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b
                      e3b a0 κ μ ν κ₅ ν₂ κ₇) =
            (302330880 : K[X]) * a2b * (h0 * tau) +
              h0 *
                alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1
                  a2b b1 κ μ κ₃ ν +
                h0 ^ 2 *
                  alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b
                    a0 κ μ ν κ₅ ν₂ κ₇ := by
          ring
        _ =
            (302330880 : K[X]) * a2b *
                ((6 : K[X]) * a1 - a2b * w1n) +
              h0 *
                alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1
                  a2b b1 κ μ κ₃ ν +
                h0 ^ 2 *
                  alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b
                    a0 κ μ ν κ₅ ν₂ κ₇ := by
          rw [htau]
        _ =
            alignedSquareW1ZeroMixedNinthHeadPoly610 w1n a1 a2b +
              h0 *
                alignedSquareW1ZeroMixedNinthC1Poly610 w1n e1b e3b a1
                  a2b b1 κ μ κ₃ ν +
                h0 ^ 2 *
                  alignedSquareW1ZeroMixedNinthC2Poly610 w1n e1b e3b
                    a0 κ μ ν κ₅ ν₂ κ₇ := by
          rw [hhead]
        _ =
            alignedSquareW1ZeroMixedNinthLoad610 h0 w1n e1b e3b a0 a1
              a2b b1 κ μ κ₃ ν κ₅ ν₂ κ₇ :=
          hsplit.symm
        _ = Polynomial.C μ₃ * h0 ^ 2 := hload
    have hpow : Polynomial.C μ₃ * h0 ^ 2 =
        h0 * (Polynomial.C μ₃ * h0) := by ring
    exact mul_left_cancel₀ hh0 (hsum.trans hpow)
  have hxsum := congrArg (fun w : K[X] => w.eval x) hcancel
  simp only [alignedSquareW1ZeroMixedNinthC1Poly610,
    alignedSquareW1ZeroMixedNinthC2Poly610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hxsum
  rw [hx] at hxsum
  have hp1x :
      (6 : K) * a1.eval x = a2b.eval x * w1n.eval x := by
    have h := congrArg (fun w : K[X] => w.eval x) htau
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat] at h
    rw [hx] at h
    linear_combination h
  have hc1 :=
    alignedSquareW1ZeroComplement_c1EqForm610 (w1n.eval x)
      (e1b.eval x) (e3b.eval x) (a1.eval x) (a2b.eval x) (b1.eval x)
      κ μ κ₃ ν hp1x
  simp only [zero_mul, mul_zero, add_zero] at hxsum
  linear_combination hxsum - hc1

/-! ## M2: valuation-4 integer eighth head after the product -/

/-- `h₀`-free part of `alignedSquareMuZeroNuZeroEighthVLoad610`. -/
def alignedSquareMuZeroNuZeroEighthVHead610
    (w1 e1n e3 v a0 a1 b2 : K) (κ κ₃ κ₅ : K) : K :=
  (1280 : K) * v ^ 2 + (2799360 : K) * w1 ^ 2 * a0 -
    (15116544 : K) * b2 - (1866240 : K) * e1n * w1 * a1 +
      (622080 : K) * e3 * a1 + κ * ((746496 : K) * w1 * a1) +
        κ * ((4608 : K) * e1n ^ 2 * w1 ^ 2) -
          κ * ((3072 : K) * e1n * e3 * w1) +
            κ * ((512 : K) * e3 ^ 2) +
              κ₃ * ((1152 : K) * e1n * w1 ^ 2) -
                κ₃ * ((384 : K) * e3 * w1) -
                  κ₅ * ((16 : K) * w1 ^ 2) -
                    (26880 : K) * e1n ^ 3 * w1 ^ 2 +
                      (11520 : K) * e1n ^ 2 * e3 * w1 -
                        (1280 : K) * e1n * e3 ^ 2

/-- Session-`01a05a10` integer primitive (content `16` of the product
eighth head). -/
def alignedSquareMuZeroNuZeroEighthVHeadInteger610
    (w1 e1n e3 v a0 a1 b2 : K) (κ κ₃ κ₅ : K) : K :=
  (174960 : K) * a0 * w1 ^ 2 - (116640 : K) * a1 * e1n * w1 +
    (38880 : K) * a1 * e3 + (46656 : K) * a1 * κ * w1 -
      (944784 : K) * b2 - (1680 : K) * e1n ^ 3 * w1 ^ 2 +
        (720 : K) * e1n ^ 2 * e3 * w1 +
          (288 : K) * e1n ^ 2 * κ * w1 ^ 2 -
            (80 : K) * e1n * e3 ^ 2 -
              (192 : K) * e1n * e3 * κ * w1 +
                (72 : K) * e1n * κ₃ * w1 ^ 2 +
                  (32 : K) * e3 ^ 2 * κ -
                    (24 : K) * e3 * κ₃ * w1 - κ₅ * w1 ^ 2 +
                      (80 : K) * v ^ 2

/-- `y`-form of the eighth `v`-head, `e₃ = y + 6 e₁n w₁`. -/
def alignedSquareMuZeroMixedEighthVHeadY610
    (w1 e1n y v a0 a1 b2 : K) (κ κ₃ κ₅ : K) : K :=
  (1280 : K) * v ^ 2 + (2799360 : K) * w1 ^ 2 * a0 -
    (15116544 : K) * b2 + (1866240 : K) * e1n * w1 * a1 +
      (622080 : K) * y * a1 + κ * ((746496 : K) * w1 * a1) +
        κ * ((4608 : K) * e1n ^ 2 * w1 ^ 2) +
          κ * ((3072 : K) * e1n * y * w1) +
            κ * ((512 : K) * y ^ 2) -
              κ₃ * ((1152 : K) * e1n * w1 ^ 2) -
                κ₃ * ((384 : K) * y * w1) -
                  κ₅ * ((16 : K) * w1 ^ 2) -
                    (3840 : K) * e1n ^ 3 * w1 ^ 2 -
                      (3840 : K) * e1n ^ 2 * y * w1 -
                        (1280 : K) * e1n * y ^ 2

/-- The landed `v`-head is `16` times the integer primitive. -/
theorem alignedSquareMuZeroNuZero_eighthVHead_integer610
    (w1 e1n e3 v a0 a1 b2 : K) (κ κ₃ κ₅ : K) :
    alignedSquareMuZeroNuZeroEighthVHead610 w1 e1n e3 v a0 a1 b2 κ κ₃
        κ₅ =
      (16 : K) *
        alignedSquareMuZeroNuZeroEighthVHeadInteger610 w1 e1n e3 v a0
          a1 b2 κ κ₃ κ₅ := by
  simp only [alignedSquareMuZeroNuZeroEighthVHead610,
    alignedSquareMuZeroNuZeroEighthVHeadInteger610]
  ring

/-- Rewriting `e₃ = y + 6 e₁n w₁` produces the mixed `y`-head. -/
theorem alignedSquareMuZeroMixed_eighthVHead_yForm610
    (w1 e1n y v a0 a1 b2 : K) (κ κ₃ κ₅ : K) :
    alignedSquareMuZeroNuZeroEighthVHead610 w1 e1n
        (y + (6 : K) * e1n * w1) v a0 a1 b2 κ κ₃ κ₅ =
      alignedSquareMuZeroMixedEighthVHeadY610 w1 e1n y v a0 a1 b2 κ
        κ₃ κ₅ := by
  simp only [alignedSquareMuZeroNuZeroEighthVHead610,
    alignedSquareMuZeroMixedEighthVHeadY610]
  ring

/-- The integer head is linear in `(p₀, p₁, q₂, v²)`, not a unit times
`v²`. -/
theorem alignedSquareMuZeroNuZero_eighthVHeadInteger_v2Coeff610
    (w1 e1n e3 v a0 a1 b2 : K) (κ κ₃ κ₅ : K) :
    alignedSquareMuZeroNuZeroEighthVHeadInteger610 w1 e1n e3 v a0 a1
          b2 κ κ₃ κ₅ -
        (80 : K) * v ^ 2 =
      (174960 : K) * a0 * w1 ^ 2 - (116640 : K) * a1 * e1n * w1 +
        (38880 : K) * a1 * e3 + (46656 : K) * a1 * κ * w1 -
          (944784 : K) * b2 - (1680 : K) * e1n ^ 3 * w1 ^ 2 +
            (720 : K) * e1n ^ 2 * e3 * w1 +
              (288 : K) * e1n ^ 2 * κ * w1 ^ 2 -
                (80 : K) * e1n * e3 ^ 2 -
                  (192 : K) * e1n * e3 * κ * w1 +
                    (72 : K) * e1n * κ₃ * w1 ^ 2 +
                      (32 : K) * e3 ^ 2 * κ -
                        (24 : K) * e3 * κ₃ * w1 - κ₅ * w1 ^ 2 := by
  simp only [alignedSquareMuZeroNuZeroEighthVHeadInteger610]
  ring

set_option maxHeartbeats 16000000 in
/-- At the unique root the eighth `v`-load is the named `y`-form. -/
theorem alignedSquareMuZeroMixed_eighthVHeadKillY610
    (h0 w1 e1n y v a0 a1 b2 : K[X])
    (κ κ₇ κ₃ κ₅ ν₂ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedEighthSquarePeeledRow610 h0 w1 (h0 * e1n)
          (h0 * (y + (6 : K[X]) * e1n * w1)) a0 a1
          ((w1 *
                ((y + (6 : K[X]) * e1n * w1) -
                  (3 : K[X]) * e1n * w1) -
              h0 * v) *
            Polynomial.C (81 : K)⁻¹)
          b2 κ 0 κ₃ 0 κ₅ ν₂ =
        Polynomial.C κ₇ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) :
    alignedSquareMuZeroMixedEighthVHeadY610 (w1.eval x) (e1n.eval x)
        (y.eval x) (v.eval x) (a0.eval x) (a1.eval x) (b2.eval x) κ
        κ₃ κ₅ =
      0 := by
  have hkill :=
    alignedSquareMuZeroNuZero_eighthVHeadKill610 h0 w1 e1n
      (y + (6 : K[X]) * e1n * w1) v a0 a1 b2 κ κ₇ κ₃ κ₅ ν₂ hh0 hrow x
      hx
  have hy :
      (y + (6 : K[X]) * e1n * w1).eval x =
        y.eval x + (6 : K) * e1n.eval x * w1.eval x := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat]
  rw [hy] at hkill
  have hform :=
    alignedSquareMuZeroMixed_eighthVHead_yForm610 (w1.eval x)
      (e1n.eval x) (y.eval x) (v.eval x) (a0.eval x) (a1.eval x)
      (b2.eval x) κ κ₃ κ₅
  simp only [alignedSquareMuZeroNuZeroEighthVHead610] at hform
  exact hform.symm.trans hkill

/-- Degree-`1` Jacobian row of a normalized aligned `(6,10)` source. -/
theorem alignedSquare610_degreeOneRow
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (p.coeff 1).derivative * q.coeff 1 +
        (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
      ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
        p.coeff 1 * (q.coeff 1).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨_j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    alignedFourteenthSquareCoefficientJacobianRow_610 hp hq hjac

/-! ## Source-facing M1/M2 packet -/

set_option maxHeartbeats 32000000 in
/-- M1/M2 refinement of the aligned-square mixed-pair packet.

On `w₁(a)=0` the complement is upgraded by the divisor
`6 p₁ - a₂b w₁n = h₀ τ`.  The next ninth head is the named linear
form plus `302330880 a₂b(a) τ(a)`.  That form is not a unit times
`q₁(a)`, and no relation here forces `w₁n(a)=0` or `τ(a)=0`, so the
Keller collision is not reached.

On `μ=0` the valuation-`4` eighth `v`-head is consumed in the mixed
`y`-coordinates.  Combined with the mixed combo (which determines
`ν₂`, not `v`) and the degree-`1` row (derivatives), this does not
force `v(a)=0`.

The square chamber is not claimed empty. -/
theorem normalized610ScaleTwo_alignedSquare_m1m2Reduction
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
        (p.coeff 1).derivative * q.coeff 1 +
            (p.coeff 0).derivative *
              (q.coeff 2 * Polynomial.C (2 : K)) -
          ((p.coeff 2 * Polynomial.C (2 : K)) *
              (q.coeff 0).derivative +
            p.coeff 1 * (q.coeff 1).derivative) =
          0 ∧
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
          ∃ w1n e1b a2b e3b tau : K[X],
            w1 = h0 * w1n ∧
              e1 = h0 * e1b ∧
                p.coeff 2 = h0 * a2b ∧
                  e3 = h0 * e3b ∧
                    a2b.eval a ≠ 0 ∧
                      (6 : K) * (p.coeff 1).eval a =
                          a2b.eval a * w1n.eval a ∧
                        (20 : K) * e1b.eval a =
                          (8 : K) * κ + (5 : K) * w1n.eval a ^ 2 ∧
                        (6 : K[X]) * p.coeff 1 - a2b * w1n =
                            h0 * tau ∧
                          -(κ *
                                  ((13436928 : K) * e1b.eval a *
                                    w1n.eval a * a2b.eval a)) +
                              κ *
                                  ((2985984 : K) * e3b.eval a *
                                    a2b.eval a) -
                                μ *
                                    ((1306368 : K) * e1b.eval a *
                                      a2b.eval a) -
                                  μ *
                                      ((326592 : K) *
                                        w1n.eval a ^ 2 *
                                          a2b.eval a) -
                                    κ₃ *
                                        ((559872 : K) *
                                          w1n.eval a * a2b.eval a) -
                                      ν *
                                          ((233280 : K) *
                                            a2b.eval a) +
                                        (39191040 : K) *
                                            e1b.eval a ^ 2 *
                                              w1n.eval a *
                                                a2b.eval a -
                                          (7464960 : K) *
                                              e1b.eval a *
                                                e3b.eval a *
                                                  a2b.eval a -
                                            (11197440 : K) *
                                                e1b.eval a *
                                                  w1n.eval a ^ 3 *
                                                    a2b.eval a +
                                              (3732480 : K) *
                                                  e3b.eval a *
                                                    w1n.eval a ^ 2 *
                                                      a2b.eval a -
                                                (1632586752 : K) *
                                                    (q.coeff 1).eval
                                                      a +
                                                  (302330880 : K) *
                                                      a2b.eval a *
                                                        tau.eval a =
                            0) ∧
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
                        alignedSquareMuZeroMixedEighthVHeadY610
                            (w1.eval a) (e1n.eval a) (y.eval a)
                            (v.eval a) ((p.coeff 0).eval a)
                            ((p.coeff 1).eval a)
                            ((q.coeff 2).eval a) κ κ₃ κ₅ =
                          0 ∧
                        (v.eval a = 0 →
                          y.eval a = 0 ∧ ν₂ = 0 ∧
                            ∃ y1 v1 : K[X],
                              y = h0 * y1 ∧ v = h0 * v1 ∧
                                (243 : K) * (p.coeff 1).eval a +
                                    v1.eval a * w1.eval a = 0)) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hD1 := alignedSquare610_degreeOneRow hsource
  obtain ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, κ₉, w1, f2, e1, e2, u2,
    e3, s2, hdeg1, hroot, hj, hrowK, hroweval, hp5w1, hp4f2, he1, he2,
    he3, hu2, hs2, hR9, hR8, hR10, hbranch, hlimbA, hlimbB⟩ :=
    normalized610ScaleTwo_alignedSquare_mixedPairReduction hsource
      hh0 hHsq haligned
  refine ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, κ₉, w1, f2, e1, e2, u2,
    e3, s2, hdeg1, hroot, hj, hrowK, hroweval, hD1, hp5w1, hp4f2, he1,
    he2, he3, hu2, hs2, hR9, hR8, hR10, hbranch, ?limbA, ?limbB⟩
  · intro hw1a
    obtain ⟨w1n, e1b, a2b, e3b, hw1, he1b, ha2b, he3b, ha2bne, hp1eq,
      he1beq⟩ := hlimbA hw1a
    have hp1eval :
        ((6 : K[X]) * p.coeff 1 - a2b * w1n).eval a = 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      linear_combination hp1eq
    obtain ⟨tau, htau⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        ((6 : K[X]) * p.coeff 1 - a2b * w1n) a hdeg1 hroot hp1eval
    have hu2m :
        u2 =
          h0 * w1n *
            (h0 * e3b -
              (3 : K[X]) * (h0 * e1b) * w1n) := by
      have hprod := hu2
      rw [hw1, he3, he1b, he3b] at hprod
      apply mul_left_cancel₀ hh0
      calc
        h0 * u2 =
            (h0 * w1n) *
              (h0 * (h0 * e3b) -
                (3 : K[X]) * (h0 * e1b) * (h0 * w1n)) :=
          hprod.symm
        _ =
            h0 *
              (h0 * w1n *
                (h0 * e3b -
                  (3 : K[X]) * (h0 * e1b) * w1n)) := by
          ring
    have hR9m := hR9
    rw [hw1, he1b, he3, he3b, ha2b, hu2m] at hR9m
    have hN :=
      alignedSquareW1ZeroComplement_ninthTauHeadKill610 h0 w1n e1b
        e3b (p.coeff 0) (p.coeff 1) a2b (q.coeff 1) tau κ μ μ₃ κ₃ ν
        κ₅ ν₂ κ₇ hh0 htau hR9m a hroot
    exact ⟨w1n, e1b, a2b, e3b, tau, hw1, he1b, ha2b, he3b, ha2bne,
      hp1eq, he1beq, htau, hN⟩
  · intro hw1x
    obtain ⟨hμ, hν, e1n, v, y, rho, he1n, hu, hy, hrho, hcube,
      hcombo, hvbranch⟩ := hlimbB hw1x
    have hy' : e3 = y + (6 : K[X]) * e1n * w1 := by
      rw [hy]; ring
    have ha2 :=
      alignedSquareMuZero_coeffTwo_of_product610 h0 w1 e1n e3 v
        (p.coeff 2)
        (alignedSquareMuZero_productReduce610 h0 w1 e1n e3 v
          (p.coeff 2) u2 hh0
          (by simpa [he1n, he3] using hu2) hu)
    have hdelta :
        e3 - (3 : K[X]) * e1n * w1 =
          y + (3 : K[X]) * e1n * w1 := by
      rw [hy]; ring
    have ha2y := ha2
    rw [hdelta] at ha2y
    have ha2arg :
        (w1 * (y + (3 : K[X]) * e1n * w1) - h0 * v) *
            Polynomial.C (81 : K)⁻¹ =
          (w1 *
                ((y + (6 : K[X]) * e1n * w1) -
                  (3 : K[X]) * e1n * w1) -
              h0 * v) *
            Polynomial.C (81 : K)⁻¹ := by
      ring
    have hR8m := hR8
    rw [he1n, he3, hμ, hν, hy', ha2y, ha2arg] at hR8m
    have h8y :=
      alignedSquareMuZeroMixed_eighthVHeadKillY610 h0 w1 e1n y v
        (p.coeff 0) (p.coeff 1) (q.coeff 2) κ κ₇ κ₃ κ₅ ν₂ hh0 hR8m a
        hroot
    refine ⟨hμ, hν, e1n, v, y, rho, he1n, hu, hy, hrho, hcube, hcombo,
      h8y, hvbranch⟩

#print axioms alignedSquareW1ZeroMixed_ninthHead_poly610
#print axioms alignedSquareW1ZeroMixed_ninthSplit610
#print axioms alignedSquareW1ZeroComplement_c1Clear610
#print axioms alignedSquareW1ZeroComplement_c1Clear_poly610
#print axioms alignedSquareW1ZeroComplement_c1EqForm_poly610
#print axioms alignedSquareW1ZeroComplement_c1EqForm610
#print axioms alignedSquareW1ZeroComplement_c1Form_q1Coeff610
#print axioms alignedSquareW1ZeroComplement_ninthFactor610
#print axioms alignedSquareW1ZeroComplement_ninthHeadKill610
#print axioms alignedSquareW1ZeroComplement_ninthTauHeadKill610
#print axioms alignedSquareMuZeroNuZero_eighthVHead_integer610
#print axioms alignedSquareMuZeroMixed_eighthVHead_yForm610
#print axioms alignedSquareMuZeroNuZero_eighthVHeadInteger_v2Coeff610
#print axioms alignedSquareMuZeroMixed_eighthVHeadKillY610
#print axioms alignedSquare610_degreeOneRow
#print axioms normalized610ScaleTwo_alignedSquare_m1m2Reduction

end Max11DegreeRoutes
