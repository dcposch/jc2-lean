import Sol410ScaleTwoAlignedSquareUFactorTenthAllocationScratch

/-! # Deep tenth-row allocation on the aligned-square `u` limb -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Exact tenth quotient after the additional source divisor
`p2=h0^2*r1`.  Its root value is `655360*g*p1^3`. -/
def alignedSquareDeepTenthLoad410
    (h0 g r1 p0 p1 q0 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 : K) : K[X] :=
  (655360 : K[X]) * g * p1 ^ 3 + h0 *
    ((6144 : K[X]) * p1 ^ 2 *
      (-(640 : K[X]) * p0 + (50 : K[X]) * g ^ 4 -
        (240 : K[X]) * g ^ 2 * r1 - Polynomial.C μ * ((7 : K[X]) * g) +
        Polynomial.C κ3 * (2 : K[X]) + (160 : K[X]) * r1 ^ 2) + h0 *
    (-(32 : K[X]) * p1 *
      ((30720 : K[X]) * p0 * g ^ 3 - (122880 : K[X]) * p0 * g * r1 -
        Polynomial.C μ * ((10752 : K[X]) * p0) -
        (1440 : K[X]) * g ^ 7 + (13440 : K[X]) * g ^ 5 * r1 +
        Polynomial.C μ * ((315 : K[X]) * g ^ 4) -
        Polynomial.C κ3 * ((96 : K[X]) * g ^ 3) -
        (38400 : K[X]) * g ^ 3 * r1 ^ 2 -
        Polynomial.C μ * ((1680 : K[X]) * g ^ 2 * r1) +
        Polynomial.C μ2 * ((30 : K[X]) * g ^ 2) +
        Polynomial.C κ3 * ((384 : K[X]) * g * r1) +
        (30720 : K[X]) * g * r1 ^ 3 +
        Polynomial.C μ * ((1344 : K[X]) * r1 ^ 2) -
        Polynomial.C μ2 * ((80 : K[X]) * r1) -
        Polynomial.C μ3 * (3 : K[X])) + h0 *
    ((983040 : K[X]) * p0 ^ 2 * g ^ 2 -
      Polynomial.C κ * ((524288 : K[X]) * p0 ^ 2) -
      (3932160 : K[X]) * p0 ^ 2 * r1 -
      (71680 : K[X]) * p0 * g ^ 6 +
      (614400 : K[X]) * p0 * g ^ 4 * r1 +
      Polynomial.C μ * ((17920 : K[X]) * p0 * g ^ 3) -
      Polynomial.C κ3 * ((6144 : K[X]) * p0 * g ^ 2) -
      (1474560 : K[X]) * p0 * g ^ 2 * r1 ^ 2 -
      Polynomial.C μ * ((86016 : K[X]) * p0 * g * r1) +
      Polynomial.C μ2 * ((2560 : K[X]) * p0 * g) +
      Polynomial.C κ3 * ((24576 : K[X]) * p0 * r1) +
      Polynomial.C κ5 * ((2048 : K[X]) * p0) +
      (655360 : K[X]) * p0 * r1 ^ 3 + (2288 : K[X]) * g ^ 10 -
      (31680 : K[X]) * g ^ 8 * r1 -
      Polynomial.C μ * ((663 : K[X]) * g ^ 7) +
      Polynomial.C κ3 * ((224 : K[X]) * g ^ 6) +
      (161280 : K[X]) * g ^ 6 * r1 ^ 2 +
      Polynomial.C μ * ((6552 : K[X]) * g ^ 5 * r1) -
      Polynomial.C μ2 * ((77 : K[X]) * g ^ 5) -
      Polynomial.C κ3 * ((1920 : K[X]) * g ^ 4 * r1) -
      (358400 : K[X]) * g ^ 4 * r1 ^ 3 -
      Polynomial.C μ * ((20160 : K[X]) * g ^ 3 * r1 ^ 2) +
      Polynomial.C μ2 * ((560 : K[X]) * g ^ 3 * r1) +
      Polynomial.C μ3 * ((5 : K[X]) * g ^ 3) +
      Polynomial.C κ3 * ((4608 : K[X]) * g ^ 2 * r1 ^ 2) -
      Polynomial.C κ7 * ((4 : K[X]) * g ^ 2) +
      (307200 : K[X]) * g ^ 2 * r1 ^ 4 +
      Polynomial.C μ * ((17920 : K[X]) * g * r1 ^ 3) -
      Polynomial.C μ2 * ((960 : K[X]) * g * r1 ^ 2) -
      Polynomial.C μ3 * ((24 : K[X]) * g * r1) +
      Polynomial.C μ4 * g - Polynomial.C κ3 * ((2048 : K[X]) * r1 ^ 3) +
      Polynomial.C κ7 * ((16 : K[X]) * r1) + Polynomial.C κ9 +
      (4194304 : K[X]) * q0 - (49152 : K[X]) * r1 ^ 5)))

set_option maxHeartbeats 8000000 in
/-- After `p2` acquires its second supplied factor, the same tenth row splits
the next exact source quotients: `g(root)=0` or `p1(root)=0`. -/
theorem alignedSquareDeepTenth_rootSplit410
    (H h0 u g r1 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 : K)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hp3 : p3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6)
    (hM6 : alignedFifthDefect410 H p0 p1 p2 p3 q5 q6 q7 κ =
      Polynomial.C μ2 * h0 ^ 15)
    (hM8 : alignedSixthDefect410 H p0 p1 p2 p3 q4 q5 q6 q7 κ =
      Polynomial.C κ5 * H ^ 9)
    (hM10 : alignedSeventhDefect410 H p0 p1 p2 p3 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ3 * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H p0 p1 p2 p3 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ7 * H ^ 12)
    (hM14 : alignedNinthDefect410 H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ4 * h0 ^ 27)
    (hM16 : alignedTenthDefect410 H p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ9 * H ^ 15)
    (hu : u = h0 * g) (hp2 : p2 = h0 ^ 2 * r1)
    (x : K) (hx : h0.eval x = 0) :
    g.eval x = 0 ∨ p1.eval x = 0 := by
  have hcore := alignedSquareTenth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14 hM16
  rw [hu, hp2] at hcore
  have hload : alignedSquareDeepTenthLoad410 h0 g r1 p0 p1 q0
      κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 7 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore
    simp only [alignedSquareDeepTenthLoad410, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
      Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination hz
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareDeepTenthLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

#print axioms alignedSquareDeepTenth_rootSplit410

end Max11DegreeRoutes
