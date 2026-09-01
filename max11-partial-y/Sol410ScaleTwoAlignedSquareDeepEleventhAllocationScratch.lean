import Sol410ScaleTwoAlignedSquareDeepTenthAllocationScratch

/-! # Deep eleventh-row allocation on the aligned-square `u` limb -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Exact eleventh quotient on `u=h0*g`, `p2=h0^2*r1`.  The root factor is
`p1^3*(4*r1-3*g^2)`. -/
def alignedSquareDeepEleventhLoad410
    (h0 g r1 p0 p1 : K[X])
    (μ κ3 μ2 μ3 κ7 μ4 μ5 : K) : K[X] :=
  -(5242880 : K[X]) * p1 ^ 3 *
      (-(3 : K[X]) * g ^ 2 + (4 : K[X]) * r1) + h0 *
    ((8192 : K[X]) * p1 ^ 2 *
      (-(7680 : K[X]) * p0 * g + (840 : K[X]) * g ^ 5 -
        (4800 : K[X]) * g ^ 3 * r1 -
        Polynomial.C μ * ((105 : K[X]) * g ^ 2) +
        Polynomial.C κ3 * ((24 : K[X]) * g) +
        (5760 : K[X]) * g * r1 ^ 2 +
        Polynomial.C μ * ((168 : K[X]) * r1) -
        Polynomial.C μ2 * (5 : K[X])) + h0 *
    ((256 : K[X]) * p1 *
      ((491520 : K[X]) * p0 ^ 2 - (76800 : K[X]) * p0 * g ^ 4 +
        (368640 : K[X]) * p0 * g ^ 2 * r1 +
        Polynomial.C μ * ((10752 : K[X]) * p0 * g) -
        Polynomial.C κ3 * ((3072 : K[X]) * p0) -
        (245760 : K[X]) * p0 * r1 ^ 2 + (3960 : K[X]) * g ^ 8 -
        (40320 : K[X]) * g ^ 6 * r1 -
        Polynomial.C μ * ((819 : K[X]) * g ^ 5) +
        Polynomial.C κ3 * ((240 : K[X]) * g ^ 4) +
        (134400 : K[X]) * g ^ 4 * r1 ^ 2 +
        Polynomial.C μ * ((5040 : K[X]) * g ^ 3 * r1) -
        Polynomial.C μ2 * ((70 : K[X]) * g ^ 3) -
        Polynomial.C κ3 * ((1152 : K[X]) * g ^ 2 * r1) -
        (153600 : K[X]) * g ^ 2 * r1 ^ 3 -
        Polynomial.C μ * ((6720 : K[X]) * g * r1 ^ 2) +
        Polynomial.C μ2 * ((240 : K[X]) * g * r1) +
        Polynomial.C μ3 * ((3 : K[X]) * g) +
        Polynomial.C κ3 * ((768 : K[X]) * r1 ^ 2) -
        Polynomial.C κ7 * (2 : K[X]) + (30720 : K[X]) * r1 ^ 4) + h0 *
    ((15728640 : K[X]) * p0 ^ 2 * g ^ 3 -
      (62914560 : K[X]) * p0 ^ 2 * g * r1 -
      Polynomial.C μ * ((5505024 : K[X]) * p0 ^ 2) -
      (1474560 : K[X]) * p0 * g ^ 7 +
      (13762560 : K[X]) * p0 * g ^ 5 * r1 +
      Polynomial.C μ * ((322560 : K[X]) * p0 * g ^ 4) -
      Polynomial.C κ3 * ((98304 : K[X]) * p0 * g ^ 3) -
      (39321600 : K[X]) * p0 * g ^ 3 * r1 ^ 2 -
      Polynomial.C μ * ((1720320 : K[X]) * p0 * g ^ 2 * r1) +
      Polynomial.C μ2 * ((30720 : K[X]) * p0 * g ^ 2) +
      Polynomial.C κ3 * ((393216 : K[X]) * p0 * g * r1) +
      (31457280 : K[X]) * p0 * g * r1 ^ 3 +
      Polynomial.C μ * ((1376256 : K[X]) * p0 * r1 ^ 2) -
      Polynomial.C μ2 * ((81920 : K[X]) * p0 * r1) -
      Polynomial.C μ3 * ((3072 : K[X]) * p0) +
      (49920 : K[X]) * g ^ 11 - (732160 : K[X]) * g ^ 9 * r1 -
      Polynomial.C μ * ((13923 : K[X]) * g ^ 8) +
      Polynomial.C κ3 * ((4608 : K[X]) * g ^ 7) +
      (4055040 : K[X]) * g ^ 7 * r1 ^ 2 +
      Polynomial.C μ * ((148512 : K[X]) * g ^ 6 * r1) -
      Polynomial.C μ2 * ((1540 : K[X]) * g ^ 6) -
      Polynomial.C κ3 * ((43008 : K[X]) * g ^ 5 * r1) -
      (10321920 : K[X]) * g ^ 5 * r1 ^ 3 -
      Polynomial.C μ * ((524160 : K[X]) * g ^ 4 * r1 ^ 2) +
      Polynomial.C μ2 * ((12320 : K[X]) * g ^ 4 * r1) +
      Polynomial.C μ3 * ((90 : K[X]) * g ^ 4) +
      Polynomial.C κ3 * ((122880 : K[X]) * g ^ 3 * r1 ^ 2) -
      Polynomial.C κ7 * ((64 : K[X]) * g ^ 3) +
      (11468800 : K[X]) * g ^ 3 * r1 ^ 4 +
      Polynomial.C μ * ((645120 : K[X]) * g ^ 2 * r1 ^ 3) -
      Polynomial.C μ2 * ((26880 : K[X]) * g ^ 2 * r1 ^ 2) -
      Polynomial.C μ3 * ((480 : K[X]) * g ^ 2 * r1) +
      Polynomial.C μ4 * ((12 : K[X]) * g ^ 2) -
      Polynomial.C κ3 * ((98304 : K[X]) * g * r1 ^ 3) +
      Polynomial.C κ7 * ((256 : K[X]) * g * r1) -
      (3932160 : K[X]) * g * r1 ^ 5 -
      Polynomial.C μ * ((143360 : K[X]) * r1 ^ 4) +
      Polynomial.C μ2 * ((10240 : K[X]) * r1 ^ 3) +
      Polynomial.C μ3 * ((384 : K[X]) * r1 ^ 2) -
      Polynomial.C μ4 * ((32 : K[X]) * r1) - Polynomial.C μ5)))

set_option maxHeartbeats 8000000 in
/-- The next exact source split supplied by the eleventh row. -/
theorem alignedSquareDeepEleventh_rootSplit410
    (H h0 u g r1 p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 μ5 : K)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hp3 : p3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6)
    (hM6 : alignedFifthDefect410 H p0 p1 p2 p3 q5 q6 q7 κ =
      Polynomial.C μ2 * h0 ^ 15)
    (hM10 : alignedSeventhDefect410 H p0 p1 p2 p3 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ3 * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H p0 p1 p2 p3 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ7 * H ^ 12)
    (hM14 : alignedNinthDefect410 H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ4 * h0 ^ 27)
    (hM18 : alignedEleventhDefect410 H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ5 * h0 ^ 33)
    (hu : u = h0 * g) (hp2 : p2 = h0 ^ 2 * r1)
    (x : K) (hx : h0.eval x = 0) :
    p1.eval x = 0 ∨
      (3 : K) * g.eval x ^ 2 - (4 : K) * r1.eval x = 0 := by
  have hcore := alignedSquareEleventh_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM10 hM12 hM14 hM18
  rw [hu, hp2] at hcore
  have hload : alignedSquareDeepEleventhLoad410 h0 g r1 p0 p1
      μ κ3 μ2 μ3 κ7 μ4 μ5 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 8 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore
    simp only [alignedSquareDeepEleventhLoad410, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
      Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination hz
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareDeepEleventhLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  rcases hloadx with hp1x | hrel
  · exact Or.inl hp1x
  · exact Or.inr (by linear_combination -hrel)

#print axioms alignedSquareDeepEleventh_rootSplit410

end Max11DegreeRoutes
