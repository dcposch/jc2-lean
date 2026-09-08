import Sol410ScaleTwoAlignedSquareUFactorNinthAllocationScratch

/-! # Tenth-row collapse on the aligned-square `u`-factor limb -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Exact quotient after `u=h0*g`, `p2=h0*r` in the square tenth core and
cancellation of `h0^5`.  The nested form exposes its root value
`-49152*r^5`. -/
def alignedSquareUFactorTenthLoad410
    (h0 g r p0 p1 q0 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 : K) : K[X] :=
  -(49152 : K[X]) * r ^ 5 + h0 *
    ((61440 : K[X]) * r ^ 2 *
      ((5 : K[X]) * g ^ 2 * r ^ 2 - (16 : K[X]) * g * p1 * r +
        (16 : K[X]) * p1 ^ 2) + h0 *
    ((512 : K[X]) *
      ((1280 : K[X]) * p0 * r ^ 3 - (700 : K[X]) * g ^ 4 * r ^ 3 +
        (2400 : K[X]) * g ^ 3 * p1 * r ^ 2 -
        (2880 : K[X]) * g ^ 2 * p1 ^ 2 * r +
        Polynomial.C μ * ((35 : K[X]) * g * r ^ 3) +
        (1280 : K[X]) * g * p1 ^ 3 -
        Polynomial.C κ3 * ((4 : K[X]) * r ^ 3) -
        Polynomial.C μ * ((84 : K[X]) * p1 * r ^ 2)) + h0 *
    (-(64 : K[X]) *
      ((23040 : K[X]) * p0 * g ^ 2 * r ^ 2 -
        (61440 : K[X]) * p0 * g * p1 * r +
        (61440 : K[X]) * p0 * p1 ^ 2 -
        (2520 : K[X]) * g ^ 6 * r ^ 2 +
        (6720 : K[X]) * g ^ 5 * p1 * r -
        (4800 : K[X]) * g ^ 4 * p1 ^ 2 +
        Polynomial.C μ * ((315 : K[X]) * g ^ 3 * r ^ 2) -
        Polynomial.C κ3 * ((72 : K[X]) * g ^ 2 * r ^ 2) -
        Polynomial.C μ * ((840 : K[X]) * g ^ 2 * p1 * r) +
        Polynomial.C κ3 * ((192 : K[X]) * g * p1 * r) +
        Polynomial.C μ * ((672 : K[X]) * g * p1 ^ 2) +
        Polynomial.C μ2 * ((15 : K[X]) * g * r ^ 2) -
        Polynomial.C κ3 * ((192 : K[X]) * p1 ^ 2) -
        Polynomial.C μ2 * ((40 : K[X]) * p1 * r)) + h0 *
    (-(8 : K[X]) *
      ((491520 : K[X]) * p0 ^ 2 * r -
        (76800 : K[X]) * p0 * g ^ 4 * r +
        (122880 : K[X]) * p0 * g ^ 3 * p1 +
        Polynomial.C μ * ((10752 : K[X]) * p0 * g * r) -
        Polynomial.C κ3 * ((3072 : K[X]) * p0 * r) -
        Polynomial.C μ * ((43008 : K[X]) * p0 * p1) +
        (3960 : K[X]) * g ^ 8 * r - (5760 : K[X]) * g ^ 7 * p1 -
        Polynomial.C μ * ((819 : K[X]) * g ^ 5 * r) +
        Polynomial.C κ3 * ((240 : K[X]) * g ^ 4 * r) +
        Polynomial.C μ * ((1260 : K[X]) * g ^ 4 * p1) -
        Polynomial.C κ3 * ((384 : K[X]) * g ^ 3 * p1) -
        Polynomial.C μ2 * ((70 : K[X]) * g ^ 3 * r) +
        Polynomial.C μ2 * ((120 : K[X]) * g ^ 2 * p1) +
        Polynomial.C μ3 * ((3 : K[X]) * g * r) -
        Polynomial.C κ7 * ((2 : K[X]) * r) -
        Polynomial.C μ3 * ((12 : K[X]) * p1)) + h0 *
    ((983040 : K[X]) * p0 ^ 2 * g ^ 2 -
      Polynomial.C κ * ((524288 : K[X]) * p0 ^ 2) -
      (71680 : K[X]) * p0 * g ^ 6 +
      Polynomial.C μ * ((17920 : K[X]) * p0 * g ^ 3) -
      Polynomial.C κ3 * ((6144 : K[X]) * p0 * g ^ 2) +
      Polynomial.C μ2 * ((2560 : K[X]) * p0 * g) +
      Polynomial.C κ5 * ((2048 : K[X]) * p0) +
      (2288 : K[X]) * g ^ 10 -
      Polynomial.C μ * ((663 : K[X]) * g ^ 7) +
      Polynomial.C κ3 * ((224 : K[X]) * g ^ 6) -
      Polynomial.C μ2 * ((77 : K[X]) * g ^ 5) +
      Polynomial.C μ3 * ((5 : K[X]) * g ^ 3) -
      Polynomial.C κ7 * ((4 : K[X]) * g ^ 2) +
      Polynomial.C μ4 * g + Polynomial.C κ9 +
      (4194304 : K[X]) * q0)))))

set_option maxHeartbeats 8000000 in
/-- The tenth row closes both alternatives of the preceding ninth split:
the quotient `r=p2/h0` vanishes at the same supplied root. -/
theorem alignedSquareUFactor_tenthRootKill410
    (H h0 u g r p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 : K[X])
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
    (hu : u = h0 * g) (hp2 : p2 = h0 * r)
    (x : K) (hx : h0.eval x = 0) : r.eval x = 0 := by
  have hcore := alignedSquareTenth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14 hM16
  rw [hu, hp2] at hcore
  have hload : alignedSquareUFactorTenthLoad410 h0 g r p0 p1 q0
      κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 5 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore
    simp only [alignedSquareUFactorTenthLoad410, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
      Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination hz
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareUFactorTenthLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

#print axioms alignedSquareUFactor_tenthRootKill410

end Max11DegreeRoutes
