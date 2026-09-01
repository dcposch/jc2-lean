import Sol410ScaleTwoAlignedSquareComplementFinalRowScratch

/-! # Ninth-row allocation on the aligned-square `u`-factor limb -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Exact quotient after substituting `u=h0*g` and `p2=h0*r` in the square
ninth core and cancelling `h0^5`.  Its root value is precisely
`20480*r^3*(3*g*r-8*p1)`. -/
def alignedSquareUFactorNinthLoad410
    (h0 g r p0 p1 q1 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 : K) : K[X] :=
  (61440 : K[X]) * g * r ^ 4 - (163840 : K[X]) * p1 * r ^ 3 + h0 *
    (-(102400 : K[X]) * g ^ 3 * r ^ 3 +
      (368640 : K[X]) * g ^ 2 * p1 * r ^ 2 -
      (491520 : K[X]) * g * p1 ^ 2 * r +
      Polynomial.C μ * ((3584 : K[X]) * r ^ 3) +
      (327680 : K[X]) * p1 ^ 3 + h0 *
      (-(491520 : K[X]) * p0 * g * r ^ 2 +
        (1966080 : K[X]) * p0 * p1 * r +
        (53760 : K[X]) * g ^ 5 * r ^ 2 -
        (153600 : K[X]) * g ^ 4 * p1 * r +
        (122880 : K[X]) * g ^ 3 * p1 ^ 2 +
        Polynomial.C κ3 * ((1536 : K[X]) * g * r ^ 2) -
        Polynomial.C μ * ((6720 : K[X]) * g ^ 2 * r ^ 2) +
        Polynomial.C μ * ((21504 : K[X]) * g * p1 * r) -
        Polynomial.C κ3 * ((6144 : K[X]) * p1 * r) -
        Polynomial.C μ * ((43008 : K[X]) * p1 ^ 2) -
        Polynomial.C μ2 * ((320 : K[X]) * r ^ 2) + h0 *
        ((245760 : K[X]) * p0 * g ^ 3 * r -
          (491520 : K[X]) * p0 * g ^ 2 * p1 +
          Polynomial.C κ * ((262144 : K[X]) * p0 * p1) -
          Polynomial.C μ * ((86016 : K[X]) * p0 * r) -
          (1048576 : K[X]) * q1 -
          (11520 : K[X]) * g ^ 7 * r +
          (17920 : K[X]) * g ^ 6 * p1 +
          Polynomial.C μ * ((2520 : K[X]) * g ^ 4 * r) -
          Polynomial.C κ3 * ((768 : K[X]) * g ^ 3 * r) -
          Polynomial.C μ * ((4480 : K[X]) * g ^ 3 * p1) +
          Polynomial.C κ3 * ((1536 : K[X]) * g ^ 2 * p1) +
          Polynomial.C μ2 * ((240 : K[X]) * g ^ 2 * r) -
          Polynomial.C μ2 * ((640 : K[X]) * g * p1) -
          Polynomial.C κ5 * ((512 : K[X]) * p1) -
          Polynomial.C μ3 * ((24 : K[X]) * r) + h0 *
          ((983040 : K[X]) * p0 ^ 2 * g -
            (30720 : K[X]) * p0 * g ^ 5 +
            Polynomial.C μ * ((10752 : K[X]) * p0 * g ^ 2) -
            Polynomial.C κ3 * ((6144 : K[X]) * p0 * g) -
            Polynomial.C μ2 * ((2560 : K[X]) * p0) +
            (880 : K[X]) * g ^ 9 -
            Polynomial.C μ * ((273 : K[X]) * g ^ 6) +
            Polynomial.C κ3 * ((96 : K[X]) * g ^ 5) -
            Polynomial.C μ2 * ((35 : K[X]) * g ^ 4) +
            Polynomial.C μ3 * ((3 : K[X]) * g ^ 2) -
            Polynomial.C κ7 * ((4 : K[X]) * g) - Polynomial.C μ4))))

set_option maxHeartbeats 8000000 in
/-- The exact ninth quotient splits the `u`-factor branch into the two honest
source divisors `h0 ∣ r` and `h0 ∣ (3*g*r-8*p1)`, stated first at the
supplied root. -/
theorem alignedSquareUFactor_ninthRootSplit410
    (H h0 u g r p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 : K)
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
    (hu : u = h0 * g) (hp2 : p2 = h0 * r)
    (x : K) (hx : h0.eval x = 0) :
    r.eval x = 0 ∨
      (3 : K) * g.eval x * r.eval x - (8 : K) * p1.eval x = 0 := by
  have hcore := alignedSquareNinth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14
  rw [hu, hp2] at hcore
  have hload : alignedSquareUFactorNinthLoad410 h0 g r p0 p1 q1
      κ μ κ3 μ2 κ5 μ3 κ7 μ4 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 5 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore
    simp only [alignedSquareUFactorNinthLoad410, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
      Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination hz
  have hloadx := congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareUFactorNinthLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  have hfactor : (20480 : K) * r.eval x ^ 3 *
      ((3 : K) * g.eval x * r.eval x - (8 : K) * p1.eval x) = 0 := by
    linear_combination hloadx
  rcases mul_eq_zero.mp hfactor with hrpre | hcomp
  · have hr3 : r.eval x ^ 3 = 0 :=
      (mul_eq_zero.mp hrpre).resolve_left (by norm_num)
    exact Or.inl ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hr3)
  · exact Or.inr hcomp

set_option maxHeartbeats 2000000 in
/-- A zero of the exact supplied `u` forces the exact supplied `p2` to vanish
at the same root, hence both are divisible by the supplied degree-one `h0`.
The ninth quotient then gives the next divisor split without changing root or
witness. -/
theorem alignedSquareUFactor_allocation410
    [IsAlgClosed K]
    (H h0 u v p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 : K)
    (hh0 : h0 ≠ 0) (hdeg : h0.natDegree = 1)
    (hHsq : H = h0 ^ 2) (hp3 : p3 = h0 ^ 2 * u)
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
    (hv : u ^ 2 - (4 : K[X]) * p2 = h0 * v)
    (x : K) (hx : h0.eval x = 0) (hux : u.eval x = 0) :
    ∃ g r : K[X], u = h0 * g ∧ p2 = h0 * r ∧
      (r.eval x = 0 ∨
        (3 : K) * g.eval x * r.eval x - (8 : K) * p1.eval x = 0) := by
  have hp2x : p2.eval x = 0 := by
    have hev := congrArg (fun w : K[X] => w.eval x) hv
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
    rw [hx, hux] at hev
    norm_num at hev
    exact hev
  have hrootUnique : ∀ y : K, h0.eval y = 0 → y = x := by
    obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
    intro y hy
    rw [← hlinear] at hx hy
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hx hy
    have hcy : c * (y - x) = 0 := by linear_combination hy - hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hcy).resolve_left hc)
  obtain ⟨g, hu⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
    rw [hrootUnique y hy]
    exact hux)
  obtain ⟨r, hp2⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
    rw [hrootUnique y hy]
    exact hp2x)
  refine ⟨g, r, hu, hp2, ?_⟩
  exact alignedSquareUFactor_ninthRootSplit410
    H h0 u g r p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7
      κ μ κ3 μ2 κ5 μ3 κ7 μ4 hh0 hHsq hp3 hM2 hM4 hM6 hM8 hM10
      hM12 hM14 hu hp2 x hx

#print axioms alignedSquareUFactor_ninthRootSplit410
#print axioms alignedSquareUFactor_allocation410

end Max11DegreeRoutes
