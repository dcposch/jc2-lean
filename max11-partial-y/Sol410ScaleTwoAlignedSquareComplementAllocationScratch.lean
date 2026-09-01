import Sol410ScaleTwoAlignedSquareComplementFinalRowScratch

/-! # Exact complement allocation on the aligned-square `(4,10)` face -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Ninth square quotient after only `v=h₀f` and `μ=0`.  Its first two
terms are the allocation certificate `5 μ₂u⁴+h₀·640(uf+8p₁)³`. -/
def alignedSquareVFactorNinthLoad410
    (h0 u f p0 p1 q1 : K[X])
    (κ κ3 κ5 κ7 μ2 μ3 μ4 : K) : K[X] :=
  Polynomial.C μ2 * ((5 : K[X]) * u ^ 4) + h0 *
    ((640 : K[X]) * (u * f + (8 : K[X]) * p1) ^ 3 + h0 *
      (-Polynomial.C μ2 * ((20 : K[X]) * f * u ^ 2) -
        Polynomial.C μ2 * ((640 : K[X]) * p1 * u) -
        Polynomial.C μ3 * ((3 : K[X]) * u ^ 2) + h0 *
        ((983040 : K[X]) * p0 ^ 2 * u -
          (30720 : K[X]) * p0 * f ^ 2 * u -
          (491520 : K[X]) * p0 * f * p1 +
          Polynomial.C κ * ((262144 : K[X]) * p0 * p1) -
          Polynomial.C κ3 * ((6144 : K[X]) * p0 * u) -
          (1048576 : K[X]) * q1 + (240 : K[X]) * f ^ 4 * u +
          (2560 : K[X]) * f ^ 3 * p1 +
          Polynomial.C κ3 * ((96 : K[X]) * f ^ 2 * u) +
          Polynomial.C κ3 * ((1536 : K[X]) * f * p1) -
          Polynomial.C κ5 * ((512 : K[X]) * p1) -
          Polynomial.C κ7 * ((4 : K[X]) * u) + h0 *
          (-Polynomial.C μ2 * ((2560 : K[X]) * p0) -
            Polynomial.C μ2 * ((20 : K[X]) * f ^ 2) +
            Polynomial.C μ3 * ((6 : K[X]) * f) - Polynomial.C μ4))))

/-- The quotient left after the ninth allocation kills `μ₂` and cancels the
supplied nonzero `h0`.  Keeping it opaque avoids elaborating the large tail
inside `mul_eq_zero`. -/
def alignedSquareVFactorNinthMu2Quotient410
    (h0 u f p0 p1 q1 : K[X])
    (κ κ3 κ5 μ3 κ7 μ4 : K) : K[X] :=
  (640 : K[X]) * (u * f + (8 : K[X]) * p1) ^ 3 + h0 *
    (-Polynomial.C μ3 * ((3 : K[X]) * u ^ 2) + h0 *
      ((983040 : K[X]) * p0 ^ 2 * u -
        (30720 : K[X]) * p0 * f ^ 2 * u -
        (491520 : K[X]) * p0 * f * p1 +
        Polynomial.C κ * ((262144 : K[X]) * p0 * p1) -
        Polynomial.C κ3 * ((6144 : K[X]) * p0 * u) -
        (1048576 : K[X]) * q1 + (240 : K[X]) * f ^ 4 * u +
        (2560 : K[X]) * f ^ 3 * p1 +
        Polynomial.C κ3 * ((96 : K[X]) * f ^ 2 * u) +
        Polynomial.C κ3 * ((1536 : K[X]) * f * p1) -
        Polynomial.C κ5 * ((512 : K[X]) * p1) -
        Polynomial.C κ7 * ((4 : K[X]) * u) + h0 *
          (Polynomial.C μ3 * ((6 : K[X]) * f) - Polynomial.C μ4)))

set_option maxHeartbeats 8000000 in
/-- The supplied `v`-factor branch allocates canonically to the complement:
the ninth row first kills `μ₂`, then forces `h₀ ∣ uf+8p₁`. -/
theorem alignedSquareVFactor_complementAllocation410
    [IsAlgClosed K]
    (H h0 u v f p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 : K[X])
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
    (hvf : v = h0 * f) (hμ : μ = 0)
    (x : K) (hx : h0.eval x = 0) (hux : u.eval x ≠ 0) :
    μ2 = 0 ∧ ∃ l : K[X], u * f + (8 : K[X]) * p1 = h0 * l := by
  have hcore := alignedSquareNinth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14
  obtain ⟨s5, s6, s7, s8, s9, hs5, hs6, hs7, hs8, _hs9, _hq1⟩ :=
    alignedSquareNinth_solved_410 hh0 hcore hv
  have hkilla : u.eval x ^ 2 = (4 : K) * p2.eval x := by
    have hev := congrArg (fun w : K[X] => w.eval x) hv
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
    rw [hx, zero_mul] at hev
    linear_combination hev
  let A : K[X] := (80 : K[X]) * u *
    ((11 : K[X]) * u ^ 2 - (12 : K[X]) * p2) * f ^ 3
  let B : K[X] := (2560 : K[X]) * p1 *
    ((7 : K[X]) * u ^ 2 - (4 : K[X]) * p2) * f ^ 2
  have hs5fac : s5 = h0 ^ 2 * A := by
    rw [hμ, hvf] at hs5
    simp only [Polynomial.C_0, zero_mul, sub_zero] at hs5
    apply mul_left_cancel₀ hh0
    dsimp only [A]
    linear_combination -hs5
  have hs6fac : s6 = h0 * (A + B) := by
    rw [hs5fac, hvf] at hs6
    apply mul_left_cancel₀ hh0
    dsimp only [A, B]
    linear_combination -hs6
  have hE :
      (35 : K) * u.eval x ^ 4 -
          (240 : K) * p2.eval x * u.eval x ^ 2 +
          (320 : K) * p2.eval x ^ 2 = -(5 : K) * u.eval x ^ 4 := by
    linear_combination
      ((40 : K) * u.eval x ^ 2 - (80 : K) * p2.eval x) * hkilla
  have hs7x := congrArg (fun w : K[X] => w.eval x) hs7
  rw [hs6fac, hvf, hμ] at hs7x
  simp only [Polynomial.C_0, zero_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hs7x
  rw [hx] at hs7x
  norm_num at hs7x
  rw [hE] at hs7x
  norm_num at hs7x
  have hμ2 : μ2 = 0 := hs7x.resolve_right hux
  have hs7fac : s7 = A + B + (122880 : K[X]) * p1 ^ 2 * u * f := by
    rw [hs6fac, hvf, hμ, hμ2] at hs7
    simp only [Polynomial.C_0, zero_mul, sub_zero] at hs7
    apply mul_left_cancel₀ hh0
    dsimp only [A, B]
    linear_combination -hs7
  have hs8x := congrArg (fun w : K[X] => w.eval x) hs8
  rw [hs7fac, hvf] at hs8x
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hs8x
  rw [hx] at hs8x
  norm_num at hs8x
  dsimp only [A, B] at hs8x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat] at hs8x
  have hcube : (640 : K) *
      (u.eval x * f.eval x + (8 : K) * p1.eval x) ^ 3 = 0 := by
    linear_combination hs8x -
      ((240 : K) * u.eval x * f.eval x ^ 3 +
        (2560 : K) * p1.eval x * f.eval x ^ 2) * hkilla
  have hL3 : (u.eval x * f.eval x + (8 : K) * p1.eval x) ^ 3 = 0 :=
    (mul_eq_zero.mp hcube).resolve_left (by norm_num)
  have hLscalar : u.eval x * f.eval x + (8 : K) * p1.eval x = 0 :=
    (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hL3
  have hLx : (u * f + (8 : K[X]) * p1).eval x = 0 := by
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat] using hLscalar
  have hrootUnique : ∀ y : K, h0.eval y = 0 → y = x := by
    obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
    intro y hy
    rw [← hlinear] at hx hy
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hx hy
    have hcy : c * (y - x) = 0 := by linear_combination hy - hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hcy).resolve_left hc)
  obtain ⟨l, hl⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
    rw [hrootUnique y hy]
    exact hLx)
  exact ⟨hμ2, l, hl⟩

#print axioms alignedSquareVFactor_complementAllocation410

end Max11DegreeRoutes
