import Sol410ScaleTwoAlignedSquareComplementLoadsScratch

/-! # Final row for the square complement reduction -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- M11 removes the wall term from M12 globally, so the final complement
invariant is divisible by `H` even when `H` has a double root. -/
theorem alignedSquareComplement_twelfthVDivisor_direct410
    (H p0 g f l : K[X]) (κ3 κ7 κ11 : K)
    (h11 :
      (64 : K[X]) * l *
          alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        (10240 : K[X]) * H * f * l ^ 3 = 0)
    (h12 :
      alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 +
          (320 : K[X]) * g * l *
            alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
          H * alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
          H ^ 2 * alignedTwelfthComplementH5Coefficient410 l = 0) :
    H ∣ alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 := by
  refine ⟨-(alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
      H * alignedTwelfthComplementH5Coefficient410 l -
      (51200 : K[X]) * g * f * l ^ 3), ?_⟩
  linear_combination h12 - (5 : K[X]) * g * h11

set_option maxHeartbeats 8000000 in
/-- The complement final-row cancellation does not require a simple root.
This exact-root form is therefore valid for the double root `H=h₀²`. -/
theorem alignedSquareComplement_finalRow_false_410
    (H p0 p1 p2 q0 q1 g f l v : K[X])
    (κ κ3 κ5 κ7 κ9 κ11 j x : K)
    (hH : H ≠ 0) (hx : H.eval x = 0)
    (hL : g * f + (8 : K[X]) * p1 = H * l)
    (hV : alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 = H * v)
    (h11 :
      (64 : K[X]) * l *
          alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        (10240 : K[X]) * H * f * l ^ 3 = 0)
    (h12 :
      alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 +
          (320 : K[X]) * g * l *
            alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
          H * alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
          H ^ 2 * alignedTwelfthComplementH5Coefficient410 l = 0)
    (h9 : alignedNinthComplementRow410 H p0 q1 g f l κ κ3 κ5 κ7 = 0)
    (h10 : alignedTenthComplementRow410 H p0 q0 g f l
      κ κ3 κ5 κ7 κ9 = 0)
    (hfinal : p0.derivative * q1 - p1 * q0.derivative = Polynomial.C j)
    (hj : j ≠ 0) : False := by
  have hp1x : (8 : K) * p1.eval x = -(g.eval x * f.eval x) := by
    have hev := congrArg (fun w : K[X] => w.eval x) hL
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat] at hev
    rw [hx] at hev
    linear_combination hev
  have hvface := alignedNonsquareTwelfth_complementQuotientRoot_410
    H p0 g f l v κ3 κ7 κ11 x hH hV h11 h12 hx
  have hvderRaw := congrArg Polynomial.derivative hV
  rw [alignedTwelfthComplementV_derivative410] at hvderRaw
  have hvder := congrArg (fun w : K[X] => w.eval x) hvderRaw
  simp only [Polynomial.derivative_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hvder
  rw [hx] at hvder
  norm_num at hvder
  have hVscalar :
      (320 : K) * ((32 : K) * p0.derivative.eval x -
          f.eval x * f.derivative.eval x) *
        (-(245760 : K) * p0.eval x ^ 2 +
          (7680 : K) * p0.eval x * f.eval x ^ 2 +
          (1536 : K) * p0.eval x * κ3 -
          (60 : K) * f.eval x ^ 4 -
          (24 : K) * f.eval x ^ 2 * κ3 + κ7) -
        H.derivative.eval x * v.eval x = 0 := by
    linear_combination hvder
  have h9x := congrArg (fun w : K[X] => w.eval x) h9
  simp only [alignedNinthComplementRow410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at h9x
  rw [hx] at h9x
  norm_num at h9x
  have h10dRaw := congrArg Polynomial.derivative h10
  have h10x := congrArg (fun w : K[X] => w.eval x) h10dRaw
  simp only [alignedTenthComplementRow410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_ofNat,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at h10x
  rw [hx] at h10x
  norm_num at h10x
  have h10scalar :
      (-(10240 : K) * f.eval x ^ 3 -
          (6144 : K) * f.eval x * κ3 +
          (1966080 : K) * f.eval x * p0.eval x -
          (1048576 : K) * κ * p0.eval x + (2048 : K) * κ5) *
          p0.derivative.eval x +
        ((240 : K) * f.eval x ^ 4 +
          (96 : K) * f.eval x ^ 2 * κ3 -
          (30720 : K) * f.eval x ^ 2 * p0.eval x -
          (6144 : K) * κ3 * p0.eval x - (4 : K) * κ7 +
          (983040 : K) * p0.eval x ^ 2) * f.derivative.eval x +
        (4194304 : K) * q0.derivative.eval x +
        H.derivative.eval x *
          ((960 : K) * f.eval x ^ 2 * l.eval x ^ 2 +
            (1280 : K) * g.eval x * l.eval x ^ 3 +
            (192 : K) * κ3 * l.eval x ^ 2 -
            (61440 : K) * l.eval x ^ 2 * p0.eval x) = 0 := by
    linear_combination h10x
  have hfinalx := congrArg (fun w : K[X] => w.eval x) hfinal
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    at hfinalx
  have hfinal8 :
      (8 : K) * p0.derivative.eval x * q1.eval x +
        g.eval x * f.eval x * q0.derivative.eval x = (8 : K) * j := by
    linear_combination (8 : K) * hfinalx + q0.derivative.eval x * hp1x
  have hzero :
      (8 : K) * p0.derivative.eval x * q1.eval x +
        g.eval x * f.eval x * q0.derivative.eval x = 0 := by
    linear_combination
      (-(p0.derivative.eval x) / 32768 : K) * h9x +
      (g.eval x * f.eval x / 4194304 : K) * h10scalar -
      (g.eval x / 335544320 : K) * hVscalar -
      (g.eval x * H.derivative.eval x / 335544320 : K) * hvface
  have hjzero : (8 : K) * j = 0 := by linear_combination hzero - hfinal8
  exact hj ((mul_eq_zero.mp hjzero).resolve_left (by norm_num))

#print axioms alignedSquareComplement_finalRow_false_410
#print axioms alignedSquareComplement_twelfthVDivisor_direct410

end Max11DegreeRoutes
