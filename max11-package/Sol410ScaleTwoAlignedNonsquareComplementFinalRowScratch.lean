import Sol410ScaleTwoAlignedNonsquareComplementTwelfthScratch

/-! # Final Keller row on the complementary aligned `(4,10)` branch -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- The ninth-row quotient after `4p₂=g²-Hf` and `8p₁=Hl-gf`. -/
def alignedNinthComplementRow410
    (H p0 q1 g f l : K[X]) (κ κ3 κ5 κ7 : K) : K[X] :=
  (160 : K[X]) * H ^ 2 * l ^ 3 +
    H * ((80 : K[X]) * f ^ 3 * l +
      (48 : K[X]) * f * Polynomial.C κ3 * l -
      (15360 : K[X]) * f * l * p0 +
      (8192 : K[X]) * Polynomial.C κ * l * p0 -
      (16 : K[X]) * Polynomial.C κ5 * l) +
    g * (-(20 : K[X]) * f ^ 4 -
      (24 : K[X]) * f ^ 2 * Polynomial.C κ3 +
      (7680 : K[X]) * f ^ 2 * p0 -
      (8192 : K[X]) * f * Polynomial.C κ * p0 +
      (16 : K[X]) * f * Polynomial.C κ5 -
      (1536 : K[X]) * Polynomial.C κ3 * p0 - Polynomial.C κ7 +
      (245760 : K[X]) * p0 ^ 2) - (262144 : K[X]) * q1

/-- The tenth-row quotient after the same complementary substitution. -/
def alignedTenthComplementRow410
    (H p0 q0 g f l : K[X]) (κ κ3 κ5 κ7 κ9 : K) : K[X] :=
  (48 : K[X]) * f ^ 5 +
    (32 : K[X]) * f ^ 3 * Polynomial.C κ3 -
    (10240 : K[X]) * f ^ 3 * p0 -
    (6144 : K[X]) * f * Polynomial.C κ3 * p0 -
    (4 : K[X]) * f * Polynomial.C κ7 +
    (983040 : K[X]) * f * p0 ^ 2 -
    (524288 : K[X]) * Polynomial.C κ * p0 ^ 2 +
    (2048 : K[X]) * Polynomial.C κ5 * p0 + Polynomial.C κ9 +
    (4194304 : K[X]) * q0 +
    H * ((960 : K[X]) * f ^ 2 * l ^ 2 +
      (1280 : K[X]) * g * l ^ 3 +
      (192 : K[X]) * Polynomial.C κ3 * l ^ 2 -
      (61440 : K[X]) * l ^ 2 * p0)

set_option maxHeartbeats 4000000 in
/-- Exact complementary cancellation of the already-solved ninth row. -/
theorem alignedNonsquareNinth_complementSolved_410
    (H p0 p1 p2 q1 g f l : K[X]) (κ κ3 κ5 κ7 : K)
    (hH : H ≠ 0)
    (hgf : g ^ 2 - (4 : K[X]) * p2 = H * f)
    (hL : g * f + (8 : K[X]) * p1 = H * l)
    (hrow :
      (80 : K[X]) * g * ((11 : K[X]) * g ^ 2 -
            (12 : K[X]) * p2) * f ^ 3 +
        (2560 : K[X]) * p1 * ((7 : K[X]) * g ^ 2 -
            (4 : K[X]) * p2) * f ^ 2 +
        (122880 : K[X]) * p1 ^ 2 * g * f +
        (327680 : K[X]) * p1 ^ 3 =
      H * ((((30720 : K[X]) * p0 - Polynomial.C κ3 * (96 : K[X])) *
            g * f ^ 2) +
        ((491520 : K[X]) * p0 - Polynomial.C κ3 * (1536 : K[X])) *
          p1 * f + (1048576 : K[X]) * q1 +
        Polynomial.C κ7 * ((4 : K[X]) * g) +
        Polynomial.C κ5 * ((512 : K[X]) * p1) +
        Polynomial.C κ3 * ((6144 : K[X]) * p0 * g) -
        (983040 : K[X]) * p0 ^ 2 * g -
        Polynomial.C κ * ((262144 : K[X]) * p0 * p1))) :
    alignedNinthComplementRow410 H p0 q1 g f l κ κ3 κ5 κ7 = 0 := by
  let U : K[X] := (8 : K[X]) * p1
  let V : K[X] := (4 : K[X]) * p2
  have hscaled :
      (80 : K[X]) * g * ((11 : K[X]) * g ^ 2 -
            (3 : K[X]) * V) * f ^ 3 +
        (320 : K[X]) * U * ((7 : K[X]) * g ^ 2 - V) * f ^ 2 +
        (1920 : K[X]) * U ^ 2 * g * f + (640 : K[X]) * U ^ 3 =
      H * ((((30720 : K[X]) * p0 - Polynomial.C κ3 * (96 : K[X])) *
            g * f ^ 2) +
        ((61440 : K[X]) * p0 - Polynomial.C κ3 * (192 : K[X])) *
          U * f + (1048576 : K[X]) * q1 +
        Polynomial.C κ7 * ((4 : K[X]) * g) +
        Polynomial.C κ5 * ((64 : K[X]) * U) +
        Polynomial.C κ3 * ((6144 : K[X]) * p0 * g) -
        (983040 : K[X]) * p0 ^ 2 * g -
        Polynomial.C κ * ((32768 : K[X]) * p0 * U)) := by
    dsimp only [U, V]
    linear_combination hrow
  have hU : U = H * l - g * f := by
    dsimp only [U]
    linear_combination hL
  have hV : V = g ^ 2 - H * f := by
    dsimp only [V]
    linear_combination -hgf
  rw [hU, hV] at hscaled
  have hfactored :
      H * ((4 : K[X]) *
        alignedNinthComplementRow410 H p0 q1 g f l κ κ3 κ5 κ7) = 0 := by
    simp only [alignedNinthComplementRow410]
    linear_combination hscaled
  have hfour := (mul_eq_zero.mp hfactored).resolve_left hH
  exact (mul_eq_zero.mp hfour).resolve_left (by norm_num)

set_option maxHeartbeats 4000000 in
/-- Exact complementary cancellation of the already-solved tenth row. -/
theorem alignedNonsquareTenth_complementSolved_410
    (H p0 p1 p2 q0 g f l : K[X]) (κ κ3 κ5 κ7 κ9 : K)
    (hH : H ≠ 0)
    (hgf : g ^ 2 - (4 : K[X]) * p2 = H * f)
    (hL : g * f + (8 : K[X]) * p1 = H * l)
    (hrow :
      (16 : K[X]) * ((143 : K[X]) * g ^ 4 -
            (264 : K[X]) * p2 * g ^ 2 + (48 : K[X]) * p2 ^ 2) * f ^ 3 +
        (15360 : K[X]) * p1 * g * ((3 : K[X]) * g ^ 2 -
            (4 : K[X]) * p2) * f ^ 2 +
        (245760 : K[X]) * p1 ^ 2 * g ^ 2 * f +
        (655360 : K[X]) * p1 ^ 3 * g =
      H * (((((61440 : K[X]) * p0 - Polynomial.C κ3 * (192 : K[X])) *
            g ^ 2 - (61440 : K[X]) * p1 ^ 2) * f ^ 2) +
        ((983040 : K[X]) * p0 - Polynomial.C κ3 * (3072 : K[X])) *
          g * p1 * f +
        ((3932160 : K[X]) * p0 - Polynomial.C κ3 * (12288 : K[X])) *
          p1 ^ 2 +
        H * (((10240 : K[X]) * p0 - Polynomial.C κ3 * (32 : K[X])) *
            f ^ 3 +
          (Polynomial.C κ3 * ((6144 : K[X]) * p0) +
            Polynomial.C κ7 * (4 : K[X]) - (983040 : K[X]) * p0 ^ 2) *
            f + Polynomial.C κ * ((524288 : K[X]) * p0 ^ 2) -
          Polynomial.C κ5 * ((2048 : K[X]) * p0) - Polynomial.C κ9 -
          (4194304 : K[X]) * q0))) :
    alignedTenthComplementRow410 H p0 q0 g f l κ κ3 κ5 κ7 κ9 = 0 := by
  let U : K[X] := (8 : K[X]) * p1
  let V : K[X] := (4 : K[X]) * p2
  have hscaled :
      (16 : K[X]) * ((143 : K[X]) * g ^ 4 -
            (66 : K[X]) * V * g ^ 2 + (3 : K[X]) * V ^ 2) * f ^ 3 +
        (1920 : K[X]) * U * g * ((3 : K[X]) * g ^ 2 - V) * f ^ 2 +
        (3840 : K[X]) * U ^ 2 * g ^ 2 * f +
        (1280 : K[X]) * U ^ 3 * g =
      H * (((((61440 : K[X]) * p0 - Polynomial.C κ3 * (192 : K[X])) *
            g ^ 2 - (960 : K[X]) * U ^ 2) * f ^ 2) +
        ((122880 : K[X]) * p0 - Polynomial.C κ3 * (384 : K[X])) *
          g * U * f +
        ((61440 : K[X]) * p0 - Polynomial.C κ3 * (192 : K[X])) * U ^ 2 +
        H * (((10240 : K[X]) * p0 - Polynomial.C κ3 * (32 : K[X])) *
            f ^ 3 +
          (Polynomial.C κ3 * ((6144 : K[X]) * p0) +
            Polynomial.C κ7 * (4 : K[X]) - (983040 : K[X]) * p0 ^ 2) *
            f + Polynomial.C κ * ((524288 : K[X]) * p0 ^ 2) -
          Polynomial.C κ5 * ((2048 : K[X]) * p0) - Polynomial.C κ9 -
          (4194304 : K[X]) * q0)) := by
    dsimp only [U, V]
    linear_combination hrow
  have hU : U = H * l - g * f := by
    dsimp only [U]
    linear_combination hL
  have hV : V = g ^ 2 - H * f := by
    dsimp only [V]
    linear_combination -hgf
  rw [hU, hV] at hscaled
  have hfactored :
      H ^ 2 * alignedTenthComplementRow410 H p0 q0 g f l
        κ κ3 κ5 κ7 κ9 = 0 := by
    simp only [alignedTenthComplementRow410]
    linear_combination hscaled
  exact (mul_eq_zero.mp hfactored).resolve_left (pow_ne_zero 2 hH)

/-- Factored derivative of the twelfth complement invariant. -/
theorem alignedTwelfthComplementV_derivative410
    (p0 f : K[X]) (κ3 κ7 κ11 : K) :
    (alignedTwelfthComplementV410 p0 f κ3 κ7 κ11).derivative =
      (320 : K[X]) * ((32 : K[X]) * p0.derivative - f * f.derivative) *
        (-(245760 : K[X]) * p0 ^ 2 +
          (7680 : K[X]) * p0 * f ^ 2 +
          (1536 : K[X]) * p0 * Polynomial.C κ3 -
          (60 : K[X]) * f ^ 4 -
          (24 : K[X]) * f ^ 2 * Polynomial.C κ3 + Polynomial.C κ7) := by
  simp only [alignedTwelfthComplementV410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_ofNat]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_zero]
  ring

/-- M11 and M12 identify the value of the exact quotient `V/H` at every
root of `H`. -/
theorem alignedNonsquareTwelfth_complementQuotientRoot_410
    (H p0 g f l v : K[X]) (κ3 κ7 κ11 x : K)
    (hH : H ≠ 0)
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
    (hx : H.eval x = 0) :
    v.eval x + (5120 : K) * f.eval x * l.eval x ^ 2 *
      (-(960 : K) * p0.eval x + (15 : K) * f.eval x ^ 2 +
        (20 : K) * g.eval x * l.eval x + (3 : K) * κ3) = 0 := by
  have hcancel :
      H * (v + alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
        H * alignedTwelfthComplementH5Coefficient410 l -
        (51200 : K[X]) * g * f * l ^ 3) = 0 := by
    rw [hV] at h12
    linear_combination h12 - (5 : K[X]) * g * h11
  have hquot := (mul_eq_zero.mp hcancel).resolve_left hH
  have hev := congrArg (fun w : K[X] => w.eval x) hquot
  simp only [alignedTwelfthComplementH4Coefficient410,
    alignedTwelfthComplementH5Coefficient410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hev
  rw [hx] at hev
  norm_num at hev
  linear_combination hev

set_option maxHeartbeats 4000000 in
/-- The exact complement packet makes the final Keller row vanish at a simple
root, contradicting its nonzero constant value. -/
theorem alignedNonsquareComplement_finalRow_false_410
    [IsAlgClosed K]
    (H p0 p1 p2 q0 q1 g f l v : K[X])
    (κ κ3 κ5 κ7 κ9 κ11 j : K)
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
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
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root H hdegne
  have hdx : H.derivative.eval x ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq hx
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

#print axioms alignedNonsquareNinth_complementSolved_410
#print axioms alignedNonsquareTenth_complementSolved_410
#print axioms alignedTwelfthComplementV_derivative410
#print axioms alignedNonsquareTwelfth_complementQuotientRoot_410
#print axioms alignedNonsquareComplement_finalRow_false_410

end Max11DegreeRoutes
