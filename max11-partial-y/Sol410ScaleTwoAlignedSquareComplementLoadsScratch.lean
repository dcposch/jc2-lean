import Sol410ScaleTwoRemainingSquareFacesScratch

/-! # Odd-load collapse on the aligned-square `(4,10)` complement limb -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- The literal quotient left by the ninth square core after
`v=h₀f`, `uf+8p₁=h₀l`, and `μ=0`. -/
def alignedSquareComplementNinthLoad410
    (h0 u f l p0 q1 : K[X])
    (κ κ3 κ5 κ7 μ2 μ3 μ4 : K) : K[X] :=
  -(983040 : K[X]) * p0 ^ 2 * h0 ^ 3 * u -
    (30720 : K[X]) * p0 * f ^ 2 * h0 ^ 3 * u +
    Polynomial.C κ * ((32768 : K[X]) * p0 * f * h0 ^ 3 * u) +
    (61440 : K[X]) * p0 * f * l * h0 ^ 4 -
    Polynomial.C κ * ((32768 : K[X]) * p0 * l * h0 ^ 4) +
    Polynomial.C κ3 * ((6144 : K[X]) * p0 * h0 ^ 3 * u) +
    Polynomial.C μ2 * ((2560 : K[X]) * p0 * h0 ^ 4) +
    (1048576 : K[X]) * q1 * h0 ^ 3 +
    (80 : K[X]) * f ^ 4 * h0 ^ 3 * u -
    (320 : K[X]) * f ^ 3 * l * h0 ^ 4 +
    Polynomial.C κ3 * ((96 : K[X]) * f ^ 2 * h0 ^ 3 * u) +
    Polynomial.C μ2 * ((20 : K[X]) * f ^ 2 * h0 ^ 4) -
    Polynomial.C κ3 * ((192 : K[X]) * f * l * h0 ^ 4) -
    Polynomial.C κ5 * ((64 : K[X]) * f * h0 ^ 3 * u) -
    Polynomial.C μ2 * ((60 : K[X]) * f * h0 ^ 2 * u ^ 2) -
    Polynomial.C μ3 * ((6 : K[X]) * f * h0 ^ 4) +
    Polynomial.C κ5 * ((64 : K[X]) * l * h0 ^ 4) +
    Polynomial.C κ7 * ((4 : K[X]) * h0 ^ 3 * u) -
    (640 : K[X]) * l ^ 3 * h0 ^ 4 +
    Polynomial.C μ2 * ((80 : K[X]) * l * h0 ^ 3 * u) -
    Polynomial.C μ2 * ((5 : K[X]) * u ^ 4) +
    Polynomial.C μ3 * ((3 : K[X]) * h0 ^ 2 * u ^ 2) +
    Polynomial.C μ4 * h0 ^ 4

/-- The ninth load after `μ₂=0`, with its remaining `h₀²` removed. -/
def alignedSquareComplementNinthMu3Quotient410
    (h0 u f l p0 q1 : K[X])
    (κ κ3 κ5 κ7 μ3 μ4 : K) : K[X] :=
  Polynomial.C μ3 * ((3 : K[X]) * u ^ 2) + h0 *
    (-(983040 : K[X]) * p0 ^ 2 * u -
      (30720 : K[X]) * p0 * f ^ 2 * u +
      Polynomial.C κ * ((32768 : K[X]) * p0 * f * u) +
      Polynomial.C κ3 * ((6144 : K[X]) * p0 * u) +
      (1048576 : K[X]) * q1 + (80 : K[X]) * f ^ 4 * u +
      Polynomial.C κ3 * ((96 : K[X]) * f ^ 2 * u) -
      Polynomial.C κ5 * ((64 : K[X]) * f * u) +
      Polynomial.C κ7 * ((4 : K[X]) * u) + h0 *
        ((61440 : K[X]) * p0 * f * l -
          Polynomial.C κ * ((32768 : K[X]) * p0 * l) -
          (320 : K[X]) * f ^ 3 * l -
          Polynomial.C κ3 * ((192 : K[X]) * f * l) +
          Polynomial.C κ5 * ((64 : K[X]) * l) -
          Polynomial.C μ3 * ((6 : K[X]) * f) -
          (640 : K[X]) * l ^ 3 + Polynomial.C μ4))

/-- Compact tenth square core on the same complement substitution. -/
def alignedSquareComplementTenthLoad410
    (h0 u f l p0 q0 : K[X]) (κ κ3 κ5 κ7 κ9 μ4 : K) : K[X] :=
  u * (Polynomial.C μ4 + (1280 : K[X]) * l ^ 3) + h0 *
    ((983040 : K[X]) * p0 ^ 2 * f -
      Polynomial.C κ * ((524288 : K[X]) * p0 ^ 2) -
      (10240 : K[X]) * p0 * f ^ 3 -
      Polynomial.C κ3 * ((6144 : K[X]) * p0 * f) +
      Polynomial.C κ5 * ((2048 : K[X]) * p0) -
      (61440 : K[X]) * p0 * l ^ 2 +
      (4194304 : K[X]) * q0 + (48 : K[X]) * f ^ 5 +
      Polynomial.C κ3 * ((32 : K[X]) * f ^ 3) +
      (960 : K[X]) * f ^ 2 * l ^ 2 -
      Polynomial.C κ7 * ((4 : K[X]) * f) +
      Polynomial.C κ3 * ((192 : K[X]) * l ^ 2) + Polynomial.C κ9)

/-- Compact eleventh square core on the same complement substitution. -/
def alignedSquareComplementEleventhLoad410
    (h0 u f l p0 : K[X]) (κ3 κ7 μ4 μ5 : K) : K[X] :=
  (20480 : K[X]) * l ^ 3 * u ^ 2 +
    Polynomial.C μ4 * ((4 : K[X]) * u ^ 2) + h0 *
      (-(983040 : K[X]) * p0 * l ^ 2 * u +
        (15360 : K[X]) * f ^ 2 * l ^ 2 * u +
        Polynomial.C κ3 * ((3072 : K[X]) * l ^ 2 * u)) + h0 ^ 2 *
      ((15728640 : K[X]) * p0 ^ 2 * l -
        (491520 : K[X]) * p0 * f ^ 2 * l -
        Polynomial.C κ3 * ((98304 : K[X]) * p0 * l) +
        (3840 : K[X]) * f ^ 4 * l +
        Polynomial.C κ3 * ((1536 : K[X]) * f ^ 2 * l) +
        (10240 : K[X]) * f * l ^ 3 +
        Polynomial.C μ4 * ((8 : K[X]) * f) -
        Polynomial.C κ7 * ((64 : K[X]) * l) - Polynomial.C μ5)

set_option maxHeartbeats 8000000 in
/-- Exact CAS-checked odd-load collapse.  No root or source witness is
reselected: all rows use the supplied `h₀,u,v`. -/
theorem alignedSquareComplement_oddLoads410
    [IsAlgClosed K]
    (H h0 u v f l p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 μ5 : K)
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
    (hM16 : alignedTenthDefect410 H p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ9 * H ^ 15)
    (hM18 : alignedEleventhDefect410 H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ5 * h0 ^ 33)
    (hv : u ^ 2 - (4 : K[X]) * p2 = h0 * v)
    (hvf : v = h0 * f) (hL : u * f + (8 : K[X]) * p1 = h0 * l)
    (hμ : μ = 0) (x : K) (hx : h0.eval x = 0) (hux : u.eval x ≠ 0) :
    μ2 = 0 ∧ μ3 = 0 ∧ μ4 = 0 ∧ μ5 = 0 ∧
      ∃ m : K[X], u * f + (8 : K[X]) * p1 = H * m := by
  have ha2 : p2 = Polynomial.C ((4 : K)⁻¹) * (u ^ 2 - h0 ^ 2 * f) := by
    have h4 : (4 : K) ≠ 0 := by norm_num
    rw [hvf] at hv
    have h4p : (4 : K[X]) * p2 = u ^ 2 - h0 ^ 2 * f := by
      linear_combination -hv
    calc
      p2 = 1 * p2 := by rw [one_mul]
      _ = ((4 : K[X]) * Polynomial.C ((4 : K)⁻¹)) * p2 := by
        rw [show (4 : K[X]) * Polynomial.C ((4 : K)⁻¹) = 1 by
          rw [show (4 : K[X]) = Polynomial.C (4 : K) from
            Polynomial.C_eq_natCast 4, ← Polynomial.C_mul,
            mul_inv_cancel₀ h4, Polynomial.C_1]]
      _ = Polynomial.C ((4 : K)⁻¹) * ((4 : K[X]) * p2) := by ring
      _ = Polynomial.C ((4 : K)⁻¹) * (u ^ 2 - h0 ^ 2 * f) := by rw [h4p]
  have ha1 : p1 = Polynomial.C ((8 : K)⁻¹) * (h0 * l - u * f) := by
    have h8 : (8 : K) ≠ 0 := by norm_num
    have h8p : (8 : K[X]) * p1 = h0 * l - u * f := by
      linear_combination hL
    calc
      p1 = 1 * p1 := by rw [one_mul]
      _ = ((8 : K[X]) * Polynomial.C ((8 : K)⁻¹)) * p1 := by
        rw [show (8 : K[X]) * Polynomial.C ((8 : K)⁻¹) = 1 by
          rw [show (8 : K[X]) = Polynomial.C (8 : K) from
            Polynomial.C_eq_natCast 8, ← Polynomial.C_mul,
            mul_inv_cancel₀ h8, Polynomial.C_1]]
      _ = Polynomial.C ((8 : K)⁻¹) * ((8 : K[X]) * p1) := by ring
      _ = Polynomial.C ((8 : K)⁻¹) * (h0 * l - u * f) := by rw [h8p]
  have hcore9 := alignedSquareNinth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14
  rw [hμ, ha2, ha1] at hcore9
  simp only [← mul_assoc] at hcore9
  norm_num [← Polynomial.C_mul] at hcore9
  have hload9 : alignedSquareComplementNinthLoad410 h0 u f l p0 q1
      κ κ3 κ5 κ7 μ2 μ3 μ4 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 5 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore9
    simp only [alignedSquareComplementNinthLoad410, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hz ⊢
    simp only [Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination -hz
  have hload9x := congrArg (fun w : K[X] => w.eval x) hload9
  simp only [alignedSquareComplementNinthLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hload9x
  rw [hx] at hload9x
  norm_num at hload9x
  have hμ2 : μ2 = 0 := hload9x.resolve_right hux
  have hq3 : alignedSquareComplementNinthMu3Quotient410 h0 u f l p0 q1
      κ κ3 κ5 κ7 μ3 μ4 = 0 := by
    have hfac : h0 ^ 2 *
        alignedSquareComplementNinthMu3Quotient410 h0 u f l p0 q1
          κ κ3 κ5 κ7 μ3 μ4 = 0 := by
      rw [hμ2] at hload9
      apply Polynomial.funext
      intro z
      have hz := congrArg (fun w : K[X] => w.eval z) hload9
      simp only [alignedSquareComplementNinthLoad410,
        alignedSquareComplementNinthMu3Quotient410, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hz ⊢
      simp only [Polynomial.eval_zero] at hz ⊢
      norm_num at hz
      linear_combination hz
    exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hh0)
  have hq3x := congrArg (fun w : K[X] => w.eval x) hq3
  simp only [alignedSquareComplementNinthMu3Quotient410,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hq3x
  rw [hx] at hq3x
  norm_num at hq3x
  have hμ3 : μ3 = 0 := hq3x.resolve_right hux
  have hcore10 := alignedSquareTenth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14 hM16
  rw [hμ, hμ2, hμ3, ha2, ha1] at hcore10
  simp only [← mul_assoc] at hcore10
  norm_num [← Polynomial.C_mul] at hcore10
  have hload10 : alignedSquareComplementTenthLoad410 h0 u f l p0 q0
      κ κ3 κ5 κ7 κ9 μ4 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 9 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore10
    simp only [alignedSquareComplementTenthLoad410, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hz ⊢
    simp only [Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination hz
  have hload10x := congrArg (fun w : K[X] => w.eval x) hload10
  simp only [alignedSquareComplementTenthLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hload10x
  rw [hx] at hload10x
  norm_num at hload10x
  have hμ4tie : μ4 + (1280 : K) * l.eval x ^ 3 = 0 := by
    exact hload10x.resolve_left hux
  have hcore11 := alignedSquareEleventh_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM10 hM12 hM14 hM18
  rw [hμ, hμ2, hμ3, ha2, ha1] at hcore11
  simp only [← mul_assoc] at hcore11
  norm_num [← Polynomial.C_mul] at hcore11
  have hload11 : alignedSquareComplementEleventhLoad410 h0 u f l p0
      κ3 κ7 μ4 μ5 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 9 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore11
    set_option maxRecDepth 10000 in
      simp only [alignedSquareComplementEleventhLoad410,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_ofNat] at hz ⊢
    simp only [Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination hz
  have hload11x := congrArg (fun w : K[X] => w.eval x) hload11
  set_option maxRecDepth 10000 in
  simp only [alignedSquareComplementEleventhLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hload11x
  rw [hx] at hload11x
  norm_num at hload11x
  have hl3 : l.eval x ^ 3 = 0 := by
    have hu2 : u.eval x ^ 2 ≠ 0 := pow_ne_zero 2 hux
    have hz : u.eval x ^ 2 * ((15360 : K) * l.eval x ^ 3) = 0 := by
      linear_combination hload11x - (4 * u.eval x ^ 2 : K) * hμ4tie
    have hz' : (15360 : K) * l.eval x ^ 3 = 0 :=
      (mul_eq_zero.mp hz).resolve_left hu2
    exact (mul_eq_zero.mp hz').resolve_left (by norm_num)
  have hlx : l.eval x = 0 :=
    (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hl3
  have hμ4 : μ4 = 0 := by rw [hl3] at hμ4tie; simpa using hμ4tie
  have hrootUnique : ∀ y : K, h0.eval y = 0 → y = x := by
    obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
    intro y hy
    rw [← hlinear] at hx hy
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hx hy
    have hcy : c * (y - x) = 0 := by linear_combination hy - hx
    have hyx : y - x = 0 := (mul_eq_zero.mp hcy).resolve_left hc
    exact sub_eq_zero.mp hyx
  obtain ⟨m, hm⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
    rw [hrootUnique y hy]
    exact hlx)
  have hμ5fac : h0 ^ 2 *
      (-(Polynomial.C μ5) + h0 *
        ((15728640 : K[X]) * p0 ^ 2 * m -
          (491520 : K[X]) * p0 * f ^ 2 * m -
          Polynomial.C κ3 * ((98304 : K[X]) * p0 * m) -
          (983040 : K[X]) * p0 * m ^ 2 * u +
          (3840 : K[X]) * f ^ 4 * m +
          Polynomial.C κ3 * ((1536 : K[X]) * f ^ 2 * m) +
          (15360 : K[X]) * f ^ 2 * m ^ 2 * u +
          (10240 : K[X]) * f * h0 ^ 2 * m ^ 3 +
          Polynomial.C κ3 * ((3072 : K[X]) * m ^ 2 * u) -
          Polynomial.C κ7 * ((64 : K[X]) * m) +
          (20480 : K[X]) * m ^ 3 * u ^ 2)) = 0 := by
    rw [hμ4, hm] at hload11
    unfold alignedSquareComplementEleventhLoad410 at hload11
    simp only [Polynomial.C_0, zero_mul, add_zero] at hload11
    linear_combination hload11
  have hμ5q := (mul_eq_zero.mp hμ5fac).resolve_left (pow_ne_zero 2 hh0)
  have hμ5x := congrArg (fun w : K[X] => w.eval x) hμ5q
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat, hx, zero_mul] at hμ5x
  have hμ5 : μ5 = 0 := by simpa using hμ5x
  refine ⟨hμ2, hμ3, hμ4, hμ5, m, ?_⟩
  rw [hHsq]
  calc
    u * f + (8 : K[X]) * p1 = h0 * l := hL
    _ = h0 ^ 2 * m := by rw [hm]; ring

#print axioms alignedSquareComplement_oddLoads410

end Max11DegreeRoutes
