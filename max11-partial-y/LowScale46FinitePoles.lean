import LowScale46PolynomialEndgame

/-! # Finite-pole exclusion for the `(4,6)` mismatch chart

This module instantiates the exact local-chart equations on rational-exponent
Hahn series.  It proves the valuation steps in the mismatch branch, including
the full higher-order remainder behind the first `J₂` face.
-/

noncomputable section

namespace Max11DegreeRoutes

section HahnOrderCalculus

variable {k : Type*} [Field k]

private theorem hahn_ne_zero_of_orderTop_eq_coe46
    (x : HahnSeries ℚ k) (a : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ)) : x ≠ 0 := by
  intro h
  rw [h, HahnSeries.orderTop_zero] at hx
  exact WithTop.coe_ne_top hx.symm

/-- Exact finite Hahn orders add under multiplication. -/
theorem hahnOrderTop_mul_eq46
    (x y : HahnSeries ℚ k) (a b : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ))
    (hy : y.orderTop = (↑b : WithTop ℚ)) :
    (x * y).orderTop = (↑(a + b) : WithTop ℚ) := by
  rw [HahnSeries.orderTop_mul, hx, hy, ← WithTop.coe_add]

/-- Exact finite Hahn orders scale under natural powers. -/
theorem hahnOrderTop_pow_eq46
    (x : HahnSeries ℚ k) (a : ℚ) (n : ℕ)
    (hx : x.orderTop = (↑a : WithTop ℚ)) :
    (x ^ n).orderTop = (↑((n : ℚ) * a) : WithTop ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, hahnOrderTop_mul_eq46 _ _ _ _ ih hx]
      rw [Nat.cast_succ, add_mul, one_mul]

/-- Exact leading coefficients multiply with exact finite Hahn orders. -/
theorem hahnLeadingCoeff_mul46
    (x y : HahnSeries ℚ k) :
    (x * y).leadingCoeff = x.leadingCoeff * y.leadingCoeff :=
  HahnSeries.leadingCoeff_mul x y

/-- Adding two terms which both lie strictly above an order keeps their sum
strictly above that order. -/
theorem hahnOrderTop_add_gt46
    (e : ℚ) (x y : HahnSeries ℚ k)
    (hx : (↑e : WithTop ℚ) < x.orderTop)
    (hy : (↑e : WithTop ℚ) < y.orderTop) :
    (↑e : WithTop ℚ) < (x + y).orderTop :=
  (lt_min hx hy).trans_le HahnSeries.min_orderTop_le_orderTop_add

/-- Multiplication by an arbitrary scalar constant preserves a strict lower
bound on a finite Hahn order (and sends a zero scalar to order `⊤`). -/
theorem hahnOrderTop_C_mul_gt46
    (c : k) (x : HahnSeries ℚ k) (e a : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ)) (hea : e < a) :
    (↑e : WithTop ℚ) < (HahnSeries.C c * x).orderTop := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [HahnSeries.orderTop_mul, HahnSeries.C_apply,
      HahnSeries.orderTop_single hc, hx]
    norm_num
    exact hea

/-- A nonzero scalar constant does not change an exact finite Hahn order. -/
theorem hahnOrderTop_C_mul_eq46
    (c : k) (x : HahnSeries ℚ k) (a : ℚ) (hc : c ≠ 0)
    (hx : x.orderTop = (↑a : WithTop ℚ)) :
    (HahnSeries.C c * x).orderTop = (↑a : WithTop ℚ) := by
  rw [HahnSeries.orderTop_mul, HahnSeries.C_apply,
    HahnSeries.orderTop_single hc, hx]
  norm_num

/-- At an exact finite order, the coefficient at that order is the Hahn
leading coefficient. -/
theorem hahnCoeff_eq_leadingCoeff_of_orderTop_eq46
    (x : HahnSeries ℚ k) (a : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ)) :
    x.coeff a = x.leadingCoeff := by
  have hx0 := hahn_ne_zero_of_orderTop_eq_coe46 x a hx
  have hord : x.order = a := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hx0, hx]
  rw [HahnSeries.leadingCoeff_eq, hord]

/-- A term with exact order one and a term with exact order `v`, modulo a
remainder of order strictly above one, can sum to zero only when `v=1`.
The leading coefficients then cancel at order one. -/
theorem hahnOrder_eq_one_of_two_terms_add_higher_eq_zero46
    (p q r : HahnSeries ℚ k) (v : ℚ)
    (hp : p.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hq : q.orderTop = (↑v : WithTop ℚ))
    (hr : (↑(1 : ℚ) : WithTop ℚ) < r.orderTop)
    (hsum : p + q + r = 0) :
    v = 1 ∧ p.coeff 1 + q.coeff 1 = 0 := by
  have hv : v = 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hvlt | hvgt
    · have hp0 : p.coeff v = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hp]
        exact WithTop.coe_lt_coe.mpr hvlt)
      have hr0 : r.coeff v = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        exact (WithTop.coe_lt_coe.mpr hvlt).trans hr)
      have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff v) hsum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hp0, hr0,
        zero_add, add_zero] at hcoeff
      exact HahnSeries.coeff_orderTop_ne hq hcoeff
    · have hq0 : q.coeff 1 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hq]
        exact WithTop.coe_lt_coe.mpr hvgt)
      have hr0 : r.coeff 1 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr
      have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff 1) hsum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hq0, hr0,
        add_zero] at hcoeff
      exact HahnSeries.coeff_orderTop_ne hp hcoeff
  subst v
  have hr0 : r.coeff 1 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr
  have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff 1) hsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hr0, add_zero] at hcoeff
  exact ⟨rfl, hcoeff⟩

end HahnOrderCalculus

section MismatchJTwoFace

variable {k : Type*} [Field k]

/-- Every term of the full mismatch `J₂` chart except `-5Ls/4` and
`-3YZ/4`.  Keeping this literal remainder makes the absence of truncation
kernel-visible. -/
def mismatchJTwoHigher46
    (L beta gamma delta k2 : k)
    (s Q Y Z : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C ((15 / 4 : k) * L) * (Q * s) +
    HahnSeries.C ((3 / 2 : k) * beta) * s ^ 3 +
    HahnSeries.C ((-15 / 4 : k) * L) * (Q ^ 2 * s) +
    HahnSeries.C (-3 * beta) * (Q * s ^ 3) +
    HahnSeries.C ((5 / 8 : k) * L) * (Z * s) +
    HahnSeries.C (-2 * delta) * s ^ 5 +
    HahnSeries.C ((5 / 4 : k) * L) * (Q ^ 3 * s) +
    HahnSeries.C ((3 / 2 : k) * beta) * (Q ^ 2 * s ^ 3) +
    HahnSeries.C ((-5 / 8 : k) * L) * (Q * Z * s) +
    HahnSeries.C (2 * delta) * (Q * s ^ 5) +
    HahnSeries.C ((5 / 8 : k) * L) * (Y ^ 2 * s) +
    HahnSeries.C (2 * gamma) * (Y * s ^ 4) +
    HahnSeries.C ((-3 / 4 : k) * beta) * (Z * s ^ 3) +
    HahnSeries.C (-k2) * s ^ 7

/-- Exact decomposition of the full local `J₂` row into its two possible
lowest terms and the displayed higher remainder. -/
theorem localChartJTwo46_eq_mismatch_faces
    (L beta gamma delta k2 : k)
    (s Q Y Z : HahnSeries ℚ k) :
    localChartJTwo46 (HahnSeries.C L) s Q Y Z
        (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C k2) =
      HahnSeries.C ((-5 / 4 : k) * L) * s +
        HahnSeries.C (-3 / 4 : k) * (Y * Z) +
        mismatchJTwoHigher46 L beta gamma delta k2 s Q Y Z := by
  simp only [localChartJTwo46, mismatchJTwoHigher46]
  simp only [map_mul, map_div₀, map_neg, map_ofNat]
  ring

/-- Under positive chart orders, every literal term in
`mismatchJTwoHigher46` has order strictly greater than one. -/
theorem mismatchJTwoHigher46_order_gt_one
    (L beta gamma delta k2 : k) (s Q Y Z : HahnSeries ℚ k)
    (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ)) :
    (↑(1 : ℚ) : WithTop ℚ) <
      (mismatchJTwoHigher46 L beta gamma delta k2 s Q Y Z).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hQ3 := hahnOrderTop_pow_eq46 Q a 3 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hQs := hahnOrderTop_mul_eq46 Q s a 1 hQ hs
  have hQ2s := hahnOrderTop_mul_eq46 (Q ^ 2) s (2 * a) 1 (by
    simpa using hQ2) hs
  have hQs3 := hahnOrderTop_mul_eq46 Q (s ^ 3) a 3 hQ (by
    simpa using hs3)
  have hZs := hahnOrderTop_mul_eq46 Z s c 1 hZ hs
  have hQ3s := hahnOrderTop_mul_eq46 (Q ^ 3) s (3 * a) 1 (by
    simpa using hQ3) hs
  have hQ2s3 := hahnOrderTop_mul_eq46 (Q ^ 2) (s ^ 3) (2 * a) 3 (by
    simpa using hQ2) (by simpa using hs3)
  have hQZ := hahnOrderTop_mul_eq46 Q Z a c hQ hZ
  have hQZs := hahnOrderTop_mul_eq46 (Q * Z) s (a + c) 1 hQZ hs
  have hQs5 := hahnOrderTop_mul_eq46 Q (s ^ 5) a 5 hQ (by
    simpa using hs5)
  have hY2s := hahnOrderTop_mul_eq46 (Y ^ 2) s (2 * b) 1 (by
    simpa using hY2) hs
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by
    simpa using hs4)
  have hZs3 := hahnOrderTop_mul_eq46 Z (s ^ 3) c 3 hZ (by
    simpa using hs3)
  have h1 := hahnOrderTop_C_mul_gt46 ((15 / 4 : k) * L) (Q * s)
    1 (a + 1) hQs (by linarith)
  have h2 := hahnOrderTop_C_mul_gt46 ((3 / 2 : k) * beta) (s ^ 3)
    1 3 (by simpa using hs3) (by norm_num)
  have h3 := hahnOrderTop_C_mul_gt46 ((-15 / 4 : k) * L) (Q ^ 2 * s)
    1 (2 * a + 1) hQ2s (by linarith)
  have h4 := hahnOrderTop_C_mul_gt46 (-3 * beta) (Q * s ^ 3)
    1 (a + 3) hQs3 (by linarith)
  have h5 := hahnOrderTop_C_mul_gt46 ((5 / 8 : k) * L) (Z * s)
    1 (c + 1) hZs (by linarith)
  have h6 := hahnOrderTop_C_mul_gt46 (-2 * delta) (s ^ 5)
    1 5 (by simpa using hs5) (by norm_num)
  have h7 := hahnOrderTop_C_mul_gt46 ((5 / 4 : k) * L) (Q ^ 3 * s)
    1 (3 * a + 1) hQ3s (by linarith)
  have h8 := hahnOrderTop_C_mul_gt46 ((3 / 2 : k) * beta) (Q ^ 2 * s ^ 3)
    1 (2 * a + 3) hQ2s3 (by linarith)
  have h9 := hahnOrderTop_C_mul_gt46 ((-5 / 8 : k) * L) (Q * Z * s)
    1 (a + c + 1) (by simpa [add_assoc] using hQZs) (by linarith)
  have h10 := hahnOrderTop_C_mul_gt46 (2 * delta) (Q * s ^ 5)
    1 (a + 5) hQs5 (by linarith)
  have h11 := hahnOrderTop_C_mul_gt46 ((5 / 8 : k) * L) (Y ^ 2 * s)
    1 (2 * b + 1) hY2s (by linarith)
  have h12 := hahnOrderTop_C_mul_gt46 (2 * gamma) (Y * s ^ 4)
    1 (b + 4) hYs4 (by linarith)
  have h13 := hahnOrderTop_C_mul_gt46 ((-3 / 4 : k) * beta) (Z * s ^ 3)
    1 (c + 3) hZs3 (by linarith)
  have h14 := hahnOrderTop_C_mul_gt46 (-k2) (s ^ 7)
    1 7 (by simpa using hs7) (by norm_num)
  dsimp only [mismatchJTwoHigher46]
  have h12sum := hahnOrderTop_add_gt46 1 _ _ h1 h2
  have h123sum := hahnOrderTop_add_gt46 1 _ _ h12sum h3
  have h1234sum := hahnOrderTop_add_gt46 1 _ _ h123sum h4
  have h12345sum := hahnOrderTop_add_gt46 1 _ _ h1234sum h5
  have h123456sum := hahnOrderTop_add_gt46 1 _ _ h12345sum h6
  have h1234567sum := hahnOrderTop_add_gt46 1 _ _ h123456sum h7
  have h12345678sum := hahnOrderTop_add_gt46 1 _ _ h1234567sum h8
  have h123456789sum := hahnOrderTop_add_gt46 1 _ _ h12345678sum h9
  have h10sum := hahnOrderTop_add_gt46 1 _ _ h123456789sum h10
  have h11sum := hahnOrderTop_add_gt46 1 _ _ h10sum h11
  have h12sum' := hahnOrderTop_add_gt46 1 _ _ h11sum h12
  have h13sum := hahnOrderTop_add_gt46 1 _ _ h12sum' h13
  exact hahnOrderTop_add_gt46 1 _ _ h13sum h14

/-- The full mismatch `J₂` chart forces `v(Y)+v(Z)=1`; at that face its two
leading coefficients satisfy the exact reviewed cancellation relation. -/
theorem mismatchJTwo46_forces_order_sum_and_coefficient
    [CharZero k]
    (L beta gamma delta k2 : k) (s Q Y Z : HahnSeries ℚ k)
    (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hL : L ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ))
    (hrow : localChartJTwo46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k2) = 0) :
    b + c = 1 ∧
      5 * L * s.leadingCoeff +
        3 * Y.leadingCoeff * Z.leadingCoeff = 0 := by
  let p : HahnSeries ℚ k := HahnSeries.C ((-5 / 4 : k) * L) * s
  let q : HahnSeries ℚ k := HahnSeries.C (-3 / 4 : k) * (Y * Z)
  let r := mismatchJTwoHigher46 L beta gamma delta k2 s Q Y Z
  have hp : p.orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ 1 (mul_ne_zero (by norm_num) hL) hs
  have hYZ := hahnOrderTop_mul_eq46 Y Z b c hY hZ
  have hq : q.orderTop = (↑(b + c) : WithTop ℚ) := by
    dsimp [q]
    exact hahnOrderTop_C_mul_eq46 _ _ (b + c) (by norm_num) hYZ
  have hr : (↑(1 : ℚ) : WithTop ℚ) < r.orderTop :=
    mismatchJTwoHigher46_order_gt_one L beta gamma delta k2 s Q Y Z
      a b c ha hb hc hs hQ hY hZ
  have hsum : p + q + r = 0 := by
    rw [← localChartJTwo46_eq_mismatch_faces L beta gamma delta k2 s Q Y Z]
    exact hrow
  obtain ⟨hbc, hcoeff⟩ :=
    hahnOrder_eq_one_of_two_terms_add_higher_eq_zero46 p q r (b + c)
      hp hq hr hsum
  have hsCoeff : s.coeff 1 = s.leadingCoeff :=
    hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 s 1 hs
  have hYZCoeff : (Y * Z).coeff 1 = Y.leadingCoeff * Z.leadingCoeff := by
    have hYZ1 : (Y * Z).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
      rw [hYZ, hbc]
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Y * Z) 1 hYZ1,
      HahnSeries.leadingCoeff_mul]
  dsimp [p, q] at hcoeff
  simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    hsCoeff, hYZCoeff] at hcoeff
  constructor
  · exact hbc
  · linear_combination -4 * hcoeff

/-- Every term of the full mismatch `J₁` chart except its two possible
lowest squares. -/
def mismatchJOneHigher46
    (L beta gamma delta k1 : k)
    (s Q Y Z : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C ((-5 / 8 : k) * L) * (Y * s) +
    HahnSeries.C ((5 / 4 : k) * L) * (Q * Y * s) +
    HahnSeries.C ((3 / 2 : k) * beta) * (Y * s ^ 3) +
    HahnSeries.C ((-5 / 8 : k) * L) * (Q ^ 2 * Y * s) +
    HahnSeries.C (-3 / 2 : k) * (Q * Y ^ 2) +
    HahnSeries.C ((-3 / 2 : k) * beta) * (Q * Y * s ^ 3) +
    HahnSeries.C ((-5 / 16 : k) * L) * (Y * Z * s) +
    HahnSeries.C delta * (Y * s ^ 5) +
    HahnSeries.C (-1 / 2 * gamma) * (Z * s ^ 4) +
    HahnSeries.C (-k1) * s ^ 8

/-- Exact full-row decomposition for the second mismatch face. -/
theorem localChartJOne46_eq_mismatch_faces
    (L beta gamma delta k1 : k)
    (s Q Y Z : HahnSeries ℚ k) :
    localChartJOne46 (HahnSeries.C L) s Q Y Z
        (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C k1) =
      HahnSeries.C (3 / 2 : k) * Y ^ 2 +
        HahnSeries.C (3 / 32 : k) * Z ^ 2 +
        mismatchJOneHigher46 L beta gamma delta k1 s Q Y Z := by
  simp only [localChartJOne46, mismatchJOneHigher46]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one]
  ring

/-- Once `b+c=1`, every remaining literal `J₁` term lies strictly above
`min(2b,2c)`. -/
theorem mismatchJOneHigher46_order_gt_min
    (L beta gamma delta k1 : k) (s Q Y Z : HahnSeries ℚ k)
    (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbc : b + c = 1)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ)) :
    (↑(min (2 * b) (2 * c)) : WithTop ℚ) <
      (mismatchJOneHigher46 L beta gamma delta k1 s Q Y Z).orderTop := by
  let e := min (2 * b) (2 * c)
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hYs := hahnOrderTop_mul_eq46 Y s b 1 hY hs
  have hQY := hahnOrderTop_mul_eq46 Q Y a b hQ hY
  have hQYs := hahnOrderTop_mul_eq46 (Q * Y) s (a + b) 1 hQY hs
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) b 3 hY (by simpa using hs3)
  have hQ2Y := hahnOrderTop_mul_eq46 (Q ^ 2) Y (2 * a) b
    (by simpa using hQ2) hY
  have hQ2Ys := hahnOrderTop_mul_eq46 (Q ^ 2 * Y) s (2 * a + b) 1 hQ2Y hs
  have hQY2 := hahnOrderTop_mul_eq46 Q (Y ^ 2) a (2 * b) hQ
    (by simpa using hY2)
  have hQYs3 := hahnOrderTop_mul_eq46 (Q * Y) (s ^ 3) (a + b) 3 hQY
    (by simpa using hs3)
  have hYZ := hahnOrderTop_mul_eq46 Y Z b c hY hZ
  have hYZs := hahnOrderTop_mul_eq46 (Y * Z) s (b + c) 1 hYZ hs
  have hYs5 := hahnOrderTop_mul_eq46 Y (s ^ 5) b 5 hY (by simpa using hs5)
  have hZs4 := hahnOrderTop_mul_eq46 Z (s ^ 4) c 4 hZ (by simpa using hs4)
  have heB : e ≤ 2 * b := by
    dsimp [e]
    exact min_le_left _ _
  have heC : e ≤ 2 * c := by
    dsimp [e]
    exact min_le_right _ _
  have he1 : e < b + 1 := by linarith
  have he2 : e < a + b + 1 := by linarith
  have he3 : e < b + 3 := by linarith
  have he4 : e < 2 * a + b + 1 := by linarith
  have he5 : e < a + 2 * b := by linarith
  have he6 : e < a + b + 3 := by linarith
  have he7 : e < b + c + 1 := by linarith
  have he8 : e < b + 5 := by linarith
  have he9 : e < c + 4 := by linarith
  have he10 : e < 8 := by linarith
  have h1 := hahnOrderTop_C_mul_gt46 ((-5 / 8 : k) * L) (Y * s)
    e (b + 1) hYs he1
  have h2 := hahnOrderTop_C_mul_gt46 ((5 / 4 : k) * L) (Q * Y * s)
    e (a + b + 1) (by simpa [add_assoc] using hQYs) he2
  have h3 := hahnOrderTop_C_mul_gt46 ((3 / 2 : k) * beta) (Y * s ^ 3)
    e (b + 3) hYs3 he3
  have h4 := hahnOrderTop_C_mul_gt46 ((-5 / 8 : k) * L) (Q ^ 2 * Y * s)
    e (2 * a + b + 1) (by simpa [add_assoc] using hQ2Ys) he4
  have h5 := hahnOrderTop_C_mul_gt46 (-3 / 2 : k) (Q * Y ^ 2)
    e (a + 2 * b) hQY2 he5
  have h6 := hahnOrderTop_C_mul_gt46 ((-3 / 2 : k) * beta) (Q * Y * s ^ 3)
    e (a + b + 3) (by simpa [add_assoc] using hQYs3) he6
  have h7 := hahnOrderTop_C_mul_gt46 ((-5 / 16 : k) * L) (Y * Z * s)
    e (b + c + 1) (by simpa [add_assoc] using hYZs) he7
  have h8 := hahnOrderTop_C_mul_gt46 delta (Y * s ^ 5)
    e (b + 5) hYs5 he8
  have h9 := hahnOrderTop_C_mul_gt46 (-1 / 2 * gamma) (Z * s ^ 4)
    e (c + 4) hZs4 he9
  have h10 := hahnOrderTop_C_mul_gt46 (-k1) (s ^ 8)
    e 8 (by simpa using hs8) he10
  dsimp only [mismatchJOneHigher46]
  have h12 := hahnOrderTop_add_gt46 e _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 e _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 e _ _ h123 h4
  have h12345 := hahnOrderTop_add_gt46 e _ _ h1234 h5
  have h123456 := hahnOrderTop_add_gt46 e _ _ h12345 h6
  have h1234567 := hahnOrderTop_add_gt46 e _ _ h123456 h7
  have h12345678 := hahnOrderTop_add_gt46 e _ _ h1234567 h8
  have h123456789 := hahnOrderTop_add_gt46 e _ _ h12345678 h9
  exact hahnOrderTop_add_gt46 e _ _ h123456789 h10

/-- The full second mismatch row forces `b=c`; together with `b+c=1` this
gives the half-order face. -/
theorem mismatchJOne46_forces_equal_orders
    [CharZero k]
    (L beta gamma delta k1 : k) (s Q Y Z : HahnSeries ℚ k)
    (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbc : b + c = 1)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ))
    (hrow : localChartJOne46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k1) = 0) :
    b = c := by
  let p : HahnSeries ℚ k := HahnSeries.C (3 / 2 : k) * Y ^ 2
  let q : HahnSeries ℚ k := HahnSeries.C (3 / 32 : k) * Z ^ 2
  let r := mismatchJOneHigher46 L beta gamma delta k1 s Q Y Z
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hZ2 := hahnOrderTop_pow_eq46 Z c 2 hZ
  have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num) (by simpa using hY2)
  have hq : q.orderTop = (↑(2 * c) : WithTop ℚ) := by
    dsimp [q]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * c) (by norm_num) (by simpa using hZ2)
  have hr := mismatchJOneHigher46_order_gt_min L beta gamma delta k1
    s Q Y Z a b c ha hb hc hbc hs hQ hY hZ
  have hsum : p + q + r = 0 := by
    rw [← localChartJOne46_eq_mismatch_faces L beta gamma delta k1 s Q Y Z]
    exact hrow
  by_contra hne
  rcases lt_or_gt_of_ne hne with hblt | hclt
  · have hq0 : q.coeff (2 * b) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hq]
      exact WithTop.coe_lt_coe.mpr (by linarith))
    have hr0 : r.coeff (2 * b) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      have hmin : min (2 * b) (2 * c) = 2 * b := min_eq_left (by linarith)
      rwa [hmin] at hr)
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff (2 * b)) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hq0, hr0,
      add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hp hcoeff
  · have hp0 : p.coeff (2 * c) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hp]
      exact WithTop.coe_lt_coe.mpr (by linarith))
    have hr0 : r.coeff (2 * c) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      have hmin : min (2 * b) (2 * c) = 2 * c := min_eq_right (by linarith)
      rwa [hmin] at hr)
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff (2 * c)) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hp0, hr0,
      zero_add, add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hq hcoeff

/-- Exact decomposition of the first boundary chart into the three possible
half-order terms and its regular boundary load. -/
theorem localChartF46_eq_mismatch_faces
    (d0 : k) (s Q Y Z : HahnSeries ℚ k) :
    localChartF46 s Q Y Z (HahnSeries.C d0) =
      Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
        HahnSeries.C (-d0) * s ^ 4 := by
  simp only [localChartF46]
  simp only [map_div₀, map_neg, map_ofNat, map_one]
  ring

/-- After the `J₂,J₁` rows force `v(Y)=v(Z)=1/2`, the exact first boundary
and second curve row force `v(Q)=1/4`. -/
theorem mismatchF46_forces_Q_order_quarter
    [CharZero k]
    (L beta gamma delta k1 d0 : k)
    (s Q Y Z : HahnSeries ℚ k) (a : ℚ) (ha : 0 < a)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hF : localChartF46 s Q Y Z (HahnSeries.C d0) = 0)
    (hJ1 : localChartJOne46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k1) = 0) :
    a = 1 / 4 := by
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y (1 / 2) 2 hY
  have hZ2 := hahnOrderTop_pow_eq46 Z (1 / 2) 2 hZ
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  norm_num at hQ2 hY2 hZ2 hs4
  have hQ2coe : (Q ^ 2).orderTop = (↑(2 * a) : WithTop ℚ) := by
    rw [hQ2, WithTop.coe_mul]
    norm_num
  have hFsum : Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
      HahnSeries.C (-d0) * s ^ 4 = 0 := by
    rw [← localChartF46_eq_mismatch_faces d0 s Q Y Z]
    exact hF
  by_cases hbelow : 2 * a < 1 / 2
  · have hY0 : Y.coeff (2 * a) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hY]
      exact WithTop.coe_lt_coe.mpr hbelow)
    have hZ0 : Z.coeff (2 * a) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hZ]
      exact WithTop.coe_lt_coe.mpr hbelow)
    have hZterm0 : (HahnSeries.C (-1 / 4 : k) * Z).coeff (2 * a) = 0 := by
      rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hZ0, mul_zero]
    have hdHigh := hahnOrderTop_C_mul_gt46 (-d0) (s ^ 4)
      (2 * a) 4 (by simpa using hs4) (by linarith)
    have hd0 : (HahnSeries.C (-d0) * s ^ 4).coeff (2 * a) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop hdHigh
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff (2 * a)) hFsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hY0, hZterm0, hd0,
      zero_add, add_zero] at hcoeff
    exact (HahnSeries.coeff_orderTop_ne hQ2coe hcoeff).elim
  · by_cases habove : 1 / 2 < 2 * a
    · have hQ0 : (Q ^ 2).coeff (1 / 2) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [hQ2]
          exact WithTop.coe_lt_coe.mpr habove)
      have hdHigh := hahnOrderTop_C_mul_gt46 (-d0) (s ^ 4)
        (1 / 2) 4 (by simpa using hs4) (by norm_num)
      have hd0 : (HahnSeries.C (-d0) * s ^ 4).coeff (1 / 2) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop hdHigh
      have hcoeffF := congrArg (fun z : HahnSeries ℚ k => z.coeff (1 / 2)) hFsum
      have hYcoeff := hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Y (1 / 2) hY
      have hZcoeff := hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Z (1 / 2) hZ
      have hZterm : (HahnSeries.C (-1 / 4 : k) * Z).coeff (1 / 2) =
          (-1 / 4 : k) * Z.leadingCoeff := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hZcoeff]
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hQ0, hZterm,
        hd0, add_zero] at hcoeffF
      rw [hYcoeff] at hcoeffF
      have hFlead : Y.leadingCoeff - (1 / 4 : k) * Z.leadingCoeff = 0 := by
        linear_combination hcoeffF
      let p : HahnSeries ℚ k := HahnSeries.C (3 / 2 : k) * Y ^ 2
      let q : HahnSeries ℚ k := HahnSeries.C (3 / 32 : k) * Z ^ 2
      let r := mismatchJOneHigher46 L beta gamma delta k1 s Q Y Z
      have hJ1sum : p + q + r = 0 := by
        rw [← localChartJOne46_eq_mismatch_faces L beta gamma delta k1 s Q Y Z]
        exact hJ1
      have hr := mismatchJOneHigher46_order_gt_min L beta gamma delta k1
        s Q Y Z a (1 / 2) (1 / 2) ha (by norm_num) (by norm_num)
        (by norm_num) hs hQ hY hZ
      have hr1 : (↑(1 : ℚ) : WithTop ℚ) < r.orderTop := by
        simpa using hr
      have hr0 : r.coeff 1 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr1
      have hcoeffJ1 := congrArg (fun z : HahnSeries ℚ k => z.coeff 1) hJ1sum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hr0, add_zero] at hcoeffJ1
      have hY2one : (Y ^ 2).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
        simpa using hY2
      have hZ2one : (Z ^ 2).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
        simpa using hZ2
      have hY2coeff : (Y ^ 2).coeff 1 = Y.leadingCoeff ^ 2 := by
        rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Y ^ 2) 1 hY2one]
        simp [pow_two, HahnSeries.leadingCoeff_mul]
      have hZ2coeff : (Z ^ 2).coeff 1 = Z.leadingCoeff ^ 2 := by
        rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Z ^ 2) 1 hZ2one]
        simp [pow_two, HahnSeries.leadingCoeff_mul]
      dsimp [p, q] at hcoeffJ1
      simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
        hY2coeff, hZ2coeff] at hcoeffJ1
      have hJ1lead : (3 / 2 : k) * Y.leadingCoeff ^ 2 +
          (3 / 32 : k) * Z.leadingCoeff ^ 2 = 0 := hcoeffJ1
      have hYlead : Y.leadingCoeff ≠ 0 := by
        rw [← hYcoeff]
        exact HahnSeries.coeff_orderTop_ne hY
      exact (mismatchQAboveFace_inconsistent46 Y.leadingCoeff Z.leadingCoeff
        hYlead hFlead hJ1lead).elim
    · linarith

/-- Every term of the full mismatch boundary `G` except its three
order-`3/4` terms. -/
def mismatchGHigher46
    (L beta gamma delta e0 : k)
    (s Q Y Z : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C ((3 / 8 : k) * L) * s +
    HahnSeries.C ((-5 / 4 : k) * L) * (Q * s) +
    HahnSeries.C (-1 / 2 * beta) * s ^ 3 +
    HahnSeries.C ((5 / 8 : k) * L) * (Y * s) +
    HahnSeries.C ((15 / 8 : k) * L) * (Q ^ 2 * s) +
    HahnSeries.C ((3 / 2 : k) * beta) * (Q * s ^ 3) +
    HahnSeries.C ((-5 / 16 : k) * L) * (Z * s) +
    HahnSeries.C delta * s ^ 5 +
    HahnSeries.C ((5 / 8 : k) * L) * (Q * Y * s) +
    HahnSeries.C gamma * (Q * s ^ 4) +
    HahnSeries.C (3 / 8 : k) * Y ^ 2 +
    HahnSeries.C ((3 / 4 : k) * beta) * (Y * s ^ 3) +
    HahnSeries.C (-e0) * s ^ 6

/-- Exact decomposition of the full second boundary row at its terminal
mismatch face. -/
theorem localChartG46_eq_mismatch_faces
    (L beta gamma delta e0 : k)
    (s Q Y Z : HahnSeries ℚ k) :
    localChartG46 (HahnSeries.C L) s Q Y Z
        (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C e0) =
      Q ^ 3 + HahnSeries.C (3 / 2 : k) * (Q * Y) +
        HahnSeries.C (-3 / 8 : k) * (Q * Z) +
        mismatchGHigher46 L beta gamma delta e0 s Q Y Z := by
  simp only [localChartG46, mismatchGHigher46]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one]
  ring

/-- At orders `(1,1/4,1/2,1/2)`, every displayed remainder term in `G`
lies strictly above `3/4`. -/
theorem mismatchGHigher46_order_gt_three_quarters
    (L beta gamma delta e0 : k) (s Q Y Z : HahnSeries ℚ k)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ)) :
    (↑(3 / 4 : ℚ) : WithTop ℚ) <
      (mismatchGHigher46 L beta gamma delta e0 s Q Y Z).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q (1 / 4) 2 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y (1 / 2) 2 hY
  have hQs := hahnOrderTop_mul_eq46 Q s (1 / 4) 1 hQ hs
  have hYs := hahnOrderTop_mul_eq46 Y s (1 / 2) 1 hY hs
  have hQ2' : (Q ^ 2).orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    calc
      (Q ^ 2).orderTop = (↑((2 : ℚ) * (1 / 4)) : WithTop ℚ) := hQ2
      _ = _ := by norm_num
  have hY2' : (Y ^ 2).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    calc
      (Y ^ 2).orderTop = (↑((2 : ℚ) * (1 / 2)) : WithTop ℚ) := hY2
      _ = _ := by norm_num
  have hQs' : (Q * s).orderTop = (↑(5 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * s).orderTop = (↑((1 / 4 : ℚ) + 1) : WithTop ℚ) := hQs
      _ = _ := by norm_num
  have hYs' : (Y * s).orderTop = (↑(3 / 2 : ℚ) : WithTop ℚ) := by
    calc
      (Y * s).orderTop = (↑((1 / 2 : ℚ) + 1) : WithTop ℚ) := hYs
      _ = _ := by norm_num
  have hQ2s := hahnOrderTop_mul_eq46 (Q ^ 2) s (1 / 2) 1
    hQ2' hs
  have hQs3 := hahnOrderTop_mul_eq46 Q (s ^ 3) (1 / 4) 3 hQ
    (by simpa using hs3)
  have hZs := hahnOrderTop_mul_eq46 Z s (1 / 2) 1 hZ hs
  have hQY := hahnOrderTop_mul_eq46 Q Y (1 / 4) (1 / 2) hQ hY
  have hQY' : (Q * Y).orderTop = (↑(3 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * Y).orderTop = (↑((1 / 4 : ℚ) + 1 / 2) : WithTop ℚ) := hQY
      _ = _ := by norm_num
  have hQYs := hahnOrderTop_mul_eq46 (Q * Y) s (3 / 4) 1
    hQY' hs
  have hQs4 := hahnOrderTop_mul_eq46 Q (s ^ 4) (1 / 4) 4 hQ
    (by simpa using hs4)
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) (1 / 2) 3 hY
    (by simpa using hs3)
  have hQ2s' : (Q ^ 2 * s).orderTop = (↑(3 / 2 : ℚ) : WithTop ℚ) := by
    calc
      (Q ^ 2 * s).orderTop = (↑((1 / 2 : ℚ) + 1) : WithTop ℚ) := hQ2s
      _ = _ := by norm_num
  have hQs3' : (Q * s ^ 3).orderTop = (↑(13 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * s ^ 3).orderTop = (↑((1 / 4 : ℚ) + 3) : WithTop ℚ) := hQs3
      _ = _ := by norm_num
  have hZs' : (Z * s).orderTop = (↑(3 / 2 : ℚ) : WithTop ℚ) := by
    calc
      (Z * s).orderTop = (↑((1 / 2 : ℚ) + 1) : WithTop ℚ) := hZs
      _ = _ := by norm_num
  have hQYs' : (Q * Y * s).orderTop = (↑(7 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * Y * s).orderTop = (↑((3 / 4 : ℚ) + 1) : WithTop ℚ) := hQYs
      _ = _ := by norm_num
  have hQs4' : (Q * s ^ 4).orderTop = (↑(17 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * s ^ 4).orderTop = (↑((1 / 4 : ℚ) + 4) : WithTop ℚ) := hQs4
      _ = _ := by norm_num
  have hYs3' : (Y * s ^ 3).orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by
    calc
      (Y * s ^ 3).orderTop = (↑((1 / 2 : ℚ) + 3) : WithTop ℚ) := hYs3
      _ = _ := by norm_num
  have h1 := hahnOrderTop_C_mul_gt46 ((3 / 8 : k) * L) s
    (3 / 4) 1 hs (by norm_num)
  have h2 := hahnOrderTop_C_mul_gt46 ((-5 / 4 : k) * L) (Q * s)
    (3 / 4) (5 / 4) hQs' (by norm_num)
  have h3 := hahnOrderTop_C_mul_gt46 (-1 / 2 * beta) (s ^ 3)
    (3 / 4) 3 (by simpa using hs3) (by norm_num)
  have h4 := hahnOrderTop_C_mul_gt46 ((5 / 8 : k) * L) (Y * s)
    (3 / 4) (3 / 2) hYs' (by norm_num)
  have h5 := hahnOrderTop_C_mul_gt46 ((15 / 8 : k) * L) (Q ^ 2 * s)
    (3 / 4) (3 / 2) hQ2s' (by norm_num)
  have h6 := hahnOrderTop_C_mul_gt46 ((3 / 2 : k) * beta) (Q * s ^ 3)
    (3 / 4) (13 / 4) hQs3' (by norm_num)
  have h7 := hahnOrderTop_C_mul_gt46 ((-5 / 16 : k) * L) (Z * s)
    (3 / 4) (3 / 2) hZs' (by norm_num)
  have h8 := hahnOrderTop_C_mul_gt46 delta (s ^ 5)
    (3 / 4) 5 (by simpa using hs5) (by norm_num)
  have h9 := hahnOrderTop_C_mul_gt46 ((5 / 8 : k) * L) (Q * Y * s)
    (3 / 4) (7 / 4) hQYs' (by norm_num)
  have h10 := hahnOrderTop_C_mul_gt46 gamma (Q * s ^ 4)
    (3 / 4) (17 / 4) hQs4' (by norm_num)
  have h11 := hahnOrderTop_C_mul_gt46 (3 / 8 : k) (Y ^ 2)
    (3 / 4) 1 hY2' (by norm_num)
  have h12 := hahnOrderTop_C_mul_gt46 ((3 / 4 : k) * beta) (Y * s ^ 3)
    (3 / 4) (7 / 2) hYs3' (by norm_num)
  have h13 := hahnOrderTop_C_mul_gt46 (-e0) (s ^ 6)
    (3 / 4) 6 (by simpa using hs6) (by norm_num)
  dsimp only [mismatchGHigher46]
  have h12sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h1 h2
  have h123sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h12sum h3
  have h1234sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h123sum h4
  have h12345sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h1234sum h5
  have h123456sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h12345sum h6
  have h1234567sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h123456sum h7
  have h12345678sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h1234567sum h8
  have h123456789sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h12345678sum h9
  have h10sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h123456789sum h10
  have h11sum := hahnOrderTop_add_gt46 (3 / 4) _ _ h10sum h11
  have h12sum' := hahnOrderTop_add_gt46 (3 / 4) _ _ h11sum h12
  exact hahnOrderTop_add_gt46 (3 / 4) _ _ h12sum' h13

/-- The full mismatch `G` row gives the reviewed order-`3/4` leading
equation. -/
theorem mismatchG46_leading_equation
    [CharZero k]
    (L beta gamma delta e0 : k) (s Q Y Z : HahnSeries ℚ k)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hG : localChartG46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C e0) = 0) :
    Q.leadingCoeff *
      (Q.leadingCoeff ^ 2 + (3 / 2 : k) * Y.leadingCoeff -
        (3 / 8 : k) * Z.leadingCoeff) = 0 := by
  let r := mismatchGHigher46 L beta gamma delta e0 s Q Y Z
  have hsum : Q ^ 3 + HahnSeries.C (3 / 2 : k) * (Q * Y) +
      HahnSeries.C (-3 / 8 : k) * (Q * Z) + r = 0 := by
    rw [← localChartG46_eq_mismatch_faces L beta gamma delta e0 s Q Y Z]
    exact hG
  have hr := mismatchGHigher46_order_gt_three_quarters
    L beta gamma delta e0 s Q Y Z hs hQ hY hZ
  have hr0 : r.coeff (3 / 4) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr
  have hQ3 := hahnOrderTop_pow_eq46 Q (1 / 4) 3 hQ
  have hQY := hahnOrderTop_mul_eq46 Q Y (1 / 4) (1 / 2) hQ hY
  have hQZ := hahnOrderTop_mul_eq46 Q Z (1 / 4) (1 / 2) hQ hZ
  have hQ3order : (Q ^ 3).orderTop = (↑(3 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q ^ 3).orderTop = (↑((3 : ℚ) * (1 / 4)) : WithTop ℚ) := hQ3
      _ = _ := by norm_num
  have hQYorder : (Q * Y).orderTop = (↑(3 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * Y).orderTop = (↑((1 / 4 : ℚ) + 1 / 2) : WithTop ℚ) := hQY
      _ = _ := by norm_num
  have hQZorder : (Q * Z).orderTop = (↑(3 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * Z).orderTop = (↑((1 / 4 : ℚ) + 1 / 2) : WithTop ℚ) := hQZ
      _ = _ := by norm_num
  have hQ3coeff : (Q ^ 3).coeff (3 / 4) = Q.leadingCoeff ^ 3 := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Q ^ 3) (3 / 4) hQ3order]
    simp [pow_succ, HahnSeries.leadingCoeff_mul]
  have hQYcoeff : (Q * Y).coeff (3 / 4) =
      Q.leadingCoeff * Y.leadingCoeff := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Q * Y) (3 / 4) hQYorder,
      HahnSeries.leadingCoeff_mul]
  have hQZcoeff : (Q * Z).coeff (3 / 4) =
      Q.leadingCoeff * Z.leadingCoeff := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Q * Z) (3 / 4) hQZorder,
      HahnSeries.leadingCoeff_mul]
  have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff (3 / 4)) hsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero,
    HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    hQ3coeff, hQYcoeff, hQZcoeff, hr0, add_zero] at hcoeff
  linear_combination hcoeff

/-- At the forced orders, the full first boundary row gives the reviewed
order-`1/2` leading equation. -/
theorem mismatchF46_leading_equation
    [CharZero k]
    (d0 : k) (s Q Y Z : HahnSeries ℚ k)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hF : localChartF46 s Q Y Z (HahnSeries.C d0) = 0) :
    Y.leadingCoeff + Q.leadingCoeff ^ 2 -
      (1 / 4 : k) * Z.leadingCoeff = 0 := by
  have hsum : Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
      HahnSeries.C (-d0) * s ^ 4 = 0 := by
    rw [← localChartF46_eq_mismatch_faces d0 s Q Y Z]
    exact hF
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hdHigh := hahnOrderTop_C_mul_gt46 (-d0) (s ^ 4)
    (1 / 2) 4 (by simpa using hs4) (by norm_num)
  have hd0 : (HahnSeries.C (-d0) * s ^ 4).coeff (1 / 2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hdHigh
  have hQ2 := hahnOrderTop_pow_eq46 Q (1 / 4) 2 hQ
  have hQ2order : (Q ^ 2).orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    calc
      (Q ^ 2).orderTop = (↑((2 : ℚ) * (1 / 4)) : WithTop ℚ) := hQ2
      _ = _ := by norm_num
  have hYcoeff := hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Y (1 / 2) hY
  have hZcoeff := hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Z (1 / 2) hZ
  have hQ2coeff : (Q ^ 2).coeff (1 / 2) = Q.leadingCoeff ^ 2 := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Q ^ 2) (1 / 2) hQ2order]
    simp [pow_two, HahnSeries.leadingCoeff_mul]
  have hZterm : (HahnSeries.C (-1 / 4 : k) * Z).coeff (1 / 2) =
      (-1 / 4 : k) * Z.leadingCoeff := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hZcoeff]
  have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff (1 / 2)) hsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hYcoeff, hQ2coeff,
    hZterm, hd0, add_zero] at hcoeff
  linear_combination hcoeff

/-- Complete finite-pole exclusion for the mismatch chart.  The theorem
consumes all four full local equations, derives the unique orders
`(1/4,1/2,1/2)`, and reaches the terminal leading-system contradiction. -/
theorem mismatchFinitePole46_impossible
    [CharZero k]
    (L beta gamma delta d0 e0 k2 k1 : k)
    (s Q Y Z : HahnSeries ℚ k) (a b c : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : L ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ))
    (hF : localChartF46 s Q Y Z (HahnSeries.C d0) = 0)
    (hG : localChartG46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C e0) = 0)
    (hJ2 : localChartJTwo46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k2) = 0)
    (hJ1 : localChartJOne46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k1) = 0) : False := by
  have hbc := (mismatchJTwo46_forces_order_sum_and_coefficient
    L beta gamma delta k2 s Q Y Z a b c ha hb hc hL hs hQ hY hZ hJ2).1
  have hbeq := mismatchJOne46_forces_equal_orders
    L beta gamma delta k1 s Q Y Z a b c ha hb hc hbc hs hQ hY hZ hJ1
  obtain ⟨hbhalf, hchalf⟩ := mismatchOrders46 b c hbc hbeq
  have hYhalf : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    rw [hY, hbhalf]
  have hZhalf : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    rw [hZ, hchalf]
  have haquarter := mismatchF46_forces_Q_order_quarter
    L beta gamma delta k1 d0 s Q Y Z a ha hs hQ hYhalf hZhalf hF hJ1
  have hQquarter : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ) := by
    rw [hQ, haquarter]
  have hFlead := mismatchF46_leading_equation d0 s Q Y Z
    hs hQquarter hYhalf hZhalf hF
  have hGlead := mismatchG46_leading_equation L beta gamma delta e0 s Q Y Z
    hs hQquarter hYhalf hZhalf hG
  have hQcoeff := hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Q (1 / 4) hQquarter
  have hQlead : Q.leadingCoeff ≠ 0 := by
    rw [← hQcoeff]
    exact HahnSeries.coeff_orderTop_ne hQquarter
  exact mismatchLeadingSystem46_inconsistent Q.leadingCoeff Y.leadingCoeff
    Z.leadingCoeff hQlead hFlead hGlead

end MismatchJTwoFace

end Max11DegreeRoutes
