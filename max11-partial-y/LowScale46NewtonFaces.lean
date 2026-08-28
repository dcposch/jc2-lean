import LowScale46Integrality

/-! # Exhaustive Newton-face arithmetic for the aligned `(4,6)` chart

For a vanishing nonarchimedean sum, its least order cannot occur exactly
once.  The predicates below encode that necessary condition for three and
four candidate orders.  The two main theorems certify the complete rational
Newton-face tables in the reviewed aligned local analysis: after the lowest
row ties, either the next row or the last row has a unique least order.
-/

namespace Max11DegreeRoutes

/-- The minimum of three ordered quantities is achieved at least twice. -/
def TripleMinimumTied (x y z : ℚ) : Prop :=
  (x = y ∧ x ≤ z) ∨ (x = z ∧ x ≤ y) ∨ (y = z ∧ y ≤ x)

/-- The minimum of four ordered quantities is achieved at least twice. -/
def QuadrupleMinimumTied (w x y z : ℚ) : Prop :=
  (w = x ∧ w ≤ y ∧ w ≤ z) ∨
  (w = y ∧ w ≤ x ∧ w ≤ z) ∨
  (w = z ∧ w ≤ x ∧ w ≤ y) ∨
  (x = y ∧ x ≤ w ∧ x ≤ z) ∨
  (x = z ∧ x ≤ w ∧ x ≤ y) ∨
  (y = z ∧ y ≤ w ∧ y ≤ x)

section HahnMinimum

variable {k : Type*} [Field k]

/-- Three nonzero Hahn terms summing to zero must have their least order
attained at least twice.  This is the valuation principle consumed by the
Newton-face tables below. -/
theorem tripleMinimumTied_of_hahn_sum_eq_zero46
    (x y z : HahnSeries ℚ k) (a b c : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ))
    (hy : y.orderTop = (↑b : WithTop ℚ))
    (hz : z.orderTop = (↑c : WithTop ℚ))
    (hsum : x + y + z = 0) : TripleMinimumTied a b c := by
  by_contra hnot
  have hunique :
      (a < b ∧ a < c) ∨ (b < a ∧ b < c) ∨ (c < a ∧ c < b) := by
    simp only [TripleMinimumTied, not_or, not_and_or, not_le] at hnot
    grind
  rcases hunique with ha | hb | hc
  · have hy0 : y.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hy]
      exact WithTop.coe_lt_coe.mpr ha.1)
    have hz0 : z.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hz]
      exact WithTop.coe_lt_coe.mpr ha.2)
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff a) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hy0, hz0,
      add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hx hcoeff
  · have hx0 : x.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hx]
      exact WithTop.coe_lt_coe.mpr hb.1)
    have hz0 : z.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hz]
      exact WithTop.coe_lt_coe.mpr hb.2)
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff b) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hx0, hz0,
      zero_add, add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hy hcoeff
  · have hx0 : x.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hx]
      exact WithTop.coe_lt_coe.mpr hc.1)
    have hy0 : y.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hy]
      exact WithTop.coe_lt_coe.mpr hc.2)
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff c) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hx0, hy0,
      zero_add] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hz hcoeff

/-- Four nonzero Hahn terms summing to zero must likewise have a tied least
order. -/
theorem quadrupleMinimumTied_of_hahn_sum_eq_zero46
    (w x y z : HahnSeries ℚ k) (a b c d : ℚ)
    (hw : w.orderTop = (↑a : WithTop ℚ))
    (hx : x.orderTop = (↑b : WithTop ℚ))
    (hy : y.orderTop = (↑c : WithTop ℚ))
    (hz : z.orderTop = (↑d : WithTop ℚ))
    (hsum : w + x + y + z = 0) : QuadrupleMinimumTied a b c d := by
  by_contra hnot
  have hunique :
      (a < b ∧ a < c ∧ a < d) ∨
      (b < a ∧ b < c ∧ b < d) ∨
      (c < a ∧ c < b ∧ c < d) ∨
      (d < a ∧ d < b ∧ d < c) := by
    simp only [QuadrupleMinimumTied, not_or, not_and_or, not_le] at hnot
    grind
  rcases hunique with ha | hb | hc | hd
  · have hx0 : x.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hx]
      exact WithTop.coe_lt_coe.mpr ha.1)
    have hy0 : y.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hy]
      exact WithTop.coe_lt_coe.mpr ha.2.1)
    have hz0 : z.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hz]
      exact WithTop.coe_lt_coe.mpr ha.2.2)
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff a) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hx0, hy0, hz0,
      add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hw hcoeff
  · have hw0 : w.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hw]
      exact WithTop.coe_lt_coe.mpr hb.1)
    have hy0 : y.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hy]
      exact WithTop.coe_lt_coe.mpr hb.2.1)
    have hz0 : z.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hz]
      exact WithTop.coe_lt_coe.mpr hb.2.2)
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff b) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hw0, hy0, hz0,
      zero_add, add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hx hcoeff
  · have hw0 : w.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hw]
      exact WithTop.coe_lt_coe.mpr hc.1)
    have hx0 : x.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hx]
      exact WithTop.coe_lt_coe.mpr hc.2.1)
    have hz0 : z.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hz]
      exact WithTop.coe_lt_coe.mpr hc.2.2)
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff c) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hw0, hx0, hz0,
      zero_add, add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hy hcoeff
  · have hw0 : w.coeff d = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hw]
      exact WithTop.coe_lt_coe.mpr hd.1)
    have hx0 : x.coeff d = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hx]
      exact WithTop.coe_lt_coe.mpr hd.2.1)
    have hy0 : y.coeff d = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hy]
      exact WithTop.coe_lt_coe.mpr hd.2.2)
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff d) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hw0, hx0, hy0,
      zero_add] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hz hcoeff

end HahnMinimum

/-- In the `beta ≠ 0` aligned stratum, any possible lowest-face tie in
`G0` forces one of the next two rows to have a unique lowest order.  The
three alternatives respectively say that `2b` is unique in `H2`, that `3`
is unique in `H2`, or that `2b` is unique in `H1`. -/
theorem alignedBetaNewtonFace46
    (a b : ℚ) (ha : 0 < a) (_hb : 0 < b)
    (hG0 : TripleMinimumTied (3 * a) (2 * b) 3) :
    (2 * b < 2 * a + b ∧ 2 * b < 3) ∨
    (3 < 2 * a + b ∧ 3 < 2 * b) ∨
    (2 * b < 4 * a ∧ 2 * b < 2 * a + b ∧
      2 * b < a + 2 * b) := by
  rcases hG0 with hxy | hxz | hyz
  · rcases hxy with ⟨hxy, hz⟩
    by_cases hlt : a < 1
    · left
      constructor <;> linarith
    · right
      right
      constructor
      · linarith
      constructor <;> linarith
  · rcases hxz with ⟨hxz, hy⟩
    by_cases hlt : 3 < 2 * b
    · right
      left
      constructor <;> linarith
    · right
      right
      constructor
      · linarith
      constructor <;> linarith
  · rcases hyz with ⟨hyz, hx⟩
    right
    right
    constructor
    · linarith
    constructor <;> linarith

/-- Consequently the three aligned `beta ≠ 0` rows cannot all satisfy the
necessary tied-minimum condition. -/
theorem alignedBetaNewtonFaces_inconsistent46
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hG0 : TripleMinimumTied (3 * a) (2 * b) 3)
    (hH2 : TripleMinimumTied (2 * a + b) (2 * b) 3)
    (hH1 : QuadrupleMinimumTied (4 * a) (2 * a + b)
      (a + 2 * b) (2 * b)) : False := by
  rcases alignedBetaNewtonFace46 a b ha hb hG0 with h2b | h3 | h1
  · rcases hH2 with hxy | hxz | hyz <;> rcases h2b with ⟨hleft, hright⟩ <;>
      rcases ‹_ ∧ _› with ⟨heq, hle⟩ <;> linarith
  · rcases hH2 with hxy | hxz | hyz <;> rcases h3 with ⟨hleft, hright⟩ <;>
      rcases ‹_ ∧ _› with ⟨heq, hle⟩ <;> linarith
  · rcases hH1 with hwx | hwy | hwz | hxy | hxz | hyz <;>
      rcases h1 with ⟨hleft, hmiddle, hright⟩ <;>
      rcases ‹_ ∧ _ ∧ _› with ⟨heq, hle1, hle2⟩ <;> linarith

/-- In the `beta = 0, delta ≠ 0` stratum, a lowest-face tie in `G0`
again forces a unique lowest order in `H2` or `H1`.  The alternatives say
that `2b` is unique in `H2`, that `5` is unique in `H2`, or that `2b` is
unique among every candidate order in `H1`. -/
theorem alignedDeltaNewtonFace46
    (a b : ℚ) (ha : 0 < a) (_hb : 0 < b)
    (hG0 : QuadrupleMinimumTied (3 * a) (2 * b) (4 + a) 5) :
    (2 * b < 2 * a + b ∧ 2 * b < 4 + b ∧ 2 * b < 5) ∨
    (5 < 2 * a + b ∧ 5 < 2 * b ∧ 5 < 4 + b) ∨
    (2 * b < 4 * a ∧ 2 * b < 2 * a + b ∧
      2 * b < a + 2 * b ∧ 2 * b < 4 + 2 * a ∧
      2 * b < 4 + b ∧ 2 * b < 5 + b ∧ 2 * b < 8) := by
  rcases hG0 with h12 | h13 | h14 | h23 | h24 | h34
  · rcases h12 with ⟨h12, h3, h4⟩
    by_cases hlt : 3 * a < 5
    · left
      constructor
      · linarith
      constructor <;> linarith
    · right
      right
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
  · rcases h13 with ⟨h13, h2, h4⟩
    exfalso
    linarith
  · rcases h14 with ⟨h14, h2, h3⟩
    by_cases hlt : 5 < 2 * b
    · right
      left
      constructor
      · linarith
      constructor <;> linarith
    · right
      right
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
  · rcases h23 with ⟨h23, h1, h4⟩
    exfalso
    linarith
  · rcases h24 with ⟨h24, h1, h3⟩
    right
    right
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · rcases h34 with ⟨h34, h1, h2⟩
    exfalso
    linarith

/-- A compact client interface for the delta-face table: if no row is
allowed a unique least order, the table is inconsistent. -/
theorem alignedDeltaNewtonFaces_inconsistent46
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hG0 : QuadrupleMinimumTied (3 * a) (2 * b) (4 + a) 5)
    (hH2b : ¬ (2 * b < 2 * a + b ∧ 2 * b < 4 + b ∧ 2 * b < 5))
    (hH25 : ¬ (5 < 2 * a + b ∧ 5 < 2 * b ∧ 5 < 4 + b))
    (hH1b : ¬ (2 * b < 4 * a ∧ 2 * b < 2 * a + b ∧
      2 * b < a + 2 * b ∧ 2 * b < 4 + 2 * a ∧
      2 * b < 4 + b ∧ 2 * b < 5 + b ∧ 2 * b < 8)) : False := by
  rcases alignedDeltaNewtonFace46 a b ha hb hG0 with h | h | h
  · exact hH2b h
  · exact hH25 h
  · exact hH1b h

/-- The first two mismatch rows force the two positive orders to be one
half once their sum is one and they agree. -/
theorem mismatchOrders46
    (b c : ℚ) (hsum : b + c = 1) (heq : b = c) :
    b = 1 / 2 ∧ c = 1 / 2 := by
  constructor <;> linarith

section MismatchCoefficients

variable {F : Type*} [Field F]

/-- If `Q` lies strictly above the half-order face, the leading parts of
`Fh` and `J1h` are already inconsistent.  This is the step that forces
`v(Q)=1/4` after `v(Y)=v(Z)=1/2`. -/
theorem mismatchQAboveFace_inconsistent46
    [CharZero F]
    (y0 z0 : F) (hy0 : y0 ≠ 0)
    (hF : y0 - (1 / 4 : F) * z0 = 0)
    (hJ1 : (3 / 2 : F) * y0 ^ 2 + (3 / 32 : F) * z0 ^ 2 = 0) :
    False := by
  have hz : z0 = 4 * y0 := by
    linear_combination -4 * hF
  rw [hz] at hJ1
  have hy2 : y0 ^ 2 = 0 := by
    linear_combination (1 / 3 : F) * hJ1
  exact pow_ne_zero 2 hy0 hy2

/-- If `Q` lies strictly below the half-order face, its square is the unique
leading term of `Fh`, which is impossible for a nonzero leading
coefficient. -/
theorem mismatchQBelowFace_inconsistent46
    (q0 : F) (hq0 : q0 ≠ 0) (hF : q0 ^ 2 = 0) : False :=
  pow_ne_zero 2 hq0 hF

end MismatchCoefficients

end Max11DegreeRoutes
