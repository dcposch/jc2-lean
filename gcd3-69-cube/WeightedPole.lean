import LocalExpansion

noncomputable section

/-! # Weighted Hahn leading terms

The coefficient at exponent zero is multiplicative on Hahn series whose
support is nonnegative.  Packaging those series as a subring turns weighted
leading-component extraction into ordinary evaluation by a ring homomorphism.
-/

/-- Constant coefficients multiply without cross-terms when both Hahn
series have nonnegative order. -/
theorem GCD369CubeHahn_coeff_zero_mul_of_nonneg
    {k : Type*} [Field k] (x y : HahnSeries ℚ k)
    (hx : (↑(0 : ℚ) : WithTop ℚ) ≤ x.orderTop)
    (hy : (↑(0 : ℚ) : WithTop ℚ) ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hxorder : (0 : ℚ) ≤ x.order :=
    HahnSeries.zero_le_orderTop_iff.mp hx
  have hyorder : (0 : ℚ) ≤ y.order :=
    HahnSeries.zero_le_orderTop_iff.mp hy
  have hlead : x.leadingCoeff * y.leadingCoeff ≠ 0 :=
    mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hx0)
      (HahnSeries.leadingCoeff_ne_zero.mpr hy0)
  have hmulorder : (x * y).order = x.order + y.order :=
    HahnSeries.order_mul_of_ne_zero hlead
  by_cases horders : x.order = 0 ∧ y.order = 0
  · have h := HahnSeries.coeff_mul_order_add_order x y
    simpa [HahnSeries.leadingCoeff_eq, horders.1, horders.2] using h
  · have hsumpos : (0 : ℚ) < x.order + y.order := by
      rcases not_and_or.mp horders with hxne | hyne
      · have hxpos : (0 : ℚ) < x.order :=
          lt_of_le_of_ne hxorder (Ne.symm hxne)
        linarith
      · have hypos : (0 : ℚ) < y.order :=
          lt_of_le_of_ne hyorder (Ne.symm hyne)
        linarith
    have hproductzero : (x * y).coeff 0 = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_order (hmulorder.symm ▸ hsumpos)
    have hfactorzero : x.coeff 0 = 0 ∨ y.coeff 0 = 0 := by
      rcases not_and_or.mp horders with hxne | hyne
      · left
        exact HahnSeries.coeff_eq_zero_of_lt_order
          (lt_of_le_of_ne hxorder (Ne.symm hxne))
      · right
        exact HahnSeries.coeff_eq_zero_of_lt_order
          (lt_of_le_of_ne hyorder (Ne.symm hyne))
    rw [hproductzero]
    rcases hfactorzero with hxcoeff | hycoeff
    · rw [hxcoeff, zero_mul]
    · rw [hycoeff, mul_zero]

/-- The subring of rational-exponent Hahn series regular at the origin. -/
def GCD369CubeHahnRegular (k : Type*) [Field k] :
    Subring (HahnSeries ℚ k) where
  carrier := {x | (↑(0 : ℚ) : WithTop ℚ) ≤ x.orderTop}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (↑(0 : ℚ) : WithTop ℚ) ≤ x.orderTop at hx
    change (↑(0 : ℚ) : WithTop ℚ) ≤ y.orderTop at hy
    change (↑(0 : ℚ) : WithTop ℚ) ≤ (x + y).orderTop
    exact (le_min hx hy).trans HahnSeries.min_orderTop_le_orderTop_add
  neg_mem' := by
    intro x hx
    change (↑(0 : ℚ) : WithTop ℚ) ≤ x.orderTop at hx
    change (↑(0 : ℚ) : WithTop ℚ) ≤ (-x).orderTop
    simpa [HahnSeries.orderTop_neg] using hx
  mul_mem' := by
    intro x y hx hy
    change (↑(0 : ℚ) : WithTop ℚ) ≤ x.orderTop at hx
    change (↑(0 : ℚ) : WithTop ℚ) ≤ y.orderTop at hy
    change (↑(0 : ℚ) : WithTop ℚ) ≤ (x * y).orderTop
    rw [HahnSeries.orderTop_mul]
    exact add_nonneg hx hy

/-- Taking the constant Hahn coefficient is a ring homomorphism on regular
series. -/
def GCD369CubeHahnRegular.constantCoeff
    {k : Type*} [Field k] : GCD369CubeHahnRegular k →+* k where
  toFun x := x.1.coeff 0
  map_one' := by simp
  map_mul' x y :=
    GCD369CubeHahn_coeff_zero_mul_of_nonneg x.1 y.1 x.2 y.2
  map_zero' := by simp
  map_add' x y := by simp [HahnSeries.coeff_add]

/-! ## Canonical shape of a weighted pole scale -/

/-- Multiplication by a Hahn monomial of weight `w*p` makes a series regular
whenever its order satisfies the corresponding weighted bound. -/
theorem GCD369CubeHahn_scaled_orderTop_nonneg
    {k : Type*} [Field k] (p : ℚ) (w : ℕ) (a : HahnSeries ℚ k)
    (hbound : 0 ≤ (w : ℚ) * p + a.order) :
    (↑(0 : ℚ) : WithTop ℚ) ≤
      ((HahnSeries.single p 1) ^ w * a).orderTop := by
  by_cases ha : a = 0
  · simp [ha]
  have ht : (HahnSeries.single p (1 : k)) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hscaled : (HahnSeries.single p (1 : k)) ^ w * a ≠ 0 :=
    mul_ne_zero (pow_ne_zero w ht) ha
  have hscaledOrder :
      ((HahnSeries.single p (1 : k)) ^ w * a).order =
        (w : ℚ) * p + a.order := by
    rw [HahnSeries.order_mul (pow_ne_zero w ht) ha,
      HahnSeries.order_pow, HahnSeries.order_single one_ne_zero]
    simp [nsmul_eq_mul]
  change (0 : WithTop ℚ) ≤
    ((HahnSeries.single p (1 : k)) ^ w * a).orderTop
  apply HahnSeries.zero_le_orderTop_iff.mpr
  rw [hscaledOrder]
  exact hbound

/-- If the weighted bound is attained by a nonzero series, its rescaling has
a nonzero constant coefficient. -/
theorem GCD369CubeHahn_scaled_coeff_zero_ne
    {k : Type*} [Field k] (p : ℚ) (w : ℕ) (a : HahnSeries ℚ k)
    (ha : a ≠ 0) (horder : (w : ℚ) * p + a.order = 0) :
    (((HahnSeries.single p 1) ^ w * a).coeff 0) ≠ 0 := by
  have ht : (HahnSeries.single p (1 : k)) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hscaled : (HahnSeries.single p 1) ^ w * a ≠ 0 :=
    mul_ne_zero (pow_ne_zero w ht) ha
  have hscaledOrder :
      ((HahnSeries.single p 1) ^ w * a).order = 0 := by
    rw [HahnSeries.order_mul (pow_ne_zero w ht) ha,
      HahnSeries.order_pow, HahnSeries.order_single one_ne_zero]
    simpa [nsmul_eq_mul] using horder
  intro hcoeff
  apply hscaled
  rw [← HahnSeries.coeff_order_eq_zero]
  rw [hscaledOrder]
  exact hcoeff

/-- A weighted pole scale for the five depressed-sextic coefficients.  The
bounds make every rescaled coefficient regular, while `hattained` records
that the maximal pole slope is achieved and hence gives a projective leading
point. -/
structure GCD369CubeHahnPoleScale (k : Type*) [Field k] where
  p : ℚ
  hp : 0 < p
  a0 : HahnSeries ℚ k
  a1 : HahnSeries ℚ k
  a2 : HahnSeries ℚ k
  a3 : HahnSeries ℚ k
  a4 : HahnSeries ℚ k
  ha0 : 0 ≤ 6 * p + a0.order
  ha1 : 0 ≤ 5 * p + a1.order
  ha2 : 0 ≤ 4 * p + a2.order
  ha3 : 0 ≤ 3 * p + a3.order
  ha4 : 0 ≤ 2 * p + a4.order
  hattained :
    (a0 ≠ 0 ∧ 6 * p + a0.order = 0) ∨
    (a1 ≠ 0 ∧ 5 * p + a1.order = 0) ∨
    (a2 ≠ 0 ∧ 4 * p + a2.order = 0) ∨
    (a3 ≠ 0 ∧ 3 * p + a3.order = 0) ∨
    (a4 ≠ 0 ∧ 2 * p + a4.order = 0)

/-- The maximum of the five weighted pole slopes. -/
def GCD369CubeHahnMaxPoleSlope {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : HahnSeries ℚ k) : ℚ :=
  max (-a0.order / 6)
    (max (-a1.order / 5)
      (max (-a2.order / 4) (max (-a3.order / 3) (-a4.order / 2))))

/-- If at least one depressed-sextic coefficient has a pole, the maximum
weighted slope canonically supplies a positive pole scale. -/
noncomputable def GCD369CubeHahnPoleScale.ofSomePole
    {k : Type*} [Field k] (a0 a1 a2 a3 a4 : HahnSeries ℚ k)
    (hpole : a0.order < 0 ∨ a1.order < 0 ∨ a2.order < 0 ∨
      a3.order < 0 ∨ a4.order < 0) :
    GCD369CubeHahnPoleScale k := by
  let s0 : ℚ := -a0.order / 6
  let s1 : ℚ := -a1.order / 5
  let s2 : ℚ := -a2.order / 4
  let s3 : ℚ := -a3.order / 3
  let s4 : ℚ := -a4.order / 2
  let r3 : ℚ := max s3 s4
  let r2 : ℚ := max s2 r3
  let r1 : ℚ := max s1 r2
  let p : ℚ := max s0 r1
  have hs0 : s0 ≤ p := le_max_left _ _
  have hs1r : s1 ≤ r1 := le_max_left _ _
  have hr1p : r1 ≤ p := le_max_right _ _
  have hs1 : s1 ≤ p := hs1r.trans hr1p
  have hs2r : s2 ≤ r2 := le_max_left _ _
  have hr2r : r2 ≤ r1 := le_max_right _ _
  have hs2 : s2 ≤ p := (hs2r.trans hr2r).trans hr1p
  have hs3r : s3 ≤ r3 := le_max_left _ _
  have hr3r : r3 ≤ r2 := le_max_right _ _
  have hs3 : s3 ≤ p := ((hs3r.trans hr3r).trans hr2r).trans hr1p
  have hs4r : s4 ≤ r3 := le_max_right _ _
  have hs4 : s4 ≤ p := ((hs4r.trans hr3r).trans hr2r).trans hr1p
  have hp : 0 < p := by
    rcases hpole with h0 | h1 | h2 | h3 | h4
    · have : 0 < s0 := by dsimp [s0]; linarith
      exact this.trans_le hs0
    · have : 0 < s1 := by dsimp [s1]; linarith
      exact this.trans_le hs1
    · have : 0 < s2 := by dsimp [s2]; linarith
      exact this.trans_le hs2
    · have : 0 < s3 := by dsimp [s3]; linarith
      exact this.trans_le hs3
    · have : 0 < s4 := by dsimp [s4]; linarith
      exact this.trans_le hs4
  refine {
    p := p
    hp := hp
    a0 := a0
    a1 := a1
    a2 := a2
    a3 := a3
    a4 := a4
    ha0 := by dsimp [s0] at hs0; linarith
    ha1 := by dsimp [s1] at hs1; linarith
    ha2 := by dsimp [s2] at hs2; linarith
    ha3 := by dsimp [s3] at hs3; linarith
    ha4 := by dsimp [s4] at hs4; linarith
    hattained := ?_
  }
  by_cases h0 : r1 ≤ s0
  · have hp0 : p = s0 := max_eq_left h0
    left
    refine ⟨?_, ?_⟩
    · intro ha
      have : p = 0 := by simp [hp0, s0, ha, HahnSeries.order_zero]
      linarith
    · rw [hp0]
      dsimp [s0]
      ring
  · have h0r : s0 ≤ r1 := le_of_not_ge h0
    have hp1 : p = r1 := max_eq_right h0r
    by_cases h1 : r2 ≤ s1
    · have hr1s1 : r1 = s1 := max_eq_left h1
      right; left
      refine ⟨?_, ?_⟩
      · intro ha
        have : p = 0 := by simp [hp1, hr1s1, s1, ha, HahnSeries.order_zero]
        linarith
      · rw [hp1, hr1s1]
        dsimp [s1]
        ring
    · have h1r : s1 ≤ r2 := le_of_not_ge h1
      have hr1r2 : r1 = r2 := max_eq_right h1r
      by_cases h2 : r3 ≤ s2
      · have hr2s2 : r2 = s2 := max_eq_left h2
        right; right; left
        refine ⟨?_, ?_⟩
        · intro ha
          have : p = 0 := by
            simp [hp1, hr1r2, hr2s2, s2, ha, HahnSeries.order_zero]
          linarith
        · rw [hp1, hr1r2, hr2s2]
          dsimp [s2]
          ring
      · have h2r : s2 ≤ r3 := le_of_not_ge h2
        have hr2r3 : r2 = r3 := max_eq_right h2r
        by_cases h3 : s4 ≤ s3
        · have hr3s3 : r3 = s3 := max_eq_left h3
          right; right; right; left
          refine ⟨?_, ?_⟩
          · intro ha
            have : p = 0 := by
              simp [hp1, hr1r2, hr2r3, hr3s3, s3, ha,
                HahnSeries.order_zero]
            linarith
          · rw [hp1, hr1r2, hr2r3, hr3s3]
            dsimp [s3]
            ring
        · have h3r : s3 ≤ s4 := le_of_not_ge h3
          have hr3s4 : r3 = s4 := max_eq_right h3r
          right; right; right; right
          refine ⟨?_, ?_⟩
          · intro ha
            have : p = 0 := by
              simp [hp1, hr1r2, hr2r3, hr3s4, s4, ha,
                HahnSeries.order_zero]
            linarith
          · rw [hp1, hr1r2, hr2r3, hr3s4]
            dsimp [s4]
            ring

namespace GCD369CubeHahnPoleScale

def t {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :
    HahnSeries ℚ k := HahnSeries.single S.p 1

def scaled0 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :=
  S.t ^ 6 * S.a0

def scaled1 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :=
  S.t ^ 5 * S.a1

def scaled2 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :=
  S.t ^ 4 * S.a2

def scaled3 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :=
  S.t ^ 3 * S.a3

def scaled4 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :=
  S.t ^ 2 * S.a4

def leading0 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) : k :=
  S.scaled0.coeff 0

def leading1 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) : k :=
  S.scaled1.coeff 0

def leading2 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) : k :=
  S.scaled2.coeff 0

def leading3 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) : k :=
  S.scaled3.coeff 0

def leading4 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) : k :=
  S.scaled4.coeff 0

theorem scaled0_regular {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    (↑(0 : ℚ) : WithTop ℚ) ≤ S.scaled0.orderTop :=
  GCD369CubeHahn_scaled_orderTop_nonneg S.p 6 S.a0 S.ha0

theorem scaled1_regular {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    (↑(0 : ℚ) : WithTop ℚ) ≤ S.scaled1.orderTop :=
  GCD369CubeHahn_scaled_orderTop_nonneg S.p 5 S.a1 S.ha1

theorem scaled2_regular {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    (↑(0 : ℚ) : WithTop ℚ) ≤ S.scaled2.orderTop :=
  GCD369CubeHahn_scaled_orderTop_nonneg S.p 4 S.a2 S.ha2

theorem scaled3_regular {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    (↑(0 : ℚ) : WithTop ℚ) ≤ S.scaled3.orderTop :=
  GCD369CubeHahn_scaled_orderTop_nonneg S.p 3 S.a3 S.ha3

theorem scaled4_regular {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    (↑(0 : ℚ) : WithTop ℚ) ≤ S.scaled4.orderTop :=
  GCD369CubeHahn_scaled_orderTop_nonneg S.p 2 S.a4 S.ha4

def regular0 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeHahnRegular k := ⟨S.scaled0, S.scaled0_regular⟩

def regular1 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeHahnRegular k := ⟨S.scaled1, S.scaled1_regular⟩

def regular2 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeHahnRegular k := ⟨S.scaled2, S.scaled2_regular⟩

def regular3 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeHahnRegular k := ⟨S.scaled3, S.scaled3_regular⟩

def regular4 {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeHahnRegular k := ⟨S.scaled4, S.scaled4_regular⟩

/-- At least one weighted leading coefficient is nonzero. -/
theorem leading_nonzero {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    S.scaled0.coeff 0 ≠ 0 ∨ S.scaled1.coeff 0 ≠ 0 ∨
      S.scaled2.coeff 0 ≠ 0 ∨ S.scaled3.coeff 0 ≠ 0 ∨
      S.scaled4.coeff 0 ≠ 0 := by
  rcases S.hattained with h0 | h1 | h2 | h3 | h4
  · exact Or.inl (GCD369CubeHahn_scaled_coeff_zero_ne S.p 6 S.a0 h0.1 h0.2)
  · exact Or.inr (Or.inl
      (GCD369CubeHahn_scaled_coeff_zero_ne S.p 5 S.a1 h1.1 h1.2))
  · exact Or.inr (Or.inr (Or.inl
      (GCD369CubeHahn_scaled_coeff_zero_ne S.p 4 S.a2 h2.1 h2.2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (GCD369CubeHahn_scaled_coeff_zero_ne S.p 3 S.a3 h3.1 h3.2))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (GCD369CubeHahn_scaled_coeff_zero_ne S.p 2 S.a4 h4.1 h4.2))))

theorem leading_N1 {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeFaberN1 S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 =
      (GCD369CubeFaberN1
        S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4).coeff 0 := by
  change GCD369CubeFaberN1
      (GCD369CubeHahnRegular.constantCoeff S.regular0)
      (GCD369CubeHahnRegular.constantCoeff S.regular1)
      (GCD369CubeHahnRegular.constantCoeff S.regular2)
      (GCD369CubeHahnRegular.constantCoeff S.regular3)
      (GCD369CubeHahnRegular.constantCoeff S.regular4) = _
  calc
    _ = GCD369CubeHahnRegular.constantCoeff
        (GCD369CubeFaberN1 S.regular0 S.regular1 S.regular2
          S.regular3 S.regular4) := by
      symm
      simp only [GCD369CubeFaberN1, map_add, map_sub, map_mul, map_pow,
        map_ofNat]
    _ = _ := rfl

theorem leading_N2 {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeFaberN2 S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 =
      (GCD369CubeFaberN2
        S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4).coeff 0 := by
  change GCD369CubeFaberN2
      (GCD369CubeHahnRegular.constantCoeff S.regular0)
      (GCD369CubeHahnRegular.constantCoeff S.regular1)
      (GCD369CubeHahnRegular.constantCoeff S.regular2)
      (GCD369CubeHahnRegular.constantCoeff S.regular3)
      (GCD369CubeHahnRegular.constantCoeff S.regular4) = _
  calc
    _ = GCD369CubeHahnRegular.constantCoeff
        (GCD369CubeFaberN2 S.regular0 S.regular1 S.regular2
          S.regular3 S.regular4) := by
      symm
      simp only [GCD369CubeFaberN2, map_add, map_sub, map_mul, map_pow,
        map_ofNat]
    _ = _ := rfl

theorem leading_N3 {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeFaberN3 S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 =
      (GCD369CubeFaberN3
        S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4).coeff 0 := by
  change GCD369CubeFaberN3
      (GCD369CubeHahnRegular.constantCoeff S.regular0)
      (GCD369CubeHahnRegular.constantCoeff S.regular1)
      (GCD369CubeHahnRegular.constantCoeff S.regular2)
      (GCD369CubeHahnRegular.constantCoeff S.regular3)
      (GCD369CubeHahnRegular.constantCoeff S.regular4) = _
  calc
    _ = GCD369CubeHahnRegular.constantCoeff
        (GCD369CubeFaberN3 S.regular0 S.regular1 S.regular2
          S.regular3 S.regular4) := by
      symm
      simp only [GCD369CubeFaberN3, map_add, map_sub, map_mul, map_pow,
        map_ofNat]
    _ = _ := rfl

theorem leading_N4 {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) :
    GCD369CubeFaberN4 S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 =
      (GCD369CubeFaberN4
        S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4).coeff 0 := by
  change GCD369CubeFaberN4
      (GCD369CubeHahnRegular.constantCoeff S.regular0)
      (GCD369CubeHahnRegular.constantCoeff S.regular1)
      (GCD369CubeHahnRegular.constantCoeff S.regular2)
      (GCD369CubeHahnRegular.constantCoeff S.regular3)
      (GCD369CubeHahnRegular.constantCoeff S.regular4) = _
  calc
    _ = GCD369CubeHahnRegular.constantCoeff
        (GCD369CubeFaberN4 S.regular0 S.regular1 S.regular2
          S.regular3 S.regular4) := by
      symm
      simp only [GCD369CubeFaberN4, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
    _ = _ := rfl

/-- Four vanishing homogeneous rows at a weighted pole give the exact
projective source consumed by the leading common-cubic/DS classification. -/
noncomputable def leadingFaberSourceOfNumerators
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnPoleScale k)
    (h1 : GCD369CubeFaberN1
      S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4 = 0)
    (h2 : GCD369CubeFaberN2
      S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4 = 0)
    (h3 : GCD369CubeFaberN3
      S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4 = 0)
    (h4 : GCD369CubeFaberN4
      S.scaled0 S.scaled1 S.scaled2 S.scaled3 S.scaled4 = 0) :
    GCD369CubeLeadingFaberSource k := by
  have hn1 : GCD369CubeFaberN1
      S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 = 0 := by
    rw [S.leading_N1, h1]
    simp
  have hn2 : GCD369CubeFaberN2
      S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 = 0 := by
    rw [S.leading_N2, h2]
    simp
  have hn3 : GCD369CubeFaberN3
      S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 = 0 := by
    rw [S.leading_N3, h3]
    simp
  have hn4 : GCD369CubeFaberN4
      S.leading0 S.leading1 S.leading2 S.leading3 S.leading4 = 0 := by
    rw [S.leading_N4, h4]
    simp
  exact {
    a0 := S.leading0
    a1 := S.leading1
    a2 := S.leading2
    a3 := S.leading3
    a4 := S.leading4
    hnonzero := S.leading_nonzero
    hr1 := by
      rw [show GCD369CubeFaberR1 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 0 0 0 0 0 0 0 =
        (3 / 256) * GCD369CubeFaberN1 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 by
        simp only [GCD369CubeFaberR1, GCD369CubeFaberN1]
        ring, hn1]
      ring
    hr2 := by
      rw [show GCD369CubeFaberR2 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 0 0 0 0 0 0 0 =
        (3 / 256) * GCD369CubeFaberN2 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 by
        simp only [GCD369CubeFaberR2, GCD369CubeFaberN2]
        ring, hn2]
      ring
    hr3 := by
      rw [show GCD369CubeFaberR3 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 0 0 0 0 0 0 0 =
        (1 / 1024) * GCD369CubeFaberN3 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 by
        simp only [GCD369CubeFaberR3, GCD369CubeFaberN3]
        ring, hn3]
      ring
    hr4 := by
      rw [show GCD369CubeFaberR4 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 0 0 0 0 0 0 0 =
        (1 / 256) * GCD369CubeFaberN4 S.leading0 S.leading1 S.leading2
          S.leading3 S.leading4 by
        simp only [GCD369CubeFaberR4, GCD369CubeFaberN4]
        ring, hn4]
      ring
  }

end GCD369CubeHahnPoleScale

#print axioms GCD369CubeHahn_coeff_zero_mul_of_nonneg
#print axioms GCD369CubeHahnRegular.constantCoeff
#print axioms GCD369CubeHahnPoleScale.ofSomePole
#print axioms GCD369CubeHahnPoleScale.leading_nonzero
#print axioms GCD369CubeHahnPoleScale.leadingFaberSourceOfNumerators
