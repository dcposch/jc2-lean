import LowScale68ScaleTwoAlignedSquareP4First

/-! # Second quartic-coefficient descent on the aligned square chamber -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareP4Second68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareP4SecondHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The consecutive `(3,4,5,6,7)` box after `p₄=h₀u`. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateOrderBoundsAfterRhoTwoOne
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 * u) :
    (↑(-3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-4 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-5 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-6 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-7 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesAfterRhoTwoOne
      hp T.scale_ne_zero hH hp6 hp5 hp4
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68AfterRhoTwoOne h0 g u) T.source.A 3 T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68AfterRhoTwoOne h0 g u (p.coeff 3)) T.source.B 4
      T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2))
      T.source.C0 5 T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 6 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 7 T.scale_order hE⟩

/-- Exact leading `A` coefficient in the second consecutive box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateInitialAAfterRhoTwoOne
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 * u) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-3 : ℚ) =
        (c ^ 3)⁻¹ * (localClearedA68AfterRhoTwoOne h0 g u).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesAfterRhoTwoOne
      hp T.scale_ne_zero hH hp6 hp5 hp4
  exact ⟨c, hc, localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedA68AfterRhoTwoOne h0 g u) T.source.A 3 hc hsingle hA⟩

/-- The unique `A⁵` face at exponent `-15`. -/
theorem SquareZeroLIntegratedLocalRootData68.topAAfterRhoTwoOne_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 * u) :
    (ratFuncAtHahn46 T.root T.source.A).coeff (-3 : ℚ) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterRhoTwoOne hp hH hp6 hp5 hp4
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-15 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-15 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_unique_A_five_consecutive
    3 (by norm_num) 0 T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-15 : ℚ) =
          (-16 / 243 : k) * (AH.coeff (-3 : ℚ)) ^ 5 := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (-16 / 243 : k) ≠ 0 := by norm_num
  have hpow : (AH.coeff (-3 : ℚ)) ^ 5 = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_left hfactor
  have hAz : AH.coeff (-3 : ℚ) = 0 := eq_zero_of_pow_eq_zero hpow
  simpa only [AH] using hAz

/-- The quotient of `p₄` by its first scale factor has another scale
factor. -/
theorem SquareZeroLIntegratedLocalRootData68.source_scale_dvd_p4_quotient
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 * u) :
    h0 ∣ u := by
  have htop := T.topAAfterRhoTwoOne_zero hp hH hp6 hp5 hp4
  obtain ⟨c, hc, hAco⟩ :=
    T.coordinateInitialAAfterRhoTwoOne hp hH hp6 hp5 hp4
  have hAroot : (localClearedA68AfterRhoTwoOne h0 g u).eval T.root =
      u.eval T.root := by
    simp [localClearedA68AfterRhoTwoOne, T.root_eq]
  rw [hAco, hAroot] at htop
  have hcinv : (c ^ 3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 3 hc)
  have huroot : u.eval T.root = 0 :=
    (mul_eq_zero.mp htop).resolve_left hcinv
  exact linearPolynomial_dvd_of_eval_eq_zero
    h0 u T.root T.scale_degree T.root_eq huroot

/-- The two consecutive I3 faces force two copies of the local scale into
the quartic source coefficient. -/
theorem SquareZeroLIntegratedLocalRootData68.source_scale_sq_dvd_p4_afterRhoTwo
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) : h0 ^ 2 ∣ p.coeff 4 := by
  obtain ⟨g, hp5⟩ := T.source_scale_fourth_dvd_p5 hp hH hp6
  obtain ⟨u, hp4⟩ := T.source_scale_dvd_p4_afterRhoTwo hp hH hp6
  obtain ⟨v, huv⟩ :=
    T.source_scale_dvd_p4_quotient hp hH hp6 hp5 hp4
  refine ⟨v, ?_⟩
  rw [hp4, huv]
  ring

end AlignedSquareP4Second68

end Max11DegreeRoutes
