import LowScale68ScaleTwoAlignedSquareRhoThree

/-! # The aligned zero-septic mixed `rho = 2` descent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoTwo68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoTwoHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The mixed zero-septic `rho=2` Newton box after `p₅=h₀³g`. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateOrderBoundsRhoTwo
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 3 * g) :
    (↑(-4 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-6 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-8 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-10 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-12 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesRhoTwo hp T.scale_ne_zero hH hp6 hp5
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68RhoTwo h0 g (p.coeff 4)) T.source.A 4 T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68RhoTwo h0 g (p.coeff 4) (p.coeff 3)) T.source.B 6
      T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68RhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2))
      T.source.C0 8 T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68RhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 10 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68RhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 12 T.scale_order hE⟩

/-- Exact five initial coefficients in the mixed zero-septic box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateInitialCoeffsRhoTwo
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 3 * g) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-4 : ℚ) =
        (c ^ 4)⁻¹ * (localClearedA68RhoTwo h0 g (p.coeff 4)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-6 : ℚ) =
        (c ^ 6)⁻¹ * (localClearedB68RhoTwo h0 g (p.coeff 4)
          (p.coeff 3)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-8 : ℚ) =
        (c ^ 8)⁻¹ * (localClearedC68RhoTwo h0 g (p.coeff 4)
          (p.coeff 3) (p.coeff 2)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-10 : ℚ) =
        (c ^ 10)⁻¹ * (localClearedD68RhoTwo h0 g (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-12 : ℚ) =
        (c ^ 12)⁻¹ * (localClearedE68RhoTwo h0 g (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesRhoTwo hp T.scale_ne_zero hH hp6 hp5
  exact ⟨c, hc,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedA68RhoTwo h0 g (p.coeff 4)) T.source.A 4 hc hsingle hA,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedB68RhoTwo h0 g (p.coeff 4) (p.coeff 3)) T.source.B 6
      hc hsingle hB,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedC68RhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2))
      T.source.C0 8 hc hsingle hC,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedD68RhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 10 hc hsingle hD,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedE68RhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 12 hc hsingle hE⟩

/-- The exact mixed I4 face at exponent `-18`. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowFourRhoTwo_zero
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 3 * g) :
    topRowFour68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-4 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-6 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-8 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-12 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.coordinateOrderBoundsRhoTwo
    hp hH hp6 hp5
  have hA2 : (↑(-2 * (2 : ℚ)) : WithTop ℚ) ≤ AH.orderTop := by
    norm_num
    exact hA
  have hB2 : (↑(-3 * (2 : ℚ)) : WithTop ℚ) ≤ BH.orderTop := by
    norm_num
    exact hB
  have hC2 : (↑(-4 * (2 : ℚ)) : WithTop ℚ) ≤ CH.orderTop := by
    norm_num
    exact hC
  have hD2 : (↑(-5 * (2 : ℚ)) : WithTop ℚ) ≤ DH.orderTop := by
    norm_num
    exact hD
  have hE2 : (↑(-6 * (2 : ℚ)) : WithTop ℚ) ≤ EH.orderTop := by
    norm_num
    exact hE
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C 0) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-18 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-18 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_at_rho 2 (by norm_num)
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA2 hB2 hC2 hD2 hE2
  have hface' :
      (firstIntegralFour68 (HahnSeries.C 0) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-18 : ℚ) =
      (8 / 81 : k) * topRowFour68 (AH.coeff (-4 : ℚ))
        (BH.coeff (-6 : ℚ)) (CH.coeff (-8 : ℚ))
        (DH.coeff (-10 : ℚ)) (EH.coeff (-12 : ℚ)) := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The independent mixed I3 face at exponent `-20`. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowThreeRhoTwo_zero
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 3 * g) :
    topRowThree68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-4 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-6 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-8 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-12 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.coordinateOrderBoundsRhoTwo
    hp hH hp6 hp5
  have hA2 : (↑(-2 * (2 : ℚ)) : WithTop ℚ) ≤ AH.orderTop := by
    norm_num
    exact hA
  have hB2 : (↑(-3 * (2 : ℚ)) : WithTop ℚ) ≤ BH.orderTop := by
    norm_num
    exact hB
  have hC2 : (↑(-4 * (2 : ℚ)) : WithTop ℚ) ≤ CH.orderTop := by
    norm_num
    exact hC
  have hD2 : (↑(-5 * (2 : ℚ)) : WithTop ℚ) ≤ DH.orderTop := by
    norm_num
    exact hD
  have hE2 : (↑(-6 * (2 : ℚ)) : WithTop ℚ) ≤ EH.orderTop := by
    norm_num
    exact hE
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
    (fun x : HahnSeries ℚ k => x.coeff (-20 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-20 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_at_rho 2 (by norm_num)
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA2 hB2 hC2 hD2 hE2
  have hface' :
      (firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-20 : ℚ) =
      (-4 / 243 : k) * topRowThree68 (AH.coeff (-4 : ℚ))
        (BH.coeff (-6 : ℚ)) (CH.coeff (-8 : ℚ))
        (DH.coeff (-10 : ℚ)) (EH.coeff (-12 : ℚ)) := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (-4 / 243 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The two mixed faces eliminate every nonzero quotient, yielding the
fourth copy of the linear scale in `p₅`. -/
theorem SquareZeroLIntegratedLocalRootData68.source_scale_fourth_dvd_p5
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) : h0 ^ 4 ∣ p.coeff 5 := by
  obtain ⟨g, hp5⟩ := T.source_scale_cube_dvd_p5 hp hH hp6
  have htop4 := T.topRowFourRhoTwo_zero hp hH hp6 hp5
  have htop3 := T.topRowThreeRhoTwo_zero hp hH hp6 hp5
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialCoeffsRhoTwo hp hH hp6 hp5
  let u : k := (c ^ 4)⁻¹ * (p.coeff 4).eval T.root
  let z : k := (c ^ 2)⁻¹ * g.eval T.root
  have hAroot : (localClearedA68RhoTwo h0 g (p.coeff 4)).eval T.root =
      (p.coeff 4).eval T.root - (5 / 12 : k) * g.eval T.root ^ 2 := by
    simp [localClearedA68RhoTwo]
  have hBroot : (localClearedB68RhoTwo h0 g (p.coeff 4)
      (p.coeff 3)).eval T.root =
      -(2 / 3 : k) * (p.coeff 4).eval T.root * g.eval T.root +
        (5 / 27 : k) * g.eval T.root ^ 3 := by
    simp [localClearedB68RhoTwo, T.root_eq]
  have hCroot : (localClearedC68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2)).eval T.root =
      (1 / 6 : k) * (p.coeff 4).eval T.root * g.eval T.root ^ 2 -
        (5 / 144 : k) * g.eval T.root ^ 4 := by
    simp [localClearedC68RhoTwo, T.root_eq]
  have hDroot : (localClearedD68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1)).eval T.root =
      -(1 / 54 : k) * (p.coeff 4).eval T.root * g.eval T.root ^ 3 +
        (1 / 324 : k) * g.eval T.root ^ 5 := by
    simp [localClearedD68RhoTwo, T.root_eq]
  have hEroot : (localClearedE68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T.root =
      (1 / 1296 : k) * (p.coeff 4).eval T.root * g.eval T.root ^ 4 -
        (5 / 46656 : k) * g.eval T.root ^ 6 := by
    simp [localClearedE68RhoTwo, T.root_eq]
  have hAform : (ratFuncAtHahn46 T.root T.source.A).coeff (-4 : ℚ) =
      rhoTwoInitialA68 u z := by
    rw [hAco, hAroot]
    simp only [rhoTwoInitialA68, u, z]
    field_simp [hc]
  have hBform : (ratFuncAtHahn46 T.root T.source.B).coeff (-6 : ℚ) =
      rhoTwoInitialB68 u z := by
    rw [hBco, hBroot]
    simp only [rhoTwoInitialB68, u, z]
    field_simp [hc]
  have hCform : (ratFuncAtHahn46 T.root T.source.C0).coeff (-8 : ℚ) =
      rhoTwoInitialC68 u z := by
    rw [hCco, hCroot]
    simp only [rhoTwoInitialC68, u, z]
    field_simp [hc]
  have hDform : (ratFuncAtHahn46 T.root T.source.D).coeff (-10 : ℚ) =
      rhoTwoInitialD68 u z := by
    rw [hDco, hDroot]
    simp only [rhoTwoInitialD68, u, z]
    field_simp [hc]
  have hEform : (ratFuncAtHahn46 T.root T.source.E).coeff (-12 : ℚ) =
      rhoTwoInitialE68 u z := by
    rw [hEco, hEroot]
    simp only [rhoTwoInitialE68, u, z]
    field_simp [hc]
  rw [hAform, hBform, hCform, hDform, hEform] at htop4 htop3
  have hz : z = 0 := rhoTwo_topRows_four_three_force_g_zero68 u z htop4 htop3
  have hgroot : g.eval T.root = 0 := by
    dsimp only [z] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (inv_ne_zero (pow_ne_zero 2 hc))
  have hgdiv : h0 ∣ g := linearPolynomial_dvd_of_eval_eq_zero
    h0 g T.root T.scale_degree T.root_eq hgroot
  obtain ⟨v, hv⟩ := hgdiv
  refine ⟨v, ?_⟩
  rw [hp5, hv]
  ring

end AlignedSquareRhoTwo68

end Max11DegreeRoutes
