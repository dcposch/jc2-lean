import LowScale68ScaleTwoAlignedSquareP4Second

/-! # The aligned zero-septic `rho = 1` component split -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOne68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The uniform `(2,3,4,5,6)` box after the proved `p₅,p₄`
divisibilities. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateOrderBoundsRhoOne
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-4 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-5 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-6 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesRhoOne
    hp T.scale_ne_zero hH hp6 hp5 hp4
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68RhoOne g u) T.source.A 2 T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68RhoOne g u (p.coeff 3)) T.source.B 3 T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)) T.source.C0 4
      T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1))
      T.source.D 5 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
        (p.coeff 0)) T.source.E 6 T.scale_order hE⟩

/-- Exact five initial coefficients in the uniform rho-one box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateInitialCoeffsRhoOne
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * (localClearedA68RhoOne g u).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-3 : ℚ) =
        (c ^ 3)⁻¹ * (localClearedB68RhoOne g u (p.coeff 3)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-4 : ℚ) =
        (c ^ 4)⁻¹ *
          (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-5 : ℚ) =
        (c ^ 5)⁻¹ * (localClearedD68RhoOne h0 g u (p.coeff 3)
          (p.coeff 2) (p.coeff 1)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-6 : ℚ) =
        (c ^ 6)⁻¹ * (localClearedE68RhoOne h0 g u (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesRhoOne
    hp T.scale_ne_zero hH hp6 hp5 hp4
  exact ⟨c, hc,
    localHahn_coeff_neg_of_cleared T.root c h0 (localClearedA68RhoOne g u)
      T.source.A 2 hc hsingle hA,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedB68RhoOne g u (p.coeff 3)) T.source.B 3 hc hsingle hB,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)) T.source.C0 4
      hc hsingle hC,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1))
      T.source.D 5 hc hsingle hD,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
        (p.coeff 0)) T.source.E 6 hc hsingle hE⟩

/-- The rho-one I4 leading face. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowFourRhoOne_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    topRowFour68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-3 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-4 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-5 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-6 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsRhoOne hp hH hp6 hp5 hp4
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
    (fun x : HahnSeries ℚ k => x.coeff (-9 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-9 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_at_rho 1 (by norm_num)
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by norm_num; exact hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralFour68 (HahnSeries.C 0) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-9 : ℚ) =
      (8 / 81 : k) * topRowFour68 (AH.coeff (-2 : ℚ))
        (BH.coeff (-3 : ℚ)) (CH.coeff (-4 : ℚ))
        (DH.coeff (-5 : ℚ)) (EH.coeff (-6 : ℚ)) := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The independent rho-one I3 leading face. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowThreeRhoOne_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    topRowThree68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-3 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-4 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-5 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-6 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsRhoOne hp hH hp6 hp5 hp4
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
    (fun x : HahnSeries ℚ k => x.coeff (-10 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-10 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_at_rho 1 (by norm_num)
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by norm_num; exact hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-10 : ℚ) =
      (-4 / 243 : k) * topRowThree68 (AH.coeff (-2 : ℚ))
        (BH.coeff (-3 : ℚ)) (CH.coeff (-4 : ℚ))
        (DH.coeff (-5 : ℚ)) (EH.coeff (-6 : ℚ)) := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (-4 / 243 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- Exact source-scaled `(t,v,z)` residual, including the selected Hahn
uniformizer. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_residual_with_scale_single
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    ∃ c t v z : k, c ≠ 0 ∧
      ratFuncAtHahn46 T.root (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c ∧
      t = (c ^ 3)⁻¹ * (p.coeff 3).eval T.root ∧
      v = (c ^ 2)⁻¹ * u.eval T.root ∧
      z = c⁻¹ * g.eval T.root ∧
      rhoOneResidualFour68 t v z = 0 ∧ rhoOneResidualThree68 t v z = 0 := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hAclear, hBclear, hCclear, hDclear, hEclear⟩ :=
    T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
  have hAco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedA68RhoOne g u) T.source.A 2 hc hsingle hAclear
  have hBco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedB68RhoOne g u (p.coeff 3)) T.source.B 3 hc hsingle hBclear
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)) T.source.C0 4
    hc hsingle hCclear
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1))
    T.source.D 5 hc hsingle hDclear
  have hEco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
      (p.coeff 0)) T.source.E 6 hc hsingle hEclear
  norm_num at hAco hBco hCco hDco hEco
  let t : k := (c ^ 3)⁻¹ * (p.coeff 3).eval T.root
  let v : k := (c ^ 2)⁻¹ * u.eval T.root
  let z : k := c⁻¹ * g.eval T.root
  have hAroot : (localClearedA68RhoOne g u).eval T.root =
      u.eval T.root - (5 / 12 : k) * g.eval T.root ^ 2 := by
    simp [localClearedA68RhoOne]
  have hBroot : (localClearedB68RhoOne g u (p.coeff 3)).eval T.root =
      (p.coeff 3).eval T.root - (2 / 3 : k) * u.eval T.root *
        g.eval T.root + (5 / 27 : k) * g.eval T.root ^ 3 := by
    simp [localClearedB68RhoOne]
  have hCroot :
      (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)).eval T.root =
        -(1 / 2 : k) * (p.coeff 3).eval T.root * g.eval T.root +
          (1 / 6 : k) * u.eval T.root * g.eval T.root ^ 2 -
          (5 / 144 : k) * g.eval T.root ^ 4 := by
    simp [localClearedC68RhoOne, T.root_eq]
  have hDroot :
      (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
        (p.coeff 1)).eval T.root =
        (1 / 12 : k) * (p.coeff 3).eval T.root * g.eval T.root ^ 2 -
          (1 / 54 : k) * u.eval T.root * g.eval T.root ^ 3 +
          (1 / 324 : k) * g.eval T.root ^ 5 := by
    simp [localClearedD68RhoOne, T.root_eq]
  have hEroot :
      (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)).eval T.root =
        -(1 / 216 : k) * (p.coeff 3).eval T.root * g.eval T.root ^ 3 +
          (1 / 1296 : k) * u.eval T.root * g.eval T.root ^ 4 -
          (5 / 46656 : k) * g.eval T.root ^ 6 := by
    simp [localClearedE68RhoOne, T.root_eq]
  have hAform : (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ) =
      rhoOneInitialA68 v z := by
    rw [hAco, hAroot]
    simp only [rhoOneInitialA68, v, z]
    field_simp [hc]
  have hBform : (ratFuncAtHahn46 T.root T.source.B).coeff (-3 : ℚ) =
      rhoOneInitialB68 t v z := by
    rw [hBco, hBroot]
    simp only [rhoOneInitialB68, t, v, z]
    field_simp [hc]
  have hCform : (ratFuncAtHahn46 T.root T.source.C0).coeff (-4 : ℚ) =
      rhoOneInitialC68 t v z := by
    rw [hCco, hCroot]
    simp only [rhoOneInitialC68, t, v, z]
    field_simp [hc]
  have hDform : (ratFuncAtHahn46 T.root T.source.D).coeff (-5 : ℚ) =
      rhoOneInitialD68 t v z := by
    rw [hDco, hDroot]
    simp only [rhoOneInitialD68, t, v, z]
    field_simp [hc]
  have hEform : (ratFuncAtHahn46 T.root T.source.E).coeff (-6 : ℚ) =
      rhoOneInitialE68 t v z := by
    rw [hEco, hEroot]
    simp only [rhoOneInitialE68, t, v, z]
    field_simp [hc]
  have htop4 := T.topRowFourRhoOne_zero hp hH hp6 hp5 hp4
  have htop3 := T.topRowThreeRhoOne_zero hp hH hp6 hp5 hp4
  rw [hAform, hBform, hCform, hDform, hEform] at htop4 htop3
  exact ⟨c, t, v, z, hc, hsingle, rfl, rfl, rfl, htop4, htop3⟩

/-- The surviving nonzero rational cubic component.  Its next transverse
row is precisely where the nonaligned proof uses a nonzero septic. -/
def RhoOneZeroLCubicSourcePacket68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  ∃ c t v z : k, c ≠ 0 ∧
    ratFuncAtHahn46 T.root (algebraMap k[X] (RatFunc k) h0) =
      HahnSeries.single (1 : ℚ) c ∧
    t = (c ^ 3)⁻¹ * (p.coeff 3).eval T.root ∧
    v = (c ^ 2)⁻¹ * u.eval T.root ∧
    z = c⁻¹ * g.eval T.root ∧ z ≠ 0 ∧
    v / z ^ 2 = 1 / 3 ∧ t / z ^ 3 = 1 / 27

/-- The explicit degree-ten noncubic component. -/
def RhoOneZeroLNoncubicSourcePacket68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  ∃ c t v z : k, c ≠ 0 ∧
    ratFuncAtHahn46 T.root (algebraMap k[X] (RatFunc k) h0) =
      HahnSeries.single (1 : ℚ) c ∧
    t = (c ^ 3)⁻¹ * (p.coeff 3).eval T.root ∧
    v = (c ^ 2)⁻¹ * u.eval T.root ∧
    z = c⁻¹ * g.eval T.root ∧ z ≠ 0 ∧
    rhoOneNoncubicVPolynomial68 (v / z ^ 2) = 0 ∧
    rhoOneAffineFour68 (t / z ^ 3) (v / z ^ 2) = 0 ∧
    rhoOneAffineThree68 (t / z ^ 3) (v / z ^ 2) = 0

/-- Exact exhaustive rho-one split.  The zero-scale branch already gives
the next three source divisibilities.  The two nonzero branches are the
rational cubic component and the explicit degree-ten component. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_component_split
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
      RhoOneZeroLCubicSourcePacket68 T g u ∨
      RhoOneZeroLNoncubicSourcePacket68 T g u := by
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, h4, h3⟩ :=
    T.rhoOne_residual_with_scale_single hp hH hp6 hp5 hp4
  by_cases hz : z = 0
  · obtain ⟨ht0, hv0⟩ := rhoOne_residual_at_z_zero68 t v
      (by simpa [hz] using h4) (by simpa [hz] using h3)
    have hgroot : g.eval T.root = 0 := by
      rw [hzdef] at hz
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hc)
    have huroot : u.eval T.root = 0 := by
      rw [hv] at hv0
      exact (mul_eq_zero.mp hv0).resolve_left
        (inv_ne_zero (pow_ne_zero 2 hc))
    have hp3root : (p.coeff 3).eval T.root = 0 := by
      rw [ht] at ht0
      exact (mul_eq_zero.mp ht0).resolve_left
        (inv_ne_zero (pow_ne_zero 3 hc))
    obtain ⟨g1, hg1⟩ := linearPolynomial_dvd_of_eval_eq_zero
      h0 g T.root T.scale_degree T.root_eq hgroot
    obtain ⟨u1, hu1⟩ := linearPolynomial_dvd_of_eval_eq_zero
      h0 u T.root T.scale_degree T.root_eq huroot
    have hp3div : h0 ∣ p.coeff 3 := linearPolynomial_dvd_of_eval_eq_zero
      h0 (p.coeff 3) T.root T.scale_degree T.root_eq hp3root
    left
    refine ⟨⟨g1, ?_⟩, ⟨u1, ?_⟩, hp3div⟩
    · rw [hp5, hg1]
      ring
    · rw [hp4, hu1]
      ring
  · have h4aff : rhoOneAffineFour68 (t / z ^ 3) (v / z ^ 2) = 0 := by
      rw [rhoOneResidualFour68_normalize t v z hz] at h4
      exact (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 9 hz)
    have h3aff : rhoOneAffineThree68 (t / z ^ 3) (v / z ^ 2) = 0 := by
      rw [rhoOneResidualThree68_normalize t v z hz] at h3
      exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 10 hz)
    rcases rhoOne_affine_component_split68 (t / z ^ 3) (v / z ^ 2)
      h4aff h3aff with hcore | hnon
    · right; left
      exact ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hcore.1,
        hcore.2⟩
    · right; right
      exact ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hnon,
        h4aff, h3aff⟩

end AlignedSquareRhoOne68

end Max11DegreeRoutes

/-
/-- The independent rho-one I3 leading face. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowThreeRhoOne_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    topRowThree68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-3 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-4 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-5 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-6 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsRhoOne hp hH hp6 hp5 hp4
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
    (fun x : HahnSeries ℚ k => x.coeff (-10 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-10 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_at_rho 1 (by norm_num)
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by norm_num; exact hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-10 : ℚ) =
      (-4 / 243 : k) * topRowThree68 (AH.coeff (-2 : ℚ))
        (BH.coeff (-3 : ℚ)) (CH.coeff (-4 : ℚ))
        (DH.coeff (-5 : ℚ)) (EH.coeff (-6 : ℚ)) := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (-4 / 243 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor
-/
