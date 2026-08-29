import LowScale68ScaleTwoAlignedSquareRhoFour

/-! # The aligned zero-septic `rho = 3` descent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoThree68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoThreeHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The zero-septic `rho=3` Newton box after writing `p₅=h₀²g`. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateOrderBoundsRhoThree
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 2 * g) :
    (↑(-6 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-9 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-12 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-15 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-18 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesRhoThree hp T.scale_ne_zero hH hp6 hp5
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68RhoThree h0 g (p.coeff 4)) T.source.A 6 T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68RhoThree h0 g (p.coeff 4) (p.coeff 3)) T.source.B 9
      T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68RhoThree h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2))
      T.source.C0 12 T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68RhoThree h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 15 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68RhoThree h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 18 T.scale_order hE⟩

/-- Exact boundary coefficients in the zero-septic `rho=3` box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateInitialCoeffsRhoThree
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 2 * g) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-6 : ℚ) =
        (c ^ 6)⁻¹ * (localClearedA68RhoThree h0 g (p.coeff 4)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-9 : ℚ) =
        (c ^ 9)⁻¹ * (localClearedB68RhoThree h0 g (p.coeff 4)
          (p.coeff 3)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-12 : ℚ) =
        (c ^ 12)⁻¹ * (localClearedC68RhoThree h0 g (p.coeff 4)
          (p.coeff 3) (p.coeff 2)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-15 : ℚ) =
        (c ^ 15)⁻¹ * (localClearedD68RhoThree h0 g (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-18 : ℚ) =
        (c ^ 18)⁻¹ * (localClearedE68RhoThree h0 g (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesRhoThree hp T.scale_ne_zero hH hp6 hp5
  exact ⟨c, hc,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedA68RhoThree h0 g (p.coeff 4)) T.source.A 6 hc hsingle hA,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedB68RhoThree h0 g (p.coeff 4) (p.coeff 3)) T.source.B 9
      hc hsingle hB,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedC68RhoThree h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2))
      T.source.C0 12 hc hsingle hC,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedD68RhoThree h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 15 hc hsingle hD,
    localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedE68RhoThree h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 18 hc hsingle hE⟩

/-- The exact weight-nine I4 face at exponent `-27`. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowFourRhoThree_zero
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 2 * g) :
    topRowFour68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-6 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-9 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-12 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-18 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.coordinateOrderBoundsRhoThree
    hp hH hp6 hp5
  have hA3 : (↑(-2 * (3 : ℚ)) : WithTop ℚ) ≤ AH.orderTop := by
    norm_num
    exact hA
  have hB3 : (↑(-3 * (3 : ℚ)) : WithTop ℚ) ≤ BH.orderTop := by
    norm_num
    exact hB
  have hC3 : (↑(-4 * (3 : ℚ)) : WithTop ℚ) ≤ CH.orderTop := by
    norm_num
    exact hC
  have hD3 : (↑(-5 * (3 : ℚ)) : WithTop ℚ) ≤ DH.orderTop := by
    norm_num
    exact hD
  have hE3 : (↑(-6 * (3 : ℚ)) : WithTop ℚ) ≤ EH.orderTop := by
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
    (fun x : HahnSeries ℚ k => x.coeff (-27 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-27 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_at_rho 3 (by norm_num)
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA3 hB3 hC3 hD3 hE3
  have hface' :
      (firstIntegralFour68 (HahnSeries.C 0) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-27 : ℚ) =
      (8 / 81 : k) * topRowFour68 (AH.coeff (-6 : ℚ))
        (BH.coeff (-9 : ℚ)) (CH.coeff (-12 : ℚ))
        (DH.coeff (-15 : ℚ)) (EH.coeff (-18 : ℚ)) := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The `rho=3` face forces the third copy of the scale into `p₅`. -/
theorem SquareZeroLIntegratedLocalRootData68.source_scale_cube_dvd_p5
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) : h0 ^ 3 ∣ p.coeff 5 := by
  obtain ⟨g, hp5⟩ := T.source_scale_sq_dvd_p5 hp hH hp6
  have htop := T.topRowFourRhoThree_zero hp hH hp6 hp5
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialCoeffsRhoThree hp hH hp6 hp5
  have hAroot : (localClearedA68RhoThree h0 g (p.coeff 4)).eval T.root =
      -(5 / 12 : k) * g.eval T.root ^ 2 := by
    simp [localClearedA68RhoThree, T.root_eq]
  have hBroot : (localClearedB68RhoThree h0 g (p.coeff 4)
      (p.coeff 3)).eval T.root = (5 / 27 : k) * g.eval T.root ^ 3 := by
    simp [localClearedB68RhoThree, T.root_eq]
  have hCroot : (localClearedC68RhoThree h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2)).eval T.root = -(5 / 144 : k) * g.eval T.root ^ 4 := by
    simp [localClearedC68RhoThree, T.root_eq]
  have hDroot : (localClearedD68RhoThree h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1)).eval T.root =
        (1 / 324 : k) * g.eval T.root ^ 5 := by
    simp [localClearedD68RhoThree, T.root_eq]
  have hEroot : (localClearedE68RhoThree h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T.root =
        -(5 / 46656 : k) * g.eval T.root ^ 6 := by
    simp [localClearedE68RhoThree, T.root_eq]
  rw [hAco, hBco, hCco, hDco, hEco, hAroot, hBroot, hCroot, hDroot,
    hEroot] at htop
  simp only [topRowFour68] at htop
  field_simp [hc] at htop
  ring_nf at htop
  norm_num at htop
  have hgdiv : h0 ∣ g := linearPolynomial_dvd_of_eval_eq_zero
    h0 g T.root T.scale_degree T.root_eq htop
  obtain ⟨u, hu⟩ := hgdiv
  refine ⟨u, ?_⟩
  rw [hp5, hu]
  ring

end AlignedSquareRhoThree68

end Max11DegreeRoutes
