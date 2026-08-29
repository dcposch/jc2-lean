import LowScale68ScaleTwoAlignedSquareLowerRows

/-! # The aligned zero-septic `rho = 4` descent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoFour68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoFourHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Improved local order box after the first zero-septic descent
`p₅ = h₀ g`. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateOrderBoundsRhoFour
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 * g) :
    (↑(-8 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-12 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-16 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-20 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-24 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesRhoFour hp T.scale_ne_zero hH hp6 hp5
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68RhoFour h0 g (p.coeff 4)) T.source.A 8
      T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68RhoFour h0 g (p.coeff 4) (p.coeff 3)) T.source.B 12
      T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68RhoFour h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2))
      T.source.C0 16 T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68RhoFour h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 20 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68RhoFour h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 24 T.scale_order hE⟩

/-- Exact five boundary coefficients in the improved zero-septic box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateInitialCoeffsRhoFour
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 * g) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-8 : ℚ) =
        (c ^ 8)⁻¹ * (localClearedA68RhoFour h0 g (p.coeff 4)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-12 : ℚ) =
        (c ^ 12)⁻¹ *
          (localClearedB68RhoFour h0 g (p.coeff 4) (p.coeff 3)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-16 : ℚ) =
        (c ^ 16)⁻¹ *
          (localClearedC68RhoFour h0 g (p.coeff 4) (p.coeff 3)
            (p.coeff 2)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-20 : ℚ) =
        (c ^ 20)⁻¹ *
          (localClearedD68RhoFour h0 g (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-24 : ℚ) =
        (c ^ 24)⁻¹ *
          (localClearedE68RhoFour h0 g (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ :=
    ratFuncAtHahn68_linearRoot_eq_single
      h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesRhoFour hp T.scale_ne_zero hH hp6 hp5
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedA68RhoFour h0 g (p.coeff 4)) T.source.A 8 hc hsingle hA
  · exact localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedB68RhoFour h0 g (p.coeff 4) (p.coeff 3)) T.source.B 12
      hc hsingle hB
  · exact localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedC68RhoFour h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2))
      T.source.C0 16 hc hsingle hC
  · exact localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedD68RhoFour h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 20 hc hsingle hD
  · exact localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedE68RhoFour h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 24 hc hsingle hE

/-- The weight-nine first integral supplies the decisive `rho=4` face at
exponent `-36`, unchanged when the septic coefficient is zero. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowFourRhoFour_zero
    {p q : k[X][X]} {j : k} {h0 H g : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 * g) :
    topRowFour68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-8 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-12 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-16 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-24 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsRhoFour hp hH hp6 hp5
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
    (fun x : HahnSeries ℚ k => x.coeff (-36 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-36 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_neg36
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA hB hC hD hE
  rw [hface] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The `rho=4` face forces a second copy of the linear scale into `p₅`. -/
theorem SquareZeroLIntegratedLocalRootData68.source_scale_sq_dvd_p5
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) : h0 ^ 2 ∣ p.coeff 5 := by
  obtain ⟨g, hp5⟩ := T.source_scale_dvd_p5 hp hH hp6
  have htop := T.topRowFourRhoFour_zero hp hH hp6 hp5
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialCoeffsRhoFour hp hH hp6 hp5
  have hAroot : (localClearedA68RhoFour h0 g (p.coeff 4)).eval T.root =
      -(5 / 12 : k) * g.eval T.root ^ 2 := by
    simp [localClearedA68RhoFour, T.root_eq]
  have hBroot :
      (localClearedB68RhoFour h0 g (p.coeff 4) (p.coeff 3)).eval T.root =
        (5 / 27 : k) * g.eval T.root ^ 3 := by
    simp [localClearedB68RhoFour, T.root_eq]
  have hCroot :
      (localClearedC68RhoFour h0 g (p.coeff 4) (p.coeff 3)
        (p.coeff 2)).eval T.root =
        -(5 / 144 : k) * g.eval T.root ^ 4 := by
    simp [localClearedC68RhoFour, T.root_eq]
  have hDroot :
      (localClearedD68RhoFour h0 g (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)).eval T.root =
        (1 / 324 : k) * g.eval T.root ^ 5 := by
    simp [localClearedD68RhoFour, T.root_eq]
  have hEroot :
      (localClearedE68RhoFour h0 g (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T.root =
        -(5 / 46656 : k) * g.eval T.root ^ 6 := by
    simp [localClearedE68RhoFour, T.root_eq]
  rw [hAco, hBco, hCco, hDco, hEco, hAroot, hBroot, hCroot, hDroot,
    hEroot] at htop
  simp only [topRowFour68] at htop
  field_simp [hc] at htop
  ring_nf at htop
  norm_num at htop
  have hgroot : g.eval T.root = 0 := htop
  have hgdiv : h0 ∣ g := linearPolynomial_dvd_of_eval_eq_zero
    h0 g T.root T.scale_degree T.root_eq hgroot
  obtain ⟨u, hu⟩ := hgdiv
  refine ⟨u, ?_⟩
  rw [hp5, hu]
  ring

end AlignedSquareRhoFour68

end Max11DegreeRoutes
