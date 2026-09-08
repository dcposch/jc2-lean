import LowScale68ScaleTwoLocalRhoThree

/-! # The mixed `rho = 2` local box for `(6,8)`

At this radius the quartic source coefficient joins the initial form.  The
first face alone has genuine extra branches, but the first two exact
integrals have coprime scalar residuals.  An explicit Bezout certificate
for those two residuals forces the new quotient to vanish and yields
`h⁴ | p₅`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LocalRhoTwo68

variable {k : Type*} [Field k] [CharZero k]

local instance localRhoTwoHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedA68RhoTwo (_h g a4 : k[X]) : k[X] :=
  a4 - C (5 / 12 : k) * g ^ 2

def localClearedB68RhoTwo (h g a4 a3 : k[X]) : k[X] :=
  a3 * h ^ 3 - C (2 / 3 : k) * a4 * g + C (5 / 27 : k) * g ^ 3

def localClearedC68RhoTwo (h g a4 a3 a2 : k[X]) : k[X] :=
  a2 * h ^ 6 - C (1 / 2 : k) * a3 * g * h ^ 3 +
    C (1 / 6 : k) * a4 * g ^ 2 - C (5 / 144 : k) * g ^ 4

def localClearedD68RhoTwo (h g a4 a3 a2 a1 : k[X]) : k[X] :=
  a1 * h ^ 9 - C (1 / 3 : k) * a2 * g * h ^ 6 +
    C (1 / 12 : k) * a3 * g ^ 2 * h ^ 3 -
    C (1 / 54 : k) * a4 * g ^ 3 + C (1 / 324 : k) * g ^ 5

def localClearedE68RhoTwo (h g a4 a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 12 - C (1 / 6 : k) * a1 * g * h ^ 9 +
    C (1 / 36 : k) * a2 * g ^ 2 * h ^ 6 -
    C (1 / 216 : k) * a3 * g ^ 3 * h ^ 3 +
    C (1 / 1296 : k) * a4 * g ^ 4 - C (5 / 46656 : k) * g ^ 6

theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 3 * g) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k)
        (localClearedA68RhoTwo h0 g (p.coeff 4)) = h ^ 4 * S.A ∧
    algebraMap k[X] (RatFunc k)
        (localClearedB68RhoTwo h0 g (p.coeff 4) (p.coeff 3)) = h ^ 6 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2)) = h ^ 8 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1)) = h ^ 10 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0)) = h ^ 12 * S.E := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    S.clearedCoordinates hp hh0 hH hp6
  let A2 := localClearedA68RhoTwo h0 g (p.coeff 4)
  let B2 := localClearedB68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
  let C2 := localClearedC68RhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
  let D2 := localClearedD68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1)
  let E2 := localClearedE68RhoTwo h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1) (p.coeff 0)
  have hfA : localClearedA68 h0 (p.coeff 5) (p.coeff 4) = h0 ^ 6 * A2 := by
    rw [hp5]
    simp only [localClearedA68, A2, localClearedA68RhoTwo]
    ring
  have hfB : localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3) =
      h0 ^ 9 * B2 := by
    rw [hp5]
    simp only [localClearedB68, B2, localClearedB68RhoTwo]
    ring
  have hfC : localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) = h0 ^ 12 * C2 := by
    rw [hp5]
    simp only [localClearedC68, C2, localClearedC68RhoTwo]
    ring
  have hfD : localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) = h0 ^ 15 * D2 := by
    rw [hp5]
    simp only [localClearedD68, D2, localClearedD68RhoTwo]
    ring
  have hfE : localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) = h0 ^ 18 * E2 := by
    rw [hp5]
    simp only [localClearedE68, E2, localClearedE68RhoTwo]
    ring
  change algebraMap k[X] (RatFunc k)
      (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) = _ at hA
  change algebraMap k[X] (RatFunc k)
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)) = _ at hB
  change algebraMap k[X] (RatFunc k)
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) = _ at hC
  change algebraMap k[X] (RatFunc k)
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) = _ at hD
  change algebraMap k[X] (RatFunc k)
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) = _ at hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact algebraMap_cancel_factoredClearing h0 _ A2 S.A 3 2 2
      hh0 hfA hA
  · exact algebraMap_cancel_factoredClearing h0 _ B2 S.B 3 2 3
      hh0 hfB hB
  · exact algebraMap_cancel_factoredClearing h0 _ C2 S.C0 3 2 4
      hh0 hfC hC
  · exact algebraMap_cancel_factoredClearing h0 _ D2 S.D 3 2 5
      hh0 hfD hD
  · exact algebraMap_cancel_factoredClearing h0 _ E2 S.E 3 2 6
      hh0 hfE hE

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialCoeffsRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

/-! ## The two mixed scalar faces -/

theorem SquareConstantLIntegratedLocalRootData68.topRowFourRhoTwo_zero
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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
      l T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
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
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA2 hB2 hC2 hD2 hE2
  have hface' :
      (firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
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

theorem firstIntegralThreeHigherHahn68_coeff_at_rho
    (rho : ℚ) (hrho : 0 < rho)
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThreeHigherHahn68 L beta gamma delta epsilon zeta
      A B C0 D E).coeff (-10 * rho) = 0 := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hw : (2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE < 10) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-10 * rho) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact weightedMonomial68_orderTop_gt c A B C0 D E
      aA aB aC aD aE rho 10 hrho hA hB hC hD hE hw
  have h1 := hzero zeta 0 1 0 0 0 (by norm_num)
  have h2 := hzero (2 * epsilon) 0 0 1 0 0 (by norm_num)
  have h3 := hzero (3 * delta) 0 0 0 1 0 (by norm_num)
  have h4 := hzero (4 * gamma) 0 0 0 0 1 (by norm_num)
  have h5 := hzero (-(35 / 216 : k) * L) 0 3 0 0 0 (by norm_num)
  have h6 := hzero (-(2 / 3 : k) * epsilon) 2 0 0 0 0 (by norm_num)
  have h7 := hzero (-(2 / 3 : k) * gamma) 0 2 0 0 0 (by norm_num)
  have h8 := hzero ((8 / 27 : k) * gamma) 3 0 0 0 0 (by norm_num)
  have h9 := hzero (-(35 / 72 : k) * L) 2 0 0 1 0 (by norm_num)
  have h10 := hzero (-(5 / 6 : k) * beta) 1 0 0 1 0 (by norm_num)
  have h11 := hzero (-(5 / 6 : k) * beta) 0 1 1 0 0 (by norm_num)
  have h12 := hzero (-(4 / 3 : k) * gamma) 1 0 1 0 0 (by norm_num)
  have h13 := hzero (-(3 / 2 : k) * delta) 1 1 0 0 0 (by norm_num)
  have h14 := hzero ((7 / 6 : k) * L) 0 1 0 0 1 (by norm_num)
  have h15 := hzero ((7 / 6 : k) * L) 0 0 1 1 0 (by norm_num)
  have h16 := hzero ((35 / 72 : k) * beta) 2 1 0 0 0 (by norm_num)
  have h17 := hzero ((385 / 1296 : k) * L) 3 1 0 0 0 (by norm_num)
  have h18 := hzero (-(35 / 36 : k) * L) 1 1 1 0 0 (by norm_num)
  simp only [firstIntegralThreeHigherHahn68, HahnSeries.coeff_add,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, add_zero]

theorem firstIntegralThreeTopFaceHahn68_coeff_at_rho
    (rho : ℚ) (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThreeTopFaceHahn68 A B C0 D E).coeff (-10 * rho) =
      (-4 / 243 : k) * topRowThree68 (A.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (C0.coeff (-4 * rho))
        (D.coeff (-5 * rho)) (E.coeff (-6 * rho)) := by
  have h1 := weightedMonomial68_coeff_at_weight
    (-16 / 243 : k) A B C0 D E 5 0 0 0 0 rho hA hB hC hD hE
  have h2 := weightedMonomial68_coeff_at_weight
    (4 / 3 : k) A B C0 D E 0 0 0 2 0 rho hA hB hC hD hE
  have h3 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 1 0 2 0 0 rho hA hB hC hD hE
  have h4 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 0 2 1 0 0 rho hA hB hC hD hE
  have h5 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 2 0 0 0 1 rho hA hB hC hD hE
  have h6 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 0 1 0 1 rho hA hB hC hD hE
  have h7 := weightedMonomial68_coeff_at_weight
    (20 / 27 : k) A B C0 D E 2 2 0 0 0 rho hA hB hC hD hE
  have h8 := weightedMonomial68_coeff_at_weight
    (40 / 81 : k) A B C0 D E 3 0 1 0 0 rho hA hB hC hD hE
  have h9 := weightedMonomial68_coeff_at_weight
    (-16 / 9 : k) A B C0 D E 1 1 0 1 0 rho hA hB hC hD hE
  have h1' :
      (weightedMonomial68 (-16 / 243 : k) A B C0 D E 5 0 0 0 0).coeff
          (-10 * rho) = (-16 / 243 : k) * (A.coeff (-2 * rho)) ^ 5 := by
    convert h1 using 1 <;> norm_num
  have h2' :
      (weightedMonomial68 (4 / 3 : k) A B C0 D E 0 0 0 2 0).coeff
          (-10 * rho) = (4 / 3 : k) * (D.coeff (-5 * rho)) ^ 2 := by
    convert h2 using 1 <;> norm_num
  have h3' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 1 0 2 0 0).coeff
          (-10 * rho) = (-8 / 9 : k) * A.coeff (-2 * rho) *
            (C0.coeff (-4 * rho)) ^ 2 := by
    convert h3 using 1 <;> norm_num
  have h4' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 0 2 1 0 0).coeff
          (-10 * rho) = (-8 / 9 : k) * (B.coeff (-3 * rho)) ^ 2 *
            C0.coeff (-4 * rho) := by
    convert h4 using 1 <;> norm_num
  have h5' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 0 1).coeff
          (-10 * rho) = (-8 / 9 : k) * (A.coeff (-2 * rho)) ^ 2 *
            E.coeff (-6 * rho) := by
    convert h5 using 1 <;> norm_num
  have h6' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 0 1).coeff
          (-10 * rho) = (8 / 3 : k) * C0.coeff (-4 * rho) *
            E.coeff (-6 * rho) := by
    convert h6 using 1 <;> norm_num
  have h7' :
      (weightedMonomial68 (20 / 27 : k) A B C0 D E 2 2 0 0 0).coeff
          (-10 * rho) = (20 / 27 : k) * (A.coeff (-2 * rho)) ^ 2 *
            (B.coeff (-3 * rho)) ^ 2 := by
    convert h7 using 1 <;> norm_num
  have h8' :
      (weightedMonomial68 (40 / 81 : k) A B C0 D E 3 0 1 0 0).coeff
          (-10 * rho) = (40 / 81 : k) * (A.coeff (-2 * rho)) ^ 3 *
            C0.coeff (-4 * rho) := by
    convert h8 using 1 <;> norm_num
  have h9' :
      (weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 0 1 0).coeff
          (-10 * rho) = (-16 / 9 : k) * A.coeff (-2 * rho) *
            B.coeff (-3 * rho) * D.coeff (-5 * rho) := by
    convert h9 using 1 <;> norm_num
  simp only [firstIntegralThreeTopFaceHahn68, HahnSeries.coeff_add]
  rw [h1', h2', h3', h4', h5', h6', h7', h8', h9']
  simp only [topRowThree68]
  ring

theorem firstIntegralThree68_coeff_at_rho
    (rho : ℚ) (hrho : 0 < rho)
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThree68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-10 * rho) =
      (-4 / 243 : k) * topRowThree68 (A.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (C0.coeff (-4 * rho))
        (D.coeff (-5 * rho)) (E.coeff (-6 * rho)) := by
  rw [firstIntegralThree68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralThreeTopFaceHahn68_coeff_at_rho rho A B C0 D E
      hA hB hC hD hE,
    firstIntegralThreeHigherHahn68_coeff_at_rho rho hrho
      L beta gamma delta epsilon zeta A B C0 D E hA hB hC hD hE,
    add_zero]

theorem SquareConstantLIntegratedLocalRootData68.topRowThreeRhoTwo_zero
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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
      l T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 (HahnSeries.C l) AH BH CH DH EH
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
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA2 hB2 hC2 hD2 hE2
  have hface' :
      (firstIntegralThree68 (HahnSeries.C l) AH BH CH DH EH
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

/-! ## Exact algebraic elimination of the mixed face -/

def rhoTwoInitialA68 (u g : k) : k := u - (5 / 12 : k) * g ^ 2
def rhoTwoInitialB68 (u g : k) : k :=
  -(2 / 3 : k) * u * g + (5 / 27 : k) * g ^ 3
def rhoTwoInitialC68 (u g : k) : k :=
  (1 / 6 : k) * u * g ^ 2 - (5 / 144 : k) * g ^ 4
def rhoTwoInitialD68 (u g : k) : k :=
  -(1 / 54 : k) * u * g ^ 3 + (1 / 324 : k) * g ^ 5
def rhoTwoInitialE68 (u g : k) : k :=
  (1 / 1296 : k) * u * g ^ 4 - (5 / 46656 : k) * g ^ 6

def rhoTwoBezoutFourMultiplier68 (u g : k) : k :=
  (179554887 / 187 : k) * g ^ 9 -
  (17775992862 / 2431 : k) * u * g ^ 7 +
  (3886959474 / 221 : k) * u ^ 2 * g ^ 5 -
  (232771158 / 17 : k) * u ^ 3 * g ^ 3 +
  (28697814 / 17 : k) * u ^ 4 * g

def rhoTwoBezoutThreeMultiplier68 (u g : k) : k :=
  -(49876722 / 187 : k) * g ^ 8 +
  (378149796 / 221 : k) * u * g ^ 6 -
  (53144100 / 17 : k) * u ^ 2 * g ^ 4 +
  (23914845 / 17 : k) * u ^ 3 * g ^ 2

set_option maxHeartbeats 2000000 in
theorem rhoTwo_topRows_four_three_bezout68 (u g : k) :
    g ^ 18 =
      rhoTwoBezoutFourMultiplier68 u g *
        topRowFour68 (rhoTwoInitialA68 u g) (rhoTwoInitialB68 u g)
          (rhoTwoInitialC68 u g) (rhoTwoInitialD68 u g)
          (rhoTwoInitialE68 u g) +
      rhoTwoBezoutThreeMultiplier68 u g *
        topRowThree68 (rhoTwoInitialA68 u g) (rhoTwoInitialB68 u g)
          (rhoTwoInitialC68 u g) (rhoTwoInitialD68 u g)
          (rhoTwoInitialE68 u g) := by
  simp only [rhoTwoBezoutFourMultiplier68, rhoTwoBezoutThreeMultiplier68,
    rhoTwoInitialA68, rhoTwoInitialB68, rhoTwoInitialC68,
    rhoTwoInitialD68, rhoTwoInitialE68, topRowFour68, topRowThree68]
  ring

theorem rhoTwo_topRows_four_three_force_g_zero68 (u g : k)
    (h4 : topRowFour68 (rhoTwoInitialA68 u g) (rhoTwoInitialB68 u g)
      (rhoTwoInitialC68 u g) (rhoTwoInitialD68 u g)
      (rhoTwoInitialE68 u g) = 0)
    (h3 : topRowThree68 (rhoTwoInitialA68 u g) (rhoTwoInitialB68 u g)
      (rhoTwoInitialC68 u g) (rhoTwoInitialD68 u g)
      (rhoTwoInitialE68 u g) = 0) : g = 0 := by
  have hpow : g ^ 18 = 0 := by
    simpa [h4, h3] using rhoTwo_topRows_four_three_bezout68 u g
  exact eq_zero_of_pow_eq_zero hpow

theorem SquareConstantLIntegratedLocalRootData68.source_scale_fourth_dvd_p5
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

end LocalRhoTwo68

#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoTwo
#print axioms firstIntegralThree68_coeff_at_rho
#print axioms rhoTwo_topRows_four_three_bezout68
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_fourth_dvd_p5

end Max11DegreeRoutes
