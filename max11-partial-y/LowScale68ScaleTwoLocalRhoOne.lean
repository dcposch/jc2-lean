import LowScale68ScaleTwoAfterRhoTwo

/-! # The uniform `rho = 1` local box for `(6,8)`

After `h⁴ ∣ p₅` and `h² ∣ p₄`, the five depressed sextic coordinates have
the uniform pole box `(2,3,4,5,6)`.  This file extracts its exact
three-parameter initial packet and the two scalar equations supplied by the
two polynomial first integrals.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LocalRhoOne68

variable {k : Type*} [Field k] [CharZero k]

local instance localRhoOneHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-! ## Exact source clearings -/

def localClearedA68RhoOne (g u : k[X]) : k[X] :=
  u - C (5 / 12 : k) * g ^ 2

def localClearedB68RhoOne (g u a3 : k[X]) : k[X] :=
  a3 - C (2 / 3 : k) * u * g + C (5 / 27 : k) * g ^ 3

def localClearedC68RhoOne (h g u a3 a2 : k[X]) : k[X] :=
  a2 * h ^ 2 - C (1 / 2 : k) * a3 * g +
    C (1 / 6 : k) * u * g ^ 2 - C (5 / 144 : k) * g ^ 4

def localClearedD68RhoOne (h g u a3 a2 a1 : k[X]) : k[X] :=
  a1 * h ^ 4 - C (1 / 3 : k) * a2 * g * h ^ 2 +
    C (1 / 12 : k) * a3 * g ^ 2 - C (1 / 54 : k) * u * g ^ 3 +
    C (1 / 324 : k) * g ^ 5

def localClearedE68RhoOne (h g u a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 6 - C (1 / 6 : k) * a1 * g * h ^ 4 +
    C (1 / 36 : k) * a2 * g ^ 2 * h ^ 2 -
    C (1 / 216 : k) * a3 * g ^ 3 + C (1 / 1296 : k) * u * g ^ 4 -
    C (5 / 46656 : k) * g ^ 6

theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoOne
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k) (localClearedA68RhoOne g u) = h ^ 2 * S.A ∧
    algebraMap k[X] (RatFunc k)
        (localClearedB68RhoOne g u (p.coeff 3)) = h ^ 3 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)) =
      h ^ 4 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1)) = h ^ 5 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0)) = h ^ 6 * S.E := by
  dsimp only
  have hp4' : p.coeff 4 = h0 * (h0 * u) := by rw [hp4]; ring
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    S.clearedCoordinatesAfterRhoTwoOne hp hh0 hH hp6 hp5 hp4'
  let A1 := localClearedA68RhoOne g u
  let B1 := localClearedB68RhoOne g u (p.coeff 3)
  let C1 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D1 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
  let E1 := localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
  have hfA : localClearedA68AfterRhoTwoOne h0 g (h0 * u) = h0 * A1 := by
    simp only [localClearedA68AfterRhoTwoOne, A1, localClearedA68RhoOne]
    ring
  have hfB : localClearedB68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3) =
      h0 * B1 := by
    simp only [localClearedB68AfterRhoTwoOne, B1, localClearedB68RhoOne]
    ring
  have hfC : localClearedC68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3)
      (p.coeff 2) = h0 * C1 := by
    simp only [localClearedC68AfterRhoTwoOne, C1, localClearedC68RhoOne]
    ring
  have hfD : localClearedD68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) = h0 * D1 := by
    simp only [localClearedD68AfterRhoTwoOne, D1, localClearedD68RhoOne]
    ring
  have hfE : localClearedE68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) = h0 * E1 := by
    simp only [localClearedE68AfterRhoTwoOne, E1, localClearedE68RhoOne]
    ring
  change algebraMap k[X] (RatFunc k)
      (localClearedA68AfterRhoTwoOne h0 g (h0 * u)) = _ at hA
  change algebraMap k[X] (RatFunc k)
      (localClearedB68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3)) = _ at hB
  change algebraMap k[X] (RatFunc k)
      (localClearedC68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3)
        (p.coeff 2)) = _ at hC
  change algebraMap k[X] (RatFunc k)
      (localClearedD68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) = _ at hD
  change algebraMap k[X] (RatFunc k)
      (localClearedE68AfterRhoTwoOne h0 g (h0 * u) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) = _ at hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact algebraMap_cancel_factoredClearing h0 _ A1 S.A 1 2 1 hh0
      (by simpa using hfA) hA
  · exact algebraMap_cancel_factoredClearing h0 _ B1 S.B 1 3 1 hh0
      (by simpa using hfB) hB
  · exact algebraMap_cancel_factoredClearing h0 _ C1 S.C0 1 4 1 hh0
      (by simpa using hfC) hC
  · exact algebraMap_cancel_factoredClearing h0 _ D1 S.D 1 5 1 hh0
      (by simpa using hfD) hD
  · exact algebraMap_cancel_factoredClearing h0 _ E1 S.E 1 6 1 hh0
      (by simpa using hfE) hE

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsRhoOne
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialCoeffsRhoOne
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

/-! ## The two exact first-integral faces -/

theorem SquareConstantLIntegratedLocalRootData68.topRowFourRhoOne_zero
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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
    (fun x : HahnSeries ℚ k => x.coeff (-9 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-9 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_at_rho 1 (by norm_num)
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by norm_num; exact hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
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

theorem SquareConstantLIntegratedLocalRootData68.topRowThreeRhoOne_zero
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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
    (fun x : HahnSeries ℚ k => x.coeff (-10 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-10 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_at_rho 1 (by norm_num)
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by norm_num; exact hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralThree68 (HahnSeries.C l) AH BH CH DH EH
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

/-! ## The exact three-parameter residual -/

def rhoOneInitialA68 (u g : k) : k :=
  u - (5 / 12 : k) * g ^ 2

def rhoOneInitialB68 (t u g : k) : k :=
  t - (2 / 3 : k) * u * g + (5 / 27 : k) * g ^ 3

def rhoOneInitialC68 (t u g : k) : k :=
  -(1 / 2 : k) * t * g + (1 / 6 : k) * u * g ^ 2 -
    (5 / 144 : k) * g ^ 4

def rhoOneInitialD68 (t u g : k) : k :=
  (1 / 12 : k) * t * g ^ 2 - (1 / 54 : k) * u * g ^ 3 +
    (1 / 324 : k) * g ^ 5

def rhoOneInitialE68 (t u g : k) : k :=
  -(1 / 216 : k) * t * g ^ 3 + (1 / 1296 : k) * u * g ^ 4 -
    (5 / 46656 : k) * g ^ 6

theorem SquareConstantLIntegratedLocalRootData68.rhoOne_firstIntegralResidual
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    ∃ c t v z : k, c ≠ 0 ∧
      t = (c ^ 3)⁻¹ * (p.coeff 3).eval T.root ∧
      v = (c ^ 2)⁻¹ * u.eval T.root ∧
      z = c⁻¹ * g.eval T.root ∧
      topRowFour68 (rhoOneInitialA68 v z) (rhoOneInitialB68 t v z)
        (rhoOneInitialC68 t v z) (rhoOneInitialD68 t v z)
        (rhoOneInitialE68 t v z) = 0 ∧
      topRowThree68 (rhoOneInitialA68 v z) (rhoOneInitialB68 t v z)
        (rhoOneInitialC68 t v z) (rhoOneInitialD68 t v z)
        (rhoOneInitialE68 t v z) = 0 := by
  have htop4 := T.topRowFourRhoOne_zero hp hH hp6 hp5 hp4
  have htop3 := T.topRowThreeRhoOne_zero hp hH hp6 hp5 hp4
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialCoeffsRhoOne hp hH hp6 hp5 hp4
  let t : k := (c ^ 3)⁻¹ * (p.coeff 3).eval T.root
  let v : k := (c ^ 2)⁻¹ * u.eval T.root
  let z : k := c⁻¹ * g.eval T.root
  have hAroot : (localClearedA68RhoOne g u).eval T.root =
      u.eval T.root - (5 / 12 : k) * g.eval T.root ^ 2 := by
    simp [localClearedA68RhoOne]
  have hBroot : (localClearedB68RhoOne g u (p.coeff 3)).eval T.root =
      (p.coeff 3).eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root +
        (5 / 27 : k) * g.eval T.root ^ 3 := by
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
  rw [hAform, hBform, hCform, hDform, hEform] at htop4 htop3
  exact ⟨c, t, v, z, hc, rfl, rfl, rfl, htop4, htop3⟩

/-- The residual is genuine: this one-parameter cubic-core family kills not
only the two first-integral faces, but all five scalar top rows. -/
theorem rhoOne_cubicCore_branch_all_topRows_zero (z : k) :
    let t := z ^ 3 / 27
    let u := z ^ 2 / 3
    topRowFour68 (rhoOneInitialA68 u z) (rhoOneInitialB68 t u z)
      (rhoOneInitialC68 t u z) (rhoOneInitialD68 t u z)
      (rhoOneInitialE68 t u z) = 0 ∧
    topRowThree68 (rhoOneInitialA68 u z) (rhoOneInitialB68 t u z)
      (rhoOneInitialC68 t u z) (rhoOneInitialD68 t u z)
      (rhoOneInitialE68 t u z) = 0 ∧
    topRowTwo68 (rhoOneInitialA68 u z) (rhoOneInitialB68 t u z)
      (rhoOneInitialC68 t u z) (rhoOneInitialD68 t u z)
      (rhoOneInitialE68 t u z) = 0 ∧
    topRowOne68 (rhoOneInitialA68 u z) (rhoOneInitialB68 t u z)
      (rhoOneInitialC68 t u z) (rhoOneInitialD68 t u z)
      (rhoOneInitialE68 t u z) = 0 ∧
    topRowZero68 (rhoOneInitialA68 u z) (rhoOneInitialB68 t u z)
      (rhoOneInitialC68 t u z) (rhoOneInitialD68 t u z)
      (rhoOneInitialE68 t u z) = 0 := by
  dsimp only
  simp only [rhoOneInitialA68, rhoOneInitialB68, rhoOneInitialC68,
    rhoOneInitialD68, rhoOneInitialE68, topRowFour68, topRowThree68,
    topRowTwo68, topRowOne68, topRowZero68]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end LocalRhoOne68

#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoOne
#print axioms SquareConstantLIntegratedLocalRootData68.rhoOne_firstIntegralResidual
#print axioms rhoOne_cubicCore_branch_all_topRows_zero

end Max11DegreeRoutes
