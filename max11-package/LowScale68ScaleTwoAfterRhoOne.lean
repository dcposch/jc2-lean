import LowScale68ScaleTwoRhoOneNoncubicElimination

/-! # The first box after the complete rho-one descent

Write `p₅=h⁵g`, `p₄=h³u`, and `p₃=hv`.  The depressed sextic coordinates
then have sharp local denominator box `(1,2,2,2,2)`; the integrated octic
formulas give the corresponding box `(P,Q,R,S,T,U,V)=(1,2,2,3,4,4,5)`.
The unique pole-six term of the first exact integral is `-(8/27)B³`, so
this box forces one more copy of `h` into `p₃`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOne68

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-! ## Exact source clearings for the `(1,2,2,2,2)` box -/

def localClearedA68AfterRhoOne (h g u : k[X]) : k[X] :=
  u - C (5 / 12 : k) * h * g ^ 2

def localClearedB68AfterRhoOne (h g u v : k[X]) : k[X] :=
  v - C (2 / 3 : k) * h * u * g + C (5 / 27 : k) * h ^ 2 * g ^ 3

def localClearedC68AfterRhoOne (h g u v a2 : k[X]) : k[X] :=
  a2 - C (1 / 2 : k) * v * g + C (1 / 6 : k) * h * u * g ^ 2 -
    C (5 / 144 : k) * h ^ 2 * g ^ 4

def localClearedD68AfterRhoOne (h g u v a2 a1 : k[X]) : k[X] :=
  a1 * h - C (1 / 3 : k) * a2 * g + C (1 / 12 : k) * v * g ^ 2 -
    C (1 / 54 : k) * h * u * g ^ 3 + C (1 / 324 : k) * h ^ 2 * g ^ 5

def localClearedE68AfterRhoOne
    (h g u v a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 2 - C (1 / 6 : k) * a1 * g * h +
    C (1 / 36 : k) * a2 * g ^ 2 - C (1 / 216 : k) * v * g ^ 3 +
    C (1 / 1296 : k) * h * u * g ^ 4 -
    C (5 / 46656 : k) * h ^ 2 * g ^ 6

theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterRhoOne
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 * v) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k) (localClearedA68AfterRhoOne h0 g u) =
        h ^ 1 * S.A ∧
    algebraMap k[X] (RatFunc k) (localClearedB68AfterRhoOne h0 g u v) =
        h ^ 2 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68AfterRhoOne h0 g u v (p.coeff 2)) = h ^ 2 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1)) =
      h ^ 2 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1)
          (p.coeff 0)) = h ^ 2 * S.E := by
  dsimp only
  have hp5' : p.coeff 5 = h0 ^ 4 * (h0 * g) := by rw [hp5]; ring
  have hp4' : p.coeff 4 = h0 ^ 2 * (h0 * u) := by rw [hp4]; ring
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    S.clearedCoordinatesRhoOne hp hh0 hH hp6 hp5' hp4'
  let A1 := localClearedA68AfterRhoOne h0 g u
  let B1 := localClearedB68AfterRhoOne h0 g u v
  let C1 := localClearedC68AfterRhoOne h0 g u v (p.coeff 2)
  let D1 := localClearedD68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1)
  let E1 := localClearedE68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1)
    (p.coeff 0)
  have hfA : localClearedA68RhoOne (h0 * g) (h0 * u) = h0 * A1 := by
    simp only [localClearedA68RhoOne, A1, localClearedA68AfterRhoOne]
    ring
  have hfB : localClearedB68RhoOne (h0 * g) (h0 * u) (p.coeff 3) =
      h0 * B1 := by
    rw [hp3]
    simp only [localClearedB68RhoOne, B1, localClearedB68AfterRhoOne]
    ring
  have hfC : localClearedC68RhoOne h0 (h0 * g) (h0 * u) (p.coeff 3)
      (p.coeff 2) = h0 ^ 2 * C1 := by
    rw [hp3]
    simp only [localClearedC68RhoOne, C1, localClearedC68AfterRhoOne]
    ring
  have hfD : localClearedD68RhoOne h0 (h0 * g) (h0 * u) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) = h0 ^ 3 * D1 := by
    rw [hp3]
    simp only [localClearedD68RhoOne, D1, localClearedD68AfterRhoOne]
    ring
  have hfE : localClearedE68RhoOne h0 (h0 * g) (h0 * u) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) = h0 ^ 4 * E1 := by
    rw [hp3]
    simp only [localClearedE68RhoOne, E1, localClearedE68AfterRhoOne]
    ring
  change algebraMap k[X] (RatFunc k)
      (localClearedA68RhoOne (h0 * g) (h0 * u)) = _ at hA
  change algebraMap k[X] (RatFunc k)
      (localClearedB68RhoOne (h0 * g) (h0 * u) (p.coeff 3)) = _ at hB
  change algebraMap k[X] (RatFunc k)
      (localClearedC68RhoOne h0 (h0 * g) (h0 * u) (p.coeff 3)
        (p.coeff 2)) = _ at hC
  change algebraMap k[X] (RatFunc k)
      (localClearedD68RhoOne h0 (h0 * g) (h0 * u) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) = _ at hD
  change algebraMap k[X] (RatFunc k)
      (localClearedE68RhoOne h0 (h0 * g) (h0 * u) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) = _ at hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact algebraMap_cancel_factoredClearing h0 _ A1 S.A 1 1 1 hh0
      (by simpa using hfA) hA
  · exact algebraMap_cancel_factoredClearing h0 _ B1 S.B 1 2 1 hh0
      (by simpa using hfB) hB
  · exact algebraMap_cancel_factoredClearing h0 _ C1 S.C0 2 2 1 hh0 hfC hC
  · exact algebraMap_cancel_factoredClearing h0 _ D1 S.D 3 2 1 hh0 hfD hD
  · exact algebraMap_cancel_factoredClearing h0 _ E1 S.E 4 2 1 hh0 hfE hE

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsAfterRhoOne
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 * v) :
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterRhoOne
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68AfterRhoOne h0 g u) T.source.A 1 T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68AfterRhoOne h0 g u v) T.source.B 2 T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68AfterRhoOne h0 g u v (p.coeff 2)) T.source.C0 2
      T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1))
      T.source.D 2 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1)
        (p.coeff 0)) T.source.E 2 T.scale_order hE⟩

/-- Exact initial packet, including the unrestricted coefficients
`p₂,p₁,p₀`. -/
theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialPacketAfterRhoOne
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 * v) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ) =
        c⁻¹ * u.eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * v.eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * ((p.coeff 2).eval T.root -
          (1 / 2 : k) * v.eval T.root * g.eval T.root) ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * (-(1 / 3 : k) * (p.coeff 2).eval T.root *
          g.eval T.root + (1 / 12 : k) * v.eval T.root * g.eval T.root ^ 2) ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * ((1 / 36 : k) * (p.coeff 2).eval T.root *
          g.eval T.root ^ 2 - (1 / 216 : k) * v.eval T.root *
          g.eval T.root ^ 3) := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterRhoOne
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  have hAco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedA68AfterRhoOne h0 g u) T.source.A 1 hc hsingle hA
  have hBco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedB68AfterRhoOne h0 g u v) T.source.B 2 hc hsingle hB
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedC68AfterRhoOne h0 g u v (p.coeff 2)) T.source.C0 2
    hc hsingle hC
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedD68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1))
    T.source.D 2 hc hsingle hD
  have hEco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedE68AfterRhoOne h0 g u v (p.coeff 2) (p.coeff 1)
      (p.coeff 0)) T.source.E 2 hc hsingle hE
  norm_num at hAco hBco hCco hDco hEco
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAco]
    simp [localClearedA68AfterRhoOne, T.root_eq]
  · rw [hBco]
    simp [localClearedB68AfterRhoOne, T.root_eq]
  · rw [hCco]
    simp [localClearedC68AfterRhoOne, T.root_eq]
  · rw [hDco]
    simp [localClearedD68AfterRhoOne, T.root_eq]
  · rw [hEco]
    simp [localClearedE68AfterRhoOne, T.root_eq]

/-! ## The unique `B³` face -/

theorem firstIntegralFour68_coeff_unique_B_cube_afterRhoOne
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-1 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-2 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-2 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-6 : ℚ) =
        (-8 / 27 : k) * (B.coeff (-2 : ℚ)) ^ 3 := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-6 : ℚ) < (aA : ℚ) * (-1) + (aB : ℚ) * (-2) +
        (aC : ℚ) * (-2) + (aD : ℚ) * (-2) + (aE : ℚ) * (-2)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-6 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-1) (-2) (-2) (-2) (-2) (-6)
      hA hB hC hD hE hlt
  have hBpow := hahnOrderTop_pow_lower46 B (-2) 3 hB
  have hconst : (0 : WithTop ℚ) ≤
      (HahnSeries.C (-8 / 27 : k) : HahnSeries ℚ k).orderTop :=
    hahnOrderTop_C_nonneg46 _
  have hmul := hahnCoeff_mul_at_lower46
    (HahnSeries.C (-8 / 27 : k)) (B ^ 3) 0 (-6) hconst (by
      convert hBpow using 1 <;> norm_num)
  have hpow : (B ^ 3).coeff (-6 : ℚ) = (B.coeff (-2 : ℚ)) ^ 3 := by
    convert hahnCoeff_pow_at_lower46 B (-2) 3 hB using 1 <;> norm_num
  have hlead :
      (weightedMonomial68 (-8 / 27 : k) A B C0 D E 0 3 0 0 0).coeff
          (-6 : ℚ) = (-8 / 27 : k) * (B.coeff (-2 : ℚ)) ^ 3 := by
    simp only [weightedMonomial68, pow_zero, one_mul, mul_one]
    rw [show (-6 : ℚ) = 0 + (-6) by norm_num, hmul,
      HahnSeries.C_apply, HahnSeries.coeff_single_same, hpow]
  have ht2 := hzero (-8 / 9 : k) 2 0 0 1 0 (by norm_num)
  have ht3 := hzero (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  have ht4 := hzero (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have ht5 := hzero (40 / 81 : k) 3 1 0 0 0 (by norm_num)
  have ht6 := hzero (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have hh1 := hzero zeta 1 0 0 0 0 (by norm_num)
  have hh2 := hzero (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hh3 := hzero (3 * delta) 0 0 1 0 0 (by norm_num)
  have hh4 := hzero (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hh5 := hzero (5 * beta) 0 0 0 0 1 (by norm_num)
  have hh6 := hzero (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have hh7 := hzero (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hh8 := hzero ((7 / 12 : k) * L) 0 0 2 0 0 (by norm_num)
  have hh9 := hzero ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have hh10 := hzero ((385 / 5184 : k) * L) 4 0 0 0 0 (by norm_num)
  have hh11 := hzero (-(35 / 72 : k) * L) 1 2 0 0 0 (by norm_num)
  have hh12 := hzero (-(35 / 72 : k) * L) 2 0 1 0 0 (by norm_num)
  have hh13 := hzero (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have hh14 := hzero (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have hh15 := hzero ((7 / 6 : k) * L) 1 0 0 0 1 (by norm_num)
  have hh16 := hzero ((7 / 6 : k) * L) 0 1 0 1 0 (by norm_num)
  rw [firstIntegralFour68_eq_localFaces]
  simp only [firstIntegralFourTopFaceHahn68, firstIntegralFourHigherHahn68,
    HahnSeries.coeff_add]
  rw [hlead, ht2, ht3, ht4, ht5, ht6, hh1, hh2, hh3, hh4, hh5, hh6,
    hh7, hh8, hh9, hh10, hh11, hh12, hh13, hh14, hh15, hh16]
  ring

theorem SquareConstantLIntegratedLocalRootData68.topBAfterRhoOne_zero
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 * v) :
    (ratFuncAtHahn46 T.root T.source.B).coeff (-2 : ℚ) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterRhoOne hp hH hp6 hp5 hp4 hp3
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
    (fun x : HahnSeries ℚ k => x.coeff (-6 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-6 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_unique_B_cube_afterRhoOne
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by simpa only [BH] using hB)
      (by simpa only [CH] using hC) (by simpa only [DH] using hD)
      (by simpa only [EH] using hE)
  rw [hface] at hcoeff
  have hpow : (BH.coeff (-2 : ℚ)) ^ 3 = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)
  have hBz : BH.coeff (-2 : ℚ) = 0 := eq_zero_of_pow_eq_zero hpow
  simpa only [BH] using hBz

theorem SquareConstantLIntegratedLocalRootData68.source_scale_dvd_p3_quotient
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 * v) :
    h0 ∣ v := by
  have htop := T.topBAfterRhoOne_zero hp hH hp6 hp5 hp4 hp3
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialPacketAfterRhoOne hp hH hp6 hp5 hp4 hp3
  rw [hBco] at htop
  have hcinv : (c ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hc)
  have hvroot : v.eval T.root = 0 :=
    (mul_eq_zero.mp htop).resolve_left hcinv
  exact linearPolynomial_dvd_of_eval_eq_zero
    h0 v T.root T.scale_degree T.root_eq hvroot

theorem SquareConstantLIntegratedLocalRootData68.source_scale_sq_dvd_p3_afterRhoOne
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 * v) :
    h0 ^ 2 ∣ p.coeff 3 := by
  obtain ⟨w, hv⟩ :=
    T.source_scale_dvd_p3_quotient hp hH hp6 hp5 hp4 hp3
  refine ⟨w, ?_⟩
  rw [hp3, hv]
  ring

/-- The local face upgrades the three divisibilities furnished by the
complete rho-one component elimination. -/
theorem SquareConstantLIntegratedLocalRootData68.afterRhoOne_upgrade_descend
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hdesc : h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
      h0 ∣ p.coeff 3) :
    h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ^ 2 ∣ p.coeff 3 := by
  rcases hdesc with ⟨⟨g, hp5⟩, ⟨u, hp4⟩, ⟨v, hp3⟩⟩
  refine ⟨⟨g, hp5⟩, ⟨u, hp4⟩, ?_⟩
  exact T.source_scale_sq_dvd_p3_afterRhoOne (g := g) (u := u) (v := v)
    hp hH hp6 hp5 hp4 hp3

/-- Source-level post-rho-one descent once the rho-one box is reached. -/
theorem SquareConstantLIntegratedLocalRootData68.afterRhoOne_next_divisibilities_of_box
    {p q : k[X][X]} {j l : k} {h0 H g0 u0 : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5rho : p.coeff 5 = h0 ^ 4 * g0)
    (hp4rho : p.coeff 4 = h0 ^ 2 * u0) :
    h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ^ 2 ∣ p.coeff 3 := by
  have hdesc := T.rhoOne_allComponents_descend hp hH hp6 hp5rho hp4rho
  exact T.afterRhoOne_upgrade_descend hp hH hp6 hdesc

/-- Source-level post-rho-one descent from the original square-source data. -/
theorem SquareConstantLIntegratedLocalRootData68.afterRhoOne_next_divisibilities
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ^ 2 ∣ p.coeff 3 := by
  obtain ⟨g0, hp5rho⟩ := T.source_scale_fourth_dvd_p5 hp hH hp6
  obtain ⟨u0, hp4rho⟩ := T.source_scale_sq_dvd_p4_afterRhoTwo hp hH hp6
  exact T.afterRhoOne_next_divisibilities_of_box hp hH hp6 hp5rho hp4rho

end AfterRhoOne68

#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterRhoOne
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateInitialPacketAfterRhoOne
#print axioms firstIntegralFour68_coeff_unique_B_cube_afterRhoOne
#print axioms SquareConstantLIntegratedLocalRootData68.topBAfterRhoOne_zero
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_dvd_p3_quotient
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_sq_dvd_p3_afterRhoOne
#print axioms SquareConstantLIntegratedLocalRootData68.rhoOne_allComponents_descend
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_fourth_dvd_p5
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_sq_dvd_p4_afterRhoTwo
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOne_upgrade_descend
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOne_next_divisibilities_of_box
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOne_next_divisibilities

end Max11DegreeRoutes
