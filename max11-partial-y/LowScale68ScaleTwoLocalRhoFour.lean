import LowScale68ScaleTwoLocalRowOneZero

/-! # The improved `rho = 4` local box for the `(6,8)` scale-two branch

The first local box proves `h | p₅`.  Writing `p₅ = h g` removes one
copy of `h` per sextic weight from the depression numerators, improving the
coordinate pole bounds from `(10,15,20,25,30)` to `(8,12,16,20,24)`.
The weight-nine first integral then forces `g` to vanish at the root, hence
`h² | p₅`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LocalRhoFour68

variable {k : Type*} [Field k] [CharZero k]

local instance localRhoFourHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedA68RhoFour (h g a4 : k[X]) : k[X] :=
  a4 * h ^ 4 - C (5 / 12 : k) * g ^ 2

def localClearedB68RhoFour (h g a4 a3 : k[X]) : k[X] :=
  a3 * h ^ 9 - C (2 / 3 : k) * a4 * g * h ^ 4 +
    C (5 / 27 : k) * g ^ 3

def localClearedC68RhoFour (h g a4 a3 a2 : k[X]) : k[X] :=
  a2 * h ^ 14 - C (1 / 2 : k) * a3 * g * h ^ 9 +
    C (1 / 6 : k) * a4 * g ^ 2 * h ^ 4 -
    C (5 / 144 : k) * g ^ 4

def localClearedD68RhoFour (h g a4 a3 a2 a1 : k[X]) : k[X] :=
  a1 * h ^ 19 - C (1 / 3 : k) * a2 * g * h ^ 14 +
    C (1 / 12 : k) * a3 * g ^ 2 * h ^ 9 -
    C (1 / 54 : k) * a4 * g ^ 3 * h ^ 4 +
    C (1 / 324 : k) * g ^ 5

def localClearedE68RhoFour (h g a4 a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 24 - C (1 / 6 : k) * a1 * g * h ^ 19 +
    C (1 / 36 : k) * a2 * g ^ 2 * h ^ 14 -
    C (1 / 216 : k) * a3 * g ^ 3 * h ^ 9 +
    C (1 / 1296 : k) * a4 * g ^ 4 * h ^ 4 -
    C (5 / 46656 : k) * g ^ 6

/-- Cancel one common scale factor per coordinate weight from an old
`rho=5` denominator clearing. -/
theorem algebraMap_rhoFour_of_factoredClearing
    (h old new : k[X]) (A : RatFunc k) (w : ℕ) (hh : h ≠ 0)
    (hfact : old = h ^ w * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h) ^ (5 * w) * A) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h) ^ (4 * w) * A := by
  let hR : RatFunc k := algebraMap k[X] (RatFunc k) h
  have hhR : hR ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hfact
  apply mul_left_cancel₀ (pow_ne_zero w hhR)
  calc
    hR ^ w * algebraMap k[X] (RatFunc k) new =
        algebraMap k[X] (RatFunc k) old := by
      dsimp only [hR]
      simpa only [map_mul, map_pow] using hmapped.symm
    _ = hR ^ (5 * w) * A := hclear
    _ = hR ^ w * (hR ^ (4 * w) * A) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

/-- The five actual depressed coordinates after the first divisibility
checkpoint admit the improved denominator exponents. -/
theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoFour
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 * g) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k)
        (localClearedA68RhoFour h0 g (p.coeff 4)) = h ^ 8 * S.A ∧
    algebraMap k[X] (RatFunc k)
        (localClearedB68RhoFour h0 g (p.coeff 4) (p.coeff 3)) =
      h ^ 12 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68RhoFour h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2)) = h ^ 16 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68RhoFour h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1)) = h ^ 20 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68RhoFour h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0)) = h ^ 24 * S.E := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    S.clearedCoordinates hp hh0 hH hp6
  let A4 := localClearedA68RhoFour h0 g (p.coeff 4)
  let B4 := localClearedB68RhoFour h0 g (p.coeff 4) (p.coeff 3)
  let C4 := localClearedC68RhoFour h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2)
  let D4 := localClearedD68RhoFour h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1)
  let E4 := localClearedE68RhoFour h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1) (p.coeff 0)
  have hfA : localClearedA68 h0 (p.coeff 5) (p.coeff 4) = h0 ^ 2 * A4 := by
    rw [hp5]
    simp only [localClearedA68, A4, localClearedA68RhoFour]
    ring
  have hfB : localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3) =
      h0 ^ 3 * B4 := by
    rw [hp5]
    simp only [localClearedB68, B4, localClearedB68RhoFour]
    ring
  have hfC : localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) = h0 ^ 4 * C4 := by
    rw [hp5]
    simp only [localClearedC68, C4, localClearedC68RhoFour]
    ring
  have hfD : localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) = h0 ^ 5 * D4 := by
    rw [hp5]
    simp only [localClearedD68, D4, localClearedD68RhoFour]
    ring
  have hfE : localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) = h0 ^ 6 * E4 := by
    rw [hp5]
    simp only [localClearedE68, E4, localClearedE68RhoFour]
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
  · exact algebraMap_rhoFour_of_factoredClearing h0 _ A4 S.A 2
      hh0 hfA hA
  · exact algebraMap_rhoFour_of_factoredClearing h0 _ B4 S.B 3
      hh0 hfB hB
  · exact algebraMap_rhoFour_of_factoredClearing h0 _ C4 S.C0 4
      hh0 hfC hC
  · exact algebraMap_rhoFour_of_factoredClearing h0 _ D4 S.D 5
      hh0 hfD hD
  · exact algebraMap_rhoFour_of_factoredClearing h0 _ E4 S.E 6
      hh0 hfE hE

/-- Improved local order box after `p₅ = h g`. -/
theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsRhoFour
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

/-- Exact boundary coefficients in the improved box. -/
theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialCoeffsRhoFour
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

/-! ## Weight-nine extraction at `rho = 4` -/

theorem firstIntegralFourHigherHahn68_coeff_neg36
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-8 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-12 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-16 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-20 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-24 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFourHigherHahn68 L beta gamma delta epsilon zeta
      A B C0 D E).coeff (-36 : ℚ) = 0 := by
  have hA4 : (↑(-2 * (4 : ℚ)) : WithTop ℚ) ≤ A.orderTop := by
    norm_num
    exact hA
  have hB4 : (↑(-3 * (4 : ℚ)) : WithTop ℚ) ≤ B.orderTop := by
    norm_num
    exact hB
  have hC4 : (↑(-4 * (4 : ℚ)) : WithTop ℚ) ≤ C0.orderTop := by
    norm_num
    exact hC
  have hD4 : (↑(-5 * (4 : ℚ)) : WithTop ℚ) ≤ D.orderTop := by
    norm_num
    exact hD
  have hE4 : (↑(-6 * (4 : ℚ)) : WithTop ℚ) ≤ E.orderTop := by
    norm_num
    exact hE
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hw : (2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE < 9) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-36 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have h := weightedMonomial68_orderTop_gt c A B C0 D E
      aA aB aC aD aE 4 9 (by norm_num) hA4 hB4 hC4 hD4 hE4 hw
    norm_num at h
    exact h
  have h1 := hzero zeta 1 0 0 0 0 (by norm_num)
  have h2 := hzero (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have h3 := hzero (3 * delta) 0 0 1 0 0 (by norm_num)
  have h4 := hzero (4 * gamma) 0 0 0 1 0 (by norm_num)
  have h5 := hzero (5 * beta) 0 0 0 0 1 (by norm_num)
  have h6 := hzero (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have h7 := hzero (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have h8 := hzero ((7 / 12 : k) * L) 0 0 2 0 0 (by norm_num)
  have h9 := hzero ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have h10 := hzero ((385 / 5184 : k) * L) 4 0 0 0 0 (by norm_num)
  have h11 := hzero (-(35 / 72 : k) * L) 1 2 0 0 0 (by norm_num)
  have h12 := hzero (-(35 / 72 : k) * L) 2 0 1 0 0 (by norm_num)
  have h13 := hzero (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have h14 := hzero (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have h15 := hzero ((7 / 6 : k) * L) 1 0 0 0 1 (by norm_num)
  have h16 := hzero ((7 / 6 : k) * L) 0 1 0 1 0 (by norm_num)
  simp only [firstIntegralFourHigherHahn68, HahnSeries.coeff_add,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, add_zero]

theorem firstIntegralFourTopFaceHahn68_coeff_neg36
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-8 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-12 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-16 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-20 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-24 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFourTopFaceHahn68 A B C0 D E).coeff (-36 : ℚ) =
      (8 / 81 : k) * topRowFour68 (A.coeff (-8 : ℚ))
        (B.coeff (-12 : ℚ)) (C0.coeff (-16 : ℚ))
        (D.coeff (-20 : ℚ)) (E.coeff (-24 : ℚ)) := by
  have hA4 : (↑(-2 * (4 : ℚ)) : WithTop ℚ) ≤ A.orderTop := by
    norm_num
    exact hA
  have hB4 : (↑(-3 * (4 : ℚ)) : WithTop ℚ) ≤ B.orderTop := by
    norm_num
    exact hB
  have hC4 : (↑(-4 * (4 : ℚ)) : WithTop ℚ) ≤ C0.orderTop := by
    norm_num
    exact hC
  have hD4 : (↑(-5 * (4 : ℚ)) : WithTop ℚ) ≤ D.orderTop := by
    norm_num
    exact hD
  have hE4 : (↑(-6 * (4 : ℚ)) : WithTop ℚ) ≤ E.orderTop := by
    norm_num
    exact hE
  have h1 := weightedMonomial68_coeff_at_weight
    (-8 / 27 : k) A B C0 D E 0 3 0 0 0 4 hA4 hB4 hC4 hD4 hE4
  have h2 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 2 0 0 1 0 4 hA4 hB4 hC4 hD4 hE4
  have h3 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 1 0 0 1 4 hA4 hB4 hC4 hD4 hE4
  have h4 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 0 1 1 0 4 hA4 hB4 hC4 hD4 hE4
  have h5 := weightedMonomial68_coeff_at_weight
    (40 / 81 : k) A B C0 D E 3 1 0 0 0 4 hA4 hB4 hC4 hD4 hE4
  have h6 := weightedMonomial68_coeff_at_weight
    (-16 / 9 : k) A B C0 D E 1 1 1 0 0 4 hA4 hB4 hC4 hD4 hE4
  have h1' :
      (weightedMonomial68 (-8 / 27 : k) A B C0 D E 0 3 0 0 0).coeff
          (-36 : ℚ) = (-8 / 27 : k) * (B.coeff (-12 : ℚ)) ^ 3 := by
    convert h1 using 1 <;> norm_num
  have h2' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 1 0).coeff
          (-36 : ℚ) = (-8 / 9 : k) * (A.coeff (-8 : ℚ)) ^ 2 *
            D.coeff (-20 : ℚ) := by
    convert h2 using 1 <;> norm_num
  have h3' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 1 0 0 1).coeff
          (-36 : ℚ) = (8 / 3 : k) * B.coeff (-12 : ℚ) *
            E.coeff (-24 : ℚ) := by
    convert h3 using 1 <;> norm_num
  have h4' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 1 0).coeff
          (-36 : ℚ) = (8 / 3 : k) * C0.coeff (-16 : ℚ) *
            D.coeff (-20 : ℚ) := by
    convert h4 using 1 <;> norm_num
  have h5' :
      (weightedMonomial68 (40 / 81 : k) A B C0 D E 3 1 0 0 0).coeff
          (-36 : ℚ) = (40 / 81 : k) * (A.coeff (-8 : ℚ)) ^ 3 *
            B.coeff (-12 : ℚ) := by
    convert h5 using 1 <;> norm_num
  have h6' :
      (weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 1 0 0).coeff
          (-36 : ℚ) = (-16 / 9 : k) * A.coeff (-8 : ℚ) *
            B.coeff (-12 : ℚ) * C0.coeff (-16 : ℚ) := by
    convert h6 using 1 <;> norm_num
  simp only [firstIntegralFourTopFaceHahn68, HahnSeries.coeff_add]
  rw [h1', h2', h3', h4', h5', h6']
  simp only [topRowFour68]
  ring

theorem firstIntegralFour68_coeff_neg36
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-8 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-12 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-16 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-20 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-24 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-36 : ℚ) =
      (8 / 81 : k) * topRowFour68 (A.coeff (-8 : ℚ))
        (B.coeff (-12 : ℚ)) (C0.coeff (-16 : ℚ))
        (D.coeff (-20 : ℚ)) (E.coeff (-24 : ℚ)) := by
  rw [firstIntegralFour68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralFourTopFaceHahn68_coeff_neg36 A B C0 D E
      hA hB hC hD hE,
    firstIntegralFourHigherHahn68_coeff_neg36
      L beta gamma delta epsilon zeta A B C0 D E hA hB hC hD hE,
    add_zero]

theorem SquareConstantLIntegratedLocalRootData68.topRowFourRhoFour_zero
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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
    (fun x : HahnSeries ℚ k => x.coeff (-36 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-36 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_neg36
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA hB hC hD hE
  rw [hface] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem linearPolynomial_dvd_of_eval_eq_zero
    (h f : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hf : f.eval a = 0) : h ∣ f := by
  have hlinearRoot : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hf
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h = C c * (X - C a) := by
    calc
      h = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

/-- The `rho=4` face forces a second copy of the scale into `p₅`. -/
theorem SquareConstantLIntegratedLocalRootData68.source_scale_sq_dvd_p5
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

end LocalRhoFour68

#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoFour
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsRhoFour
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateInitialCoeffsRhoFour
#print axioms firstIntegralFour68_coeff_neg36
#print axioms SquareConstantLIntegratedLocalRootData68.topRowFourRhoFour_zero
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_sq_dvd_p5

end Max11DegreeRoutes
