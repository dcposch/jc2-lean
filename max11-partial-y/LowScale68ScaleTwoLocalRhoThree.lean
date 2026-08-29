import LowScale68ScaleTwoLocalRhoFour

/-! # The improved `rho = 3` local box for `(6,8)`

Starting with `h² | p₅`, write `p₅ = h² g`.  The five depressed
coordinates then have polynomial clearings at exponents
`(6,9,12,15,18)`.  A parameterized version of the first-integral face
extracts the weight-nine equation at exponent `-27`, forcing `h | g` and
therefore `h³ | p₅`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LocalRhoThree68

variable {k : Type*} [Field k] [CharZero k]

local instance localRhoThreeHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedA68RhoThree (h g a4 : k[X]) : k[X] :=
  a4 * h ^ 2 - C (5 / 12 : k) * g ^ 2

def localClearedB68RhoThree (h g a4 a3 : k[X]) : k[X] :=
  a3 * h ^ 6 - C (2 / 3 : k) * a4 * g * h ^ 2 +
    C (5 / 27 : k) * g ^ 3

def localClearedC68RhoThree (h g a4 a3 a2 : k[X]) : k[X] :=
  a2 * h ^ 10 - C (1 / 2 : k) * a3 * g * h ^ 6 +
    C (1 / 6 : k) * a4 * g ^ 2 * h ^ 2 -
    C (5 / 144 : k) * g ^ 4

def localClearedD68RhoThree (h g a4 a3 a2 a1 : k[X]) : k[X] :=
  a1 * h ^ 14 - C (1 / 3 : k) * a2 * g * h ^ 10 +
    C (1 / 12 : k) * a3 * g ^ 2 * h ^ 6 -
    C (1 / 54 : k) * a4 * g ^ 3 * h ^ 2 +
    C (1 / 324 : k) * g ^ 5

def localClearedE68RhoThree (h g a4 a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 18 - C (1 / 6 : k) * a1 * g * h ^ 14 +
    C (1 / 36 : k) * a2 * g ^ 2 * h ^ 10 -
    C (1 / 216 : k) * a3 * g ^ 3 * h ^ 6 +
    C (1 / 1296 : k) * a4 * g ^ 4 * h ^ 2 -
    C (5 / 46656 : k) * g ^ 6

/-- General cancellation of a factored polynomial denominator clearing. -/
theorem algebraMap_cancel_factoredClearing
    (h old new : k[X]) (A : RatFunc k) (s r w : ℕ) (hh : h ≠ 0)
    (hfact : old = h ^ (s * w) * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h) ^ ((r + s) * w) * A) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h) ^ (r * w) * A := by
  let hR : RatFunc k := algebraMap k[X] (RatFunc k) h
  have hhR : hR ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hfact
  apply mul_left_cancel₀ (pow_ne_zero (s * w) hhR)
  calc
    hR ^ (s * w) * algebraMap k[X] (RatFunc k) new =
        algebraMap k[X] (RatFunc k) old := by
      dsimp only [hR]
      simpa only [map_mul, map_pow] using hmapped.symm
    _ = hR ^ ((r + s) * w) * A := hclear
    _ = hR ^ (s * w) * (hR ^ (r * w) * A) := by
      rw [Nat.add_mul, pow_add]
      ring

theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoThree
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 2 * g) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k)
        (localClearedA68RhoThree h0 g (p.coeff 4)) = h ^ 6 * S.A ∧
    algebraMap k[X] (RatFunc k)
        (localClearedB68RhoThree h0 g (p.coeff 4) (p.coeff 3)) =
      h ^ 9 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68RhoThree h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2)) = h ^ 12 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68RhoThree h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1)) = h ^ 15 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68RhoThree h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0)) = h ^ 18 * S.E := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    S.clearedCoordinates hp hh0 hH hp6
  let A3 := localClearedA68RhoThree h0 g (p.coeff 4)
  let B3 := localClearedB68RhoThree h0 g (p.coeff 4) (p.coeff 3)
  let C3 := localClearedC68RhoThree h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2)
  let D3 := localClearedD68RhoThree h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1)
  let E3 := localClearedE68RhoThree h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1) (p.coeff 0)
  have hfA : localClearedA68 h0 (p.coeff 5) (p.coeff 4) = h0 ^ 4 * A3 := by
    rw [hp5]
    simp only [localClearedA68, A3, localClearedA68RhoThree]
    ring
  have hfB : localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3) =
      h0 ^ 6 * B3 := by
    rw [hp5]
    simp only [localClearedB68, B3, localClearedB68RhoThree]
    ring
  have hfC : localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) = h0 ^ 8 * C3 := by
    rw [hp5]
    simp only [localClearedC68, C3, localClearedC68RhoThree]
    ring
  have hfD : localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) = h0 ^ 10 * D3 := by
    rw [hp5]
    simp only [localClearedD68, D3, localClearedD68RhoThree]
    ring
  have hfE : localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) = h0 ^ 12 * E3 := by
    rw [hp5]
    simp only [localClearedE68, E3, localClearedE68RhoThree]
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
  · exact algebraMap_cancel_factoredClearing h0 _ A3 S.A 2 3 2
      hh0 hfA hA
  · exact algebraMap_cancel_factoredClearing h0 _ B3 S.B 2 3 3
      hh0 hfB hB
  · exact algebraMap_cancel_factoredClearing h0 _ C3 S.C0 2 3 4
      hh0 hfC hC
  · exact algebraMap_cancel_factoredClearing h0 _ D3 S.D 2 3 5
      hh0 hfD hD
  · exact algebraMap_cancel_factoredClearing h0 _ E3 S.E 2 3 6
      hh0 hfE hE

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsRhoThree
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialCoeffsRhoThree
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

/-! ## A reusable positive-radius first face -/

theorem firstIntegralFourHigherHahn68_coeff_at_rho
    (rho : ℚ) (hrho : 0 < rho)
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFourHigherHahn68 L beta gamma delta epsilon zeta
      A B C0 D E).coeff (-9 * rho) = 0 := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hw : (2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE < 9) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-9 * rho) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact weightedMonomial68_orderTop_gt c A B C0 D E
      aA aB aC aD aE rho 9 hrho hA hB hC hD hE hw
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

theorem firstIntegralFourTopFaceHahn68_coeff_at_rho
    (rho : ℚ) (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFourTopFaceHahn68 A B C0 D E).coeff (-9 * rho) =
      (8 / 81 : k) * topRowFour68 (A.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (C0.coeff (-4 * rho))
        (D.coeff (-5 * rho)) (E.coeff (-6 * rho)) := by
  have h1 := weightedMonomial68_coeff_at_weight
    (-8 / 27 : k) A B C0 D E 0 3 0 0 0 rho hA hB hC hD hE
  have h2 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 2 0 0 1 0 rho hA hB hC hD hE
  have h3 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 1 0 0 1 rho hA hB hC hD hE
  have h4 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 0 1 1 0 rho hA hB hC hD hE
  have h5 := weightedMonomial68_coeff_at_weight
    (40 / 81 : k) A B C0 D E 3 1 0 0 0 rho hA hB hC hD hE
  have h6 := weightedMonomial68_coeff_at_weight
    (-16 / 9 : k) A B C0 D E 1 1 1 0 0 rho hA hB hC hD hE
  have h1' :
      (weightedMonomial68 (-8 / 27 : k) A B C0 D E 0 3 0 0 0).coeff
          (-9 * rho) = (-8 / 27 : k) * (B.coeff (-3 * rho)) ^ 3 := by
    convert h1 using 1 <;> norm_num
  have h2' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 1 0).coeff
          (-9 * rho) = (-8 / 9 : k) * (A.coeff (-2 * rho)) ^ 2 *
            D.coeff (-5 * rho) := by
    convert h2 using 1 <;> norm_num
  have h3' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 1 0 0 1).coeff
          (-9 * rho) = (8 / 3 : k) * B.coeff (-3 * rho) *
            E.coeff (-6 * rho) := by
    convert h3 using 1 <;> norm_num
  have h4' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 1 0).coeff
          (-9 * rho) = (8 / 3 : k) * C0.coeff (-4 * rho) *
            D.coeff (-5 * rho) := by
    convert h4 using 1 <;> norm_num
  have h5' :
      (weightedMonomial68 (40 / 81 : k) A B C0 D E 3 1 0 0 0).coeff
          (-9 * rho) = (40 / 81 : k) * (A.coeff (-2 * rho)) ^ 3 *
            B.coeff (-3 * rho) := by
    convert h5 using 1 <;> norm_num
  have h6' :
      (weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 1 0 0).coeff
          (-9 * rho) = (-16 / 9 : k) * A.coeff (-2 * rho) *
            B.coeff (-3 * rho) * C0.coeff (-4 * rho) := by
    convert h6 using 1 <;> norm_num
  simp only [firstIntegralFourTopFaceHahn68, HahnSeries.coeff_add]
  rw [h1', h2', h3', h4', h5', h6']
  simp only [topRowFour68]
  ring

theorem firstIntegralFour68_coeff_at_rho
    (rho : ℚ) (hrho : 0 < rho)
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-9 * rho) =
      (8 / 81 : k) * topRowFour68 (A.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (C0.coeff (-4 * rho))
        (D.coeff (-5 * rho)) (E.coeff (-6 * rho)) := by
  rw [firstIntegralFour68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralFourTopFaceHahn68_coeff_at_rho rho A B C0 D E
      hA hB hC hD hE,
    firstIntegralFourHigherHahn68_coeff_at_rho rho hrho
      L beta gamma delta epsilon zeta A B C0 D E hA hB hC hD hE,
    add_zero]

theorem SquareConstantLIntegratedLocalRootData68.topRowFourRhoThree_zero
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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
    (fun x : HahnSeries ℚ k => x.coeff (-27 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-27 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_at_rho 3 (by norm_num)
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA3 hB3 hC3 hD3 hE3
  have hface' :
      (firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
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

theorem SquareConstantLIntegratedLocalRootData68.source_scale_cube_dvd_p5
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

end LocalRhoThree68

#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoThree
#print axioms firstIntegralFour68_coeff_at_rho
#print axioms SquareConstantLIntegratedLocalRootData68.topRowFourRhoThree_zero
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_cube_dvd_p5

end Max11DegreeRoutes
