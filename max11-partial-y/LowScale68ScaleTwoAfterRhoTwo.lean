import LowScale68ScaleTwoLocalRhoTwo

/-! # The nonuniform faces after the `rho = 2` descent

Once `h⁴ | p₅`, the quartic coefficient limits the next cancellation.
The coordinate pole boxes become consecutive rather than weighted:
`(4,5,6,7,8)`, and after the first forced factor of `h` in `p₄`,
`(3,4,5,6,7)`.  In either box the unique worst term of the second exact
first integral is `(-16/243) A⁵`.  This file extracts that face and proves
`h² | p₄`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoTwo68

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoTwoHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-! ## A generic consecutive-box extractor -/

theorem weightedMonomial68_orderTop_lower_general
    (c : k) (A B C0 D E : HahnSeries ℚ k)
    (aA aB aC aD aE : ℕ) (rA rB rC rD rE : ℚ)
    (hA : (↑rA : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑rB : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑rC : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑rD : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑rE : WithTop ℚ) ≤ E.orderTop) :
    (↑((aA : ℚ) * rA + (aB : ℚ) * rB + (aC : ℚ) * rC +
        (aD : ℚ) * rD + (aE : ℚ) * rE) : WithTop ℚ) ≤
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).orderTop := by
  have hc : (0 : WithTop ℚ) ≤
      (HahnSeries.C c : HahnSeries ℚ k).orderTop := hahnOrderTop_C_nonneg46 c
  have hAp := hahnOrderTop_pow_lower46 A rA aA hA
  have hBp := hahnOrderTop_pow_lower46 B rB aB hB
  have hCp := hahnOrderTop_pow_lower46 C0 rC aC hC
  have hDp := hahnOrderTop_pow_lower46 D rD aD hD
  have hEp := hahnOrderTop_pow_lower46 E rE aE hE
  have hcA := hahnOrderTop_mul_lower46 (HahnSeries.C c) (A ^ aA)
    0 ((aA : ℚ) * rA) hc hAp
  have hcAB := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA) (B ^ aB)
    (0 + (aA : ℚ) * rA) ((aB : ℚ) * rB) hcA hBp
  have hcABC := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB) (C0 ^ aC)
    ((0 + (aA : ℚ) * rA) + (aB : ℚ) * rB) ((aC : ℚ) * rC) hcAB hCp
  have hcABCD := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC) (D ^ aD)
    (((0 + (aA : ℚ) * rA) + (aB : ℚ) * rB) + (aC : ℚ) * rC)
    ((aD : ℚ) * rD) hcABC hDp
  have hfull := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC * D ^ aD) (E ^ aE)
    ((((0 + (aA : ℚ) * rA) + (aB : ℚ) * rB) + (aC : ℚ) * rC) +
      (aD : ℚ) * rD) ((aE : ℚ) * rE) hcABCD hEp
  have hfull' :
      (↑(0 + (aA : ℚ) * rA + (aB : ℚ) * rB + (aC : ℚ) * rC +
          (aD : ℚ) * rD + (aE : ℚ) * rE) : WithTop ℚ) ≤
        (weightedMonomial68 c A B C0 D E aA aB aC aD aE).orderTop := by
    simpa only [weightedMonomial68] using hfull
  convert hfull' using 1 <;> norm_num

theorem weightedMonomial68_coeff_zero_of_general_lower
    (c : k) (A B C0 D E : HahnSeries ℚ k)
    (aA aB aC aD aE : ℕ) (rA rB rC rD rE target : ℚ)
    (hA : (↑rA : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑rB : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑rC : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑rD : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑rE : WithTop ℚ) ≤ E.orderTop)
    (hlt : target < (aA : ℚ) * rA + (aB : ℚ) * rB +
      (aC : ℚ) * rC + (aD : ℚ) * rD + (aE : ℚ) * rE) :
    (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff target = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  exact (WithTop.coe_lt_coe.mpr hlt).trans_le
    (weightedMonomial68_orderTop_lower_general c A B C0 D E
      aA aB aC aD aE rA rB rC rD rE hA hB hC hD hE)

set_option maxHeartbeats 3000000

/- In every consecutive pole box `(m,m+1,…,m+4)` with `m>2`, the
coefficient at `-5m` of the second exact first integral is its unique
`A⁵` term. -/
theorem firstIntegralThree68_coeff_unique_A_five_consecutive
    (m : ℚ) (hm : 2 < m)
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-m) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-(m + 1)) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-(m + 2)) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-(m + 3)) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-(m + 4)) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThree68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-5 * m) =
      (-16 / 243 : k) * (A.coeff (-m)) ^ 5 := by
  let rA : ℚ := -m
  let rB : ℚ := -(m + 1)
  let rC : ℚ := -(m + 2)
  let rD : ℚ := -(m + 3)
  let rE : ℚ := -(m + 4)
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : -5 * m < (aA : ℚ) * rA + (aB : ℚ) * rB +
        (aC : ℚ) * rC + (aD : ℚ) * rD + (aE : ℚ) * rE) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-5 * m) = 0 := by
    apply weightedMonomial68_coeff_zero_of_general_lower
      c A B C0 D E aA aB aC aD aE rA rB rC rD rE (-5 * m)
      (by simpa only [rA] using hA) (by simpa only [rB] using hB)
      (by simpa only [rC] using hC) (by simpa only [rD] using hD)
      (by simpa only [rE] using hE) hlt
  have hleadOrder := hahnOrderTop_pow_lower46 A (-m) 5 hA
  have hconstOrder : (0 : WithTop ℚ) ≤
      (HahnSeries.C (-16 / 243 : k) : HahnSeries ℚ k).orderTop :=
    hahnOrderTop_C_nonneg46 _
  have hleadMul := hahnCoeff_mul_at_lower46
    (HahnSeries.C (-16 / 243 : k)) (A ^ 5) 0 (5 * (-m))
      hconstOrder hleadOrder
  have hleadPow :
      (A ^ 5).coeff (5 * (-m)) = (A.coeff (-m)) ^ 5 := by
    convert hahnCoeff_pow_at_lower46 A (-m) 5 hA using 1 <;> norm_num
  have hlead :
      (weightedMonomial68 (-16 / 243 : k) A B C0 D E 5 0 0 0 0).coeff
          (-5 * m) = (-16 / 243 : k) * (A.coeff (-m)) ^ 5 := by
    simp only [weightedMonomial68, pow_zero, mul_one]
    rw [show -5 * m = 0 + 5 * (-m) by ring, hleadMul,
      HahnSeries.C_apply, HahnSeries.coeff_single_same, hleadPow]
  have ht2 := hzero (4 / 3 : k) 0 0 0 2 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have ht3 := hzero (-8 / 9 : k) 1 0 2 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have ht4 := hzero (-8 / 9 : k) 0 2 1 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have ht5 := hzero (-8 / 9 : k) 2 0 0 0 1 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have ht6 := hzero (8 / 3 : k) 0 0 1 0 1 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have ht7 := hzero (20 / 27 : k) 2 2 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have ht8 := hzero (40 / 81 : k) 3 0 1 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have ht9 := hzero (-16 / 9 : k) 1 1 0 1 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh1 := hzero zeta 0 1 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh2 := hzero (2 * epsilon) 0 0 1 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh3 := hzero (3 * delta) 0 0 0 1 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh4 := hzero (4 * gamma) 0 0 0 0 1 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh5 := hzero (-(35 / 216 : k) * L) 0 3 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh6 := hzero (-(2 / 3 : k) * epsilon) 2 0 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh7 := hzero (-(2 / 3 : k) * gamma) 0 2 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh8 := hzero ((8 / 27 : k) * gamma) 3 0 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh9 := hzero (-(35 / 72 : k) * L) 2 0 0 1 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh10 := hzero (-(5 / 6 : k) * beta) 1 0 0 1 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh11 := hzero (-(5 / 6 : k) * beta) 0 1 1 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh12 := hzero (-(4 / 3 : k) * gamma) 1 0 1 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh13 := hzero (-(3 / 2 : k) * delta) 1 1 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh14 := hzero ((7 / 6 : k) * L) 0 1 0 0 1 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh15 := hzero ((7 / 6 : k) * L) 0 0 1 1 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh16 := hzero ((35 / 72 : k) * beta) 2 1 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh17 := hzero ((385 / 1296 : k) * L) 3 1 0 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  have hh18 := hzero (-(35 / 36 : k) * L) 1 1 1 0 0 (by dsimp [rA,rB,rC,rD,rE]; nlinarith)
  rw [firstIntegralThree68_eq_localFaces]
  simp only [firstIntegralThreeTopFaceHahn68,
    firstIntegralThreeHigherHahn68, HahnSeries.coeff_add]
  rw [hlead, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9,
    hh1, hh2, hh3, hh4, hh5, hh6, hh7, hh8, hh9, hh10, hh11,
    hh12, hh13, hh14, hh15, hh16, hh17, hh18]
  ring

/-! ## First nonuniform box: force `h | p₄` -/

def localClearedA68AfterRhoTwo (h g a4 : k[X]) : k[X] :=
  a4 - C (5 / 12 : k) * h ^ 2 * g ^ 2

def localClearedB68AfterRhoTwo (h g a4 a3 : k[X]) : k[X] :=
  a3 * h ^ 2 - C (2 / 3 : k) * a4 * g + C (5 / 27 : k) * h ^ 2 * g ^ 3

def localClearedC68AfterRhoTwo (h g a4 a3 a2 : k[X]) : k[X] :=
  a2 * h ^ 4 - C (1 / 2 : k) * a3 * g * h ^ 2 +
    C (1 / 6 : k) * a4 * g ^ 2 - C (5 / 144 : k) * h ^ 2 * g ^ 4

def localClearedD68AfterRhoTwo (h g a4 a3 a2 a1 : k[X]) : k[X] :=
  a1 * h ^ 6 - C (1 / 3 : k) * a2 * g * h ^ 4 +
    C (1 / 12 : k) * a3 * g ^ 2 * h ^ 2 -
    C (1 / 54 : k) * a4 * g ^ 3 + C (1 / 324 : k) * h ^ 2 * g ^ 5

def localClearedE68AfterRhoTwo (h g a4 a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 8 - C (1 / 6 : k) * a1 * g * h ^ 6 +
    C (1 / 36 : k) * a2 * g ^ 2 * h ^ 4 -
    C (1 / 216 : k) * a3 * g ^ 3 * h ^ 2 +
    C (1 / 1296 : k) * a4 * g ^ 4 - C (5 / 46656 : k) * h ^ 2 * g ^ 6

theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k)
        (localClearedA68AfterRhoTwo h0 g (p.coeff 4)) = h ^ 4 * S.A ∧
    algebraMap k[X] (RatFunc k)
        (localClearedB68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)) =
      h ^ 5 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2)) = h ^ 6 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1)) = h ^ 7 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0)) = h ^ 8 * S.E := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    S.clearedCoordinates hp hh0 hH hp6
  let A0 := localClearedA68AfterRhoTwo h0 g (p.coeff 4)
  let B0 := localClearedB68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
  let C0 := localClearedC68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2)
  let D0 := localClearedD68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1)
  let E0 := localClearedE68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1) (p.coeff 0)
  have hfA : localClearedA68 h0 (p.coeff 5) (p.coeff 4) = h0 ^ 6 * A0 := by
    rw [hp5]
    simp only [localClearedA68, A0, localClearedA68AfterRhoTwo]
    ring
  have hfB : localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3) =
      h0 ^ 10 * B0 := by
    rw [hp5]
    simp only [localClearedB68, B0, localClearedB68AfterRhoTwo]
    ring
  have hfC : localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) = h0 ^ 14 * C0 := by
    rw [hp5]
    simp only [localClearedC68, C0, localClearedC68AfterRhoTwo]
    ring
  have hfD : localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) = h0 ^ 18 * D0 := by
    rw [hp5]
    simp only [localClearedD68, D0, localClearedD68AfterRhoTwo]
    ring
  have hfE : localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) = h0 ^ 22 * E0 := by
    rw [hp5]
    simp only [localClearedE68, E0, localClearedE68AfterRhoTwo]
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
  · exact algebraMap_cancel_factoredClearing h0 _ A0 S.A 6 4 1
      hh0 hfA hA
  · exact algebraMap_cancel_factoredClearing h0 _ B0 S.B 10 5 1
      hh0 hfB hB
  · exact algebraMap_cancel_factoredClearing h0 _ C0 S.C0 14 6 1
      hh0 hfC hC
  · exact algebraMap_cancel_factoredClearing h0 _ D0 S.D 18 7 1
      hh0 hfD hD
  · exact algebraMap_cancel_factoredClearing h0 _ E0 S.E 22 8 1
      hh0 hfE hE

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsAfterRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 4 * g) :
    (↑(-4 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-5 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-6 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-7 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-8 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesAfterRhoTwo
      hp T.scale_ne_zero hH hp6 hp5
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68AfterRhoTwo h0 g (p.coeff 4)) T.source.A 4
      T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)) T.source.B 5
      T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2))
      T.source.C0 6 T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1)) T.source.D 7 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) T.source.E 8 T.scale_order hE⟩

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialAAfterRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 4 * g) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-4 : ℚ) =
        (c ^ 4)⁻¹ *
          (localClearedA68AfterRhoTwo h0 g (p.coeff 4)).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinatesAfterRhoTwo
      hp T.scale_ne_zero hH hp6 hp5
  exact ⟨c, hc, localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedA68AfterRhoTwo h0 g (p.coeff 4)) T.source.A 4
    hc hsingle hA⟩

theorem SquareConstantLIntegratedLocalRootData68.topAAfterRhoTwo_zero
    {p q : k[X][X]} {j l : k} {h0 H g : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hp5 : p.coeff 5 = h0 ^ 4 * g) :
    (ratFuncAtHahn46 T.root T.source.A).coeff (-4 : ℚ) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterRhoTwo hp hH hp6 hp5
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
  have hface := firstIntegralThree68_coeff_unique_A_five_consecutive
    4 (by norm_num) l T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralThree68 (HahnSeries.C l) AH BH CH DH EH
        (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
        (HahnSeries.C T.source.zeta)).coeff (-20 : ℚ) =
          (-16 / 243 : k) * (AH.coeff (-4 : ℚ)) ^ 5 := by
    convert hface using 1 <;> norm_num
  rw [hface'] at hcoeff
  have hfactor : (-16 / 243 : k) ≠ 0 := by norm_num
  have hpow : (AH.coeff (-4 : ℚ)) ^ 5 = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_left hfactor
  have hAz : AH.coeff (-4 : ℚ) = 0 := eq_zero_of_pow_eq_zero hpow
  simpa only [AH] using hAz

theorem SquareConstantLIntegratedLocalRootData68.source_scale_dvd_p4_afterRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) : h0 ∣ p.coeff 4 := by
  obtain ⟨g, hp5⟩ := T.source_scale_fourth_dvd_p5 hp hH hp6
  have htop := T.topAAfterRhoTwo_zero hp hH hp6 hp5
  obtain ⟨c, hc, hAco⟩ :=
    T.coordinateInitialAAfterRhoTwo hp hH hp6 hp5
  have hAroot :
      (localClearedA68AfterRhoTwo h0 g (p.coeff 4)).eval T.root =
        (p.coeff 4).eval T.root := by
    simp [localClearedA68AfterRhoTwo, T.root_eq]
  rw [hAco, hAroot] at htop
  have hcinv : (c ^ 4)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 4 hc)
  have hp4root : (p.coeff 4).eval T.root = 0 :=
    (mul_eq_zero.mp htop).resolve_left hcinv
  exact linearPolynomial_dvd_of_eval_eq_zero
    h0 (p.coeff 4) T.root T.scale_degree T.root_eq hp4root

/-! ## Second consecutive box: force the second copy of `h` in `p₄` -/

def localClearedA68AfterRhoTwoOne (h g u : k[X]) : k[X] :=
  u - C (5 / 12 : k) * h * g ^ 2

def localClearedB68AfterRhoTwoOne (h g u a3 : k[X]) : k[X] :=
  a3 * h - C (2 / 3 : k) * u * g + C (5 / 27 : k) * h * g ^ 3

def localClearedC68AfterRhoTwoOne (h g u a3 a2 : k[X]) : k[X] :=
  a2 * h ^ 3 - C (1 / 2 : k) * a3 * g * h +
    C (1 / 6 : k) * u * g ^ 2 - C (5 / 144 : k) * h * g ^ 4

def localClearedD68AfterRhoTwoOne (h g u a3 a2 a1 : k[X]) : k[X] :=
  a1 * h ^ 5 - C (1 / 3 : k) * a2 * g * h ^ 3 +
    C (1 / 12 : k) * a3 * g ^ 2 * h -
    C (1 / 54 : k) * u * g ^ 3 + C (1 / 324 : k) * h * g ^ 5

def localClearedE68AfterRhoTwoOne (h g u a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 7 - C (1 / 6 : k) * a1 * g * h ^ 5 +
    C (1 / 36 : k) * a2 * g ^ 2 * h ^ 3 -
    C (1 / 216 : k) * a3 * g ^ 3 * h +
    C (1 / 1296 : k) * u * g ^ 4 - C (5 / 46656 : k) * h * g ^ 6

theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterRhoTwoOne
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 * u) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k)
        (localClearedA68AfterRhoTwoOne h0 g u) = h ^ 3 * S.A ∧
    algebraMap k[X] (RatFunc k)
        (localClearedB68AfterRhoTwoOne h0 g u (p.coeff 3)) = h ^ 4 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)) =
      h ^ 5 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1)) = h ^ 6 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0)) = h ^ 7 * S.E := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    S.clearedCoordinatesAfterRhoTwo hp hh0 hH hp6 hp5
  let A1 := localClearedA68AfterRhoTwoOne h0 g u
  let B1 := localClearedB68AfterRhoTwoOne h0 g u (p.coeff 3)
  let C1 := localClearedC68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D1 := localClearedD68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
  let E1 := localClearedE68AfterRhoTwoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
  have hfA : localClearedA68AfterRhoTwo h0 g (p.coeff 4) = h0 * A1 := by
    rw [hp4]
    simp only [localClearedA68AfterRhoTwo, A1,
      localClearedA68AfterRhoTwoOne]
    ring
  have hfB : localClearedB68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3) =
      h0 * B1 := by
    rw [hp4]
    simp only [localClearedB68AfterRhoTwo, B1,
      localClearedB68AfterRhoTwoOne]
    ring
  have hfC : localClearedC68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2) = h0 * C1 := by
    rw [hp4]
    simp only [localClearedC68AfterRhoTwo, C1,
      localClearedC68AfterRhoTwoOne]
    ring
  have hfD : localClearedD68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) = h0 * D1 := by
    rw [hp4]
    simp only [localClearedD68AfterRhoTwo, D1,
      localClearedD68AfterRhoTwoOne]
    ring
  have hfE : localClearedE68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) = h0 * E1 := by
    rw [hp4]
    simp only [localClearedE68AfterRhoTwo, E1,
      localClearedE68AfterRhoTwoOne]
    ring
  change algebraMap k[X] (RatFunc k)
      (localClearedA68AfterRhoTwo h0 g (p.coeff 4)) = _ at hA
  change algebraMap k[X] (RatFunc k)
      (localClearedB68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)) = _ at hB
  change algebraMap k[X] (RatFunc k)
      (localClearedC68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) = _ at hC
  change algebraMap k[X] (RatFunc k)
      (localClearedD68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) = _ at hD
  change algebraMap k[X] (RatFunc k)
      (localClearedE68AfterRhoTwo h0 g (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) = _ at hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact algebraMap_cancel_factoredClearing h0 _ A1 S.A 1 3 1
      hh0 (by simpa using hfA) hA
  · exact algebraMap_cancel_factoredClearing h0 _ B1 S.B 1 4 1
      hh0 (by simpa using hfB) hB
  · exact algebraMap_cancel_factoredClearing h0 _ C1 S.C0 1 5 1
      hh0 (by simpa using hfC) hC
  · exact algebraMap_cancel_factoredClearing h0 _ D1 S.D 1 6 1
      hh0 (by simpa using hfD) hD
  · exact algebraMap_cancel_factoredClearing h0 _ E1 S.E 1 7 1
      hh0 (by simpa using hfE) hE

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsAfterRhoTwoOne
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialAAfterRhoTwoOne
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

theorem SquareConstantLIntegratedLocalRootData68.topAAfterRhoTwoOne_zero
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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
    (fun x : HahnSeries ℚ k => x.coeff (-15 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-15 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_unique_A_five_consecutive
    3 (by norm_num) l T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by norm_num; exact hB)
      (by norm_num; exact hC) (by norm_num; exact hD)
      (by norm_num; exact hE)
  have hface' :
      (firstIntegralThree68 (HahnSeries.C l) AH BH CH DH EH
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

theorem SquareConstantLIntegratedLocalRootData68.source_scale_dvd_p4_quotient
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
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

/-- The two consecutive unique `A⁵` faces after the `rho=2` descent force
two copies of the local scale into the next sextic coefficient. -/
theorem SquareConstantLIntegratedLocalRootData68.source_scale_sq_dvd_p4_afterRhoTwo
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) : h0 ^ 2 ∣ p.coeff 4 := by
  obtain ⟨g, hp5⟩ := T.source_scale_fourth_dvd_p5 hp hH hp6
  obtain ⟨u, hp4⟩ := T.source_scale_dvd_p4_afterRhoTwo hp hH hp6
  obtain ⟨v, huv⟩ :=
    T.source_scale_dvd_p4_quotient hp hH hp6 hp5 hp4
  refine ⟨v, ?_⟩
  rw [hp4, huv]
  ring

end AfterRhoTwo68

#print axioms firstIntegralThree68_coeff_unique_A_five_consecutive
#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterRhoTwo
#print axioms SquareConstantLIntegratedLocalRootData68.topAAfterRhoTwo_zero
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_sq_dvd_p4_afterRhoTwo

end Max11DegreeRoutes
