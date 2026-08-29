import LowScale68ScaleTwoAfterRhoOneAfterP4

/-! # The box after the third scale factor enters `p₃`

With `p₅=h⁵g`, `p₄=h⁴u`, `p₃=h³v`, and `p₂=hw`, the sharp
depressed box is `(0,0,1,1,1)`.  Its weight `-2` fourth- and third-integral
faces give either a second scale factor in `p₂` or one explicit quadratic
residual at the simple root.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOneAfterP368

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneAfterP3HahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedB68AfterP3 (g u v : k[X]) : k[X] :=
  v - C (2 / 3 : k) * u * g + C (5 / 27 : k) * g ^ 3

def localClearedC68AfterP3 (h g u v w : k[X]) : k[X] :=
  w - C (1 / 2 : k) * h * v * g + C (1 / 6 : k) * h * u * g ^ 2 -
    C (5 / 144 : k) * h * g ^ 4

def localClearedD68AfterP3
    (h g u v w a1 : k[X]) : k[X] :=
  a1 - C (1 / 3 : k) * w * g + C (1 / 12 : k) * h * v * g ^ 2 -
    C (1 / 54 : k) * h * u * g ^ 3 + C (1 / 324 : k) * h * g ^ 5

def localClearedE68AfterP3
    (h g u v w a1 a0 : k[X]) : k[X] :=
  a0 * h - C (1 / 6 : k) * a1 * g + C (1 / 36 : k) * w * g ^ 2 -
    C (1 / 216 : k) * h * v * g ^ 3 + C (1 / 1296 : k) * h * u * g ^ 4 -
    C (5 / 46656 : k) * h * g ^ 6

set_option maxHeartbeats 800000 in
theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterP3
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k) (localClearedA68AfterP4 g u) = S.A ∧
    algebraMap k[X] (RatFunc k) (localClearedB68AfterP3 g u v) = S.B ∧
    algebraMap k[X] (RatFunc k) (localClearedC68AfterP3 h0 g u v w) =
        h * S.C0 ∧
    algebraMap k[X] (RatFunc k)
      (localClearedD68AfterP3 h0 g u v w (p.coeff 1)) = h * S.D ∧
    algebraMap k[X] (RatFunc k)
      (localClearedE68AfterP3 h0 g u v w (p.coeff 1) (p.coeff 0)) =
        h * S.E := by
  dsimp only
  have hp3' : p.coeff 3 = h0 ^ 2 * (h0 * v) := by rw [hp3]; ring
  obtain ⟨hA, hB, hC, hD, hE⟩ := S.clearedCoordinatesAfterP4P2
    hp hh0 hH hp6 hp5 hp4 hp3' hp2
  let B0 := localClearedB68AfterP3 g u v
  have hfB : localClearedB68AfterP4 h0 g u (h0 * v) = h0 * B0 := by
    simp only [localClearedB68AfterP4, B0, localClearedB68AfterP3]
    ring
  change algebraMap k[X] (RatFunc k)
    (localClearedB68AfterP4 h0 g u (h0 * v)) = _ at hB
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · have hb := algebraMap_cancel_factoredClearing h0 _ B0 S.B
      1 0 1 hh0 (by simpa using hfB) (by convert hB using 1 <;> norm_num)
    simpa only [B0, Nat.zero_mul, pow_zero, one_mul] using hb
  · convert hC using 1 <;>
      simp only [localClearedC68AfterP3, localClearedC68AfterP4P2] <;> ring
  · convert hD using 1 <;>
      simp only [localClearedD68AfterP3, localClearedD68AfterP4P2] <;> ring
  · convert hE using 1 <;>
      simp only [localClearedE68AfterP3, localClearedE68AfterP4P2] <;> ring

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsAfterP3
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterP3
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3 hp2
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68AfterP4 g u) T.source.A 0 T.scale_order (by simpa using hA),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68AfterP3 g u v) T.source.B 0 T.scale_order (by simpa using hB),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68AfterP3 h0 g u v w) T.source.C0 1 T.scale_order
        (by simpa only [pow_one] using hC),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68AfterP3 h0 g u v w (p.coeff 1)) T.source.D 1
        T.scale_order (by simpa only [pow_one] using hD),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68AfterP3 h0 g u v w (p.coeff 1) (p.coeff 0))
        T.source.E 1 T.scale_order (by simpa only [pow_one] using hE)⟩

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialPacketAfterP3
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (0 : ℚ) =
        u.eval T.root - (5 / 12 : k) * g.eval T.root ^ 2 ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-1 : ℚ) =
        c⁻¹ * w.eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-1 : ℚ) =
        c⁻¹ * ((p.coeff 1).eval T.root -
          (1 / 3 : k) * w.eval T.root * g.eval T.root) ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-1 : ℚ) =
        c⁻¹ * (-(1 / 6 : k) * (p.coeff 1).eval T.root *
          g.eval T.root + (1 / 36 : k) * w.eval T.root * g.eval T.root ^ 2) := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterP3
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3 hp2
  have hAco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedA68AfterP4 g u) T.source.A 0 hc hsingle (by simpa using hA)
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedC68AfterP3 h0 g u v w) T.source.C0 1 hc hsingle
      (by simpa only [pow_one] using hC)
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedD68AfterP3 h0 g u v w (p.coeff 1)) T.source.D 1 hc hsingle
      (by simpa only [pow_one] using hD)
  have hEco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedE68AfterP3 h0 g u v w (p.coeff 1) (p.coeff 0)) T.source.E 1
      hc hsingle (by simpa only [pow_one] using hE)
  norm_num at hAco hCco hDco hEco
  refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
  · rw [hAco]
    simp [localClearedA68AfterP4, T.root_eq]
  · rw [hCco]
    simp [localClearedC68AfterP3, T.root_eq]
  · rw [hDco]
    simp [localClearedD68AfterP3, T.root_eq]
  · rw [hEco]
    simp [localClearedE68AfterP3, T.root_eq]

def afterP3FourFace68 (L x d : k) : k :=
  (8 / 3 : k) * x * d + (7 / 12 : k) * L * x ^ 2

def afterP3ThreeFace68 (L a x d e : k) : k :=
  (4 / 3 : k) * d ^ 2 - (8 / 9 : k) * a * x ^ 2 +
    (8 / 3 : k) * x * e +
    (7 / 6 : k) * L * x * d

theorem firstIntegralFour68_coeff_neg2_afterP3
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop)
    (hB : (0 : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-1 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-1 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-1 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-2 : ℚ) =
      afterP3FourFace68 L (C0.coeff (-1 : ℚ)) (D.coeff (-1 : ℚ)) := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-2 : ℚ) < (aA : ℚ) * 0 + (aB : ℚ) * 0 +
        (aC : ℚ) * (-1) + (aD : ℚ) * (-1) + (aE : ℚ) * (-1)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-2 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE 0 0 (-1) (-1) (-1) (-2)
      hA hB hC hD hE hlt
  have hlead (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * 0 + (aB : ℚ) * 0 + (aC : ℚ) * (-1) +
          (aD : ℚ) * (-1) + (aE : ℚ) * (-1) = -2) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff (-2 : ℚ) =
        c * (A.coeff 0) ^ aA * (B.coeff 0) ^ aB *
          (C0.coeff (-1 : ℚ)) ^ aC * (D.coeff (-1 : ℚ)) ^ aD *
          (E.coeff (-1 : ℚ)) ^ aE := by
    rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B C0 D E
      aA aB aC aD aE 0 0 (-1) (-1) (-1) hA hB hC hD hE
  have ht1 := hzero (-8 / 27 : k) 0 3 0 0 0 (by norm_num)
  have ht2 := hzero (-8 / 9 : k) 2 0 0 1 0 (by norm_num)
  have ht3 := hzero (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  have ht4 := hlead (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have ht5 := hzero (40 / 81 : k) 3 1 0 0 0 (by norm_num)
  have ht6 := hzero (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have hh1 := hzero zeta 1 0 0 0 0 (by norm_num)
  have hh2 := hzero (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hh3 := hzero (3 * delta) 0 0 1 0 0 (by norm_num)
  have hh4 := hzero (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hh5 := hzero (5 * beta) 0 0 0 0 1 (by norm_num)
  have hh6 := hzero (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have hh7 := hzero (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hh8 := hlead ((7 / 12 : k) * L) 0 0 2 0 0 (by norm_num)
  have hh9 := hzero ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have hh10 := hzero ((385 / 5184 : k) * L) 4 0 0 0 0 (by norm_num)
  have hh11 := hzero (-(35 / 72 : k) * L) 1 2 0 0 0 (by norm_num)
  have hh12 := hzero (-(35 / 72 : k) * L) 2 0 1 0 0 (by norm_num)
  have hh13 := hzero (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have hh14 := hzero (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have hh15 := hzero ((7 / 6 : k) * L) 1 0 0 0 1 (by norm_num)
  have hh16 := hzero ((7 / 6 : k) * L) 0 1 0 1 0 (by norm_num)
  rw [firstIntegralFour68_eq_localFaces]
  simp only [firstIntegralFourTopFaceHahn68,
    firstIntegralFourHigherHahn68, HahnSeries.coeff_add]
  rw [ht1, ht2, ht3, ht4, ht5, ht6, hh1, hh2, hh3, hh4, hh5, hh6,
    hh7, hh8, hh9, hh10, hh11, hh12, hh13, hh14, hh15, hh16]
  simp only [afterP3FourFace68]
  norm_num

theorem firstIntegralThree68_coeff_neg2_afterP3
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop)
    (hB : (0 : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-1 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-1 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-1 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThree68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-2 : ℚ) =
      afterP3ThreeFace68 L (A.coeff (0 : ℚ)) (C0.coeff (-1 : ℚ))
        (D.coeff (-1 : ℚ)) (E.coeff (-1 : ℚ)) := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-2 : ℚ) < (aA : ℚ) * 0 + (aB : ℚ) * 0 +
        (aC : ℚ) * (-1) + (aD : ℚ) * (-1) + (aE : ℚ) * (-1)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-2 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE 0 0 (-1) (-1) (-1) (-2)
      hA hB hC hD hE hlt
  have hlead (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * 0 + (aB : ℚ) * 0 + (aC : ℚ) * (-1) +
          (aD : ℚ) * (-1) + (aE : ℚ) * (-1) = -2) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff (-2 : ℚ) =
        c * (A.coeff 0) ^ aA * (B.coeff 0) ^ aB *
          (C0.coeff (-1 : ℚ)) ^ aC * (D.coeff (-1 : ℚ)) ^ aD *
          (E.coeff (-1 : ℚ)) ^ aE := by
    rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B C0 D E
      aA aB aC aD aE 0 0 (-1) (-1) (-1) hA hB hC hD hE
  have ht1 := hzero (-16 / 243 : k) 5 0 0 0 0 (by norm_num)
  have ht2 := hlead (4 / 3 : k) 0 0 0 2 0 (by norm_num)
  have ht3 := hlead (-8 / 9 : k) 1 0 2 0 0 (by norm_num)
  have ht4 := hzero (-8 / 9 : k) 0 2 1 0 0 (by norm_num)
  have ht5 := hzero (-8 / 9 : k) 2 0 0 0 1 (by norm_num)
  have ht6 := hlead (8 / 3 : k) 0 0 1 0 1 (by norm_num)
  have ht7 := hzero (20 / 27 : k) 2 2 0 0 0 (by norm_num)
  have ht8 := hzero (40 / 81 : k) 3 0 1 0 0 (by norm_num)
  have ht9 := hzero (-16 / 9 : k) 1 1 0 1 0 (by norm_num)
  have hh1 := hzero zeta 0 1 0 0 0 (by norm_num)
  have hh2 := hzero (2 * epsilon) 0 0 1 0 0 (by norm_num)
  have hh3 := hzero (3 * delta) 0 0 0 1 0 (by norm_num)
  have hh4 := hzero (4 * gamma) 0 0 0 0 1 (by norm_num)
  have hh5 := hzero (-(35 / 216 : k) * L) 0 3 0 0 0 (by norm_num)
  have hh6 := hzero (-(2 / 3 : k) * epsilon) 2 0 0 0 0 (by norm_num)
  have hh7 := hzero (-(2 / 3 : k) * gamma) 0 2 0 0 0 (by norm_num)
  have hh8 := hzero ((8 / 27 : k) * gamma) 3 0 0 0 0 (by norm_num)
  have hh9 := hzero (-(35 / 72 : k) * L) 2 0 0 1 0 (by norm_num)
  have hh10 := hzero (-(5 / 6 : k) * beta) 1 0 0 1 0 (by norm_num)
  have hh11 := hzero (-(5 / 6 : k) * beta) 0 1 1 0 0 (by norm_num)
  have hh12 := hzero (-(4 / 3 : k) * gamma) 1 0 1 0 0 (by norm_num)
  have hh13 := hzero (-(3 / 2 : k) * delta) 1 1 0 0 0 (by norm_num)
  have hh14 := hzero ((7 / 6 : k) * L) 0 1 0 0 1 (by norm_num)
  have hh15 := hlead ((7 / 6 : k) * L) 0 0 1 1 0 (by norm_num)
  have hh16 := hzero ((35 / 72 : k) * beta) 2 1 0 0 0 (by norm_num)
  have hh17 := hzero ((385 / 1296 : k) * L) 3 1 0 0 0 (by norm_num)
  have hh18 := hzero (-(35 / 36 : k) * L) 1 1 1 0 0 (by norm_num)
  rw [firstIntegralThree68_eq_localFaces]
  simp only [firstIntegralThreeTopFaceHahn68,
    firstIntegralThreeHigherHahn68, HahnSeries.coeff_add]
  rw [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, hh1, hh2, hh3,
    hh4, hh5, hh6, hh7, hh8, hh9, hh10, hh11, hh12, hh13, hh14,
    hh15, hh16, hh17, hh18]
  simp only [afterP3ThreeFace68]
  norm_num
  ring

theorem SquareConstantLIntegratedLocalRootData68.afterP3_integralFaces
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    let x := (ratFuncAtHahn46 T.root T.source.C0).coeff (-1 : ℚ)
    let a := (ratFuncAtHahn46 T.root T.source.A).coeff (0 : ℚ)
    let d := (ratFuncAtHahn46 T.root T.source.D).coeff (-1 : ℚ)
    let e := (ratFuncAtHahn46 T.root T.source.E).coeff (-1 : ℚ)
    afterP3FourFace68 l x d = 0 ∧ afterP3ThreeFace68 l a x d e = 0 := by
  dsimp only
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterP3 hp hH hp6 hp5 hp4 hp3 hp2
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      l T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hi3H' :
      firstIntegralThree68 (HahnSeries.C l) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  have hcoeff4 := congrArg
    (fun z : HahnSeries ℚ k => z.coeff (-2 : ℚ)) hi4H'
  have hcoeff3 := congrArg
    (fun z : HahnSeries ℚ k => z.coeff (-2 : ℚ)) hi3H'
  have hconst4 : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-2 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  have hconst3 : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-2 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst4] at hcoeff4
  rw [hconst3] at hcoeff3
  have hface4 := firstIntegralFour68_coeff_neg2_afterP3
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by simpa only [BH] using hB)
      (by simpa only [CH] using hC) (by simpa only [DH] using hD)
      (by simpa only [EH] using hE)
  have hface3 := firstIntegralThree68_coeff_neg2_afterP3
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by simpa only [BH] using hB)
      (by simpa only [CH] using hC) (by simpa only [DH] using hD)
      (by simpa only [EH] using hE)
  rw [hface4] at hcoeff4
  rw [hface3] at hcoeff3
  exact ⟨hcoeff4, hcoeff3⟩

theorem afterP3_faces_nonzero_elimination
    (L a x d e z : k) (hx : x ≠ 0)
    (he : e = -(1 / 6 : k) * d * z - (1 / 36 : k) * x * z ^ 2)
    (hfour : afterP3FourFace68 L x d = 0)
    (hthree : afterP3ThreeFace68 L a x d e = 0) :
    32 * d + 7 * L * x = 0 ∧
      6144 * a + 1323 * L ^ 2 - 672 * L * z + 512 * z ^ 2 = 0 := by
  have hfac : x * ((8 / 3 : k) * d + (7 / 12 : k) * L * x) = 0 := by
    rw [afterP3FourFace68] at hfour
    linear_combination hfour
  have hinner := (mul_eq_zero.mp hfac).resolve_left hx
  have hlinear : 32 * d + 7 * L * x = 0 := by
    linear_combination (12 : k) * hinner
  have hd : d = -(7 / 32 : k) * L * x := by
    linear_combination (1 / 32 : k) * hlinear
  have he' : e = (7 / 192 : k) * L * x * z -
      (1 / 36 : k) * x * z ^ 2 := by
    rw [he, hd]
    ring
  rw [afterP3ThreeFace68, hd, he'] at hthree
  have hpolyfac : x ^ 2 * (-(8 / 9 : k) * a -
      (49 / 256 : k) * L ^ 2 + (7 / 72 : k) * L * z -
      (2 / 27 : k) * z ^ 2) = 0 := by
    linear_combination hthree
  have hpoly := (mul_eq_zero.mp hpolyfac).resolve_left (pow_ne_zero 2 hx)
  refine ⟨hlinear, ?_⟩
  linear_combination (-6912 : k) * hpoly

def AfterP3NonzeroResidual68
    {p q : k[X][X]} {j l : k} {h0 : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (g u w : k[X]) : Prop :=
  ∃ c : k, c ≠ 0 ∧
    let a := u.eval T.root - (5 / 12 : k) * g.eval T.root ^ 2
    let x := c⁻¹ * w.eval T.root
    let d := c⁻¹ * ((p.coeff 1).eval T.root -
      (1 / 3 : k) * w.eval T.root * g.eval T.root)
    x ≠ 0 ∧ 32 * d + 7 * l * x = 0 ∧
      6144 * a + 1323 * l ^ 2 - 672 * l * g.eval T.root +
        512 * g.eval T.root ^ 2 = 0

theorem SquareConstantLIntegratedLocalRootData68.afterP3_face_dichotomy
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    h0 ^ 2 ∣ p.coeff 2 ∨ AfterP3NonzeroResidual68 T g u w := by
  obtain ⟨hfour, hthree⟩ := T.afterP3_integralFaces
    hp hH hp6 hp5 hp4 hp3 hp2
  obtain ⟨c, hc, hAco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialPacketAfterP3 hp hH hp6 hp5 hp4 hp3 hp2
  let a : k := u.eval T.root - (5 / 12 : k) * g.eval T.root ^ 2
  let x : k := c⁻¹ * w.eval T.root
  let d : k := c⁻¹ * ((p.coeff 1).eval T.root -
    (1 / 3 : k) * w.eval T.root * g.eval T.root)
  let e : k := c⁻¹ * (-(1 / 6 : k) * (p.coeff 1).eval T.root *
    g.eval T.root + (1 / 36 : k) * w.eval T.root * g.eval T.root ^ 2)
  rw [hCco, hDco] at hfour
  rw [hAco, hCco, hDco, hEco] at hthree
  change afterP3FourFace68 l x d = 0 at hfour
  change afterP3ThreeFace68 l a x d e = 0 at hthree
  by_cases hx : x = 0
  · apply Or.inl
    have hx' : c⁻¹ * w.eval T.root = 0 := by simpa only [x] using hx
    have hwroot : w.eval T.root = 0 :=
      (mul_eq_zero.mp hx').resolve_left (inv_ne_zero hc)
    obtain ⟨t, hwt⟩ := linearPolynomial_dvd_of_eval_eq_zero h0 w T.root
      T.scale_degree T.root_eq hwroot
    refine ⟨t, ?_⟩
    rw [hp2, hwt]
    ring
  · apply Or.inr
    have heq : e = -(1 / 6 : k) * d * g.eval T.root -
        (1 / 36 : k) * x * g.eval T.root ^ 2 := by
      dsimp only [e, d, x]
      ring
    obtain ⟨hlinear, hpoly⟩ := afterP3_faces_nonzero_elimination
      l a x d e (g.eval T.root) hx heq hfour hthree
    refine ⟨c, hc, ?_⟩
    dsimp only
    exact ⟨hx, hlinear, hpoly⟩

/-- Original-data form of the next sharp box. -/
theorem SquareConstantLIntegratedLocalRootData68.afterP3_global_packet
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u v w : k[X],
      p.coeff 5 = h0 ^ 5 * g ∧ p.coeff 4 = h0 ^ 4 * u ∧
      p.coeff 3 = h0 ^ 3 * v ∧ p.coeff 2 = h0 * w ∧
      (h0 ^ 2 ∣ p.coeff 2 ∨ AfterP3NonzeroResidual68 T g u w) := by
  rcases T.afterP4_global_descend hp hH hp6 with
    ⟨⟨g, hp5⟩, ⟨u, hp4⟩, ⟨v, hp3⟩⟩
  have hp3old : p.coeff 3 = h0 ^ 2 * (h0 * v) := by rw [hp3]; ring
  obtain ⟨w, hp2⟩ := T.afterP4_forces_p2 hp hH hp6 hp5 hp4 hp3old
  refine ⟨g, u, v, w, hp5, hp4, hp3, hp2, ?_⟩
  exact T.afterP3_face_dichotomy hp hH hp6 hp5 hp4 hp3 hp2

end AfterRhoOneAfterP368

end Max11DegreeRoutes
