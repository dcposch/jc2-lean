import LowScale68ScaleTwoAfterRhoOne

/-! # The next box after `h² ∣ p₃`

With `p₅=h⁵g`, `p₄=h³u`, and `p₃=h²v`, the sharp depressed-coordinate
box is `(1,1,2,2,2)`.  The associated integrated octic box is
`(1,1,2,2,3,3,4)`.  The pole-five face of the second exact integral
factors into three elementary branches.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOneNextBox68

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneNextHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-! ## Exact source clearings -/

def localClearedB68AfterRhoOneNext (h g u v : k[X]) : k[X] :=
  v - C (2 / 3 : k) * u * g + C (5 / 27 : k) * h * g ^ 3

def localClearedC68AfterRhoOneNext (h g u v a2 : k[X]) : k[X] :=
  a2 - C (1 / 2 : k) * h * v * g + C (1 / 6 : k) * h * u * g ^ 2 -
    C (5 / 144 : k) * h ^ 2 * g ^ 4

def localClearedD68AfterRhoOneNext (h g u v a2 a1 : k[X]) : k[X] :=
  a1 * h - C (1 / 3 : k) * a2 * g + C (1 / 12 : k) * h * v * g ^ 2 -
    C (1 / 54 : k) * h * u * g ^ 3 + C (1 / 324 : k) * h ^ 2 * g ^ 5

def localClearedE68AfterRhoOneNext
    (h g u v a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 2 - C (1 / 6 : k) * a1 * g * h +
    C (1 / 36 : k) * a2 * g ^ 2 - C (1 / 216 : k) * h * v * g ^ 3 +
    C (1 / 1296 : k) * h * u * g ^ 4 -
    C (5 / 46656 : k) * h ^ 2 * g ^ 6

theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterRhoOneNext
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k) (localClearedA68AfterRhoOne h0 g u) =
        h ^ 1 * S.A ∧
    algebraMap k[X] (RatFunc k) (localClearedB68AfterRhoOneNext h0 g u v) =
        h ^ 1 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68AfterRhoOneNext h0 g u v (p.coeff 2)) = h ^ 2 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1)) =
      h ^ 2 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1)
          (p.coeff 0)) = h ^ 2 * S.E := by
  dsimp only
  have hp3' : p.coeff 3 = h0 * (h0 * v) := by rw [hp3]; ring
  obtain ⟨hA, hB, hC, hD, hE⟩ := S.clearedCoordinatesAfterRhoOne
    hp hh0 hH hp6 hp5 hp4 hp3'
  let B1 := localClearedB68AfterRhoOneNext h0 g u v
  have hfB : localClearedB68AfterRhoOne h0 g u (h0 * v) = h0 * B1 := by
    simp only [localClearedB68AfterRhoOne, B1,
      localClearedB68AfterRhoOneNext]
    ring
  change algebraMap k[X] (RatFunc k)
      (localClearedB68AfterRhoOne h0 g u (h0 * v)) = _ at hB
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · exact algebraMap_cancel_factoredClearing h0 _ B1 S.B 1 1 1 hh0
      (by simpa using hfB) hB
  · simpa only [localClearedC68AfterRhoOneNext,
      localClearedC68AfterRhoOne, mul_assoc] using hC
  · simpa only [localClearedD68AfterRhoOneNext,
      localClearedD68AfterRhoOne, mul_assoc] using hD
  · simpa only [localClearedE68AfterRhoOneNext,
      localClearedE68AfterRhoOne, mul_assoc] using hE

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsAfterRhoOneNext
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterRhoOneNext
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68AfterRhoOne h0 g u) T.source.A 1 T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68AfterRhoOneNext h0 g u v) T.source.B 1 T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68AfterRhoOneNext h0 g u v (p.coeff 2)) T.source.C0 2
      T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1))
      T.source.D 2 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1)
        (p.coeff 0)) T.source.E 2 T.scale_order hE⟩

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialPacketAfterRhoOneNext
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ) =
        c⁻¹ * u.eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-1 : ℚ) =
        c⁻¹ * (v.eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root) ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * (p.coeff 2).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * (-(1 / 3 : k) * (p.coeff 2).eval T.root *
          g.eval T.root) ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * ((1 / 36 : k) * (p.coeff 2).eval T.root *
          g.eval T.root ^ 2) := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterRhoOneNext
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  have hAco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedA68AfterRhoOne h0 g u) T.source.A 1 hc hsingle hA
  have hBco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedB68AfterRhoOneNext h0 g u v) T.source.B 1 hc hsingle hB
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedC68AfterRhoOneNext h0 g u v (p.coeff 2)) T.source.C0 2
    hc hsingle hC
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedD68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1))
    T.source.D 2 hc hsingle hD
  have hEco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedE68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1)
      (p.coeff 0)) T.source.E 2 hc hsingle hE
  norm_num at hAco hBco hCco hDco hEco
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAco]
    simp [localClearedA68AfterRhoOne, T.root_eq]
  · rw [hBco]
    simp [localClearedB68AfterRhoOneNext, T.root_eq]
  · rw [hCco]
    simp [localClearedC68AfterRhoOneNext, T.root_eq]
  · rw [hDco]
    simp [localClearedD68AfterRhoOneNext, T.root_eq]
  · rw [hEco]
    simp [localClearedE68AfterRhoOneNext, T.root_eq]

/-! ## General boundary coefficient and the pole-five face -/

theorem weightedMonomial68_coeff_at_general_lower_next
    (c : k) (A B C0 D E : HahnSeries ℚ k)
    (aA aB aC aD aE : ℕ) (rA rB rC rD rE : ℚ)
    (hA : (↑rA : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑rB : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑rC : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑rD : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑rE : WithTop ℚ) ≤ E.orderTop) :
    (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
        ((aA : ℚ) * rA + (aB : ℚ) * rB + (aC : ℚ) * rC +
          (aD : ℚ) * rD + (aE : ℚ) * rE) =
      c * (A.coeff rA) ^ aA * (B.coeff rB) ^ aB *
        (C0.coeff rC) ^ aC * (D.coeff rD) ^ aD *
        (E.coeff rE) ^ aE := by
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
  rw [weightedMonomial68]
  rw [show (aA : ℚ) * rA + (aB : ℚ) * rB + (aC : ℚ) * rC +
      (aD : ℚ) * rD + (aE : ℚ) * rE =
      ((((0 + (aA : ℚ) * rA) + (aB : ℚ) * rB) + (aC : ℚ) * rC) +
        (aD : ℚ) * rD) + (aE : ℚ) * rE by ring]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC * D ^ aD) (E ^ aE)
      ((((0 + (aA : ℚ) * rA) + (aB : ℚ) * rB) + (aC : ℚ) * rC) +
        (aD : ℚ) * rD) ((aE : ℚ) * rE) hcABCD hEp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC) (D ^ aD)
      (((0 + (aA : ℚ) * rA) + (aB : ℚ) * rB) + (aC : ℚ) * rC)
      ((aD : ℚ) * rD) hcABC hDp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB) (C0 ^ aC)
      ((0 + (aA : ℚ) * rA) + (aB : ℚ) * rB) ((aC : ℚ) * rC) hcAB hCp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA) (B ^ aB)
      (0 + (aA : ℚ) * rA) ((aB : ℚ) * rB) hcA hBp]
  rw [hahnCoeff_mul_at_lower46 (HahnSeries.C c) (A ^ aA)
    0 ((aA : ℚ) * rA) hc hAp]
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same,
    hahnCoeff_pow_at_lower46 A rA aA hA,
    hahnCoeff_pow_at_lower46 B rB aB hB,
    hahnCoeff_pow_at_lower46 C0 rC aC hC,
    hahnCoeff_pow_at_lower46 D rD aD hD,
    hahnCoeff_pow_at_lower46 E rE aE hE]

theorem firstIntegralThree68_coeff_neg5_afterRhoOneNext
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-1 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-2 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-2 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThree68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-5 : ℚ) =
      (-8 / 243 : k) * A.coeff (-1 : ℚ) *
        (3 * C0.coeff (-2 : ℚ) - A.coeff (-1 : ℚ) ^ 2) *
        (9 * C0.coeff (-2 : ℚ) - 2 * A.coeff (-1 : ℚ) ^ 2) := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-5 : ℚ) < (aA : ℚ) * (-1) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-2) + (aD : ℚ) * (-2) + (aE : ℚ) * (-2)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-5 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-1) (-1) (-2) (-2) (-2) (-5)
      hA hB hC hD hE hlt
  have hlead (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-1) + (aB : ℚ) * (-1) +
          (aC : ℚ) * (-2) + (aD : ℚ) * (-2) + (aE : ℚ) * (-2) = -5) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff (-5 : ℚ) =
        c * (A.coeff (-1 : ℚ)) ^ aA * (B.coeff (-1 : ℚ)) ^ aB *
          (C0.coeff (-2 : ℚ)) ^ aC * (D.coeff (-2 : ℚ)) ^ aD *
          (E.coeff (-2 : ℚ)) ^ aE := by
    rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B C0 D E
      aA aB aC aD aE (-1) (-1) (-2) (-2) (-2) hA hB hC hD hE
  have ht1 := hlead (-16 / 243 : k) 5 0 0 0 0 (by norm_num)
  have ht3 := hlead (-8 / 9 : k) 1 0 2 0 0 (by norm_num)
  have ht8 := hlead (40 / 81 : k) 3 0 1 0 0 (by norm_num)
  have ht2 := hzero (4 / 3 : k) 0 0 0 2 0 (by norm_num)
  have ht4 := hzero (-8 / 9 : k) 0 2 1 0 0 (by norm_num)
  have ht5 := hzero (-8 / 9 : k) 2 0 0 0 1 (by norm_num)
  have ht6 := hzero (8 / 3 : k) 0 0 1 0 1 (by norm_num)
  have ht7 := hzero (20 / 27 : k) 2 2 0 0 0 (by norm_num)
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
  have hh15 := hzero ((7 / 6 : k) * L) 0 0 1 1 0 (by norm_num)
  have hh16 := hzero ((35 / 72 : k) * beta) 2 1 0 0 0 (by norm_num)
  have hh17 := hzero ((385 / 1296 : k) * L) 3 1 0 0 0 (by norm_num)
  have hh18 := hzero (-(35 / 36 : k) * L) 1 1 1 0 0 (by norm_num)
  rw [firstIntegralThree68_eq_localFaces]
  simp only [firstIntegralThreeTopFaceHahn68,
    firstIntegralThreeHigherHahn68, HahnSeries.coeff_add]
  rw [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9,
    hh1, hh2, hh3, hh4, hh5, hh6, hh7, hh8, hh9, hh10, hh11,
    hh12, hh13, hh14, hh15, hh16, hh17, hh18]
  norm_num
  ring

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_face
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    let a := (ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ)
    let c := (ratFuncAtHahn46 T.root T.source.C0).coeff (-2 : ℚ)
    a * (3 * c - a ^ 2) * (9 * c - 2 * a ^ 2) = 0 := by
  dsimp only
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
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
    (fun x : HahnSeries ℚ k => x.coeff (-5 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-5 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_neg5_afterRhoOneNext
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by simpa only [BH] using hB)
      (by simpa only [CH] using hC) (by simpa only [DH] using hD)
      (by simpa only [EH] using hE)
  rw [hface] at hcoeff
  have hfactor : (-8 / 243 : k) ≠ 0 := by norm_num
  have hcoeff' : (-8 / 243 : k) *
      (AH.coeff (-1 : ℚ) *
        (3 * CH.coeff (-2 : ℚ) - AH.coeff (-1 : ℚ) ^ 2) *
        (9 * CH.coeff (-2 : ℚ) - 2 * AH.coeff (-1 : ℚ) ^ 2)) = 0 := by
    simpa only [mul_assoc] using hcoeff
  exact (mul_eq_zero.mp hcoeff').resolve_left hfactor

def AfterRhoOneNextResidual68
    {p q : k[X][X]} {j l : k} {h0 : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (u : k[X]) : Prop :=
  ∃ c : k, c ≠ 0 ∧
    let a := c⁻¹ * u.eval T.root
    let x := (c ^ 2)⁻¹ * (p.coeff 2).eval T.root
    3 * x - a ^ 2 = 0 ∨ 9 * x - 2 * a ^ 2 = 0

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_split
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    h0 ^ 4 ∣ p.coeff 4 ∨ AfterRhoOneNextResidual68 T u := by
  have hface := T.afterRhoOneNext_face hp hH hp6 hp5 hp4 hp3
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialPacketAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
  dsimp only at hface
  rw [hAco, hCco] at hface
  let a : k := c⁻¹ * u.eval T.root
  let x : k := (c ^ 2)⁻¹ * (p.coeff 2).eval T.root
  change a * (3 * x - a ^ 2) * (9 * x - 2 * a ^ 2) = 0 at hface
  rw [mul_assoc] at hface
  rcases mul_eq_zero.mp hface with ha | hrest
  · left
    have hcinv : c⁻¹ ≠ 0 := inv_ne_zero hc
    have ha' : c⁻¹ * u.eval T.root = 0 := by simpa only [a] using ha
    have huroot : u.eval T.root = 0 := (mul_eq_zero.mp ha').resolve_left hcinv
    obtain ⟨w, huw⟩ := linearPolynomial_dvd_of_eval_eq_zero
      h0 u T.root T.scale_degree T.root_eq huroot
    refine ⟨w, ?_⟩
    rw [hp4, huw]
    ring
  · right
    refine ⟨c, hc, ?_⟩
    change 3 * x - a ^ 2 = 0 ∨ 9 * x - 2 * a ^ 2 = 0
    exact mul_eq_zero.mp hrest

/-- Original-data wrapper: either the quartic coefficient descends once
more, or the exact two-branch residual above survives. -/
theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_globalSplit
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    h0 ^ 4 ∣ p.coeff 4 ∨ ∃ u : k[X],
      p.coeff 4 = h0 ^ 3 * u ∧ AfterRhoOneNextResidual68 T u := by
  rcases T.afterRhoOne_next_divisibilities hp hH hp6 with
    ⟨⟨g, hp5⟩, ⟨u, hp4⟩, ⟨v, hp3⟩⟩
  rcases T.afterRhoOneNext_split hp hH hp6 hp5 hp4 hp3 with hdiv | hres
  · exact Or.inl hdiv
  · exact Or.inr ⟨u, hp4, hres⟩

end AfterRhoOneNextBox68

#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterRhoOneNext
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateInitialPacketAfterRhoOneNext
#print axioms firstIntegralThree68_coeff_neg5_afterRhoOneNext
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_face
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_split
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_globalSplit

end Max11DegreeRoutes
