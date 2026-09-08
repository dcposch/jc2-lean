import LowScale68ScaleTwoAfterRhoOneBranchRows

/-! # Improved quadratic defects on the two post-rho-one branches

At the `(1,1,2,2,2)` box the pole-five row is the product of the two
quadratic defects `3C-A²` and `9C-2A²`.  On either surviving branch the
corresponding cleared defect vanishes at the simple scale root, so one
factor of the scale cancels.  This file records that cancellation and the
resulting transverse coefficient of the second exact first integral.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOneImprovedDefect68

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneImprovedDefectHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def afterRhoOneFirstDefect68 {F : Type*} [Field F] (A C0 : F) : F :=
  3 * C0 - A ^ 2

def afterRhoOneSecondDefect68 {F : Type*} [Field F] (A C0 : F) : F :=
  9 * C0 - 2 * A ^ 2

def localClearedFirstDefect68
    (h g u v a2 : k[X]) : k[X] :=
  3 * localClearedC68AfterRhoOneNext h g u v a2 -
    localClearedA68AfterRhoOne h g u ^ 2

def localClearedSecondDefect68
    (h g u v a2 : k[X]) : k[X] :=
  9 * localClearedC68AfterRhoOneNext h g u v a2 -
    2 * localClearedA68AfterRhoOne h g u ^ 2

theorem SquareConstantLIntegratedSourceData68.clearedDefectsAfterRhoOneNext
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    let h := algebraMap k[X] (RatFunc k) h0
    let F1 := afterRhoOneFirstDefect68 S.A S.C0
    let F2 := afterRhoOneSecondDefect68 S.A S.C0
    algebraMap k[X] (RatFunc k)
        (localClearedFirstDefect68 h0 g u v (p.coeff 2)) = h ^ 2 * F1 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedSecondDefect68 h0 g u v (p.coeff 2)) = h ^ 2 * F2 := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ := S.clearedCoordinatesAfterRhoOneNext
    hp hh0 hH hp6 hp5 hp4 hp3
  constructor
  · simp only [localClearedFirstDefect68, afterRhoOneFirstDefect68,
      map_sub, map_mul, map_pow, map_ofNat]
    rw [hA, hC]
    ring
  · simp only [localClearedSecondDefect68, afterRhoOneSecondDefect68,
      map_sub, map_mul, map_pow, map_ofNat]
    rw [hA, hC]
    ring

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialPacketAtScaleSingleAfterRhoOneNext
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c) :
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

theorem SquareConstantLIntegratedLocalRootData68.defectOrdinaryPacketAfterRhoOneNext
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c) :
    let AH := ratFuncAtHahn46 T.root T.source.A
    let CH := ratFuncAtHahn46 T.root T.source.C0
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (afterRhoOneFirstDefect68 AH CH).orderTop ∧
    (afterRhoOneFirstDefect68 AH CH).coeff (-2 : ℚ) =
      3 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root) -
        (c⁻¹ * u.eval T.root) ^ 2 ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (afterRhoOneSecondDefect68 AH CH).orderTop ∧
    (afterRhoOneSecondDefect68 AH CH).coeff (-2 : ℚ) =
      9 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root) -
        2 * (c⁻¹ * u.eval T.root) ^ 2 := by
  dsimp only
  let F0 := localClearedFirstDefect68 h0 g u v (p.coeff 2)
  let G0 := localClearedSecondDefect68 h0 g u v (p.coeff 2)
  let FR : RatFunc k := afterRhoOneFirstDefect68 T.source.A T.source.C0
  let GR : RatFunc k := afterRhoOneSecondDefect68 T.source.A T.source.C0
  obtain ⟨hFclear, hGclear⟩ := T.source.clearedDefectsAfterRhoOneNext
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  change algebraMap k[X] (RatFunc k) F0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * FR at hFclear
  change algebraMap k[X] (RatFunc k) G0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * GR at hGclear
  have hFord := localHahn_orderTop_ge_of_cleared T.root h0 F0 FR 2
    T.scale_order hFclear
  have hGord := localHahn_orderTop_ge_of_cleared T.root h0 G0 GR 2
    T.scale_order hGclear
  have hFco := localHahn_coeff_neg_of_cleared T.root c h0 F0 FR 2
    hc hsingle hFclear
  have hGco := localHahn_coeff_neg_of_cleared T.root c h0 G0 GR 2
    hc hsingle hGclear
  norm_num at hFco hGco
  have hFmap : ratFuncAtHahn46 T.root FR = afterRhoOneFirstDefect68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [FR, afterRhoOneFirstDefect68]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  have hGmap : ratFuncAtHahn46 T.root GR = afterRhoOneSecondDefect68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [GR, afterRhoOneSecondDefect68]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [← hFmap, ← hGmap]
  refine ⟨hFord, ?_, hGord, ?_⟩
  · rw [hFco]
    dsimp only [F0, localClearedFirstDefect68]
    simp [localClearedC68AfterRhoOneNext, localClearedA68AfterRhoOne,
      T.root_eq]
    field_simp [hc]
  · rw [hGco]
    dsimp only [G0, localClearedSecondDefect68]
    simp [localClearedC68AfterRhoOneNext, localClearedA68AfterRhoOne,
      T.root_eq]
    field_simp [hc]

theorem SquareConstantLIntegratedLocalRootData68.firstDefectImprovedPacket
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c)
    (hx : 3 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root) -
      (c⁻¹ * u.eval T.root) ^ 2 = 0) :
    ∃ w : k[X],
      localClearedFirstDefect68 h0 g u v (p.coeff 2) = h0 * w ∧
      (↑(-1 : ℚ) : WithTop ℚ) ≤
        (afterRhoOneFirstDefect68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop ∧
      (afterRhoOneFirstDefect68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (-1 : ℚ) =
        c⁻¹ * w.eval T.root := by
  let F0 := localClearedFirstDefect68 h0 g u v (p.coeff 2)
  let FR : RatFunc k := afterRhoOneFirstDefect68 T.source.A T.source.C0
  obtain ⟨hFclear, hGclear⟩ := T.source.clearedDefectsAfterRhoOneNext
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  change algebraMap k[X] (RatFunc k) F0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * FR at hFclear
  have hx' : 3 * (p.coeff 2).eval T.root - u.eval T.root ^ 2 = 0 := by
    field_simp [hc] at hx
    linear_combination hx
  have hFroot : F0.eval T.root = 0 := by
    dsimp only [F0, localClearedFirstDefect68]
    simp [localClearedC68AfterRhoOneNext, localClearedA68AfterRhoOne,
      T.root_eq]
    linear_combination hx'
  obtain ⟨w, hFw⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 F0 T.root T.scale_degree T.root_eq hFroot
  have hwclear : algebraMap k[X] (RatFunc k) w =
      (algebraMap k[X] (RatFunc k) h0) ^ 1 * FR := by
    exact algebraMap_cancel_factoredClearing h0 F0 w FR 1 1 1
      T.scale_ne_zero (by simpa using hFw) (by simpa using hFclear)
  have hword : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root FR).orderTop :=
    localHahn_orderTop_ge_of_cleared T.root h0 w FR 1
      T.scale_order hwclear
  have hwcoeff := localHahn_coeff_neg_of_cleared T.root c h0 w FR 1
    hc hsingle hwclear
  norm_num at hwcoeff
  have hmap : ratFuncAtHahn46 T.root FR =
      afterRhoOneFirstDefect68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [FR, afterRhoOneFirstDefect68]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [F0] using hFw
  · rw [← hmap]
    exact hword
  · rw [← hmap]
    exact hwcoeff

theorem SquareConstantLIntegratedLocalRootData68.secondDefectImprovedPacket
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c)
    (hx : 9 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root) -
      2 * (c⁻¹ * u.eval T.root) ^ 2 = 0) :
    ∃ w : k[X],
      localClearedSecondDefect68 h0 g u v (p.coeff 2) = h0 * w ∧
      (↑(-1 : ℚ) : WithTop ℚ) ≤
        (afterRhoOneSecondDefect68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop ∧
      (afterRhoOneSecondDefect68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (-1 : ℚ) =
        c⁻¹ * w.eval T.root := by
  let G0 := localClearedSecondDefect68 h0 g u v (p.coeff 2)
  let GR : RatFunc k := afterRhoOneSecondDefect68 T.source.A T.source.C0
  obtain ⟨hFclear, hGclear⟩ := T.source.clearedDefectsAfterRhoOneNext
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  change algebraMap k[X] (RatFunc k) G0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * GR at hGclear
  have hx' : 9 * (p.coeff 2).eval T.root - 2 * u.eval T.root ^ 2 = 0 := by
    field_simp [hc] at hx
    linear_combination hx
  have hGroot : G0.eval T.root = 0 := by
    dsimp only [G0, localClearedSecondDefect68]
    simp [localClearedC68AfterRhoOneNext, localClearedA68AfterRhoOne,
      T.root_eq]
    linear_combination hx'
  obtain ⟨w, hGw⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 G0 T.root T.scale_degree T.root_eq hGroot
  have hwclear : algebraMap k[X] (RatFunc k) w =
      (algebraMap k[X] (RatFunc k) h0) ^ 1 * GR := by
    exact algebraMap_cancel_factoredClearing h0 G0 w GR 1 1 1
      T.scale_ne_zero (by simpa using hGw) (by simpa using hGclear)
  have hword : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root GR).orderTop :=
    localHahn_orderTop_ge_of_cleared T.root h0 w GR 1
      T.scale_order hwclear
  have hwcoeff := localHahn_coeff_neg_of_cleared T.root c h0 w GR 1
    hc hsingle hwclear
  norm_num at hwcoeff
  have hmap : ratFuncAtHahn46 T.root GR =
      afterRhoOneSecondDefect68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [GR, afterRhoOneSecondDefect68]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [G0] using hGw
  · rw [← hmap]
    exact hword
  · rw [← hmap]
    exact hwcoeff

def afterRhoOneNextThreeRemainder68
    (L a b x d e : k) : k :=
  (4 / 3 : k) * d ^ 2 - (8 / 9 : k) * b ^ 2 * x -
    (8 / 9 : k) * a ^ 2 * e + (8 / 3 : k) * x * e +
    (20 / 27 : k) * a ^ 2 * b ^ 2 - (16 / 9 : k) * a * b * d -
    (35 / 72 : k) * a ^ 2 * d * L + (7 / 6 : k) * x * d * L +
    (385 / 1296 : k) * a ^ 3 * b * L -
    (35 / 36 : k) * a * b * x * L

theorem firstIntegralThree68_coeff_neg4_of_improvedDefect
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E F1 F2 : HahnSeries ℚ k) (r1 r2 : ℚ)
    (hF1 : F1 = afterRhoOneFirstDefect68 A C0)
    (hF2 : F2 = afterRhoOneSecondDefect68 A C0)
    (hA : (↑(-1 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-2 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-2 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hO1 : (↑r1 : WithTop ℚ) ≤ F1.orderTop)
    (hO2 : (↑r2 : WithTop ℚ) ≤ F2.orderTop)
    (hr : (-1 : ℚ) + r1 + r2 = -4) :
    (firstIntegralThree68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-4 : ℚ) =
      (-8 / 243 : k) * A.coeff (-1 : ℚ) * F1.coeff r1 * F2.coeff r2 +
        afterRhoOneNextThreeRemainder68 L (A.coeff (-1 : ℚ))
          (B.coeff (-1 : ℚ)) (C0.coeff (-2 : ℚ))
          (D.coeff (-2 : ℚ)) (E.coeff (-2 : ℚ)) := by
  have hZ : (0 : WithTop ℚ) ≤ (0 : HahnSeries ℚ k).orderTop := by simp
  have hfactor0 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 243 : k) A F1 F2 0 0 1 1 1 0 0 (-1) r1 r2 0 0
      hA hO1 hO2 hZ hZ
  have hfactor :
      (weightedMonomial68 (-8 / 243 : k) A F1 F2 0 0 1 1 1 0 0).coeff
          (-4 : ℚ) =
        (-8 / 243 : k) * A.coeff (-1 : ℚ) * F1.coeff r1 *
          F2.coeff r2 := by
    rw [← hr]
    convert hfactor0 using 1 <;> norm_num
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-4 : ℚ) < (aA : ℚ) * (-1) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-2) + (aD : ℚ) * (-2) + (aE : ℚ) * (-2)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-4 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-1) (-1) (-2) (-2) (-2) (-4)
      hA hB hC hD hE hlt
  have hlead (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-1) + (aB : ℚ) * (-1) +
          (aC : ℚ) * (-2) + (aD : ℚ) * (-2) + (aE : ℚ) * (-2) = -4) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff (-4 : ℚ) =
        c * (A.coeff (-1 : ℚ)) ^ aA * (B.coeff (-1 : ℚ)) ^ aB *
          (C0.coeff (-2 : ℚ)) ^ aC * (D.coeff (-2 : ℚ)) ^ aD *
          (E.coeff (-2 : ℚ)) ^ aE := by
    rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B C0 D E
      aA aB aC aD aE (-1) (-1) (-2) (-2) (-2) hA hB hC hD hE
  have hD2 := hlead (4 / 3 : k) 0 0 0 2 0 (by norm_num)
  have hB2C := hlead (-8 / 9 : k) 0 2 1 0 0 (by norm_num)
  have hA2E := hlead (-8 / 9 : k) 2 0 0 0 1 (by norm_num)
  have hCE := hlead (8 / 3 : k) 0 0 1 0 1 (by norm_num)
  have hA2B2 := hlead (20 / 27 : k) 2 2 0 0 0 (by norm_num)
  have hABD := hlead (-16 / 9 : k) 1 1 0 1 0 (by norm_num)
  have hA2DL := hlead (-(35 / 72 : k) * L) 2 0 0 1 0 (by norm_num)
  have hCDL := hlead ((7 / 6 : k) * L) 0 0 1 1 0 (by norm_num)
  have hA3BL := hlead ((385 / 1296 : k) * L) 3 1 0 0 0 (by norm_num)
  have hABCL := hlead (-(35 / 36 : k) * L) 1 1 1 0 0 (by norm_num)
  have hzeta := hzero zeta 0 1 0 0 0 (by norm_num)
  have hepsilon := hzero (2 * epsilon) 0 0 1 0 0 (by norm_num)
  have hdelta := hzero (3 * delta) 0 0 0 1 0 (by norm_num)
  have hgammaE := hzero (4 * gamma) 0 0 0 0 1 (by norm_num)
  have hB3L := hzero (-(35 / 216 : k) * L) 0 3 0 0 0 (by norm_num)
  have hA2eps := hzero (-(2 / 3 : k) * epsilon) 2 0 0 0 0 (by norm_num)
  have hB2gam := hzero (-(2 / 3 : k) * gamma) 0 2 0 0 0 (by norm_num)
  have hA3gam := hzero ((8 / 27 : k) * gamma) 3 0 0 0 0 (by norm_num)
  have hADbeta := hzero (-(5 / 6 : k) * beta) 1 0 0 1 0 (by norm_num)
  have hBCbeta := hzero (-(5 / 6 : k) * beta) 0 1 1 0 0 (by norm_num)
  have hACgam := hzero (-(4 / 3 : k) * gamma) 1 0 1 0 0 (by norm_num)
  have hABdel := hzero (-(3 / 2 : k) * delta) 1 1 0 0 0 (by norm_num)
  have hBEL := hzero ((7 / 6 : k) * L) 0 1 0 0 1 (by norm_num)
  have hA2Bbeta := hzero ((35 / 72 : k) * beta) 2 1 0 0 0 (by norm_num)
  have hdecomp :
      firstIntegralThree68 (HahnSeries.C L) A B C0 D E
        (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
        (HahnSeries.C epsilon) (HahnSeries.C zeta) =
      weightedMonomial68 (-8 / 243 : k) A F1 F2 0 0 1 1 1 0 0 +
      weightedMonomial68 (4 / 3 : k) A B C0 D E 0 0 0 2 0 +
      weightedMonomial68 zeta A B C0 D E 0 1 0 0 0 +
      weightedMonomial68 (2 * epsilon) A B C0 D E 0 0 1 0 0 +
      weightedMonomial68 (3 * delta) A B C0 D E 0 0 0 1 0 +
      weightedMonomial68 (4 * gamma) A B C0 D E 0 0 0 0 1 +
      weightedMonomial68 (-(35 / 216 : k) * L) A B C0 D E 0 3 0 0 0 +
      weightedMonomial68 (-8 / 9 : k) A B C0 D E 0 2 1 0 0 +
      weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 0 1 +
      weightedMonomial68 (-(2 / 3 : k) * epsilon) A B C0 D E 2 0 0 0 0 +
      weightedMonomial68 (-(2 / 3 : k) * gamma) A B C0 D E 0 2 0 0 0 +
      weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 0 1 +
      weightedMonomial68 ((8 / 27 : k) * gamma) A B C0 D E 3 0 0 0 0 +
      weightedMonomial68 (20 / 27 : k) A B C0 D E 2 2 0 0 0 +
      weightedMonomial68 (-(35 / 72 : k) * L) A B C0 D E 2 0 0 1 0 +
      weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 0 1 0 +
      weightedMonomial68 (-(5 / 6 : k) * beta) A B C0 D E 1 0 0 1 0 +
      weightedMonomial68 (-(5 / 6 : k) * beta) A B C0 D E 0 1 1 0 0 +
      weightedMonomial68 (-(4 / 3 : k) * gamma) A B C0 D E 1 0 1 0 0 +
      weightedMonomial68 (-(3 / 2 : k) * delta) A B C0 D E 1 1 0 0 0 +
      weightedMonomial68 ((7 / 6 : k) * L) A B C0 D E 0 1 0 0 1 +
      weightedMonomial68 ((7 / 6 : k) * L) A B C0 D E 0 0 1 1 0 +
      weightedMonomial68 ((35 / 72 : k) * beta) A B C0 D E 2 1 0 0 0 +
      weightedMonomial68 ((385 / 1296 : k) * L) A B C0 D E 3 1 0 0 0 +
      weightedMonomial68 (-(35 / 36 : k) * L) A B C0 D E 1 1 1 0 0 := by
    simp only [firstIntegralThree68, weightedMonomial68, hF1, hF2,
      afterRhoOneFirstDefect68, afterRhoOneSecondDefect68]
    simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one]
    ring
  rw [hdecomp]
  simp only [HahnSeries.coeff_add]
  rw [hfactor, hD2, hzeta, hepsilon, hdelta, hgammaE, hB3L, hB2C,
    hA2E, hA2eps, hB2gam, hCE, hA3gam, hA2B2, hA2DL, hABD,
    hADbeta, hBCbeta, hACgam, hABdel, hBEL, hCDL, hA2Bbeta,
    hA3BL, hABCL]
  simp only [afterRhoOneNextThreeRemainder68]
  norm_num
  ring

def afterRhoOneFirstBranchTransverse68 (L a d y : k) : k :=
  (-8 / 243 : k) * a ^ 3 * y + (4 / 3 : k) * d ^ 2 +
    (91 / 288 : k) * L * a ^ 2 * d +
    (160769 / 5308416 : k) * L ^ 2 * a ^ 4

def afterRhoOneSecondBranchTransverse68 (L a b e y : k) : k :=
  (8 / 729 : k) * a ^ 3 * y + (8 / 81 : k) * a ^ 2 * b ^ 2 -
    (8 / 27 : k) * a ^ 2 * e + (35 / 1728 : k) * L * a ^ 3 * b +
    (22099 / 5308416 : k) * L ^ 2 * a ^ 4

theorem afterRhoOne_firstBranch_transverse_of_rows
    (L a b x d e y : k)
    (hx : 3 * x - a ^ 2 = 0)
    (hb : 512 * b + 119 * L * a = 0)
    (hrow : (-8 / 243 : k) * a * y * (9 * x - 2 * a ^ 2) +
      afterRhoOneNextThreeRemainder68 L a b x d e = 0) :
    afterRhoOneFirstBranchTransverse68 L a d y = 0 := by
  have hx' : x = a ^ 2 / 3 := by linear_combination (1 / 3 : k) * hx
  have hb' : b = -(119 / 512 : k) * L * a := by
    linear_combination (1 / 512 : k) * hb
  rw [hx', hb'] at hrow
  rw [afterRhoOneFirstBranchTransverse68]
  simp only [afterRhoOneNextThreeRemainder68] at hrow
  linear_combination hrow

theorem afterRhoOne_secondBranch_transverse_of_rows
    (L a b x d e y : k)
    (hx : 9 * x - 2 * a ^ 2 = 0)
    (hd : 4608 * d - 1536 * a * b + 77 * L * a ^ 2 = 0)
    (hrow : (-8 / 243 : k) * a * (3 * x - a ^ 2) * y +
      afterRhoOneNextThreeRemainder68 L a b x d e = 0) :
    afterRhoOneSecondBranchTransverse68 L a b e y = 0 := by
  have hx' : x = 2 * a ^ 2 / 9 := by linear_combination (1 / 9 : k) * hx
  have hd' : d = (1 / 3 : k) * a * b - (77 / 4608 : k) * L * a ^ 2 := by
    linear_combination (1 / 4608 : k) * hd
  rw [hx', hd'] at hrow
  rw [afterRhoOneSecondBranchTransverse68]
  simp only [afterRhoOneNextThreeRemainder68] at hrow
  linear_combination hrow

theorem SquareConstantLIntegratedLocalRootData68.exactThreeRowAfterRhoOneNext
    {p q : k[X][X]} {j l c y1 y2 : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c)
    (r1 r2 : ℚ)
    (hO1 : (↑r1 : WithTop ℚ) ≤
      (afterRhoOneFirstDefect68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hO2 : (↑r2 : WithTop ℚ) ≤
      (afterRhoOneSecondDefect68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hy1 : (afterRhoOneFirstDefect68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff r1 = y1)
    (hy2 : (afterRhoOneSecondDefect68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff r2 = y2)
    (hr : (-1 : ℚ) + r1 + r2 = -4) :
    let a := c⁻¹ * u.eval T.root
    let b := c⁻¹ *
      (v.eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root)
    let x := (c ^ 2)⁻¹ * (p.coeff 2).eval T.root
    let d := (c ^ 2)⁻¹ *
      (-(1 / 3 : k) * (p.coeff 2).eval T.root * g.eval T.root)
    let e := (c ^ 2)⁻¹ *
      ((1 / 36 : k) * (p.coeff 2).eval T.root * g.eval T.root ^ 2)
    (-8 / 243 : k) * a * y1 * y2 +
      afterRhoOneNextThreeRemainder68 l a b x d e = 0 := by
  dsimp only
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  let F1 := afterRhoOneFirstDefect68 AH CH
  let F2 := afterRhoOneSecondDefect68 AH CH
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
  obtain ⟨hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialPacketAtScaleSingleAfterRhoOneNext
      hp hH hp6 hp5 hp4 hp3 hc hsingle
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
      map_pow, map_div₀, map_ofNat, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  have hcoeff := congrArg
    (fun z : HahnSeries ℚ k => z.coeff (-4 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-4 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hcalc := firstIntegralThree68_coeff_neg4_of_improvedDefect
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH F1 F2 r1 r2
      (by rfl) (by rfl)
      (by simpa only [AH] using hA) (by simpa only [BH] using hB)
      (by simpa only [CH] using hC) (by simpa only [DH] using hD)
      (by simpa only [EH] using hE)
      (by simpa only [F1, AH, CH] using hO1)
      (by simpa only [F2, AH, CH] using hO2) hr
  rw [hcalc] at hcoeff
  change F1.coeff r1 = y1 at hy1
  change F2.coeff r2 = y2 at hy2
  rw [hy1, hy2] at hcoeff
  rw [hAco, hBco, hCco, hDco, hEco] at hcoeff
  exact hcoeff

theorem SquareConstantLIntegratedLocalRootData68.firstBranchImprovedThreeRow
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c)
    (hx : 3 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root) -
      (c⁻¹ * u.eval T.root) ^ 2 = 0)
    (hb : 512 * (c⁻¹ *
        (v.eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root)) +
      119 * l * (c⁻¹ * u.eval T.root) = 0) :
    ∃ w : k[X],
      localClearedFirstDefect68 h0 g u v (p.coeff 2) = h0 * w ∧
      afterRhoOneFirstBranchTransverse68 l (c⁻¹ * u.eval T.root)
        ((c ^ 2)⁻¹ * (-(1 / 3 : k) * (p.coeff 2).eval T.root *
          g.eval T.root)) (c⁻¹ * w.eval T.root) = 0 := by
  obtain ⟨w, hFw, hF1ord, hF1co⟩ := T.firstDefectImprovedPacket
    hp hH hp6 hp5 hp4 hp3 hc hsingle hx
  obtain ⟨hF1old, hF1oldco, hF2ord, hF2co⟩ :=
    T.defectOrdinaryPacketAfterRhoOneNext
      hp hH hp6 hp5 hp4 hp3 hc hsingle
  have hrow := T.exactThreeRowAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
    hc hsingle (-1) (-2) hF1ord hF2ord hF1co hF2co (by norm_num)
  refine ⟨w, hFw, ?_⟩
  exact afterRhoOne_firstBranch_transverse_of_rows
    l (c⁻¹ * u.eval T.root)
      (c⁻¹ * (v.eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root))
      ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root)
      ((c ^ 2)⁻¹ * (-(1 / 3 : k) * (p.coeff 2).eval T.root *
        g.eval T.root))
      ((c ^ 2)⁻¹ * ((1 / 36 : k) * (p.coeff 2).eval T.root *
        g.eval T.root ^ 2))
      (c⁻¹ * w.eval T.root) hx hb hrow

theorem SquareConstantLIntegratedLocalRootData68.secondBranchImprovedThreeRow
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c)
    (hx : 9 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root) -
      2 * (c⁻¹ * u.eval T.root) ^ 2 = 0)
    (hd : 4608 * ((c ^ 2)⁻¹ *
        (-(1 / 3 : k) * (p.coeff 2).eval T.root * g.eval T.root)) -
      1536 * (c⁻¹ * u.eval T.root) *
        (c⁻¹ * (v.eval T.root - (2 / 3 : k) * u.eval T.root *
          g.eval T.root)) + 77 * l * (c⁻¹ * u.eval T.root) ^ 2 = 0) :
    ∃ w : k[X],
      localClearedSecondDefect68 h0 g u v (p.coeff 2) = h0 * w ∧
      afterRhoOneSecondBranchTransverse68 l (c⁻¹ * u.eval T.root)
        (c⁻¹ * (v.eval T.root - (2 / 3 : k) * u.eval T.root *
          g.eval T.root))
        ((c ^ 2)⁻¹ * ((1 / 36 : k) * (p.coeff 2).eval T.root *
          g.eval T.root ^ 2)) (c⁻¹ * w.eval T.root) = 0 := by
  obtain ⟨w, hGw, hF2ord, hF2co⟩ := T.secondDefectImprovedPacket
    hp hH hp6 hp5 hp4 hp3 hc hsingle hx
  obtain ⟨hF1ord, hF1co, hF2old, hF2oldco⟩ :=
    T.defectOrdinaryPacketAfterRhoOneNext
      hp hH hp6 hp5 hp4 hp3 hc hsingle
  have hrow := T.exactThreeRowAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
    hc hsingle (-2) (-1) hF1ord hF2ord hF1co hF2co (by norm_num)
  refine ⟨w, hGw, ?_⟩
  exact afterRhoOne_secondBranch_transverse_of_rows
    l (c⁻¹ * u.eval T.root)
      (c⁻¹ * (v.eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root))
      ((c ^ 2)⁻¹ * (p.coeff 2).eval T.root)
      ((c ^ 2)⁻¹ * (-(1 / 3 : k) * (p.coeff 2).eval T.root *
        g.eval T.root))
      ((c ^ 2)⁻¹ * ((1 / 36 : k) * (p.coeff 2).eval T.root *
        g.eval T.root ^ 2))
      (c⁻¹ * w.eval T.root) hx hd hrow

end AfterRhoOneImprovedDefect68

#print axioms SquareConstantLIntegratedSourceData68.clearedDefectsAfterRhoOneNext
#print axioms SquareConstantLIntegratedLocalRootData68.firstDefectImprovedPacket
#print axioms SquareConstantLIntegratedLocalRootData68.secondDefectImprovedPacket
#print axioms firstIntegralThree68_coeff_neg4_of_improvedDefect
#print axioms SquareConstantLIntegratedLocalRootData68.firstBranchImprovedThreeRow
#print axioms SquareConstantLIntegratedLocalRootData68.secondBranchImprovedThreeRow

end Max11DegreeRoutes
