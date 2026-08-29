import LowScale68ScaleTwoAlignedFace

/-! # First zero-septic local descent for aligned `(6,8)`, scale two

The first local Newton box and its first two integral faces do not use the
nonvanishing of the septic coefficient.  This file transports those facts
to the exact zero-septic local record produced by the aligned square-core
source bridge.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareDescent68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareDescentHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Exact first Newton-box order bounds for a zero-septic local package. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateOrderBounds
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    let a := T.root
    (↑(-10 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.A).orderTop ∧
    (↑(-15 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.B).orderTop ∧
    (↑(-20 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.C0).orderTop ∧
    (↑(-25 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.D).orderTop ∧
    (↑(-30 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.E).orderTop := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) T.source.A 10
      T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30
      T.scale_order hE
  ⟩

/-- Exact worst-pole coefficients of all five depressed sextic coordinates
in the aligned zero-septic box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateInitialCoeffs
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ) =
        (c ^ 10)⁻¹ *
          (localClearedA68 h0 (p.coeff 5) (p.coeff 4)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ) =
        (c ^ 15)⁻¹ *
          (localClearedB68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ) =
        (c ^ 20)⁻¹ *
          (localClearedC68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ) =
        (c ^ 25)⁻¹ *
          (localClearedD68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ) =
        (c ^ 30)⁻¹ *
          (localClearedE68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0)).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ :=
    ratFuncAtHahn68_linearRoot_eq_single
      h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) T.source.A 10 hc
      hsingle hA
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 hc hsingle hB
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 hc hsingle hC
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 hc hsingle hD
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30 hc hsingle hE

/-- The weight-nine local face remains valid when the septic coefficient is
zero. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowFour_zero
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowFour68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ)) = 0 := by
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.B
  let CH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.C0
  let DH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.D
  let EH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.coordinateOrderBounds hp hH hp6
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
    (fun x : HahnSeries ℚ k => x.coeff (-45 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-45 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_neg45
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA hB hC hD hE
  rw [hface] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The independent weight-ten local face likewise survives unchanged on
the zero-septic chamber. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowThree_zero
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowThree68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ)) = 0 := by
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.B
  let CH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.C0
  let DH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.D
  let EH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.coordinateOrderBounds hp hH hp6
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-50 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-50 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_neg50
    0 T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA hB hC hD hE
  rw [hface] at hcoeff
  have hfactor : (-4 / 243 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- A compact, reviewable packet for the exact first two zero-septic local
faces. -/
structure SquareZeroLFirstTwoRowsPacket68
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) where
  top_four :
    topRowFour68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ)) = 0
  top_three :
    topRowThree68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ)) = 0

theorem SquareZeroLIntegratedLocalRootData68.firstTwoRowsPacket
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    SquareZeroLFirstTwoRowsPacket68 (H := H) T :=
  ⟨T.topRowFour_zero hp hH hp6, T.topRowThree_zero hp hH hp6⟩

end AlignedSquareDescent68

end Max11DegreeRoutes
