import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4TenSourceScratch

/-! # The unique `B[12]` face of `I4(10)` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4TenB12Transport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_replaceB12_68
    (B : HahnSeries ℚ k) (b12 : k) : HahnSeries ℚ k :=
  B - HahnSeries.single (12 : ℚ) (B.coeff 12) +
    HahnSeries.single (12 : ℚ) b12

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_replaceB12_self68 (B : HahnSeries ℚ k) :
    rhoOne_boundaryG_replaceB12_68 B (B.coeff 12) = B := by
  dsimp only [rhoOne_boundaryG_replaceB12_68]
  abel

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i4ten_replaceB12_affine68
    (gamma epsilon : k) (B C F G : HahnSeries ℚ k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop) (b12 : k) :
    (rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
      (rhoOne_boundaryG_replaceB12_68 B b12) C F G).coeff 10 =
    (rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
      (rhoOne_boundaryG_replaceB12_68 B 0) C F G).coeff 10 +
      (8 / 3 : k) * G.coeff (-2) * b12 := by
  let B0 := rhoOne_boundaryG_replaceB12_68 B 0
  let s : HahnSeries ℚ k := HahnSeries.single 12 b12
  have hBform : rhoOne_boundaryG_replaceB12_68 B b12 = B0 + s := by
    dsimp only [B0, s, rhoOne_boundaryG_replaceB12_68]
    simp
  have hsingle : (↑(2 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (12 : ℚ) (B.coeff 12) : HahnSeries ℚ k).orderTop := by
    by_cases hb : B.coeff 12 = 0
    · simp [hb]
    · rw [HahnSeries.orderTop_single hb]
      exact WithTop.coe_le_coe.mpr (by norm_num)
  have hB0 : (↑(2 : ℚ) : WithTop ℚ) ≤ B0.orderTop := by
    dsimp only [B0, rhoOne_boundaryG_replaceB12_68]
    rw [show (HahnSeries.single (12 : ℚ) (0 : k) : HahnSeries ℚ k) = 0 by
      simp, add_zero]
    have hmin : (↑(2 : ℚ) : WithTop ℚ) ≤
        min B.orderTop
          (HahnSeries.single (12 : ℚ) (B.coeff 12) : HahnSeries ℚ k).orderTop :=
      min_le_min hB hsingle
    exact le_trans hmin HahnSeries.min_orderTop_le_orderTop_sub
  have hB02 : (↑(4 : ℚ) : WithTop ℚ) ≤ (B0 ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (by convert add_le_add hB0 hB0 using 1 <;> norm_num)
      HahnSeries.orderTop_add_le_mul
  have hB02neg2 : (B0 ^ 2).coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB02)
  have hB0neg14 : B0.coeff (-14) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB0)
  have hsB02 : (s * B0 ^ 2).coeff 10 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
    simp [hB02neg2]
  have hs2B0 : (s ^ 2 * B0).coeff 10 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
    norm_num
    simp [hB0neg14]
  have hs3 : (s ^ 3).coeff 10 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single]
    norm_num
  have hsG : (s * G).coeff 10 = b12 * G.coeff (-2) := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hs : s.coeff 10 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single]
    norm_num
  have hpoly :
      rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          (B0 + s) C F G =
        rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          B0 C F G +
        HahnSeries.C (-(24 / 27 : k)) * (s * B0 ^ 2) +
        HahnSeries.C (-(24 / 27 : k)) * (s ^ 2 * B0) +
        HahnSeries.C (-(8 / 27 : k)) * s ^ 3 +
        HahnSeries.C (8 / 3 : k) * (s * G) +
        HahnSeries.C (2 * epsilon) * s := by
    simp only [rhoOneI4ZeroFactored68, HahnSeries.C_eq_algebraMap,
      map_mul, map_neg, map_div₀, map_ofNat]
    ring
  have hscale (c : k) (X : HahnSeries ℚ k) (n : ℚ) :
      (HahnSeries.C c * X).coeff n = c * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [hBform, hpoly]
  simp only [HahnSeries.coeff_add, hscale, hsB02, hs2B0, hs3, hsG,
    hs, mul_zero, add_zero]
  ring

def rhoOne_boundaryG_i4tenAtB12_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (b12 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (rhoOneI4ZeroFactored68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon)
    (rhoOne_boundaryG_replaceB12_68 B b12) C F G).coeff 10

def rhoOne_boundaryG_i4tenB12Slope68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (8 / 3 : k) * G.coeff (-2)

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i4ten_actual_B12_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_i4tenAtB12_68 T
        ((ratFuncAtHahn46 T.root T.source.B).coeff 12) =
      rhoOne_boundaryG_i4tenFactoredSourceRow68 T := by
  dsimp only [rhoOne_boundaryG_i4tenAtB12_68,
    rhoOne_boundaryG_i4tenFactoredSourceRow68]
  rw [rhoOne_boundaryG_replaceB12_self68]

def rhoOne_boundaryG_i4tenB12Transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let B := ratFuncAtHahn46 T.root T.source.B
  let Row0 := rhoOne_boundaryG_i4tenAtB12_68 T 0
  let Slope := rhoOne_boundaryG_i4tenB12Slope68 T
  Row0 + Slope * B.coeff 12 = 0 ∧ Slope ≠ 0 ∧
    B.coeff 12 = -Row0 / Slope

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4TenB12Transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4TenSource68 T ∧
  rhoOne_boundaryG_i4tenB12Transport68 T

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i4ten_B12_transport68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4TenSource68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4TenB12Transport68 T := by
  have Rc := R.1.1.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffTransport68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hcells⟩
  let B := ratFuncAtHahn46 T.root T.source.B
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hBord : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop := by
    simpa only [B] using rhoOne_boundaryG_B_order_of_quadratic_residual68 T Q
  have hAff := rhoOne_boundaryG_i4ten_replaceB12_affine68
    T.source.gamma T.source.epsilon B C F G hBord (B.coeff 12)
  have hActual := T.rhoOne_boundaryG_i4ten_actual_B12_68
  have hAffSource : rhoOne_boundaryG_i4tenAtB12_68 T (B.coeff 12) =
      rhoOne_boundaryG_i4tenAtB12_68 T 0 +
        rhoOne_boundaryG_i4tenB12Slope68 T * B.coeff 12 := by
    dsimp only [rhoOne_boundaryG_i4tenAtB12_68,
      rhoOne_boundaryG_i4tenB12Slope68]
    simpa only [A, B, C, F, G] using hAff
  have hrow : rhoOne_boundaryG_i4tenAtB12_68 T 0 +
      rhoOne_boundaryG_i4tenB12Slope68 T * B.coeff 12 = 0 := by
    rw [hActual, R.2] at hAffSource
    exact hAffSource.symm
  have hSlope : rhoOne_boundaryG_i4tenB12Slope68 T ≠ 0 := by
    dsimp only [rhoOne_boundaryG_i4tenB12Slope68]
    exact mul_ne_zero (by norm_num) hgm2
  have hsolve : B.coeff 12 =
      -rhoOne_boundaryG_i4tenAtB12_68 T 0 /
        rhoOne_boundaryG_i4tenB12Slope68 T := by
    apply (eq_div_iff hSlope).2
    linear_combination hrow
  refine ⟨R, ?_⟩
  dsimp only [rhoOne_boundaryG_i4tenB12Transport68]
  exact ⟨hrow, hSlope, by simpa only [B] using hsolve⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4TenB12Transport68

end Max11DegreeRoutes
