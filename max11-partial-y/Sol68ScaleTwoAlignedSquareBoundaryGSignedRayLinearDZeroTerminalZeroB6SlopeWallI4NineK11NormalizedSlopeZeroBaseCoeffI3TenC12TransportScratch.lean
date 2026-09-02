import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3TenSourceScratch

/-! # The unique `C[12]` face of the first unused `I3(10)` row -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3TenC12Transport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_replaceC12_68
    (C : HahnSeries ℚ k) (c12 : k) : HahnSeries ℚ k :=
  C - HahnSeries.single (12 : ℚ) (C.coeff 12) +
    HahnSeries.single (12 : ℚ) c12

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_replaceC12_self68 (C : HahnSeries ℚ k) :
    rhoOne_boundaryG_replaceC12_68 C (C.coeff 12) = C := by
  dsimp only [rhoOne_boundaryG_replaceC12_68]
  abel

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3ten_replaceC12_affine68
    (gamma epsilon : k) (A B C F G : HahnSeries ℚ k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop) (c12 : k) :
    (rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
      A B (rhoOne_boundaryG_replaceC12_68 C c12) F G).coeff 10 =
    (rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
      A B (rhoOne_boundaryG_replaceC12_68 C 0) F G).coeff 10 +
      (8 / 3 : k) * G.coeff (-2) * c12 := by
  let C0 := rhoOne_boundaryG_replaceC12_68 C 0
  let s : HahnSeries ℚ k := HahnSeries.single 12 c12
  have hCform : rhoOne_boundaryG_replaceC12_68 C c12 = C0 + s := by
    dsimp only [C0, s, rhoOne_boundaryG_replaceC12_68]
    simp
  have hB2 : (↑(4 : ℚ) : WithTop ℚ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (by convert add_le_add hB hB using 1 <;> norm_num)
      HahnSeries.orderTop_add_le_mul
  have hB2neg2 : (B ^ 2).coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB2)
  have hB2s : (B ^ 2 * s).coeff 10 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_mul_single]
    norm_num
    simp [hB2neg2]
  have hsG : (s * G).coeff 10 = c12 * G.coeff (-2) := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hs : s.coeff 10 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single]
    norm_num
  have hpoly :
      rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          A B (C0 + s) F G =
        rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          A B C0 F G +
        HahnSeries.C (-(8 / 9 : k)) * (B ^ 2 * s) +
        HahnSeries.C (8 / 3 : k) * (s * G) +
        HahnSeries.C (2 * epsilon) * s := by
    simp only [rhoOneI3CapFactored68, HahnSeries.C_eq_algebraMap,
      map_mul, map_neg, map_div₀, map_ofNat]
    ring
  have hscale (c : k) (X : HahnSeries ℚ k) (n : ℚ) :
      (HahnSeries.C c * X).coeff n = c * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [hCform, hpoly]
  simp only [HahnSeries.coeff_add, hscale, hB2s, hsG, hs, mul_zero,
    add_zero]
  ring

def rhoOne_boundaryG_i3tenAtC12_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (c12 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (rhoOneI3CapFactored68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon) A B
    (rhoOne_boundaryG_replaceC12_68 C c12) F G).coeff 10

def rhoOne_boundaryG_i3tenC12Slope68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (8 / 3 : k) * G.coeff (-2)

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i3ten_actual_C12_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_i3tenAtC12_68 T
        ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 12) =
      rhoOne_boundaryG_i3tenFactoredSourceRow68 T := by
  dsimp only [rhoOne_boundaryG_i3tenAtC12_68,
    rhoOne_boundaryG_i3tenFactoredSourceRow68]
  rw [rhoOne_boundaryG_replaceC12_self68]

theorem rhoOne_boundaryG_B_order_of_quadratic_residual68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop := by
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcross⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  exact Rbasec.2.2.2.2.1

def rhoOne_boundaryG_i3tenC12Transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let Row0 := rhoOne_boundaryG_i3tenAtC12_68 T 0
  let Slope := rhoOne_boundaryG_i3tenC12Slope68 T
  Row0 + Slope * C.coeff 12 = 0 ∧ Slope ≠ 0 ∧
    C.coeff 12 = -Row0 / Slope

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3TenC12Transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3TenSource68 T ∧
  rhoOne_boundaryG_i3tenC12Transport68 T

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i3ten_C12_transport68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3TenSource68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3TenC12Transport68 T := by
  have Rc := R.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffTransport68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hcells⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hBord : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop := by
    simpa only [B] using rhoOne_boundaryG_B_order_of_quadratic_residual68 T Q
  have hAff := rhoOne_boundaryG_i3ten_replaceC12_affine68
    T.source.gamma T.source.epsilon A B C F G hBord (C.coeff 12)
  have hActual := T.rhoOne_boundaryG_i3ten_actual_C12_68
  have hAffSource : rhoOne_boundaryG_i3tenAtC12_68 T (C.coeff 12) =
      rhoOne_boundaryG_i3tenAtC12_68 T 0 +
        rhoOne_boundaryG_i3tenC12Slope68 T * C.coeff 12 := by
    dsimp only [rhoOne_boundaryG_i3tenAtC12_68,
      rhoOne_boundaryG_i3tenC12Slope68]
    simpa only [A, B, C, F, G] using hAff
  have hrow : rhoOne_boundaryG_i3tenAtC12_68 T 0 +
      rhoOne_boundaryG_i3tenC12Slope68 T * C.coeff 12 = 0 := by
    rw [hActual, R.2] at hAffSource
    exact hAffSource.symm
  have hSlope : rhoOne_boundaryG_i3tenC12Slope68 T ≠ 0 := by
    dsimp only [rhoOne_boundaryG_i3tenC12Slope68]
    exact mul_ne_zero (by norm_num) hgm2
  have hsolve : C.coeff 12 =
      -rhoOne_boundaryG_i3tenAtC12_68 T 0 /
        rhoOne_boundaryG_i3tenC12Slope68 T := by
    apply (eq_div_iff hSlope).2
    linear_combination hrow
  refine ⟨R, ?_⟩
  dsimp only [rhoOne_boundaryG_i3tenC12Transport68]
  exact ⟨hrow, hSlope, by simpa only [C] using hsolve⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3TenC12Transport68

end Max11DegreeRoutes
