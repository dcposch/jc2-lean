import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminantScratch

/-! # The first finite high-jet reduction of the paired ninth rows -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_replaceB11_68 (B : HahnSeries ℚ k) (b11 : k) :
    HahnSeries ℚ k :=
  B - HahnSeries.single 11 (B.coeff 11) + HahnSeries.single 11 b11

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_replaceB11_self68 (B : HahnSeries ℚ k) :
    rhoOne_boundaryG_replaceB11_68 B (B.coeff 11) = B := by
  dsimp only [rhoOne_boundaryG_replaceB11_68]
  abel

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_replaceB11_i3nine_affine68
    (gamma epsilon : k) (A B C F G : HahnSeries ℚ k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop) (b11 : k) :
    (rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        A (rhoOne_boundaryG_replaceB11_68 B b11) C F G).coeff 9 =
      (rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        A (rhoOne_boundaryG_replaceB11_68 B 0) C F G).coeff 9 +
      (-(8 / 9 : k)) * (A * F).coeff (-2) * b11 := by
  let B0 := rhoOne_boundaryG_replaceB11_68 B 0
  let s : HahnSeries ℚ k := HahnSeries.single 11 b11
  have hform : rhoOne_boundaryG_replaceB11_68 B b11 = B0 + s := by
    dsimp only [B0, s, rhoOne_boundaryG_replaceB11_68]
    simp
  have hs11 : (↑(2 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (11 : ℚ) (B.coeff 11) : HahnSeries ℚ k).orderTop := by
    by_cases hb : B.coeff 11 = 0
    · simp [hb]
    · rw [HahnSeries.orderTop_single hb]
      exact WithTop.coe_le_coe.mpr (by norm_num)
  have hB0 : (↑(2 : ℚ) : WithTop ℚ) ≤ B0.orderTop := by
    dsimp only [B0, rhoOne_boundaryG_replaceB11_68]
    rw [show (HahnSeries.single (11 : ℚ) (0 : k) : HahnSeries ℚ k) = 0 by
      simp, add_zero]
    have hmin : (↑(2 : ℚ) : WithTop ℚ) ≤
        min B.orderTop
          (HahnSeries.single (11 : ℚ) (B.coeff 11) : HahnSeries ℚ k).orderTop :=
      min_le_min hB hs11
    exact le_trans hmin HahnSeries.min_orderTop_le_orderTop_sub
  have hB0C : (↑(2 : ℚ) : WithTop ℚ) ≤ (B0 * C).orderTop :=
    le_trans (by convert add_le_add hB0 hC using 1 <;> norm_num)
      HahnSeries.orderTop_add_le_mul
  have hB0neg2 : B0.coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB0)
  have hB0Cneg2 : (B0 * C).coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB0C)
  have hCneg13 : C.coeff (-13) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hC)
  have hsAF : (s * (A * F)).coeff 9 = b11 * (A * F).coeff (-2) := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hsBC : (s * (B0 * C)).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
    simp [hB0Cneg2]
  have hs2C : (s ^ 2 * C).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
    norm_num
    simp [hCneg13]
  have hsB : (s * B0).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
    simp [hB0neg2]
  have hs2 : (s ^ 2).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single]
    norm_num
  have hpoly :
      rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          A (B0 + s) C F G =
        rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          A B0 C F G +
        HahnSeries.C (-(8 / 9 : k)) * (s * (A * F)) +
        HahnSeries.C (-(16 / 9 : k)) * (s * (B0 * C)) +
        HahnSeries.C (-(8 / 9 : k)) * (s ^ 2 * C) +
        HahnSeries.C (-(4 / 3 : k) * gamma) * (s * B0) +
        HahnSeries.C (-(2 / 3 : k) * gamma) * s ^ 2 := by
    simp only [rhoOneI3CapFactored68, HahnSeries.C_eq_algebraMap,
      map_mul, map_neg, map_div₀, map_ofNat]
    ring
  have hscale (c : k) (X : HahnSeries ℚ k) (n : ℚ) :
      (HahnSeries.C c * X).coeff n = c * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [hform, hpoly]
  simp only [HahnSeries.coeff_add, hscale, hsAF, hsBC, hs2C, hsB,
    hs2, mul_zero, add_zero]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_replaceB11_i4nine_affine68
    (gamma epsilon : k) (B C F G : HahnSeries ℚ k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop) (b11 : k) :
    (rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        (rhoOne_boundaryG_replaceB11_68 B b11) C F G).coeff 9 =
      (rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        (rhoOne_boundaryG_replaceB11_68 B 0) C F G).coeff 9 +
      (8 / 3 : k) * G.coeff (-2) * b11 := by
  let B0 := rhoOne_boundaryG_replaceB11_68 B 0
  let s : HahnSeries ℚ k := HahnSeries.single 11 b11
  have hform : rhoOne_boundaryG_replaceB11_68 B b11 = B0 + s := by
    dsimp only [B0, s, rhoOne_boundaryG_replaceB11_68]
    simp
  have hs11 : (↑(2 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (11 : ℚ) (B.coeff 11) : HahnSeries ℚ k).orderTop := by
    by_cases hb : B.coeff 11 = 0
    · simp [hb]
    · rw [HahnSeries.orderTop_single hb]
      exact WithTop.coe_le_coe.mpr (by norm_num)
  have hB0 : (↑(2 : ℚ) : WithTop ℚ) ≤ B0.orderTop := by
    dsimp only [B0, rhoOne_boundaryG_replaceB11_68]
    rw [show (HahnSeries.single (11 : ℚ) (0 : k) : HahnSeries ℚ k) = 0 by
      simp, add_zero]
    have hmin : (↑(2 : ℚ) : WithTop ℚ) ≤
        min B.orderTop
          (HahnSeries.single (11 : ℚ) (B.coeff 11) : HahnSeries ℚ k).orderTop :=
      min_le_min hB hs11
    exact le_trans hmin HahnSeries.min_orderTop_le_orderTop_sub
  have hB02 : (↑(4 : ℚ) : WithTop ℚ) ≤ (B0 ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (by convert add_le_add hB0 hB0 using 1 <;> norm_num)
      HahnSeries.orderTop_add_le_mul
  have hB02neg2 : (B0 ^ 2).coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB02)
  have hB0neg13 : B0.coeff (-13) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB0)
  have hsB02 : (s * B0 ^ 2).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
    simp [hB02neg2]
  have hs2B0 : (s ^ 2 * B0).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
    norm_num
    simp [hB0neg13]
  have hs3 : (s ^ 3).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single]
    norm_num
  have hsG : (s * G).coeff 9 = b11 * G.coeff (-2) := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hs : s.coeff 9 = 0 := by
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
    ring_nf
  have hscale (c : k) (X : HahnSeries ℚ k) (n : ℚ) :
      (HahnSeries.C c * X).coeff n = c * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [hform, hpoly]
  simp only [HahnSeries.coeff_add, hscale, hsB02, hs2B0, hs3, hsG,
    hs, mul_zero, add_zero]
  ring

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i3nineAtB6B11_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (b11 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := rhoOne_boundaryG_replaceB6_68
    (ratFuncAtHahn46 T.root T.source.B) 0
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A
    (ratFuncAtHahn46 T.root T.source.B)
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (rhoOneI3CapFactored68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon) A
    (rhoOne_boundaryG_replaceB11_68 B b11) C F G).coeff 9

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4nineAtB6B11_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (b11 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := rhoOne_boundaryG_replaceB6_68
    (ratFuncAtHahn46 T.root T.source.B) 0
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A
    (ratFuncAtHahn46 T.root T.source.B)
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (rhoOneI4ZeroFactored68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon)
    (rhoOne_boundaryG_replaceB11_68 B b11) C F G).coeff 9

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_double_affine_split68
    (D K b : k) (h : D + K * b = 0) :
    (K = 0 ∧ D = 0) ∨ (K ≠ 0 ∧ b = -D / K) :=
  rhoOne_boundaryG_i3nine_zero_slope_split68 D K b h

def rhoOne_boundaryG_signedRayLinearDZeroI4NineB11Cells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let W90 := rhoOne_boundaryG_i4nineAtB6_68 T 0
  let G3 := G.coeff 3
  let J110 := rhoOne_boundaryG_i3nineAtB6B11_68 T 0
  let P11 := (-(8 / 9 : k)) * (A * F).coeff (-2)
  let W110 := rhoOne_boundaryG_i4nineAtB6B11_68 T 0
  let Q11 := (8 / 3 : k) * G.coeff (-2)
  let D11 := (8 : k) * G3 * J110 - 3 * N9 * W110
  let K11 := (8 : k) * G3 * P11 - 3 * N9 * Q11
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineDeterminantCells68 T sigma r ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * W90 = 0 →
      J90 = J110 + P11 * B.coeff 11 ∧
      W90 = W110 + Q11 * B.coeff 11 ∧
      D11 + K11 * B.coeff 11 = 0 ∧
      ((K11 = 0 ∧ D11 = 0) ∨
       (K11 ≠ 0 ∧ B.coeff 11 = -D11 / K11)))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68 T ∧
  ∃ sigma r : k, r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4NineB11Cells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_B11_reduction68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68] at Rc
  rcases Rc.2 with ⟨sigma, r, hr0, hr, hcellsOld⟩
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdetOld⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcrossOld⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let B0 := rhoOne_boundaryG_replaceB6_68 B 0
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hs6 : (↑(2 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (6 : ℚ) (B.coeff 6) : HahnSeries ℚ k).orderTop := by
    by_cases hb : B.coeff 6 = 0
    · simp [hb]
    · rw [HahnSeries.orderTop_single hb]
      exact WithTop.coe_le_coe.mpr (by norm_num)
  have hB0 : (↑(2 : ℚ) : WithTop ℚ) ≤ B0.orderTop := by
    dsimp only [B0, rhoOne_boundaryG_replaceB6_68]
    rw [show (HahnSeries.single (6 : ℚ) (0 : k) : HahnSeries ℚ k) = 0 by
      simp, add_zero]
    have hmin : (↑(2 : ℚ) : WithTop ℚ) ≤
        min B.orderTop
          (HahnSeries.single (6 : ℚ) (B.coeff 6) : HahnSeries ℚ k).orderTop :=
      min_le_min hB hs6
    exact le_trans hmin HahnSeries.min_orderTop_le_orderTop_sub
  have hb11 : B0.coeff 11 = B.coeff 11 := by
    dsimp only [B0, rhoOne_boundaryG_replaceB6_68]
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub,
      HahnSeries.coeff_single, if_neg (by norm_num : (11 : ℚ) ≠ 6),
      sub_zero, add_zero]
  have hJaff : rhoOne_boundaryG_i3nineAtB6_68 T 0 =
      rhoOne_boundaryG_i3nineAtB6B11_68 T 0 +
        (-(8 / 9 : k)) * (A * F).coeff (-2) * B.coeff 11 := by
    have h := rhoOne_boundaryG_replaceB11_i3nine_affine68 T.source.gamma
      T.source.epsilon A B0 C F G hB0 hC (B0.coeff 11)
    rw [rhoOne_boundaryG_replaceB11_self68] at h
    rw [hb11] at h
    dsimp only [A, B, B0, C, F, G, rhoOne_boundaryG_i3nineAtB6_68,
      rhoOne_boundaryG_i3nineAtB6B11_68] at h ⊢
    exact h
  have hWaff : rhoOne_boundaryG_i4nineAtB6_68 T 0 =
      rhoOne_boundaryG_i4nineAtB6B11_68 T 0 +
        (8 / 3 : k) * G.coeff (-2) * B.coeff 11 := by
    have h := rhoOne_boundaryG_replaceB11_i4nine_affine68 T.source.gamma
      T.source.epsilon B0 C F G hB0 (B0.coeff 11)
    rw [rhoOne_boundaryG_replaceB11_self68] at h
    rw [hb11] at h
    dsimp only [A, B, B0, C, F, G, rhoOne_boundaryG_i4nineAtB6_68,
      rhoOne_boundaryG_i4nineAtB6B11_68] at h ⊢
    exact h
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4NineB11Cells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineB11Cells68]
    intro hD
    have hold := hcellsOld hD
    refine ⟨hcellsOld, ?_⟩
    intro hdbl
    have hD11 :
        ((8 : k) * G.coeff 3 * rhoOne_boundaryG_i3nineAtB6B11_68 T 0 -
          3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
            rhoOne_boundaryG_i4nineAtB6B11_68 T 0) +
        ((8 : k) * G.coeff 3 *
            ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
          3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
            ((8 / 3 : k) * G.coeff (-2))) * B.coeff 11 = 0 := by
      rw [hJaff, hWaff] at hdbl
      linear_combination hdbl.2.2
    have hsplit := rhoOne_boundaryG_double_affine_split68
      ((8 : k) * G.coeff 3 * rhoOne_boundaryG_i3nineAtB6B11_68 T 0 -
        3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
          rhoOne_boundaryG_i4nineAtB6B11_68 T 0)
      ((8 : k) * G.coeff 3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
        3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
          ((8 / 3 : k) * G.coeff (-2)))
      (B.coeff 11) hD11
    exact ⟨hJaff, hWaff, hD11, hsplit⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68]
  exact ⟨R, sigma, r, hr0, hr, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68

end Max11DegreeRoutes
