import Sol68ScaleTwoAlignedSquareBoundaryGQuadraticWallScratch

/-! # The coordinate endpoint of the aligned-square `G[-2]` minor wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGCoordinateEndpoint68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundaryGCoordinateLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
/-- Coefficient four of the zero-`I4` factor after the coordinate endpoint
raises `ord B` to three and `ord F` to one. -/
theorem rhoOne_boundaryG_coordinate_i4four_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(3 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(1 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hGm : G.coeff (-1) = 0)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    B.coeff 3 * G.coeff 1 + B.coeff 4 * G.coeff 0 +
      B.coeff 6 * G.coeff (-2) + C.coeff 1 * F.coeff 3 +
      C.coeff 2 * F.coeff 2 + C.coeff 3 * F.coeff 1 +
      (3 / 4 : k) * epsilon * B.coeff 4 = 0 := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
  have hSco0 : S.coeff 0 = 0 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    linear_combination hS0
  have hS := laurent_orderTop_ge_succ_of_coeff_zero68 S 0 hSbase hSco0
  have hSco (n : ℤ) (hn : n ≠ 0) : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    rw [if_neg hn]
    ring
  have hBG := laurent_coeff_mul_lower_three68 B G 3 (-2) hB hG
  have hSF := laurent_coeff_mul_lower_two68 S F 1 1 hS hF
  norm_num at hBG hSF
  rw [hGm] at hBG
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num)] at hSF
  have hB3ord : (↑(9 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow (x := B) (n := 3)
    have ht := nsmul_le_nsmul_right hB 3
    norm_num at ht
    exact le_trans ht hp
  have hB3z : (B ^ 3).coeff 4 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB3ord)
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 4 = 0 := by
    simp [HahnSeries.C_apply]
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hi4rewrite : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G =
      HahnSeries.C (-(8 / 27 : k)) * (B ^ 3) +
        HahnSeries.C (8 / 3 : k) * (B * G) +
        HahnSeries.C (4 / 3 : k) * (S * F) +
        HahnSeries.C (2 * epsilon) * B := by
    simp only [rhoOneI4ZeroFactored68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 4) hi4
  rw [hi4rewrite] at hc
  simp only [HahnSeries.coeff_add, hscale] at hc
  rw [hB3z, hBG, hSF, hi4rhs] at hc
  linear_combination (3 / 8 : k) * hc

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_coordinate_i4four68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hGm : (ratFuncAtHahn46 root G).coeff (-1) = 0)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    (ratFuncAtHahn46 root B).coeff 3 * (ratFuncAtHahn46 root G).coeff 1 +
      (ratFuncAtHahn46 root B).coeff 4 * (ratFuncAtHahn46 root G).coeff 0 +
      (ratFuncAtHahn46 root B).coeff 6 * (ratFuncAtHahn46 root G).coeff (-2) +
      (ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root F).coeff 3 +
      (ratFuncAtHahn46 root C).coeff 2 * (ratFuncAtHahn46 root F).coeff 2 +
      (ratFuncAtHahn46 root C).coeff 3 * (ratFuncAtHahn46 root F).coeff 1 +
      (3 / 4 : k) * epsilon * (ratFuncAtHahn46 root B).coeff 4 = 0 := by
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 3 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 1 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-2) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi4L' : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) BL CL FL GLa = HahnSeries.C i4 := by
    simpa only [BL, CL, FL, GLa, rhoOneI4ZeroFactored68,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi4L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hGmL : GLa.coeff (-1) = 0 := by rw [← hcs G (-1)]; exact hGm
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by rw [← hcs C 0]; exact hS0
  have hf := rhoOne_boundaryG_coordinate_i4four_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hGmL hS0L hi4L'
  have hf' := hf
  simp only [BL, CL, FL, GLa, ← hcs B 3, ← hcs B 4, ← hcs B 6,
    ← hcs C 1, ← hcs C 2, ← hcs C 3,
    ← hcs F 1, ← hcs F 2, ← hcs F 3,
    ← hcs G (-2), ← hcs G 0, ← hcs G 1] at hf'
  convert hf' using 1 <;> norm_num

def RhoOneAlignedSquareGNegTwoCoordinateGain68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
  B.coeff 2 = 0 ∧ F.coeff 0 = 0 ∧ G.coeff (-1) = 0 ∧
  (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
  (↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
  B.coeff 3 * G.coeff 1 + B.coeff 4 * G.coeff 0 +
    B.coeff 6 * G.coeff (-2) + C.coeff 1 * F.coeff 3 +
    C.coeff 2 * F.coeff 2 + C.coeff 3 * F.coeff 1 +
    (3 / 4 : k) * T.source.epsilon * B.coeff 4 = 0

def RhoOneAlignedSquareGNegTwoSignedRayWitness68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  B.coeff 2 ≠ 0 ∧ G.coeff (-1) ≠ 0 ∧
  ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    ((27 * G.coeff (-1) = r ^ 3 * B.coeff 2 ∧
        r * F.coeff 0 = 3 * G.coeff (-1)) ∨
     (27 * G.coeff (-1) = -(r ^ 3 * B.coeff 2) ∧
        r * F.coeff 0 = -(3 * G.coeff (-1))))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_coordinateEndpoint68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        RhoOneAlignedSquareGNegTwoSignedRayWitness68 T) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Rc
  rcases Rc with ⟨Rm, hsplit⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3old, i4old, hi3srcOld, hi4srcOld, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hterminal⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, hi3zero, hterminalOld⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hb1, hS, hscalar, hi4face⟩
  rcases hsplit with ⟨hwall, hred, hends⟩ | hnon
  · rcases hends with hcoord | hray
    · left
      let A : RatFunc k := T.source.A
      let B : RatFunc k := T.source.B
      let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
      let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
      let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
      let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
      have hCmap : ratFuncAtHahn46 T.root C =
          rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0) := by
        dsimp only [C, A, rhoOneCDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hFmap : ratFuncAtHahn46 T.root F =
          rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D) := by
        dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
        simp only [map_sub, map_mul, ratFuncAtHahn46_C]
      have hEmap : ratFuncAtHahn46 T.root E =
          rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E) := by
        dsimp only [E, A, rhoOneEDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hGmap : ratFuncAtHahn46 T.root G =
          rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E)) := by
        dsimp only [G, rhoOneTangentEDefectHahn68]
        rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
      have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
      have hB2 : (ratFuncAtHahn46 T.root B).coeff ((2 : ℤ) : ℚ) = 0 := by
        norm_num
        simpa only [B] using hcoord.1
      have hB3 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root B 2 hBH hB2
      norm_num at hB3
      have hFH : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root F).orderTop := by rw [hFmap]; exact hF
      have hF0 : (ratFuncAtHahn46 T.root F).coeff ((0 : ℤ) : ℚ) = 0 := by
        norm_num
        rw [hFmap]
        exact hcoord.2.1
      have hF1 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root F 0 hFH hF0
      norm_num at hF1
      have hCH : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root C).orderTop := by rw [hCmap]; exact hC
      have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
      obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
        T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
      have hrow := ratFunc_boundaryG_coordinate_i4four68 T.root
        T.source.gamma T.source.epsilon i4 B C F G hB3 hCH hF1 hGH
        (by rw [hGmap]; exact hcoord.2.2)
        (by rw [hCmap]; exact hS) hi4f
      rw [hCmap, hFmap, hGmap] at hrow
      dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGain68]
      refine ⟨R, hcoord.1, hcoord.2.1, hcoord.2.2, ?_, ?_, hrow⟩
      · convert hB3 using 1 <;> norm_num
      · rw [← hFmap]
        exact hF1
    · exact Or.inr (Or.inl ⟨R, hray⟩)
  · exact Or.inr (Or.inr ⟨R, hnon.1⟩)

end AlignedSquareBoundaryGCoordinateEndpoint68

end Max11DegreeRoutes
