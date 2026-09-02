import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroI3SixReductionScratch

/-! # Exact `I4(6)` on the two signed-linear `K` cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroI4SixCross68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Exact coefficient six of the constant `I4` factor. -/
theorem rhoOne_boundaryG_i4six_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    -(B.coeff 2 ^ 3) / 9 +
      B.coeff 2 * G.coeff 4 + B.coeff 3 * G.coeff 3 +
      B.coeff 4 * G.coeff 2 + B.coeff 5 * G.coeff 1 +
      B.coeff 6 * G.coeff 0 + B.coeff 7 * G.coeff (-1) +
      B.coeff 8 * G.coeff (-2) +
      C.coeff 1 * F.coeff 5 + C.coeff 2 * F.coeff 4 +
      C.coeff 3 * F.coeff 3 + C.coeff 4 * F.coeff 2 +
      C.coeff 5 * F.coeff 1 + C.coeff 6 * F.coeff 0 +
      (3 / 4 : k) * epsilon * B.coeff 6 = 0 := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]; simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]; simp
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
  have hBG := laurent_coeff_mul_lower_six68 B G 2 (-2) hB hG
  have hSF := laurent_coeff_mul_lower_five68 S F 1 0 hS hF
  have hB3 := laurent_coeff_mul_three_lower_terminal68 B B B 2 2 2 hB hB hB
  norm_num at hBG hSF hB3
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num), hSco 4 (by norm_num),
    hSco 5 (by norm_num), hSco 6 (by norm_num)] at hSF
  have hB3' : (B ^ 3).coeff 6 = B.coeff 2 ^ 3 := by
    rw [show B ^ 3 = B * B * B by ring]
    rw [hB3]
    ring
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 6 = 0 := by
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
      map_mul, map_add, map_neg, map_div₀, map_ofNat]
    ring
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 6) hi4
  rw [hi4rewrite] at hc
  simp only [HahnSeries.coeff_add, hscale] at hc
  rw [hB3', hBG, hSF, hi4rhs] at hc
  linear_combination (3 / 8 : k) * hc

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4sixHahnRow68
    (epsilon : k) (B C F G : HahnSeries ℚ k) : k :=
  -(B.coeff 2 ^ 3) / 9 +
    B.coeff 2 * G.coeff 4 + B.coeff 3 * G.coeff 3 +
    B.coeff 4 * G.coeff 2 + B.coeff 5 * G.coeff 1 +
    B.coeff 6 * G.coeff 0 + B.coeff 7 * G.coeff (-1) +
    B.coeff 8 * G.coeff (-2) +
    C.coeff 1 * F.coeff 5 + C.coeff 2 * F.coeff 4 +
    C.coeff 3 * F.coeff 3 + C.coeff 4 * F.coeff 2 +
    C.coeff 5 * F.coeff 1 + C.coeff 6 * F.coeff 0 +
    (3 / 4 : k) * epsilon * B.coeff 6

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_i4six68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    rhoOne_boundaryG_i4sixHahnRow68 epsilon
      (ratFuncAtHahn46 root B) (ratFuncAtHahn46 root C)
      (ratFuncAtHahn46 root F) (ratFuncAtHahn46 root G) = 0 := by
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 2 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-2) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi4L' : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) BL CL FL GLa = HahnSeries.C i4 := by
    simpa only [BL, CL, FL, GLa, rhoOneI4ZeroFactored68,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi4L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by
    rw [← hcs C 0]
    exact hS0
  have hf := rhoOne_boundaryG_i4six_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hS0L hi4L'
  have hf' := hf
  simp only [rhoOne_boundaryG_i4sixHahnRow68, BL, CL, FL, GLa,
    ← hcs B 2, ← hcs B 3, ← hcs B 4, ← hcs B 5,
    ← hcs B 6, ← hcs B 7, ← hcs B 8,
    ← hcs C 1, ← hcs C 2, ← hcs C 3, ← hcs C 4,
    ← hcs C 5, ← hcs C 6,
    ← hcs F 0, ← hcs F 1, ← hcs F 2, ← hcs F 3,
    ← hcs F 4, ← hcs F 5,
    ← hcs G (-2), ← hcs G (-1), ← hcs G 0, ← hcs G 1,
    ← hcs G 2, ← hcs G 3, ← hcs G 4] at hf'
  dsimp only [rhoOne_boundaryG_i4sixHahnRow68]
  norm_num at hf' ⊢
  linear_combination hf'

/-- Source-coordinate expanded `I4(6)`. -/
def rhoOne_boundaryG_i4sixExpandedSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  rhoOne_boundaryG_i4sixHahnRow68 T.source.epsilon B C F G

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i4six_expanded_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i4sixExpandedSourceRow68 T = 0 := by
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
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
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
  have hCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root C).orderTop := by rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root F).orderTop := by rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hrow := ratFunc_boundaryG_i4six68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS0) hi4f
  rw [hCmap, hFmap, hGmap] at hrow
  exact hrow

omit [IsAlgClosed k] in
/-- `I4(6)` after the signed `D=0` substitutions, with `B[6]` affine. -/
def rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (-(B.coeff 2 ^ 3) / 9 + B.coeff 2 * G.coeff 4 +
    B.coeff 4 * G.coeff 2 + B.coeff 5 * G.coeff 1 + b6 * G.coeff 0 +
    B.coeff 7 * (sigma * r ^ 3 * B.coeff 2 / 27) +
    B.coeff 8 * G.coeff (-2) -
    (sigma * r * B.coeff 2 / 3) * F.coeff 5 +
    C.coeff 2 * F.coeff 4 + C.coeff 3 * F.coeff 3 +
    C.coeff 4 * F.coeff 2 +
    C.coeff 5 * (A.coeff (-1) * B.coeff 2 / 3) +
    C.coeff 6 * (r ^ 2 * B.coeff 2 / 9) +
    (3 / 4 : k) * T.source.epsilon * b6)

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i4six_reduce68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0)
    (hray : 27 * (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2)
    (hrf : r * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      3 * sigma * (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    (hlinear : 3 * (rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 +
      sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0)
    (hb3 : (ratFuncAtHahn46 T.root T.source.B).coeff 3 = 0)
    (hD : 3 * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
      (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
        (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0)
    (hi4 : rhoOne_boundaryG_i4sixExpandedSourceRow68 T = 0) :
    rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r
      ((ratFuncAtHahn46 T.root T.source.B).coeff 6) = 0 := by
  have hgm1 : (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hc1 : (rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 =
      -(sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  have hf0mul : r * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      r * (r ^ 2 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) := by
    calc
      _ = 3 * sigma * (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) := hrf
      _ = r * (r ^ 2 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) := by
        rw [hgm1]
        calc
          3 * sigma * (sigma * r ^ 3 *
              (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27) =
              sigma ^ 2 * r ^ 3 *
                (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9 := by ring
          _ = r * (r ^ 2 *
              (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) := by
            rw [hsigma]
            ring
  have hf0 : (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      r ^ 2 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9 :=
    mul_left_cancel₀ hr0 hf0mul
  have hf1 : (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1 =
      (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
        (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3 := by
    linear_combination (1 / 3 : k) * hD
  dsimp only [rhoOne_boundaryG_i4sixExpandedSourceRow68,
    rhoOne_boundaryG_i4sixHahnRow68,
    rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68] at hi4 ⊢
  rw [hb3, hgm1, hc1, hf0, hf1] at hi4
  linear_combination hi4

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i4six_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
    rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r b6 =
      rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0 + M * b6 := by
  dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i3six_i4six_cross68
    (L J0 M K0 b6 : k)
    (h3 : J0 - (8 / 81 : k) * L * b6 = 0)
    (h4 : K0 + M * b6 = 0) :
    81 * M * J0 + 8 * L * K0 = 0 := by
  linear_combination 81 * (M * h3 + (8 / 81 : k) * L * h4)

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i4five_i4six_cross68
    (sigma r b I4b M K0 b6 : k)
    (h5 : I4b + (sigma * r ^ 3 * b / 27) * b6 = 0)
    (h6 : K0 + M * b6 = 0) :
    sigma * r ^ 3 * b * K0 - 27 * M * I4b = 0 := by
  linear_combination 27 *
    ((sigma * r ^ 3 * b / 27) * h6 - M * h5)

/-- The two old `K` cells, now carrying exact `I4(6)` and both eliminants. -/
def rhoOne_boundaryG_signedRayLinearDZeroI4SixCells68
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
  let K := r ^ 4 * B.coeff 2 ^ 2 - 162 * C.coeff 2 * G.coeff (-2)
  let T0 := rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
    T sigma r 0
  let I0 := rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
    T sigma r 0
  let I4b := rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r
  let J0 := rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0
  let L := -3 * r ^ 2 * F.coeff 2 +
    3 * A.coeff (-1) ^ 2 * B.coeff 2 + A.coeff 0 * r ^ 2 * B.coeff 2
  let K0 := rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  D0 = 0 →
    ((K = 0 ∧ C.coeff 2 ≠ 0 ∧ I0 = 0 ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r
          (B.coeff 6) = 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r
          (B.coeff 6) = 0 ∧
        3 * sigma * r ^ 3 * B.coeff 2 * J0 + 8 * L * I4b = 0 ∧
        81 * M * J0 + 8 * L * K0 = 0 ∧
        sigma * r ^ 3 * B.coeff 2 * K0 - 27 * M * I4b = 0) ∨
      (K ≠ 0 ∧ (T0 = 0 ↔ I0 = 0) ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r
          (B.coeff 6) = 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r
          (B.coeff 6) = 0 ∧
        3 * sigma * r ^ 3 * B.coeff 2 * J0 + 8 * L * I4b = 0 ∧
        81 * M * J0 + 8 * L * K0 = 0 ∧
        sigma * r ^ 3 * B.coeff 2 * K0 - 27 * M * I4b = 0))

/-- Source-facing successor carrying the exact `I4(6)` cross. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixCross68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3SixReduction68 T ∧
  rhoOne_boundaryG_i4sixExpandedSourceRow68 T = 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4SixCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i4six_cross68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3SixReduction68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixCross68 T := by
  have hrow := T.rhoOne_boundaryG_i4six_expanded_source68 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3SixReduction68] at Rc
  rcases Rc with ⟨Rterm, hi3sixSource, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68] at Rtermc
  rcases Rtermc with ⟨Rfour, hlead, sigma', r', hsigma', hr0', hb', hgm2',
    hr', hray', hrf', hlinear', hb3', hwitness', hcellsTerminal⟩
  have Rfourc := Rfour
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4FiveCross68] at Rfourc
  rcases Rfourc with ⟨Rkeep, hi4five, sigma'', r'', hsigma'', hr0'', hb'', hgm2'',
    hr'', hray'', hrf'', hlinear'', hb3'', hwitness'', hcross4⟩
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4SixCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4SixCells68]
    intro hD
    have h6actual := rhoOne_boundaryG_signedRayLinear_dZero_i4six_reduce68
      T sigma r hsigma hr0 hray hrf hlinear hb3 hD hrow
    have h6aff := rhoOne_boundaryG_signedRayLinear_dZero_i4six_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    dsimp only at h6aff
    have h6base :
        rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0 +
          ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
            (3 / 4 : k) * T.source.epsilon) *
          (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← h6aff]
      exact h6actual
    have h3old := hcellsOld hD
    have h3actual : rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68
        T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6) = 0 := by
      rcases h3old with hz | hn
      · exact hz.2.2.2.2.1
      · exact hn.2.2.2.1
    have hprior : 3 * sigma * r ^ 3 *
          (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
          rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0 +
        8 * (-3 * r ^ 2 * (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 2 +
          3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-1) ^ 2 *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 +
          (ratFuncAtHahn46 T.root T.source.A).coeff 0 * r ^ 2 *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2) *
          rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r = 0 := by
      rcases h3old with hz | hn
      · exact hz.2.2.2.2.2
      · exact hn.2.2.2.2
    have h3aff := rhoOne_boundaryG_signedRayLinear_dZero_i3six_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    dsimp only at h3aff
    have h3base :
        rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0 -
          (8 / 81 : k) *
            (-3 * r ^ 2 * (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 2 +
             3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-1) ^ 2 *
               (ratFuncAtHahn46 T.root T.source.B).coeff 2 +
             (ratFuncAtHahn46 T.root T.source.A).coeff 0 * r ^ 2 *
               (ratFuncAtHahn46 T.root T.source.B).coeff 2) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← h3aff]
      exact h3actual
    have h5actual := rhoOne_boundaryG_signedRayLinear_dZero_i4five_reduce68
      T sigma r hsigma hr0 hray hrf hlinear hb3 hD hi4five
    have h36 := rhoOne_boundaryG_signedRayLinear_dZero_i3six_i4six_cross68
      (-3 * r ^ 2 * (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 2 +
       3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-1) ^ 2 *
         (ratFuncAtHahn46 T.root T.source.B).coeff 2 +
       (ratFuncAtHahn46 T.root T.source.A).coeff 0 * r ^ 2 *
         (ratFuncAtHahn46 T.root T.source.B).coeff 2)
      (rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0)
      ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
        (3 / 4 : k) * T.source.epsilon)
      (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 6) h3base h6base
    have h46 := rhoOne_boundaryG_signedRayLinear_dZero_i4five_i4six_cross68
      sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
      (rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r)
      ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
        (3 / 4 : k) * T.source.epsilon)
      (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 6) h5actual h6base
    rcases h3old with hz | hn
    · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1,
        h3actual, h6actual, hprior, h36, h46⟩
    · exact Or.inr ⟨hn.1, hn.2.1, hn.2.2.1,
        h3actual, h6actual, hprior, h36, h46⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixCross68]
  exact ⟨R, hrow, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcells⟩

/-- Outer selector preserving coordinate, QR, and nonsingular siblings. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i4six_cross_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixCross68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_i3six_reduction_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hzero | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_i4six_cross68
          hsigned.1 hzero)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroI4SixCross68

end Max11DegreeRoutes
