import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroI3EightReductionScratch

/-! # Exact source-backed `I4(8)` on the frozen signed-ray boundary -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroI4EightSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4eightHahnRow68
    (epsilon : k) (B C F G : HahnSeries ℚ k) : k :=
  -(B.coeff 2 ^ 2 * B.coeff 4 + B.coeff 2 * B.coeff 3 ^ 2) / 3 +
    B.coeff 2 * G.coeff 6 + B.coeff 3 * G.coeff 5 +
    B.coeff 4 * G.coeff 4 + B.coeff 5 * G.coeff 3 +
    B.coeff 6 * G.coeff 2 + B.coeff 7 * G.coeff 1 +
    B.coeff 8 * G.coeff 0 + B.coeff 9 * G.coeff (-1) +
    B.coeff 10 * G.coeff (-2) +
    C.coeff 1 * F.coeff 7 + C.coeff 2 * F.coeff 6 +
    C.coeff 3 * F.coeff 5 + C.coeff 4 * F.coeff 4 +
    C.coeff 5 * F.coeff 3 + C.coeff 6 * F.coeff 2 +
    C.coeff 7 * F.coeff 1 + C.coeff 8 * F.coeff 0 +
    (3 / 4 : k) * epsilon * B.coeff 8

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i4eight_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    -(B.coeff 2 ^ 2 * B.coeff 4 + B.coeff 2 * B.coeff 3 ^ 2) / 3 +
      B.coeff 2 * G.coeff 6 + B.coeff 3 * G.coeff 5 +
      B.coeff 4 * G.coeff 4 + B.coeff 5 * G.coeff 3 +
      B.coeff 6 * G.coeff 2 + B.coeff 7 * G.coeff 1 +
      B.coeff 8 * G.coeff 0 + B.coeff 9 * G.coeff (-1) +
      B.coeff 10 * G.coeff (-2) +
      C.coeff 1 * F.coeff 7 + C.coeff 2 * F.coeff 6 +
      C.coeff 3 * F.coeff 5 + C.coeff 4 * F.coeff 4 +
      C.coeff 5 * F.coeff 3 + C.coeff 6 * F.coeff 2 +
      C.coeff 7 * F.coeff 1 + C.coeff 8 * F.coeff 0 +
      (3 / 4 : k) * epsilon * B.coeff 8 = 0 := by
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
  have hBG := laurent_coeff_mul_lower_eight_boundary68 B G 2 (-2) hB hG
  have hSF := laurent_coeff_mul_lower_seven68 S F 1 0 hS hF
  have hB3 := laurent_coeff_mul_three_lower_two68 B B B 2 2 2 hB hB hB
  norm_num at hBG hSF hB3
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num), hSco 4 (by norm_num),
    hSco 5 (by norm_num), hSco 6 (by norm_num),
    hSco 7 (by norm_num), hSco 8 (by norm_num)] at hSF
  have hB3' : (B ^ 3).coeff 8 =
      3 * B.coeff 2 ^ 2 * B.coeff 4 +
        3 * B.coeff 2 * B.coeff 3 ^ 2 := by
    rw [show B ^ 3 = B * B * B by ring]
    rw [hB3]
    ring
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 8 = 0 := by
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 8) hi4
  rw [hi4rewrite] at hc
  simp only [HahnSeries.coeff_add, hscale] at hc
  rw [hB3', hBG, hSF, hi4rhs] at hc
  linear_combination (3 / 8 : k) * hc

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_i4eight68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    rhoOne_boundaryG_i4eightHahnRow68 epsilon
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
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by rw [← hcs C 0]; exact hS0
  have hf := rhoOne_boundaryG_i4eight_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hS0L hi4L'
  have hf' := hf
  simp only [BL, CL, FL, GLa,
    ← hcs B 2, ← hcs B 3, ← hcs B 4, ← hcs B 5,
    ← hcs B 6, ← hcs B 7, ← hcs B 8, ← hcs B 9, ← hcs B 10,
    ← hcs C 1, ← hcs C 2, ← hcs C 3, ← hcs C 4,
    ← hcs C 5, ← hcs C 6, ← hcs C 7, ← hcs C 8,
    ← hcs F 0, ← hcs F 1, ← hcs F 2, ← hcs F 3,
    ← hcs F 4, ← hcs F 5, ← hcs F 6, ← hcs F 7,
    ← hcs G (-2), ← hcs G (-1), ← hcs G 0, ← hcs G 1,
    ← hcs G 2, ← hcs G 3, ← hcs G 4, ← hcs G 5, ← hcs G 6] at hf'
  dsimp only [rhoOne_boundaryG_i4eightHahnRow68]
  norm_num at hf' ⊢
  linear_combination hf'

def rhoOne_boundaryG_i4eightExpandedSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  rhoOne_boundaryG_i4eightHahnRow68 T.source.epsilon B C F G

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i4eight_expanded_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i4eightExpandedSourceRow68 T = 0 := by
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
  have hCmap : ratFuncAtHahn46 T.root C = rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F = rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E = rhoOneEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G = rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hrow := ratFunc_boundaryG_i4eight68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS0) hi4f
  rw [hCmap, hFmap, hGmap] at hrow
  exact hrow

end AlignedSquareBoundaryGSignedRayLinearDZeroI4EightSource68

end Max11DegreeRoutes
