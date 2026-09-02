import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDeterminantSolveScratch

/-! # Exact `I3(4)` on the zero determinant-coefficient cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroI3Four68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The fourth jet above the lower face of a Laurent triple product. -/
theorem laurent_coeff_mul_three_lower_four_boundary68
    (X Y Z : LaurentSeries k) (m n r : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
    (X * Y * Z).coeff (m + n + r + 4) =
      X.coeff m * Y.coeff n * Z.coeff (r + 4) +
      (X.coeff m * Y.coeff (n + 1) + X.coeff (m + 1) * Y.coeff n) *
        Z.coeff (r + 3) +
      (X.coeff m * Y.coeff (n + 2) +
        X.coeff (m + 1) * Y.coeff (n + 1) +
        X.coeff (m + 2) * Y.coeff n) * Z.coeff (r + 2) +
      (X.coeff m * Y.coeff (n + 3) +
        X.coeff (m + 1) * Y.coeff (n + 2) +
        X.coeff (m + 2) * Y.coeff (n + 1) +
        X.coeff (m + 3) * Y.coeff n) * Z.coeff (r + 1) +
      (X.coeff m * Y.coeff (n + 4) +
        X.coeff (m + 1) * Y.coeff (n + 3) +
        X.coeff (m + 2) * Y.coeff (n + 2) +
        X.coeff (m + 3) * Y.coeff (n + 1) +
        X.coeff (m + 4) * Y.coeff n) * Z.coeff r := by
  have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have ho := laurent_coeff_mul_lower_four68 (X * Y) Z (m + n) r hXY hZ
  have h0 := laurent_coeff_mul_lower68 X Y m n hX hY
  have h1 := laurent_coeff_mul_lower_succ68 X Y m n hX hY
  have h2 := laurent_coeff_mul_lower_two68 X Y m n hX hY
  have h3 := laurent_coeff_mul_lower_three68 X Y m n hX hY
  have h4 := laurent_coeff_mul_lower_four68 X Y m n hX hY
  rw [h0, h1, h2, h3, h4] at ho
  convert ho using 1 <;> ring

omit [IsAlgClosed k] in
/-- Exact coefficient four of the constant `I3` factor.  It is genuinely
new: besides the solved `F[2],F[3],G[2]`, it first sees
`B[6],C[6],F[4],G[3]`. -/
theorem rhoOne_boundaryG_i3four_laurent68
    (gamma epsilon i3 : k) (A B C F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    (-(8 / 9 : k)) *
        (A.coeff (-2) * B.coeff 2 * F.coeff 4 +
          (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 3 +
          (A.coeff (-2) * B.coeff 4 + A.coeff (-1) * B.coeff 3 +
            A.coeff 0 * B.coeff 2) * F.coeff 2 +
          (A.coeff (-2) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
            A.coeff 0 * B.coeff 3 + A.coeff 1 * B.coeff 2) * F.coeff 1 +
          (A.coeff (-2) * B.coeff 6 + A.coeff (-1) * B.coeff 5 +
            A.coeff 0 * B.coeff 4 + A.coeff 1 * B.coeff 3 +
            A.coeff 2 * B.coeff 2) * F.coeff 0) -
      (8 / 9 : k) * B.coeff 2 ^ 2 * C.coeff 0 +
      (8 / 3 : k) *
        (C.coeff 1 * G.coeff 3 + C.coeff 2 * G.coeff 2 +
          C.coeff 3 * G.coeff 1 + C.coeff 4 * G.coeff 0 +
          C.coeff 5 * G.coeff (-1) + C.coeff 6 * G.coeff (-2)) +
      (4 / 3 : k) *
        (2 * F.coeff 0 * F.coeff 4 + 2 * F.coeff 1 * F.coeff 3 +
          F.coeff 2 ^ 2) -
      (2 / 3 : k) * gamma * B.coeff 2 ^ 2 +
      2 * epsilon * C.coeff 4 = 0 := by
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
  have hABF := laurent_coeff_mul_three_lower_four_boundary68
    A B F (-2) 2 0 hA hB hF
  have hBBord : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (by convert add_le_add hB hB using 1 <;> norm_num)
      HahnSeries.orderTop_add_le_mul
  have hBB := laurent_coeff_mul_lower68 B B 2 2 hB hB
  have hBBC := laurent_coeff_mul_lower68 (B ^ 2) C 4 0 hBBord hC
  have hSG := laurent_coeff_mul_lower_five68 S G 1 (-2) hS hG
  have hFF := laurent_coeff_mul_lower_four68 F F 0 0 hF hF
  norm_num at hABF hBB hBBC hSG hFF
  have hBBpow : (B ^ 2).coeff 4 = B.coeff 2 * B.coeff 2 := by
    simpa only [pow_two] using hBB
  rw [hBBpow] at hBBC
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num), hSco 4 (by norm_num),
    hSco 5 (by norm_num), hSco 6 (by norm_num)] at hSG
  have hi3rhs : (HahnSeries.C i3 : LaurentSeries k).coeff 4 = 0 := by
    simp [HahnSeries.C_apply]
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hi3rewrite : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G =
      HahnSeries.C (-(8 / 9 : k)) * (A * B * F) +
        HahnSeries.C (-(8 / 9 : k)) * (B ^ 2 * C) +
        HahnSeries.C (4 / 3 : k) * (S * G) +
        HahnSeries.C (4 / 3 : k) * (F * F) +
        HahnSeries.C (-(2 / 3 : k) * gamma) * (B ^ 2) +
        HahnSeries.C (2 * epsilon) * C := by
    simp only [rhoOneI3CapFactored68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 4) hi3
  rw [hi3rewrite] at hc
  simp only [HahnSeries.coeff_add, hscale] at hc
  rw [hABF, hBBC, hSG, hFF, hBBpow, hi3rhs] at hc
  linear_combination hc

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i3fourHahnRow68
    (gamma epsilon : k) (A B C F G : HahnSeries ℚ k) : k :=
  (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 4 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 3 +
        (A.coeff (-2) * B.coeff 4 + A.coeff (-1) * B.coeff 3 +
          A.coeff 0 * B.coeff 2) * F.coeff 2 +
        (A.coeff (-2) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
          A.coeff 0 * B.coeff 3 + A.coeff 1 * B.coeff 2) * F.coeff 1 +
        (A.coeff (-2) * B.coeff 6 + A.coeff (-1) * B.coeff 5 +
          A.coeff 0 * B.coeff 4 + A.coeff 1 * B.coeff 3 +
          A.coeff 2 * B.coeff 2) * F.coeff 0) -
    (8 / 9 : k) * B.coeff 2 ^ 2 * C.coeff 0 +
    (8 / 3 : k) *
      (C.coeff 1 * G.coeff 3 + C.coeff 2 * G.coeff 2 +
        C.coeff 3 * G.coeff 1 + C.coeff 4 * G.coeff 0 +
        C.coeff 5 * G.coeff (-1) + C.coeff 6 * G.coeff (-2)) +
    (4 / 3 : k) *
      (2 * F.coeff 0 * F.coeff 4 + 2 * F.coeff 1 * F.coeff 3 +
        F.coeff 2 ^ 2) -
    (2 / 3 : k) * gamma * B.coeff 2 ^ 2 + 2 * epsilon * C.coeff 4

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_i3four68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi3 : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    rhoOne_boundaryG_i3fourHahnRow68 gamma epsilon
      (ratFuncAtHahn46 root A) (ratFuncAtHahn46 root B)
      (ratFuncAtHahn46 root C) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) = 0 := by
  let AL := ratFuncAtLaurent46 root A
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 2 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-2) hG
  have hi3L := congrArg (ratFuncAtLaurent46 root) hi3
  have hi3L' : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) AL BL CL FL GLa = HahnSeries.C i3 := by
    simpa only [AL, BL, CL, FL, GLa, rhoOneI3CapFactored68,
      map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi3L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by
    rw [← hcs C 0]; exact hS0
  have hf := rhoOne_boundaryG_i3four_laurent68 gamma epsilon i3
    AL BL CL FL GLa hAL hBL hCL hFL hGL hS0L hi3L'
  have hf' := hf
  simp only [rhoOne_boundaryG_i3fourHahnRow68, AL, BL, CL, FL, GLa,
    ← hcs A (-2), ← hcs A (-1), ← hcs A 0, ← hcs A 1,
    ← hcs A 2, ← hcs B 2, ← hcs B 3, ← hcs B 4, ← hcs B 5,
    ← hcs B 6, ← hcs C 0, ← hcs C 1, ← hcs C 2, ← hcs C 3,
    ← hcs C 4, ← hcs C 5, ← hcs C 6, ← hcs F 0, ← hcs F 1,
    ← hcs F 2, ← hcs F 3, ← hcs F 4, ← hcs G (-2),
    ← hcs G (-1), ← hcs G 0, ← hcs G 1, ← hcs G 2, ← hcs G 3] at hf'
  dsimp only [rhoOne_boundaryG_i3fourHahnRow68]
  norm_num at hf' ⊢
  linear_combination hf'

def rhoOne_boundaryG_i3fourSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  rhoOne_boundaryG_i3fourHahnRow68 T.source.gamma T.source.epsilon A B C F G

/-- Source backwire for the first genuinely unused row after the determinant
solve. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i3four_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i3fourSourceRow68 T = 0 := by
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
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
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
  have hrow := ratFunc_boundaryG_i3four68 T.root T.source.gamma
    T.source.epsilon i3 A B C F G hAH hBH hCH hFH hGH
      (by rw [hCmap]; exact hS0) hi3f
  rw [hCmap, hFmap, hGmap] at hrow
  exact hrow

/-- `I3(4)` after substituting every value already solved on the `D=0`
cell.  The remaining new coordinates are exactly
`B[6],C[6],F[4],G[3]` (and the corresponding `A[2]` source jet). -/
def rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let b := B.coeff 2
  let f1z := A.coeff (-1) * b / 3
  let f2z := rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
    (A.coeff (-1)) (A.coeff 0) b (B.coeff 4) (C.coeff 2)
    (G.coeff (-2)) / (6561 * G.coeff (-2) ^ 2)
  let R0 := rhoOne_boundaryG_signedRayLinearI3ThreeRest68 sigma r
    (A.coeff (-1)) (A.coeff 0) (A.coeff 1) b (B.coeff 4)
    (B.coeff 5) (C.coeff 2) (C.coeff 3) (C.coeff 4) (C.coeff 5)
    f1z f2z (G.coeff 1) (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let S0 := rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r b
    (B.coeff 4) (B.coeff 5) (B.coeff 6) (C.coeff 2) (C.coeff 3)
    (C.coeff 4) f1z f2z (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let f3z := -(R0 + 108 * r * sigma * S0) / (36 * b * r ^ 2)
  let g2z := -(R0 + 216 * r * sigma * S0) / (108 * b * r * sigma)
  (-(8 / 9 : k)) *
      ((-(r ^ 2 / 3)) * b * F.coeff 4 + A.coeff (-1) * b * f3z +
        ((-(r ^ 2 / 3)) * B.coeff 4 + A.coeff 0 * b) * f2z +
        ((-(r ^ 2 / 3)) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
          A.coeff 1 * b) * f1z +
        ((-(r ^ 2 / 3)) * B.coeff 6 + A.coeff (-1) * B.coeff 5 +
          A.coeff 0 * B.coeff 4 + A.coeff 2 * b) * (r ^ 2 * b / 9)) -
    (8 / 9 : k) * b ^ 2 * C.coeff 0 +
    (8 / 3 : k) *
      ((-(sigma * r * b / 3)) * G.coeff 3 + C.coeff 2 * g2z +
        C.coeff 3 * G.coeff 1 + C.coeff 4 * G.coeff 0 +
        C.coeff 5 * (sigma * r ^ 3 * b / 27) + C.coeff 6 * G.coeff (-2)) +
    (4 / 3 : k) *
      (2 * (r ^ 2 * b / 9) * F.coeff 4 + 2 * f1z * f3z + f2z ^ 2) -
    (2 / 3 : k) * T.source.gamma * b ^ 2 + 2 * T.source.epsilon * C.coeff 4

/-- Source-facing D-zero refinement by the first unused I3 coefficient. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68 T ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    (((3 * F.coeff 1 - A.coeff (-1) * B.coeff 2 = 0) ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68 T sigma r = 0) ∨
      ((3 * F.coeff 1 - A.coeff (-1) * B.coeff 2 ≠ 0) ∧
        4 * (3 * F.coeff 1 - A.coeff (-1) * B.coeff 2) *
            rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
              (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
              (C.coeff 2) (G.coeff (-2)) =
          -243 * G.coeff (-2) ^ 2 *
            rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
              (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
              (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
              (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 3)
              (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
              T.source.epsilon))

/-- Substitute the already solved values into `I3(4)` on the zero cell;
the nonzero cell is carried literally. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i3four68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3Four68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68] at Rc
  rcases Rc with ⟨Rprev, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hF3, hG2, hsplit⟩
  have hrow := T.rhoOne_boundaryG_i3four_source68 Q
  have hrowc := hrow
  dsimp only [rhoOne_boundaryG_i3fourSourceRow68,
    rhoOne_boundaryG_i3fourHahnRow68] at hrowc
  have ha : (ratFuncAtHahn46 T.root T.source.A).coeff (-2) =
      -(r ^ 2 / 3) := by
    linear_combination (1 / 3 : k) * hr
  have hgm1 :
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hf0 :
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      r ^ 2 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9 := by
    apply (mul_left_cancel₀ hr0)
    rw [hrf, hgm1]
    linear_combination
      (r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) * hsigma
  have hc1 :
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 =
      -(sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  have hfinal :
      ((3 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0) ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68 T sigma r = 0) ∨
      (3 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 ≠ 0 ∧
        4 * (3 * (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
            (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
              (ratFuncAtHahn46 T.root T.source.B).coeff 2) *
          rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
            ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
            ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
            ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) =
        -243 * (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 *
          rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
            ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
            ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
            ((ratFuncAtHahn46 T.root T.source.A).coeff 1)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 4)
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 5)
            ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
            ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
            ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
            ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 1)
            ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
            ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
            T.source.epsilon) := by
    rcases hsplit with hzero | hnon
    · left
      refine ⟨hzero.1, ?_⟩
      have hf1 : (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 =
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3 := by
        linear_combination (1 / 3 : k) * hzero.1
      have hf2 := hzero.2.2
      have hf3 := hF3
      have hg2 := hG2
      rw [hf1, hf2] at hf3 hg2
      rw [ha, hb3, hc1, hf0, hgm1, hf1, hf2, hf3, hg2] at hrowc
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68]
      linear_combination hrowc
    · exact Or.inr hnon
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3Four68]
  exact ⟨R, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hfinal⟩

/-- Outer selector with only the determinant-solved linear child refined. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i3four_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3Four68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_determinantSolved_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hlinear | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_i3four68
          hsigned.1 hlinear)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroI3Four68

end Max11DegreeRoutes
