import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalNegOneScratch

/-! # Exact `I3(6)` on the two signed-linear `K` cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroI3SixReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Sixth jet above the lower face of a Laurent triple product. -/
theorem laurent_coeff_mul_three_lower_six_boundary68
    (X Y Z : LaurentSeries k) (m n r : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
    (X * Y * Z).coeff (m + n + r + 6) =
      X.coeff m * Y.coeff n * Z.coeff (r + 6) +
      (X.coeff m * Y.coeff (n + 1) + X.coeff (m + 1) * Y.coeff n) *
        Z.coeff (r + 5) +
      (X.coeff m * Y.coeff (n + 2) +
        X.coeff (m + 1) * Y.coeff (n + 1) +
        X.coeff (m + 2) * Y.coeff n) * Z.coeff (r + 4) +
      (X.coeff m * Y.coeff (n + 3) +
        X.coeff (m + 1) * Y.coeff (n + 2) +
        X.coeff (m + 2) * Y.coeff (n + 1) +
        X.coeff (m + 3) * Y.coeff n) * Z.coeff (r + 3) +
      (X.coeff m * Y.coeff (n + 4) +
        X.coeff (m + 1) * Y.coeff (n + 3) +
        X.coeff (m + 2) * Y.coeff (n + 2) +
        X.coeff (m + 3) * Y.coeff (n + 1) +
        X.coeff (m + 4) * Y.coeff n) * Z.coeff (r + 2) +
      (X.coeff m * Y.coeff (n + 5) +
        X.coeff (m + 1) * Y.coeff (n + 4) +
        X.coeff (m + 2) * Y.coeff (n + 3) +
        X.coeff (m + 3) * Y.coeff (n + 2) +
        X.coeff (m + 4) * Y.coeff (n + 1) +
        X.coeff (m + 5) * Y.coeff n) * Z.coeff (r + 1) +
      (X.coeff m * Y.coeff (n + 6) +
        X.coeff (m + 1) * Y.coeff (n + 5) +
        X.coeff (m + 2) * Y.coeff (n + 4) +
        X.coeff (m + 3) * Y.coeff (n + 3) +
        X.coeff (m + 4) * Y.coeff (n + 2) +
        X.coeff (m + 5) * Y.coeff (n + 1) +
        X.coeff (m + 6) * Y.coeff n) * Z.coeff r := by
  have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have ho := laurent_coeff_mul_lower_six68 (X * Y) Z (m + n) r hXY hZ
  have h0 := laurent_coeff_mul_lower68 X Y m n hX hY
  have h1 := laurent_coeff_mul_lower_succ68 X Y m n hX hY
  have h2 := laurent_coeff_mul_lower_two68 X Y m n hX hY
  have h3 := laurent_coeff_mul_lower_three68 X Y m n hX hY
  have h4 := laurent_coeff_mul_lower_four68 X Y m n hX hY
  have h5 := laurent_coeff_mul_lower_five68 X Y m n hX hY
  have h6 := laurent_coeff_mul_lower_six68 X Y m n hX hY
  rw [h0, h1, h2, h3, h4, h5, h6] at ho
  convert ho using 1 <;> ring

omit [IsAlgClosed k] in
/-- Exact finite expansion of coefficient six of the constant `I3`. -/
def rhoOne_boundaryG_i3sixHahnRow68
    (gamma epsilon : k) (A B C F G : HahnSeries ℚ k) : k :=
  (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 6 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 5 +
        (A.coeff (-2) * B.coeff 4 + A.coeff (-1) * B.coeff 3 +
          A.coeff 0 * B.coeff 2) * F.coeff 4 +
        (A.coeff (-2) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
          A.coeff 0 * B.coeff 3 + A.coeff 1 * B.coeff 2) * F.coeff 3 +
        (A.coeff (-2) * B.coeff 6 + A.coeff (-1) * B.coeff 5 +
          A.coeff 0 * B.coeff 4 + A.coeff 1 * B.coeff 3 +
          A.coeff 2 * B.coeff 2) * F.coeff 2 +
        (A.coeff (-2) * B.coeff 7 + A.coeff (-1) * B.coeff 6 +
          A.coeff 0 * B.coeff 5 + A.coeff 1 * B.coeff 4 +
          A.coeff 2 * B.coeff 3 + A.coeff 3 * B.coeff 2) * F.coeff 1 +
        (A.coeff (-2) * B.coeff 8 + A.coeff (-1) * B.coeff 7 +
          A.coeff 0 * B.coeff 6 + A.coeff 1 * B.coeff 5 +
          A.coeff 2 * B.coeff 4 + A.coeff 3 * B.coeff 3 +
          A.coeff 4 * B.coeff 2) * F.coeff 0) -
    (8 / 9 : k) * (B.coeff 2 ^ 2 * C.coeff 2 +
      2 * B.coeff 2 * B.coeff 3 * C.coeff 1 +
      (2 * B.coeff 2 * B.coeff 4 + B.coeff 3 ^ 2) * C.coeff 0) +
    (8 / 3 : k) * (C.coeff 1 * G.coeff 5 + C.coeff 2 * G.coeff 4 +
      C.coeff 3 * G.coeff 3 + C.coeff 4 * G.coeff 2 +
      C.coeff 5 * G.coeff 1 + C.coeff 6 * G.coeff 0 +
      C.coeff 7 * G.coeff (-1) + C.coeff 8 * G.coeff (-2)) +
    (8 / 3 : k) * (F.coeff 0 * F.coeff 6 +
      F.coeff 1 * F.coeff 5 + F.coeff 2 * F.coeff 4) +
    (4 / 3 : k) * F.coeff 3 ^ 2 -
    (4 / 3 : k) * gamma * B.coeff 2 * B.coeff 4 -
    (2 / 3 : k) * gamma * B.coeff 3 ^ 2 + 2 * epsilon * C.coeff 6

omit [IsAlgClosed k] in
/-- Integer-index copy of the same scalar row, used only for the Laurent
coefficient calculation before transport to rational indices. -/
def rhoOne_boundaryG_i3sixLaurentRow68
    (gamma epsilon : k) (A B C F G : LaurentSeries k) : k :=
  (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 6 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 5 +
        (A.coeff (-2) * B.coeff 4 + A.coeff (-1) * B.coeff 3 +
          A.coeff 0 * B.coeff 2) * F.coeff 4 +
        (A.coeff (-2) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
          A.coeff 0 * B.coeff 3 + A.coeff 1 * B.coeff 2) * F.coeff 3 +
        (A.coeff (-2) * B.coeff 6 + A.coeff (-1) * B.coeff 5 +
          A.coeff 0 * B.coeff 4 + A.coeff 1 * B.coeff 3 +
          A.coeff 2 * B.coeff 2) * F.coeff 2 +
        (A.coeff (-2) * B.coeff 7 + A.coeff (-1) * B.coeff 6 +
          A.coeff 0 * B.coeff 5 + A.coeff 1 * B.coeff 4 +
          A.coeff 2 * B.coeff 3 + A.coeff 3 * B.coeff 2) * F.coeff 1 +
        (A.coeff (-2) * B.coeff 8 + A.coeff (-1) * B.coeff 7 +
          A.coeff 0 * B.coeff 6 + A.coeff 1 * B.coeff 5 +
          A.coeff 2 * B.coeff 4 + A.coeff 3 * B.coeff 3 +
          A.coeff 4 * B.coeff 2) * F.coeff 0) -
    (8 / 9 : k) * (B.coeff 2 ^ 2 * C.coeff 2 +
      2 * B.coeff 2 * B.coeff 3 * C.coeff 1 +
      (2 * B.coeff 2 * B.coeff 4 + B.coeff 3 ^ 2) * C.coeff 0) +
    (8 / 3 : k) * (C.coeff 1 * G.coeff 5 + C.coeff 2 * G.coeff 4 +
      C.coeff 3 * G.coeff 3 + C.coeff 4 * G.coeff 2 +
      C.coeff 5 * G.coeff 1 + C.coeff 6 * G.coeff 0 +
      C.coeff 7 * G.coeff (-1) + C.coeff 8 * G.coeff (-2)) +
    (8 / 3 : k) * (F.coeff 0 * F.coeff 6 +
      F.coeff 1 * F.coeff 5 + F.coeff 2 * F.coeff 4) +
    (4 / 3 : k) * F.coeff 3 ^ 2 -
    (4 / 3 : k) * gamma * B.coeff 2 * B.coeff 4 -
    (2 / 3 : k) * gamma * B.coeff 3 ^ 2 + 2 * epsilon * C.coeff 6

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3six_laurent68
    (gamma epsilon i3 : k) (A B C F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    rhoOne_boundaryG_i3sixLaurentRow68 gamma epsilon A B C F G = 0 := by
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
  have hABF := laurent_coeff_mul_three_lower_six_boundary68
    A B F (-2) 2 0 hA hB hF
  have hBBord : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (by convert add_le_add hB hB using 1 <;> norm_num)
      HahnSeries.orderTop_add_le_mul
  have hBB0 := laurent_coeff_mul_lower68 B B 2 2 hB hB
  have hBB1 := laurent_coeff_mul_lower_succ68 B B 2 2 hB hB
  have hBB2 := laurent_coeff_mul_lower_two68 B B 2 2 hB hB
  have hBBC := laurent_coeff_mul_lower_two68 (B ^ 2) C 4 0 hBBord hC
  have hSG := laurent_coeff_mul_lower_seven68 S G 1 (-2) hS hG
  have hFF := laurent_coeff_mul_lower_six68 F F 0 0 hF hF
  norm_num at hABF hBB0 hBB1 hBB2 hBBC hSG hFF
  have hBBpow0 : (B ^ 2).coeff 4 = B.coeff 2 * B.coeff 2 := by
    simpa only [pow_two] using hBB0
  have hBBpow1 : (B ^ 2).coeff 5 = B.coeff 2 * B.coeff 3 +
      B.coeff 3 * B.coeff 2 := by simpa only [pow_two] using hBB1
  have hBBpow2 : (B ^ 2).coeff 6 = B.coeff 2 * B.coeff 4 +
      B.coeff 3 * B.coeff 3 + B.coeff 4 * B.coeff 2 := by
    simpa only [pow_two] using hBB2
  rw [hBBpow0, hBBpow1, hBBpow2] at hBBC
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num), hSco 4 (by norm_num),
    hSco 5 (by norm_num), hSco 6 (by norm_num),
    hSco 7 (by norm_num), hSco 8 (by norm_num)] at hSG
  have hi3rhs : (HahnSeries.C i3 : LaurentSeries k).coeff 6 = 0 := by
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 6) hi3
  rw [hi3rewrite] at hc
  simp only [HahnSeries.coeff_add, hscale] at hc
  rw [hABF, hBBC, hSG, hFF, hBBpow2, hi3rhs] at hc
  dsimp only [rhoOne_boundaryG_i3sixLaurentRow68]
  linear_combination hc

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_i3six68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi3 : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    rhoOne_boundaryG_i3sixHahnRow68 gamma epsilon
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
    rw [← hcs C 0]
    exact hS0
  have hf := rhoOne_boundaryG_i3six_laurent68 gamma epsilon i3
    AL BL CL FL GLa hAL hBL hCL hFL hGL hS0L hi3L'
  have hf' := hf
  simp only [rhoOne_boundaryG_i3sixLaurentRow68, AL, BL, CL, FL, GLa,
    ← hcs A (-2), ← hcs A (-1), ← hcs A 0, ← hcs A 1,
    ← hcs A 2, ← hcs A 3, ← hcs A 4,
    ← hcs B 2, ← hcs B 3, ← hcs B 4, ← hcs B 5,
    ← hcs B 6, ← hcs B 7, ← hcs B 8,
    ← hcs C 0, ← hcs C 1, ← hcs C 2, ← hcs C 3,
    ← hcs C 4, ← hcs C 5, ← hcs C 6, ← hcs C 7, ← hcs C 8,
    ← hcs F 0, ← hcs F 1, ← hcs F 2, ← hcs F 3,
    ← hcs F 4, ← hcs F 5, ← hcs F 6,
    ← hcs G (-2), ← hcs G (-1), ← hcs G 0, ← hcs G 1,
    ← hcs G 2, ← hcs G 3, ← hcs G 4, ← hcs G 5] at hf'
  dsimp only [rhoOne_boundaryG_i3sixHahnRow68]
  norm_num at hf' ⊢
  linear_combination hf'

/-- Expanded `I3(6)` in the source chart. -/
def rhoOne_boundaryG_i3sixExpandedSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  rhoOne_boundaryG_i3sixHahnRow68 T.source.gamma T.source.epsilon A B C F G

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i3six_expanded_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i3sixExpandedSourceRow68 T = 0 := by
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
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hrow := ratFunc_boundaryG_i3six68 T.root T.source.gamma
    T.source.epsilon i3 A B C F G hAH hBH hCH hFH hGH
      (by rw [hCmap]; exact hS0) hi3f
  rw [hCmap, hFmap, hGmap] at hrow
  exact hrow

omit [IsAlgClosed k] in
/-- `I3(6)` after all signed-ray and `D=0` substitutions, with `B[6]`
left as the single affine parameter. -/
def rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68
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
  let b := B.coeff 2
  let f0z := r ^ 2 * b / 9
  let f1z := A.coeff (-1) * b / 3
  (-(8 / 9 : k)) *
      ((-(r ^ 2 / 3)) * b * F.coeff 6 + A.coeff (-1) * b * F.coeff 5 +
        ((-(r ^ 2 / 3)) * B.coeff 4 + A.coeff 0 * b) * F.coeff 4 +
        ((-(r ^ 2 / 3)) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
          A.coeff 1 * b) * F.coeff 3 +
        ((-(r ^ 2 / 3)) * b6 + A.coeff (-1) * B.coeff 5 +
          A.coeff 0 * B.coeff 4 + A.coeff 2 * b) * F.coeff 2 +
        ((-(r ^ 2 / 3)) * B.coeff 7 + A.coeff (-1) * b6 +
          A.coeff 0 * B.coeff 5 + A.coeff 1 * B.coeff 4 +
          A.coeff 3 * b) * f1z +
        ((-(r ^ 2 / 3)) * B.coeff 8 + A.coeff (-1) * B.coeff 7 +
          A.coeff 0 * b6 + A.coeff 1 * B.coeff 5 +
          A.coeff 2 * B.coeff 4 + A.coeff 4 * b) * f0z) -
    (8 / 9 : k) * (b ^ 2 * C.coeff 2 +
      2 * b * B.coeff 4 * C.coeff 0) +
    (8 / 3 : k) * ((-(sigma * r * b / 3)) * G.coeff 5 +
      C.coeff 2 * G.coeff 4 + C.coeff 3 * G.coeff 3 +
      C.coeff 4 * G.coeff 2 + C.coeff 5 * G.coeff 1 +
      C.coeff 6 * G.coeff 0 +
      C.coeff 7 * (sigma * r ^ 3 * b / 27) +
      C.coeff 8 * G.coeff (-2)) +
    (8 / 3 : k) * (f0z * F.coeff 6 + f1z * F.coeff 5 +
      F.coeff 2 * F.coeff 4) + (4 / 3 : k) * F.coeff 3 ^ 2 -
    (4 / 3 : k) * T.source.gamma * b * B.coeff 4 +
    2 * T.source.epsilon * C.coeff 6

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i3six_reduce68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0)
    (hr : r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2))
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
        (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0) :
    rhoOne_boundaryG_i3sixExpandedSourceRow68 T =
      rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r
        ((ratFuncAtHahn46 T.root T.source.B).coeff 6) := by
  have ha : (ratFuncAtHahn46 T.root T.source.A).coeff (-2) =
      -(r ^ 2 / 3) := by linear_combination (1 / 3 : k) * hr
  have hc1 : (rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 =
      -(sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  have hgm1 : (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27 := by
    linear_combination (1 / 27 : k) * hray
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
  dsimp only [rhoOne_boundaryG_i3sixExpandedSourceRow68,
    rhoOne_boundaryG_i3sixHahnRow68,
    rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68]
  rw [ha, hb3, hc1, hgm1, hf0, hf1]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i3six_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let L := -3 * r ^ 2 * F.coeff 2 +
      3 * A.coeff (-1) ^ 2 * B.coeff 2 +
      A.coeff 0 * r ^ 2 * B.coeff 2
    rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r b6 =
      rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0 -
        (8 / 81 : k) * L * b6 := by
  dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i3six_i4five_cross68
    (sigma r b L J0 I4b b6 : k)
    (h3 : J0 - (8 / 81 : k) * L * b6 = 0)
    (h4 : I4b + (sigma * r ^ 3 * b / 27) * b6 = 0) :
    3 * sigma * r ^ 3 * b * J0 + 8 * L * I4b = 0 := by
  linear_combination 81 *
    ((sigma * r ^ 3 * b / 27) * h3 + (8 / 81 : k) * L * h4)

/-- The exact two-cell `I3(6)` reduction. -/
def rhoOne_boundaryG_signedRayLinearDZeroI3SixCells68
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
  D0 = 0 →
    ((K = 0 ∧ C.coeff 2 ≠ 0 ∧ I0 = 0 ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r
          (B.coeff 6) = 0 ∧
        3 * sigma * r ^ 3 * B.coeff 2 * J0 + 8 * L * I4b = 0) ∨
      (K ≠ 0 ∧ (T0 = 0 ↔ I0 = 0) ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r
          (B.coeff 6) = 0 ∧
        3 * sigma * r ^ 3 * B.coeff 2 * J0 + 8 * L * I4b = 0))

/-- Source-facing successor carrying the exact `I3(6)` cross. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3SixReduction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68 T ∧
  rhoOne_boundaryG_i3sixExpandedSourceRow68 T = 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroI3SixCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i3six_reduction68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3SixReduction68 T := by
  have hrow := T.rhoOne_boundaryG_i3six_expanded_source68 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68] at Rc
  rcases Rc with ⟨Rfour, hlead, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have Rfourc := Rfour
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4FiveCross68] at Rfourc
  rcases Rfourc with ⟨Rkeep, hi4five, sigma', r', hsigma', hr0', hb', hgm2',
    hr', hray', hrf', hlinear', hb3', hwitness', hcross4⟩
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI3SixCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3SixCells68]
    intro hD
    have hredEq := rhoOne_boundaryG_signedRayLinear_dZero_i3six_reduce68
      T sigma r hsigma hr0 hr hray hrf hlinear hb3 hD
    have h3actual :
        rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r
          ((ratFuncAtHahn46 T.root T.source.B).coeff 6) = 0 := by
      rw [← hredEq]
      exact hrow
    have haff := rhoOne_boundaryG_signedRayLinear_dZero_i3six_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    dsimp only at haff
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
      rw [← haff]
      exact h3actual
    have h4old := hcellsOld hD
    have hi4 : rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r +
        (sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27) *
          (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rcases h4old with hz | hn
      · exact hz.2.2.2.2.1
      · exact hn.2.2.2.1
    have hnew := rhoOne_boundaryG_signedRayLinear_dZero_i3six_i4five_cross68
      sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
      (-3 * r ^ 2 * (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 2 +
       3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-1) ^ 2 *
         (ratFuncAtHahn46 T.root T.source.B).coeff 2 +
       (ratFuncAtHahn46 T.root T.source.A).coeff 0 * r ^ 2 *
         (ratFuncAtHahn46 T.root T.source.B).coeff 2)
      (rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0)
      (rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 6) h3base hi4
    have hw := hwitness
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68] at hw
    rcases hw with hzero | hnon
    · rcases hzero.2 with hk | hnk
      · exact Or.inl ⟨hk.1, hk.2.1, hk.2.2, hlead, h3actual, hnew⟩
      · exact Or.inr ⟨hnk.1, hnk.2, hlead, h3actual, hnew⟩
    · exact (hnon.1 hD).elim
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3SixReduction68]
  exact ⟨R, hrow, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcells⟩

/-- Outer selector preserving coordinate, QR, and nonsingular siblings. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i3six_reduction_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3SixReduction68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negOne_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hzero | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_i3six_reduction68
          hsigned.1 hzero)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroI3SixReduction68

end Max11DegreeRoutes
