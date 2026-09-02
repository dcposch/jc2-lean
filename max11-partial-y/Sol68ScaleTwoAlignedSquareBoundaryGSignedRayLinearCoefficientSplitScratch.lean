import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearI3ThreeReductionScratch

/-! # Coefficient split and `I4(4)` on the signed linear factor -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearCoefficientSplit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Exact split forced by the compact `F[2]` resultant. -/
theorem rhoOne_boundaryG_signedRayLinear_coefficient_split68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 c4 c5
      f1 f2 f3 g2 g1 g0 gm2 epsilon : k)
    (hred : rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
      a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon = 0)
    (helim : rhoOne_boundaryG_signedRayLinearI3ThreeTerminalElim68 sigma r
      a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f3 g2 g1 g0 gm2 epsilon = 0) :
    ((3 * f1 - a1 * b = 0 ∧
        rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
          a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f3 g2 g1 g0 gm2 epsilon = 0) ∨
      (3 * f1 - a1 * b ≠ 0 ∧
        4 * (3 * f1 - a1 * b) *
            rhoOne_boundaryG_signedRayLinearTerminalBase68
              sigma r a1 a0 b b4 c2 gm2 =
          -243 * gm2 ^ 2 *
            rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
              a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f3
              g2 g1 g0 gm2 epsilon)) := by
  by_cases hD : 3 * f1 - a1 * b = 0
  · left
    refine ⟨hD, ?_⟩
    dsimp only [rhoOne_boundaryG_signedRayLinearI3ThreeReduced68,
      rhoOne_boundaryG_signedRayLinearI3ThreeBase68] at hred ⊢
    linear_combination hred - 108 * f2 * hD
  · right
    refine ⟨hD, ?_⟩
    dsimp only [rhoOne_boundaryG_signedRayLinearI3ThreeTerminalElim68] at helim
    linear_combination -helim

omit [IsAlgClosed k] in
/-- Coefficient four of the constant `I4` factor at orders
`B≥2,C≥0,F≥0,G≥-2`. -/
theorem rhoOne_boundaryG_i4four_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    B.coeff 2 * G.coeff 2 + B.coeff 3 * G.coeff 1 +
      B.coeff 4 * G.coeff 0 + B.coeff 5 * G.coeff (-1) +
      B.coeff 6 * G.coeff (-2) + C.coeff 1 * F.coeff 3 +
      C.coeff 2 * F.coeff 2 + C.coeff 3 * F.coeff 1 +
      C.coeff 4 * F.coeff 0 + (3 / 4 : k) * epsilon * B.coeff 4 = 0 := by
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
  have hBG := laurent_coeff_mul_lower_four68 B G 2 (-2) hB hG
  have hSF := laurent_coeff_mul_lower_three68 S F 1 0 hS hF
  norm_num at hBG hSF
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num), hSco 4 (by norm_num)] at hSF
  have hB3ord : (↑(6 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
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
theorem ratFunc_boundaryG_i4four68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    (ratFuncAtHahn46 root B).coeff 2 * (ratFuncAtHahn46 root G).coeff 2 +
      (ratFuncAtHahn46 root B).coeff 3 * (ratFuncAtHahn46 root G).coeff 1 +
      (ratFuncAtHahn46 root B).coeff 4 * (ratFuncAtHahn46 root G).coeff 0 +
      (ratFuncAtHahn46 root B).coeff 5 * (ratFuncAtHahn46 root G).coeff (-1) +
      (ratFuncAtHahn46 root B).coeff 6 * (ratFuncAtHahn46 root G).coeff (-2) +
      (ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root F).coeff 3 +
      (ratFuncAtHahn46 root C).coeff 2 * (ratFuncAtHahn46 root F).coeff 2 +
      (ratFuncAtHahn46 root C).coeff 3 * (ratFuncAtHahn46 root F).coeff 1 +
      (ratFuncAtHahn46 root C).coeff 4 * (ratFuncAtHahn46 root F).coeff 0 +
      (3 / 4 : k) * epsilon * (ratFuncAtHahn46 root B).coeff 4 = 0 := by
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
    rw [← hcs C 0]; exact hS0
  have hf := rhoOne_boundaryG_i4four_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hS0L hi4L'
  have hf' := hf
  simp only [BL, CL, FL, GLa, ← hcs B 2, ← hcs B 3, ← hcs B 4,
    ← hcs B 5, ← hcs B 6, ← hcs C 1, ← hcs C 2,
    ← hcs C 3, ← hcs C 4, ← hcs F 0, ← hcs F 1,
    ← hcs F 2, ← hcs F 3, ← hcs G (-2), ← hcs G (-1),
    ← hcs G 0, ← hcs G 1, ← hcs G 2] at hf'
  convert hf' using 1 <;> norm_num

omit [IsAlgClosed k] in
/-- Signed reduction of the new `I4(4)` row. -/
def rhoOne_boundaryG_signedRayLinearI4FourBase68
    (sigma r b b4 b5 b6 c2 c3 c4 f1 f2 g0 gm2 epsilon : k) : k :=
  b4 * g0 + b5 * (sigma * r ^ 3 * b / 27) + b6 * gm2 +
    c2 * f2 + c3 * f1 + c4 * (r ^ 2 * b / 9) +
    (3 / 4 : k) * epsilon * b4

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_i4four_reduce68
    (sigma r b b3 b4 b5 b6 c1 c2 c3 c4
      f0 f1 f2 f3 gm1 g0 g1 g2 gm2 epsilon : k)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (hf0 : f0 = r ^ 2 * b / 9)
    (hlinear : 3 * c1 + sigma * r * b = 0)
    (hb3 : b3 = 0)
    (hi4 : b * g2 + b3 * g1 + b4 * g0 + b5 * gm1 + b6 * gm2 +
      c1 * f3 + c2 * f2 + c3 * f1 + c4 * f0 +
      (3 / 4 : k) * epsilon * b4 = 0) :
    b * g2 - (sigma * r * b / 3) * f3 +
      rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r b b4 b5 b6
        c2 c3 c4 f1 f2 g0 gm2 epsilon = 0 := by
  have hgm1 : gm1 = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hc1 : c1 = -(sigma * r * b / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  rw [hb3, hgm1, hc1, hf0] at hi4
  dsimp only [rhoOne_boundaryG_signedRayLinearI4FourBase68]
  linear_combination hi4

omit [IsAlgClosed k] in
/-- The two independent I3/I4 transports for `F[3]` and `G[2]`. -/
theorem rhoOne_boundaryG_signedRayLinear_i3_i4four_transports68
    (sigma r a1 a0 aOne b b4 b5 b6 c2 c3 c4 c5
      f1 f2 f3 g2 g1 g0 gm2 epsilon : k)
    (hsigma : sigma ^ 2 = 1)
    (hi3 : rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
      a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon = 0)
    (hi4 : b * g2 - (sigma * r * b / 3) * f3 +
      rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r b b4 b5 b6
        c2 c3 c4 f1 f2 g0 gm2 epsilon = 0) :
    (36 * b * r ^ 2 * f3 +
        (rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
          a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon -
          72 * b * f3 * r ^ 2 + 108 * b * g2 * r * sigma) +
        108 * r * sigma *
          rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r b b4 b5 b6
            c2 c3 c4 f1 f2 g0 gm2 epsilon = 0) ∧
      (108 * b * r * sigma * g2 +
        (rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
          a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon -
          72 * b * f3 * r ^ 2 + 108 * b * g2 * r * sigma) +
        216 * r * sigma *
          rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r b b4 b5 b6
            c2 c3 c4 f1 f2 g0 gm2 epsilon = 0) := by
  constructor <;>
    dsimp only [rhoOne_boundaryG_signedRayLinearI3ThreeReduced68,
      rhoOne_boundaryG_signedRayLinearI4FourBase68] at *
  · linear_combination hi3 + 108 * r * sigma * hi4 +
      36 * b * r ^ 2 * f3 * hsigma
  · linear_combination hi3 + 216 * r * sigma * hi4 +
      72 * b * r ^ 2 * f3 * hsigma

/-- Source-coordinate form of `I4(4)`. -/
def rhoOne_boundaryG_i4fourSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  B.coeff 2 * G.coeff 2 + B.coeff 3 * G.coeff 1 +
    B.coeff 4 * G.coeff 0 + B.coeff 5 * G.coeff (-1) +
    B.coeff 6 * G.coeff (-2) + C.coeff 1 * F.coeff 3 +
    C.coeff 2 * F.coeff 2 + C.coeff 3 * F.coeff 1 +
    C.coeff 4 * F.coeff 0 + (3 / 4 : k) * T.source.epsilon * B.coeff 4

/-- Exact source backwire for the general boundary `I4(4)` row. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i4four_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i4fourSourceRow68 T = 0 := by
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
  have hrow := ratFunc_boundaryG_i4four68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS0) hi4f
  rw [hCmap, hFmap, hGmap] at hrow
  exact hrow

/-- The coefficient split, its source-backed `I4(4)` row, and the two
independent top-coordinate transports. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearCoefficientSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68 T ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    (((3 * F.coeff 1 - A.coeff (-1) * B.coeff 2 = 0) ∧
        rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
          (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
          (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
          (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 3)
          (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
          T.source.epsilon = 0) ∨
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
              T.source.epsilon)) ∧
    rhoOne_boundaryG_i4fourSourceRow68 T = 0 ∧
    let I4b := rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r
      (B.coeff 2) (B.coeff 4) (B.coeff 5) (B.coeff 6)
      (C.coeff 2) (C.coeff 3) (C.coeff 4) (F.coeff 1) (F.coeff 2)
      (G.coeff 0) (G.coeff (-2)) T.source.epsilon
    let I3r := rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
      (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
      (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
      (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 2)
      (F.coeff 3) (G.coeff 2) (G.coeff 1) (G.coeff 0)
      (G.coeff (-2)) T.source.epsilon
    B.coeff 2 * G.coeff 2 - (sigma * r * B.coeff 2 / 3) * F.coeff 3 +
        I4b = 0 ∧
      36 * B.coeff 2 * r ^ 2 * F.coeff 3 +
        (I3r - 72 * B.coeff 2 * F.coeff 3 * r ^ 2 +
          108 * B.coeff 2 * G.coeff 2 * r * sigma) +
        108 * r * sigma * I4b = 0 ∧
      108 * B.coeff 2 * r * sigma * G.coeff 2 +
        (I3r - 72 * B.coeff 2 * F.coeff 3 * r ^ 2 +
          108 * B.coeff 2 * G.coeff 2 * r * sigma) +
        216 * r * sigma * I4b = 0

/-- Assemble the split and the first independent `I4(4)` transports on
the same signed witness. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_coefficientSplit68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearCoefficientSplit68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68] at Rc
  rcases Rc with ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf,
    hlinear, hb3, hterminal, hi3source, hred, helim⟩
  have hsplit := rhoOne_boundaryG_signedRayLinear_coefficient_split68 sigma r
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
      (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
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
    T.source.epsilon hred helim
  have hi4source := T.rhoOne_boundaryG_i4four_source68 Q
  have hi4c := hi4source
  dsimp only [rhoOne_boundaryG_i4fourSourceRow68] at hi4c
  have hgmEq :
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
    rw [hrf, hgmEq]
    linear_combination
      (r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) * hsigma
  have hi4red := rhoOne_boundaryG_signedRayLinear_i4four_reduce68 sigma r
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 3)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 4)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 1)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
    T.source.epsilon hray hf0 hlinear hb3 hi4c
  have htransport := rhoOne_boundaryG_signedRayLinear_i3_i4four_transports68
    sigma r
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
    ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
    ((ratFuncAtHahn46 T.root T.source.A).coeff 1)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
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
      (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
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
    T.source.epsilon hsigma hred hi4red
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearCoefficientSplit68]
  exact ⟨R, sigma, r, hsigma, hr0, hb, hr, hray, hrf, hlinear, hb3,
    hsplit, hi4source, hi4red, htransport.1, htransport.2⟩

/-- Full selector with every alternative sibling carried verbatim. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_coefficientSplit_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearCoefficientSplit68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_i3three_reduction_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hlinear | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_coefficientSplit68
          hsigned.1 hlinear)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearCoefficientSplit68

end Max11DegreeRoutes
