import Sol68ScaleTwoAlignedSquareBoundarySelectorsTerminalScratch

/-! # Next exact reductions on the two aligned-square boundary limbs -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundarySelectorsTerminalNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundarySelectorsTerminalNextLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
/-- The old `I4(0)` witness becomes completely scalar after the new
terminal relation on the `F[-1]` limb. -/
theorem rhoOne_boundaryF_i4_terminal_cross68
    (a b fm gm c1 i4 : k)
    (hi4 : i4 = (8 / 3 : k) * (b * gm + c1 * fm))
    (hrel : 3 * fm = 2 * a * b)
    (hterminal : 2 * a * c1 + 9 * gm = 0) :
    27 * i4 = 32 * a * b * c1 ∧
      3 * i4 + 16 * b * gm = 0 ∧
      9 * i4 - 16 * fm * c1 = 0 := by
  constructor
  · linear_combination 27 * hi4 + 24 * c1 * hrel + 8 * b * hterminal
  constructor
  · linear_combination
      3 * hi4 + (8 / 3 : k) * c1 * hrel + (8 / 3 : k) * b * hterminal
  · linear_combination
      9 * hi4 + (8 / 3 : k) * c1 * hrel + (8 / 3 : k) * b * hterminal

omit [IsAlgClosed k] in
/-- Exact coefficient two of the arbitrary-ground zero-`I4` factor on
the `G[-2]` limb. -/
theorem rhoOne_boundaryG_i4two_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    B.coeff 2 * G.coeff 0 + B.coeff 3 * G.coeff (-1) +
      B.coeff 4 * G.coeff (-2) + C.coeff 1 * F.coeff 1 +
      C.coeff 2 * F.coeff 0 + (3 / 4 : k) * epsilon * B.coeff 2 = 0 := by
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
  have hBG := laurent_coeff_mul_lower_two68 B G 2 (-2) hB hG
  have hSF := laurent_coeff_mul_lower_succ68 S F 1 0 hS hF
  norm_num at hBG hSF
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num)] at hSF
  have hBB : (↑(4 : ℤ) : WithTop ℤ) ≤ (B * B).orderTop := by
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hB hB
    norm_num at ht ⊢
    exact ht
  have hB3ord : (↑(6 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [pow_succ, pow_two]
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hBB hB
    norm_num at ht ⊢
    exact ht
  have hB3z : (B ^ 3).coeff 2 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB3ord)
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 2 = 0 := by
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
  have hi4c := congrArg (fun X : LaurentSeries k => X.coeff 2) hi4
  rw [hi4rewrite] at hi4c
  simp only [HahnSeries.coeff_add, hscale] at hi4c
  rw [hB3z, hBG, hSF, hi4rhs] at hi4c
  linear_combination (3 / 8 : k) * hi4c

omit [IsAlgClosed k] in
/-- Rational transport of the `I4(2)` face. -/
theorem ratFunc_boundaryG_i4two68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    (ratFuncAtHahn46 root B).coeff 2 * (ratFuncAtHahn46 root G).coeff 0 +
      (ratFuncAtHahn46 root B).coeff 3 * (ratFuncAtHahn46 root G).coeff (-1) +
      (ratFuncAtHahn46 root B).coeff 4 * (ratFuncAtHahn46 root G).coeff (-2) +
      (ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root F).coeff 1 +
      (ratFuncAtHahn46 root C).coeff 2 * (ratFuncAtHahn46 root F).coeff 0 +
      (3 / 4 : k) * epsilon * (ratFuncAtHahn46 root B).coeff 2 = 0 := by
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
  have hf := rhoOne_boundaryG_i4two_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hS0L hi4L'
  have hf' := hf
  simp only [BL, CL, FL, GLa, ← hcs B 2, ← hcs B 3, ← hcs B 4,
    ← hcs C 1, ← hcs C 2, ← hcs F 0, ← hcs F 1,
    ← hcs G (-2), ← hcs G (-1), ← hcs G 0] at hf'
  convert hf' using 1 <;> norm_num

omit [IsAlgClosed k] in
/-- Cross-elimination of the new `I4(2)` face with the preceding scalar
packet removes `G[0]`, `F[1]`, `F[0]`, and `B[3]G[-1]`. -/
theorem rhoOne_boundaryG_i4two_cross68
    (a a1 b b3 b4 f f1 g gm gp c1 c2 c3 epsilon : k)
    (hscalar : 3 * f + a * b = 0)
    (hi4one : b * gm + b3 * g + c1 * f = 0)
    (hterminal : g * (3 * f1 + a1 * b) = a * b * gm)
    (hprev : 4 * a ^ 3 * b ^ 2 * c1 - 36 * a ^ 2 * b ^ 2 * gm +
      36 * a * a1 * b ^ 2 * g + 81 * c1 * epsilon * g +
      108 * c1 * g * gp + 108 * c2 * g * gm + 108 * c3 * g ^ 2 = 0)
    (hi4two : b * gp + b3 * gm + b4 * g + c1 * f1 + c2 * f +
      (3 / 4 : k) * epsilon * b = 0) :
    a ^ 3 * b ^ 3 * c1 - 9 * a ^ 2 * b ^ 3 * gm +
      9 * a * a1 * b ^ 3 * g - 18 * a * b * c1 ^ 2 * gm +
      9 * a * b * c1 * c2 * g + 9 * a1 * b * c1 ^ 2 * g +
      27 * b * c1 * gm ^ 2 + 27 * b * c2 * g * gm +
      27 * b * c3 * g ^ 2 - 27 * b4 * c1 * g ^ 2 = 0 := by
  linear_combination
    (1 / 4 : k) * b * hprev - 27 * c1 * g * hi4two +
    9 * c1 ^ 2 * hterminal + 9 * c1 * c2 * g * hscalar +
    27 * c1 * gm * hi4one - 9 * c1 ^ 2 * gm * hscalar

def RhoOneAlignedSquareFNegOneBoundaryTerminalNext68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareFNegOneBoundaryTerminal68 T g u ∧
  ∃ i4 : k,
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
    27 * i4 = 32 * A.coeff (-2) * B.coeff 1 * C.coeff 1 ∧
    3 * i4 + 16 * B.coeff 1 * G.coeff (-1) = 0 ∧
    9 * i4 - 16 * F.coeff (-1) * C.coeff 1 = 0

def RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoBoundaryTerminal68 T g u ∧
  ∃ i4 : k,
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
    B.coeff 2 * G.coeff 0 + B.coeff 3 * G.coeff (-1) +
      B.coeff 4 * G.coeff (-2) + C.coeff 1 * F.coeff 1 +
      C.coeff 2 * F.coeff 0 + (3 / 4 : k) * T.source.epsilon * B.coeff 2 = 0 ∧
    A.coeff (-2) ^ 3 * B.coeff 2 ^ 3 * C.coeff 1 -
        9 * A.coeff (-2) ^ 2 * B.coeff 2 ^ 3 * G.coeff (-1) +
      9 * A.coeff (-2) * A.coeff (-1) * B.coeff 2 ^ 3 * G.coeff (-2) -
      18 * A.coeff (-2) * B.coeff 2 * C.coeff 1 ^ 2 * G.coeff (-1) +
      9 * A.coeff (-2) * B.coeff 2 * C.coeff 1 * C.coeff 2 * G.coeff (-2) +
      9 * A.coeff (-1) * B.coeff 2 * C.coeff 1 ^ 2 * G.coeff (-2) +
      27 * B.coeff 2 * C.coeff 1 * G.coeff (-1) ^ 2 +
      27 * B.coeff 2 * C.coeff 2 * G.coeff (-2) * G.coeff (-1) +
      27 * B.coeff 2 * C.coeff 3 * G.coeff (-2) ^ 2 -
      27 * B.coeff 4 * C.coeff 1 * G.coeff (-2) ^ 2 = 0

/-- Source-facing scalar collapse of the `F[-1]` limb, retaining the
literal arbitrary-ground `I4` witness. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryF_terminal_next
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareFNegOneBoundaryTerminal68 T g u) :
    RhoOneAlignedSquareFNegOneBoundaryTerminalNext68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminal68] at Rc
  rcases Rc with ⟨Rf, hterminal⟩
  have Rfc := Rf
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryFollowing68] at Rfc
  rcases Rfc with ⟨Rn, hfollowing⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, i4, hi4src, hi4face, hnext⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hS, hb, hrel⟩
  have hs := rhoOne_boundaryF_i4_terminal_cross68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-1 : ℚ))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff (1 : ℚ))
    i4 hi4face hrel hterminal
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminalNext68]
  exact ⟨R, i4, hi4src, hs.1, hs.2.1, hs.2.2⟩

/-- Source-facing `I4(2)` reduction of the `G[-2]` limb.  The existing
nonzero selector and both first-integral witnesses are retained. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_next
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryTerminal68 T g u) :
    RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rc
  rcases Rc with ⟨Rf, i3old, hi3srcOld, hi3faceOld, hprev⟩
  have Rfc := Rf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfc
  rcases Rfc with ⟨Rn, i4old, hi4srcOld, hi4one, hterminal⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, hi3oldPacket, hterminalOld⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hb1, hS, hscalar, hi4oldFace⟩
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
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
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
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap]
    rw [map_mul, ratFuncAtHahn46_C]
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
  have hi4twoR := ratFunc_boundaryG_i4two68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS) hi4f
  have hi4two := hi4twoR
  rw [hCmap, hFmap, hGmap] at hi4two
  have hcross := rhoOne_boundaryG_i4two_cross68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (3 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (4 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
    T.source.epsilon hscalar hi4one hterminal hprev hi4two
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68]
  exact ⟨R, i4, hi4src, hi4two, hcross⟩

/-- The strict two-limb successor, preserving the final order box and its
source provenance literally. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundarySelectors_terminal_next
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareFNegOneBoundaryTerminal68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryTerminal68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0)) :
    RhoOneAlignedSquareFNegOneBoundaryTerminalNext68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  rcases R with hF | hG | hbox
  · exact Or.inl (T.rhoOne_boundaryF_terminal_next hF)
  · exact Or.inr (Or.inl (T.rhoOne_boundaryG_terminal_next hG))
  · exact Or.inr (Or.inr hbox)

end AlignedSquareBoundarySelectorsTerminalNext68

end Max11DegreeRoutes
