import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI4NextScratch

/-! # Finite `C/B` induction above the terminal cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapCI3Induction68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapCI3InductionHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The third first integral in the double-zero main-tangent coordinates. -/
def rhoOneI3CapFactored68 (gamma epsilon A B C F G : k) : k :=
  (-8 / 9 : k) * A * B * F - (8 / 9 : k) * B ^ 2 * C +
    (4 / 3 : k) * (2 * C + 3 * gamma) * G +
    (4 / 3 : k) * F ^ 2 - (2 / 3 : k) * gamma * B ^ 2 +
    2 * epsilon * C

theorem firstIntegralThree_cap_factor68
    (gamma epsilon A B C F G i3 : k)
    (hi3 : firstIntegralThree68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      0 gamma 0 epsilon 0 = i3) :
    rhoOneI3CapFactored68 gamma epsilon A B C F G = i3 := by
  rw [firstIntegralThree_mainTangent_decomposition68] at hi3
  simp only [firstIntegralThreeMainTangentTop68,
    firstIntegralThreeMainTangentLower68, rhoOneI3CapFactored68] at hi3 ⊢
  linear_combination hi3

/-- For indices `3 ≤ n ≤ 6`, the positive `I₃[n-1]` row has the unique
`(2C+3γ)[n]G[-1]` face. -/
theorem rhoOneI3CapFactored_coordinate_induction68
    (n : ℚ) (hn3 : 3 ≤ n) (hn6 : n ≤ 6)
    (gamma epsilon i3 : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(n + 4) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑n : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hCprev : C.coeff (n - 1) = 0)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    C.coeff n * G.coeff (-1 : ℚ) = 0 := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑n : WithTop ℚ) ≤ S.orderTop := by simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : n - 1 < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (n - 1) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (n - 1)
      h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have hABF := hz (-8 / 9) A B F C G 1 1 1 0 0
    (-2) (n + 4) 3 0 (-1) hA hB hF hC hG (by norm_num; linarith)
  have hB2C := hz (-8 / 9) B C A F G 2 1 0 0 0
    (n + 4) 0 (-2) 3 (-1) hB hC hA hF hG (by norm_num; linarith)
  have hSGraw := lead (4 / 3) S G A B F 1 1 0 0 0
    n (-1) (-2) (n + 4) 3 hS' hG hA hB hF
  have hSG :
      (weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0).coeff
        (n - 1) = (4 / 3 : k) * S.coeff n * G.coeff (-1 : ℚ) := by
    convert hSGraw using 1 <;> ring
  have hF2 := hz (4 / 3) F A B C G 2 0 0 0 0
    3 (-2) (n + 4) 0 (-1) hF hA hB hC hG (by norm_num; linarith)
  have hgammaB2 := hz (-(2 / 3) * gamma) B A C F G 2 0 0 0 0
    (n + 4) (-2) 0 3 (-1) hB hA hC hF hG (by norm_num; linarith)
  have hepsC :
      (weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0).coeff
        (n - 1) = 0 := by
    simp only [weightedMonomial68, pow_one, pow_zero, mul_one,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hCprev,
      mul_zero]
  have hright : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (n - 1) = 0 := by
    simp only [HahnSeries.C_apply]
    rw [HahnSeries.coeff_single_of_ne]
    linarith
  have hrewrite : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G =
      weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0 +
      weightedMonomial68 (-8 / 9 : k) B C A F G 2 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) F A B C G 2 0 0 0 0 +
      weightedMonomial68 (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0 +
      weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0 := by
    simp only [rhoOneI3CapFactored68, S, weightedMonomial68, pow_zero,
      pow_one, mul_one, map_mul, map_div₀, map_neg, map_ofNat]
    ring
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff (n - 1)) hi3
  rw [hrewrite] at hc
  simp only [HahnSeries.coeff_add] at hc
  rw [hABF, hB2C, hSG, hF2, hgammaB2, hepsC, hright] at hc
  have hSco : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff n = 2 * C.coeff n := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp only [HahnSeries.C_apply]
    rw [HahnSeries.coeff_single_of_ne]
    · ring
    · linarith
  rw [hSco] at hc
  linear_combination (3 / 8 : k) * hc

/-- The matching indexed leading `I₄` face after a `C`-order gain. -/
theorem rhoOneI4ZeroFactored_cap_coordinate_induction68
    (n : ℚ) (hn3 : 3 ≤ n) (gamma epsilon : k)
    (B C F G : HahnSeries ℚ k)
    (hB : (↑(n + 4) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑n : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) B C F G = 0) :
    B.coeff (n + 4) * G.coeff (-1 : ℚ) +
      C.coeff n * F.coeff (3 : ℚ) = 0 := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑n : WithTop ℚ) ≤ S.orderTop := by simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : n + 3 < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (n + 3) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (n + 3)
      h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have hB3 := hz (-8 / 27) B B B F G 3 0 0 0 0
    (n + 4) (n + 4) (n + 4) 3 (-1) hB hB hB hF hG
      (by norm_num; linarith)
  have hBGraw := lead (8 / 3) B G C F S 1 1 0 0 0
    (n + 4) (-1) 0 3 n hB hG hC hF hS'
  have hBG :
      (weightedMonomial68 (8 / 3 : k) B G C F S 1 1 0 0 0).coeff
        (n + 3) = (8 / 3 : k) * B.coeff (n + 4) * G.coeff (-1 : ℚ) := by
    convert hBGraw using 1 <;> ring
  have hSFraw := lead (4 / 3) S F B C G 1 1 0 0 0
    n 3 (n + 4) 0 (-1) hS' hF hB hC hG
  have hSF :
      (weightedMonomial68 (4 / 3 : k) S F B C G 1 1 0 0 0).coeff
        (n + 3) = (4 / 3 : k) * S.coeff n * F.coeff (3 : ℚ) := by
    convert hSFraw using 1 <;> ring
  have heB := hz (2 * epsilon) B C F G S 1 0 0 0 0
    (n + 4) 0 3 (-1) n hB hC hF hG hS' (by norm_num)
  have hfactor' :
      weightedMonomial68 (-8 / 27 : k) B B B F G 3 0 0 0 0 +
      weightedMonomial68 (8 / 3 : k) B G C F S 1 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) S F B C G 1 1 0 0 0 +
      weightedMonomial68 (2 * epsilon) B C F G S 1 0 0 0 0 = 0 := by
    simpa only [rhoOneI4ZeroFactored68, S, weightedMonomial68, pow_zero,
      pow_one, mul_one, map_add, map_mul, map_div₀, map_neg, map_ofNat,
      map_one] using hfactor
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff (n + 3)) hfactor'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  rw [hB3, hBG, hSF, heB] at hc
  have hSco : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff n = 2 * C.coeff n := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp only [HahnSeries.C_apply]
    rw [HahnSeries.coeff_single_of_ne]
    · ring
    · linarith
  rw [hSco] at hc
  linear_combination (3 / 8 : k) * hc

/-- At the first index beyond the coordinate induction, the `I₃` face meets
the square of the surviving terminal coefficient. -/
theorem rhoOneI3CapFactored_coordinate_cap68
    (gamma epsilon i3 : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hC6 : C.coeff (6 : ℚ) = 0)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    2 * C.coeff (7 : ℚ) * G.coeff (-1 : ℚ) +
      F.coeff (3 : ℚ) ^ 2 = 0 := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑(7 : ℚ) : WithTop ℚ) ≤ S.orderTop := by
    simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (6 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (6 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 6
      h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have hABF := hz (-8 / 9) A B F C G 1 1 1 0 0
    (-2) 11 3 0 (-1) hA hB hF hC hG (by norm_num)
  have hB2C := hz (-8 / 9) B C A F G 2 1 0 0 0
    11 0 (-2) 3 (-1) hB hC hA hF hG (by norm_num)
  have hSGraw := lead (4 / 3) S G A B F 1 1 0 0 0
    7 (-1) (-2) 11 3 hS' hG hA hB hF
  have hSG :
      (weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0).coeff 6 =
        (4 / 3 : k) * S.coeff 7 * G.coeff (-1 : ℚ) := by
    convert hSGraw using 1 <;> norm_num
  have hF2raw := lead (4 / 3) F A B C G 2 0 0 0 0
    3 (-2) 11 0 (-1) hF hA hB hC hG
  have hF2 :
      (weightedMonomial68 (4 / 3 : k) F A B C G 2 0 0 0 0).coeff 6 =
        (4 / 3 : k) * F.coeff 3 ^ 2 := by
    convert hF2raw using 1 <;> ring
  have hgammaB2 := hz (-(2 / 3) * gamma) B A C F G 2 0 0 0 0
    11 (-2) 0 3 (-1) hB hA hC hF hG (by norm_num)
  have hepsC :
      (weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0).coeff 6 = 0 := by
    simp only [weightedMonomial68, pow_one, pow_zero, mul_one,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hC6, mul_zero]
  have hright : (HahnSeries.C i3 : HahnSeries ℚ k).coeff 6 = 0 := by
    simp [HahnSeries.C_apply]
  have hrewrite : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G =
      weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0 +
      weightedMonomial68 (-8 / 9 : k) B C A F G 2 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) F A B C G 2 0 0 0 0 +
      weightedMonomial68 (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0 +
      weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0 := by
    simp only [rhoOneI3CapFactored68, S, weightedMonomial68, pow_zero,
      pow_one, mul_one, map_mul, map_div₀, map_neg, map_ofNat]
    ring
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff 6) hi3
  rw [hrewrite] at hc
  simp only [HahnSeries.coeff_add] at hc
  rw [hABF, hB2C, hSG, hF2, hgammaB2, hepsC, hright] at hc
  have hSco : S.coeff 7 = 2 * C.coeff 7 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff 7 = 2 * C.coeff 7 := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hSco] at hc
  linear_combination (3 / 4 : k) * hc

/-- Exact finite cap reached when both of the first two positive `C` jets
vanish.  The nonzero `C[7]` and `B[11]` faces are retained for the next row. -/
def RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68
    (gamma epsilon i3 : k) (A B C F G : HahnSeries ℚ k) : Prop :=
  rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
      A B C F G = HahnSeries.C i3 ∧
    C.coeff (3 : ℚ) = 0 ∧ C.coeff (4 : ℚ) = 0 ∧
    C.coeff (5 : ℚ) = 0 ∧ C.coeff (6 : ℚ) = 0 ∧
    B.coeff (7 : ℚ) = 0 ∧ B.coeff (8 : ℚ) = 0 ∧
    B.coeff (9 : ℚ) = 0 ∧ B.coeff (10 : ℚ) = 0 ∧
    (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop ∧
    (↑(11 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
    2 * C.coeff (7 : ℚ) * G.coeff (-1 : ℚ) +
      F.coeff (3 : ℚ) ^ 2 = 0 ∧
    C.coeff (7 : ℚ) ≠ 0 ∧
    B.coeff (11 : ℚ) * G.coeff (-1 : ℚ) +
      C.coeff (7 : ℚ) * F.coeff (3 : ℚ) = 0 ∧
    B.coeff (11 : ℚ) ≠ 0 ∧
    B.orderTop = (↑(11 : ℚ) : WithTop ℚ)

/-- The four-step `C/B` induction and its finite cap, stated directly for
rational functions so every order gain uses their integral support. -/
theorem rhoOneI3I4_coordinate_finite_cap68
    (root gamma epsilon i3 : k) (AR BR CR FR GR : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root AR).orderTop)
    (hB7 : (↑(7 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root BR).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root CR).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root FR).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root GR).orderTop)
    (hS3 : (↑(3 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root CR + HahnSeries.C (3 * gamma)).orderTop)
    (hC2 : (ratFuncAtHahn46 root CR).coeff (2 : ℚ) = 0)
    (hGne : (ratFuncAtHahn46 root GR).coeff (-1 : ℚ) ≠ 0)
    (hF3ne : (ratFuncAtHahn46 root FR).coeff (3 : ℚ) ≠ 0)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) (ratFuncAtHahn46 root AR)
      (ratFuncAtHahn46 root BR) (ratFuncAtHahn46 root CR)
      (ratFuncAtHahn46 root FR) (ratFuncAtHahn46 root GR) = HahnSeries.C i3)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) (ratFuncAtHahn46 root BR)
      (ratFuncAtHahn46 root CR) (ratFuncAtHahn46 root FR)
      (ratFuncAtHahn46 root GR) = 0) :
    RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68 gamma epsilon i3
      (ratFuncAtHahn46 root AR) (ratFuncAtHahn46 root BR)
      (ratFuncAtHahn46 root CR) (ratFuncAtHahn46 root FR)
      (ratFuncAtHahn46 root GR) := by
  let A := ratFuncAtHahn46 root AR
  let B := ratFuncAtHahn46 root BR
  let C := ratFuncAtHahn46 root CR
  let F := ratFuncAtHahn46 root FR
  let G := ratFuncAtHahn46 root GR
  let SR : RatFunc k := 2 * CR + RatFunc.C (3 * gamma)
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hSRmap : ratFuncAtHahn46 root SR = S := by
    dsimp only [SR, S, C]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
  have scoeff (n : ℤ) (hn : n ≠ 0) (hc : C.coeff (n : ℚ) = 0) :
      (ratFuncAtHahn46 root SR).coeff (n : ℚ) = 0 := by
    rw [hSRmap]
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff (n : ℚ) = 2 * C.coeff (n : ℚ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo, hc]
    simp only [HahnSeries.C_apply]
    rw [HahnSeries.coeff_single_of_ne]
    · ring
    · exact_mod_cast hn
  have hA' : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop := by simpa only [A] using hA
  have hB7' : (↑(7 : ℚ) : WithTop ℚ) ≤ B.orderTop := by simpa only [B] using hB7
  have hC' : (0 : WithTop ℚ) ≤ C.orderTop := by simpa only [C] using hC
  have hF' : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop := by simpa only [F] using hF
  have hG' : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop := by simpa only [G] using hG
  have hS3' : (↑(3 : ℚ) : WithTop ℚ) ≤ S.orderTop := by simpa only [S, C] using hS3
  have hC3prod := rhoOneI3CapFactored_coordinate_induction68
    3 (by norm_num) (by norm_num) gamma epsilon i3 A B C F G
      hA' (by convert hB7' using 1 <;> norm_num) hC' hF' hG' hS3'
      (by
        change C.coeff (2 : ℚ) = 0 at hC2
        convert hC2 using 1 <;> norm_num)
      (by simpa only [A, B, C, F, G] using hi3)
  norm_num at hC3prod
  have hc3 : C.coeff (3 : ℚ) = 0 :=
    hC3prod.resolve_right (by simpa only [G] using hGne)
  have hS4raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root SR 3 (by rw [hSRmap]; exact hS3') (scoeff 3 (by norm_num) hc3)
  norm_num at hS4raw
  have hS4 : (↑(4 : ℚ) : WithTop ℚ) ≤ S.orderTop := by rw [← hSRmap]; exact hS4raw
  have hrow3 := rhoOneI4ZeroFactored_cap_coordinate_induction68
    3 (by norm_num) gamma epsilon B C F G
      (by convert hB7' using 1 <;> norm_num) hC' hF' hG' hS3'
      (by simpa only [B, C, F, G] using hi4)
  norm_num at hrow3
  have hb7 : B.coeff (7 : ℚ) = 0 := by
    rw [hc3] at hrow3
    norm_num at hrow3
    exact hrow3.resolve_right (by simpa only [G] using hGne)
  have hB8raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root BR 7 (by convert hB7 using 1 <;> norm_num)
      (by change (ratFuncAtHahn46 root BR).coeff (7 : ℚ) = 0; exact hb7)
  norm_num at hB8raw
  have hB8 : (↑(8 : ℚ) : WithTop ℚ) ≤ B.orderTop := by
    dsimp only [B]
    convert hB8raw using 1 <;> norm_num
  have hC4prod := rhoOneI3CapFactored_coordinate_induction68
    4 (by norm_num) (by norm_num) gamma epsilon i3 A B C F G
      hA' (by convert hB8 using 1 <;> norm_num) hC' hF' hG' hS4
      (by convert hc3 using 1 <;> norm_num)
      (by simpa only [A, B, C, F, G] using hi3)
  norm_num at hC4prod
  have hc4 : C.coeff (4 : ℚ) = 0 :=
    hC4prod.resolve_right (by simpa only [G] using hGne)
  have hS5raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root SR 4 (by rw [hSRmap]; exact hS4) (scoeff 4 (by norm_num) hc4)
  norm_num at hS5raw
  have hS5 : (↑(5 : ℚ) : WithTop ℚ) ≤ S.orderTop := by rw [← hSRmap]; exact hS5raw
  have hrow4 := rhoOneI4ZeroFactored_cap_coordinate_induction68
    4 (by norm_num) gamma epsilon B C F G
      (by convert hB8 using 1 <;> norm_num) hC' hF' hG' hS4
      (by simpa only [B, C, F, G] using hi4)
  norm_num at hrow4
  have hb8 : B.coeff (8 : ℚ) = 0 := by
    rw [hc4] at hrow4
    norm_num at hrow4
    exact hrow4.resolve_right (by simpa only [G] using hGne)
  have hB9raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root BR 8 (by dsimp only [B] at hB8; convert hB8 using 1 <;> norm_num)
      (by dsimp only [B] at hb8; convert hb8 using 1 <;> norm_num)
  norm_num at hB9raw
  have hB9 : (↑(9 : ℚ) : WithTop ℚ) ≤ B.orderTop := by
    dsimp only [B]
    convert hB9raw using 1 <;> norm_num
  have hC5prod := rhoOneI3CapFactored_coordinate_induction68
    5 (by norm_num) (by norm_num) gamma epsilon i3 A B C F G
      hA' (by convert hB9 using 1 <;> norm_num) hC' hF' hG' hS5
      (by convert hc4 using 1 <;> norm_num)
      (by simpa only [A, B, C, F, G] using hi3)
  norm_num at hC5prod
  have hc5 : C.coeff (5 : ℚ) = 0 :=
    hC5prod.resolve_right (by simpa only [G] using hGne)
  have hS6raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root SR 5 (by rw [hSRmap]; exact hS5) (scoeff 5 (by norm_num) hc5)
  norm_num at hS6raw
  have hS6 : (↑(6 : ℚ) : WithTop ℚ) ≤ S.orderTop := by rw [← hSRmap]; exact hS6raw
  have hrow5 := rhoOneI4ZeroFactored_cap_coordinate_induction68
    5 (by norm_num) gamma epsilon B C F G
      (by convert hB9 using 1 <;> norm_num) hC' hF' hG' hS5
      (by simpa only [B, C, F, G] using hi4)
  norm_num at hrow5
  have hb9 : B.coeff (9 : ℚ) = 0 := by
    rw [hc5] at hrow5
    norm_num at hrow5
    exact hrow5.resolve_right (by simpa only [G] using hGne)
  have hB10raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root BR 9 (by dsimp only [B] at hB9; convert hB9 using 1 <;> norm_num)
      (by dsimp only [B] at hb9; convert hb9 using 1 <;> norm_num)
  norm_num at hB10raw
  have hB10 : (↑(10 : ℚ) : WithTop ℚ) ≤ B.orderTop := by
    dsimp only [B]
    convert hB10raw using 1 <;> norm_num
  have hC6prod := rhoOneI3CapFactored_coordinate_induction68
    6 (by norm_num) (by norm_num) gamma epsilon i3 A B C F G
      hA' (by convert hB10 using 1 <;> norm_num) hC' hF' hG' hS6
      (by convert hc5 using 1 <;> norm_num)
      (by simpa only [A, B, C, F, G] using hi3)
  norm_num at hC6prod
  have hc6 : C.coeff (6 : ℚ) = 0 :=
    hC6prod.resolve_right (by simpa only [G] using hGne)
  have hS7raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root SR 6 (by rw [hSRmap]; exact hS6) (scoeff 6 (by norm_num) hc6)
  norm_num at hS7raw
  have hS7 : (↑(7 : ℚ) : WithTop ℚ) ≤ S.orderTop := by rw [← hSRmap]; exact hS7raw
  have hrow6 := rhoOneI4ZeroFactored_cap_coordinate_induction68
    6 (by norm_num) gamma epsilon B C F G
      (by convert hB10 using 1 <;> norm_num) hC' hF' hG' hS6
      (by simpa only [B, C, F, G] using hi4)
  norm_num at hrow6
  have hb10 : B.coeff (10 : ℚ) = 0 := by
    rw [hc6] at hrow6
    norm_num at hrow6
    exact hrow6.resolve_right (by simpa only [G] using hGne)
  have hB11raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    root BR 10 (by dsimp only [B] at hB10; convert hB10 using 1 <;> norm_num)
      (by dsimp only [B] at hb10; convert hb10 using 1 <;> norm_num)
  norm_num at hB11raw
  have hB11 : (↑(11 : ℚ) : WithTop ℚ) ≤ B.orderTop := by
    dsimp only [B]
    convert hB11raw using 1 <;> norm_num
  have hcap := rhoOneI3CapFactored_coordinate_cap68 gamma epsilon i3 A B C F G
    hA' hB11 hC' hF' hG' hS7 hc6
      (by simpa only [A, B, C, F, G] using hi3)
  have hc7ne : C.coeff (7 : ℚ) ≠ 0 := by
    intro hc7
    rw [hc7] at hcap
    norm_num at hcap
    exact hF3ne (by simpa only [F] using hcap)
  have hrow7 := rhoOneI4ZeroFactored_cap_coordinate_induction68
    7 (by norm_num) gamma epsilon B C F G
      (by convert hB11 using 1 <;> norm_num) hC' hF' hG' hS7
      (by simpa only [B, C, F, G] using hi4)
  norm_num at hrow7
  have hb11ne : B.coeff (11 : ℚ) ≠ 0 := by
    intro hb11
    rw [hb11] at hrow7
    norm_num at hrow7
    rcases hrow7 with hc7 | hf3
    · exact hc7ne hc7
    · exact hF3ne (by simpa only [F] using hf3)
  have hBexact : B.orderTop = (↑(11 : ℚ) : WithTop ℚ) :=
    le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hb11ne) hB11
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68]
  exact ⟨by simpa only [A, B, C, F, G] using hi3,
    hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10, hS7, hB11,
    hcap, hc7ne, hrow7, hb11ne, hBexact⟩

/-- The previous cap residual, refined only on its `C[1]=C[2]=0`
coordinate child.  In particular its full `C[1]≠0` coefficient-five row and
both nonzero quadratic rays remain verbatim in the first conjunct. -/
def RhoOneDoubleZeroTerminalGBoundaryCapCI3InductionResidual68
    (root j gamma epsilon : k) (h0R BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI4NextResidual68
      root j gamma epsilon h0R BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 : k,
        RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68
          gamma epsilon i3 A B C F G)

/-- Literal source backwire of the `C₃,…,C₆` / `B₇,…,B₁₀` induction
and its first nonzero cap. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapCI3InductionResidual
    [IsAlgClosed k]
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryCapCI3InductionResidual68
        T.root j T.source.gamma T.source.epsilon
        (algebraMap k[X] (RatFunc k) h0) BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapCI3InductionResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI4NextResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hprev with hcapNext | hbad
    · left
      refine ⟨hcapNext, ?_⟩
      intro hcoord hc1 hc2
      have htarget := hcapNext.2 hcoord
      rcases htarget with ⟨hrow5full, hCsplit⟩
      rcases hCsplit with hCzero | hCne
      · rcases hCzero with ⟨⟨hc1', hb5, hB6⟩, hC2split⟩
        rcases hC2split with hC2zero | hC2ne
        · rcases hC2zero with ⟨hc2', hb6, hB7⟩
          have hfinite := hcapNext.1.1
          dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hfinite
          rcases hfinite with ⟨hfact, hboundary | hrays⟩
          · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
              hi4three, hf3ne⟩
            rcases hcurrent with ⟨hprev4, hb3, hB4, hi4two⟩
            rcases hprev4 with ⟨hprev3, hf1, hF2⟩
            rcases hprev3 with ⟨hprev2, hb2, hB3, hi4one⟩
            rcases hprev2 with ⟨hprev1, hf0, hF1⟩
            rcases hprev1 with ⟨hcoord', hB2, hS1, hi4zero⟩
            let AR : RatFunc k := T.source.A
            let BR : RatFunc k := T.source.B
            let CR : RatFunc k :=
              T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
            let FR : RatFunc k :=
              T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
            let GR : RatFunc k :=
              (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
                RatFunc.C (1 / 3 : k) * AR * CR
            have hCRmap : ratFuncAtHahn46 T.root CR =
                rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0) := by
              dsimp only [CR, AR, rhoOneCDefectHahn68]
              simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
            have hFRmap : ratFuncAtHahn46 T.root FR =
                rhoOneTangentDDefectHahn68
                  (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.B)
                  (ratFuncAtHahn46 T.root T.source.D) := by
              dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
              simp only [map_sub, map_mul, ratFuncAtHahn46_C]
            have hGRmap : ratFuncAtHahn46 T.root GR =
                rhoOneTangentEDefectHahn68
                  (ratFuncAtHahn46 T.root T.source.A)
                  (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.C0))
                  (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.E)) := by
              dsimp only [GR, CR, AR, rhoOneTangentEDefectHahn68,
                rhoOneCDefectHahn68, rhoOneEDefectHahn68]
              simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
            let SR : RatFunc k := 2 * CR + RatFunc.C (3 * T.source.gamma)
            have hSRmap : ratFuncAtHahn46 T.root SR =
                2 * ratFuncAtHahn46 T.root CR +
                  HahnSeries.C (3 * T.source.gamma) := by
              dsimp only [SR]
              simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
            have hscoeff (n : ℤ) (hn : n ≠ 0)
                (hcn : (ratFuncAtHahn46 T.root CR).coeff (n : ℚ) = 0) :
                (ratFuncAtHahn46 T.root SR).coeff (n : ℚ) = 0 := by
              rw [hSRmap, HahnSeries.coeff_add]
              have htwo :
                  (2 * ratFuncAtHahn46 T.root CR).coeff (n : ℚ) =
                    2 * (ratFuncAtHahn46 T.root CR).coeff (n : ℚ) := by
                rw [two_mul, HahnSeries.coeff_add]
                ring
              rw [htwo, hcn]
              simp only [HahnSeries.C_apply]
              rw [HahnSeries.coeff_single_of_ne]
              · ring
              · exact_mod_cast hn
            have hS1R : (↑(1 : ℚ) : WithTop ℚ) ≤
                (ratFuncAtHahn46 T.root SR).orderTop := by
              rw [hSRmap, hCRmap]
              exact hS1
            have hS2raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
              T.root SR 1 hS1R (hscoeff 1 (by norm_num) (by
                rw [hCRmap]
                exact hc1))
            norm_num at hS2raw
            have hS3raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
              T.root SR 2 hS2raw (hscoeff 2 (by norm_num) (by
                rw [hCRmap]
                exact hc2))
            norm_num at hS3raw
            have hbounds := P.2.1
            dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
            have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
                (ratFuncAtHahn46 T.root AR).orderTop := by
              simpa only [AR] using hbounds.1
            obtain ⟨i4, i3, hi4raw, hi3raw⟩ :=
              integratedFirstIntegrals_exist_ground68
                T.source.A T.source.B T.source.C0 T.source.D T.source.E
                (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
                0 T.source.alpha T.source.beta T.source.gamma T.source.delta
                T.source.epsilon T.source.zeta T.source.eta (by
                  simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
            rw [hbeta, hdelta, hzeta] at hi3raw
            have hCrec : AR ^ 2 / 3 + CR = T.source.C0 := by
              dsimp only [CR, AR]
              simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
              ring
            have hDrec : AR * BR / 3 + FR = T.source.D := by
              dsimp only [FR, AR, BR]
              simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
              ring
            have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = T.source.E := by
              dsimp only [GR, CR, AR]
              simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
              ring
            have hi3T :
                firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR)
                  (AR * BR / 3 + FR) (AR ^ 3 / 27 + AR * CR / 3 + GR)
                  0 (RatFunc.C T.source.gamma) 0 (RatFunc.C T.source.epsilon)
                  0 = RatFunc.C i3 := by
              rw [hCrec, hDrec, hErec]
              simpa only [AR, BR, RatFunc.algebraMap_eq_C, map_zero] using hi3raw
            have hi3R := firstIntegralThree_cap_factor68
              (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
              AR BR CR FR GR (RatFunc.C i3) hi3T
            have hi3Hraw := congrArg (ratFuncAtHahn46 T.root) hi3R
            have hi3H : rhoOneI3CapFactored68
                (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
                (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
                (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
                (ratFuncAtHahn46 T.root GR) = HahnSeries.C i3 := by
              simpa only [rhoOneI3CapFactored68, map_add, map_sub, map_mul,
                map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
                RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hi3Hraw
            change rhoOneI4ZeroFactored68
              (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
              BR CR FR GR = 0 at hfact
            have hi4Hraw := congrArg (ratFuncAtHahn46 T.root) hfact
            have hi4H : rhoOneI4ZeroFactored68
                (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
                (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
                (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR) = 0 := by
              simpa only [rhoOneI4ZeroFactored68, map_add, map_mul, map_pow,
                map_neg, map_div₀, map_ofNat, map_zero, map_one,
                ratFuncAtHahn46_C] using hi4Hraw
            have hpacket := rhoOneI3I4_coordinate_finite_cap68
              T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
              hAH (by simpa only [BR] using hB7)
              (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF3)
              (by rw [hGRmap]; exact hG)
              (by rw [hSRmap] at hS3raw; exact hS3raw)
              (by rw [hCRmap]; exact hc2)
              (by rw [hGRmap]; exact hGne) (by rw [hFRmap]; exact hf3ne)
              hi3H hi4H
            refine ⟨i3, ?_⟩
            rw [hCRmap, hFRmap, hGRmap] at hpacket
            simpa only [AR, BR] using hpacket
          · exact (hrays.1 hcoord.1).elim
        · exact (hC2ne.1 hc2).elim
      · exact (hCne.1 hc1).elim
    · exact (hGne hbad.1).elim
  · right
    refine ⟨hGzero, hG0, ?_⟩
    have hres :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hbad | ⟨_, _, htail'⟩
    · exact (hbad hGzero).elim
    · exact htail'

end AlignedSquareTerminalGBoundaryCapCI3Induction68

end Max11DegreeRoutes
