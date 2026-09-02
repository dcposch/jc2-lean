import Sol68ScaleTwoAlignedSquareNormalizedFinalInventoryScratch
import Sol68ScaleTwoAlignedSquareTerminalGNonzeroSourceScratch

/-! # Source consumers for the two last pre-order-box boundaries -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundarySelectorsConsumer68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance alignedSquareBoundarySelectorsConsumerHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Differentiation lowers the local order `-2` by at most one.  This is
the missing derivative bound for the old `G[-2]` selector; the proof uses
`H^2 f`, so it does not assume that `G[-1]` is nonzero. -/
theorem ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
    (a : k) (h0 : k[X]) (f : RatFunc k)
    (hscale :
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ))
    (hf : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a f).orderTop) :
    (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (Differential.deriv f)).orderTop := by
  let H : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let HH : HahnSeries ℚ k := ratFuncAtHahn46 a H
  let FH : HahnSeries ℚ k := ratFuncAtHahn46 a f
  let dHH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv H)
  let dFH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv f)
  have hHH : HH.orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    simpa only [HH, H] using hscale
  have hFH : (↑(-2 : ℚ) : WithTop ℚ) ≤ FH.orderTop := by
    simpa only [FH] using hf
  have hHnonneg : (0 : WithTop ℚ) ≤ HH.orderTop := by
    rw [hHH]
    norm_num
  have hdH : (0 : WithTop ℚ) ≤ dHH.orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a H hHnonneg
  have hHsq : (↑(2 : ℚ) : WithTop ℚ) ≤ (HH * HH).orderTop := by
    rw [HahnSeries.orderTop_mul, hHH]
    norm_num
  have hprod : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (H ^ 2 * f)).orderTop := by
    have hm := hahnOrderTop_mul_lower46 (HH * HH) FH 2 (-2) hHsq hFH
    norm_num at hm
    simpa only [map_mul, map_pow, pow_two, HH, FH, H,
      HahnSeries.orderTop_mul] using hm
  have hdprod : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (Differential.deriv (H ^ 2 * f))).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a (H ^ 2 * f) hprod
  have hdHsq : (↑(1 : ℚ) : WithTop ℚ) ≤
      (HH * dHH + HH * dHH).orderTop := by
    have hm : (↑(1 : ℚ) : WithTop ℚ) ≤ (HH * dHH).orderTop := by
      have h := hahnOrderTop_mul_lower46 HH dHH 1 0 hHH.ge hdH
      rw [HahnSeries.orderTop_mul]
      convert h using 1 <;> norm_num
    exact (le_min hm hm).trans HahnSeries.min_orderTop_le_orderTop_add
  have hcross : (↑(-1 : ℚ) : WithTop ℚ) ≤
      ((HH * dHH + HH * dHH) * FH).orderTop := by
    have hm := hahnOrderTop_mul_lower46 (HH * dHH + HH * dHH) FH
      1 (-2) hdHsq hFH
    rw [HahnSeries.orderTop_mul]
    convert hm using 1 <;> norm_num
  have hsum : (↑(-1 : ℚ) : WithTop ℚ) ≤
      ((ratFuncAtHahn46 a (Differential.deriv (H ^ 2 * f))) -
        (HH * dHH + HH * dHH) * FH).orderTop := by
    rw [sub_eq_add_neg]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · exact le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hdprod
    · rw [HahnSeries.orderTop_neg]
      exact hcross
  have hleibniz :
      ratFuncAtHahn46 a (Differential.deriv (H ^ 2 * f)) -
          (HH * dHH + HH * dHH) * FH =
        (HH * HH) * dFH := by
    dsimp only [HH, FH, dHH, dFH]
    simp only [pow_two, Derivation.leibniz, map_add, map_mul, smul_eq_mul]
    ring
  rw [hleibniz] at hsum
  change (↑(-3 : ℚ) : WithTop ℚ) ≤ dFH.orderTop
  cases hm : dFH.orderTop with
  | top => simp [hm]
  | coe q =>
      rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, hHH, hm] at hsum
      have hq : (-1 : ℚ) ≤ 1 + 1 + q := by
        exact WithTop.coe_le_coe.mp (by
          simpa only [WithTop.coe_add] using hsum)
      exact WithTop.coe_le_coe.mpr (by linarith)

/-- The first terminal coefficient visible in the original boundary box.
It is exactly the old refined `I4(-1)` face plus the genuinely new product
`F[-1]G[-2]`. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_negSix_boundary68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-1 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (↑(-2 : ℚ) : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ)) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff (-6 : ℚ) =
      (8 / 9 : k) * A.coeff (-2 : ℚ) * F.coeff (-1 : ℚ) *
          G.coeff (-2 : ℚ) +
        (4 / 27 : k) * A.coeff (-2 : ℚ) ^ 2 *
          rhoOneZeroLCubicDoubleZeroRefinedFour68 gamma
            (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
            (F.coeff (-1 : ℚ)) (G.coeff (-2 : ℚ)) := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS : (0 : WithTop ℚ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · simpa only [two_mul] using
        (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (-6 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (-6 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (-6)
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
  have hrewrite : rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG =
      weightedMonomial68 (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0 +
      weightedMonomial68 (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F G dA A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F F dB A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) C F dC A B 1 1 1 0 0 +
      weightedMonomial68 ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) B F dF A C 1 1 1 0 0 +
      weightedMonomial68 (4 / 9 : k) B C dG A F 1 1 1 0 0 +
      weightedMonomial68 ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0 +
      weightedMonomial68 (4 / 27 : k) B C C dA A 1 1 1 1 0 +
      weightedMonomial68 (-(2 / 27 : k)) A F dA S B 1 1 1 1 0 +
      weightedMonomial68 (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B G dA C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B F dB C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B B dF C 1 1 1 1 0 := by
    simp only [rhoOneMainTangentTerminalFourHahn68, S, weightedMonomial68,
      pow_zero, pow_one, mul_one, map_add, map_mul, map_neg, map_div₀,
      map_ofNat, map_one]
    ring
  have h1 := hz (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0
    (-1) 0 (-2) 1 0 hF hdC hA hB hC (by norm_num)
  have h2 := hz (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0
    (-1) (-3) (-2) 1 0 hF hdA hA hB hC (by norm_num)
  have h3 := lead (-(4 / 9 : k)) F G dA A B 1 1 1 0 0
    (-1) (-2) (-3) (-2) 1 hF hG hdA hA hB
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    (-1) (-1) 0 (-2) 1 hF hF hdB hA hB (by norm_num)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 (-1) 0 (-2) 1 hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    1 (-3) (-2) 0 (-1) hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    1 (-1) (-2) (-2) 0 hB hF hdF hA hC (by norm_num)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    1 0 (-3) (-2) (-1) hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    1 0 (-3) (-2) (-1) hB hC hdA hA hF (by norm_num)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    1 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num)
  have h11 := lead (-(2 / 27 : k)) A F dA S B 1 1 1 1 0
    (-2) (-1) (-3) 0 1 hA hF hdA hS hB
  have h12 := hz (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) 1 (-3) 0 (-1) hA hB hdA hC hF (by norm_num)
  have h13 := lead (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) 1 (-2) (-3) 0 hA hB hG hdA hC
  have h14 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) 1 (-1) 0 0 hA hB hF hdB hC (by norm_num)
  have h15 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) 1 1 (-2) 0 hA hB hB hdF hC (by norm_num)
  norm_num at h3 h11 h13
  have hSco : S.coeff (0 : ℚ) =
      2 * C.coeff (0 : ℚ) + 3 * gamma := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff (0 : ℚ) = 2 * C.coeff (0 : ℚ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hrewrite]
  simp only [HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, hdAco, hSco]
  simp only [rhoOneZeroLCubicDoubleZeroRefinedFour68]
  ring

/-- On the `F[-1]=0`, `G[-2]!=0` child, the next terminal coefficient is
the scalar `3 F[0] + A[-2] B[2]`. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_negFive_gNegTwoBoundary68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ))
    (hS : 2 * C.coeff (0 : ℚ) + 3 * gamma = 0) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff (-5 : ℚ) =
      (8 / 27 : k) * A.coeff (-2 : ℚ) * G.coeff (-2 : ℚ) *
        (3 * F.coeff (0 : ℚ) +
          A.coeff (-2 : ℚ) * B.coeff (2 : ℚ)) := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hSord : (0 : WithTop ℚ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · simpa only [two_mul] using
        (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (-5 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (-5 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (-5)
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
  have hrewrite : rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG =
      weightedMonomial68 (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0 +
      weightedMonomial68 (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F G dA A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F F dB A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) C F dC A B 1 1 1 0 0 +
      weightedMonomial68 ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) B F dF A C 1 1 1 0 0 +
      weightedMonomial68 (4 / 9 : k) B C dG A F 1 1 1 0 0 +
      weightedMonomial68 ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0 +
      weightedMonomial68 (4 / 27 : k) B C C dA A 1 1 1 1 0 +
      weightedMonomial68 (-(2 / 27 : k)) A F dA S B 1 1 1 1 0 +
      weightedMonomial68 (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B G dA C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B F dB C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B B dF C 1 1 1 1 0 := by
    simp only [rhoOneMainTangentTerminalFourHahn68, S, weightedMonomial68,
      pow_zero, pow_one, mul_one, map_add, map_mul, map_neg, map_div₀,
      map_ofNat, map_one]
    ring
  have h1 := hz (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0
    0 0 (-2) 2 0 hF hdC hA hB hC (by norm_num)
  have h2 := hz (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0
    0 (-3) (-2) 2 0 hF hdA hA hB hC (by norm_num)
  have h3 := lead (-(4 / 9 : k)) F G dA A B 1 1 1 0 0
    0 (-2) (-3) (-2) 2 hF hG hdA hA hB
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    0 0 0 (-2) 2 hF hF hdB hA hB (by norm_num)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 0 0 (-2) 2 hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    2 (-3) (-2) 0 0 hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    2 0 0 (-2) 0 hB hF hdF hA hC (by norm_num)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    2 0 (-3) (-2) 0 hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    2 0 (-3) (-2) 0 hB hC hdA hA hF (by norm_num)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    2 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num)
  have h11 := lead (-(2 / 27 : k)) A F dA S B 1 1 1 1 0
    (-2) 0 (-3) 0 2 hA hF hdA hSord hB
  have h12 := hz (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) 2 (-3) 0 0 hA hB hdA hC hF (by norm_num)
  have h13 := lead (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) 2 (-2) (-3) 0 hA hB hG hdA hC
  have h14 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) 2 0 0 0 hA hB hF hdB hC (by norm_num)
  have h15 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) 2 2 0 0 hA hB hB hdF hC (by norm_num)
  norm_num at h3 h11 h13
  have hSco : S.coeff (0 : ℚ) =
      2 * C.coeff (0 : ℚ) + 3 * gamma := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff (0 : ℚ) = 2 * C.coeff (0 : ℚ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hrewrite]
  simp only [HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, hdAco, hSco, hS]
  ring

/-- Exact finite residual on the old `F[-1] != 0` selector.  The terminal
row raises `G` by one order, and the two old invariant faces then determine
the affine factor and `F[-1]` itself. -/
def RhoOneAlignedSquareFNegOneBoundaryResidual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
  T.source.beta = 0 ∧ T.source.delta = 0 ∧ T.source.zeta = 0 ∧
  (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
  (0 : WithTop ℚ) ≤ C.orderTop ∧
  (↑(-1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
  (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧
  F.coeff (-1 : ℚ) ≠ 0 ∧ G.coeff (-2 : ℚ) = 0 ∧
  2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0 ∧
  B.coeff (1 : ℚ) ≠ 0 ∧
  3 * F.coeff (-1 : ℚ) =
    2 * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ)

/-- Exact finite residual on the old `G[-2] != 0` selector.  Besides the
already source-backed `I4(0)` load, terminal coefficient `-5` supplies the
new scalar `3F[0]+A[-2]B[2]=0`. -/
def RhoOneAlignedSquareGNegTwoBoundaryResidual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
  T.source.beta = 0 ∧ T.source.delta = 0 ∧ T.source.zeta = 0 ∧
  (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
  (0 : WithTop ℚ) ≤ C.orderTop ∧
  (0 : WithTop ℚ) ≤ F.orderTop ∧
  (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧
  F.coeff (-1 : ℚ) = 0 ∧ G.coeff (-2 : ℚ) ≠ 0 ∧
  B.coeff (1 : ℚ) = 0 ∧
  2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0 ∧
  3 * F.coeff (0 : ℚ) +
    A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) = 0 ∧
  ∃ i4 : k,
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
    i4 = (8 / 3 : k) * B.coeff (2 : ℚ) * G.coeff (-2 : ℚ)

/-- Source-backed consumption of both pre-order-box boundary selectors.
No later `G[-1]` nonvanishing is assumed. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundarySelectors_consumer
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
    (hF : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    RhoOneAlignedSquareFNegOneBoundaryResidual68 T g u ∨
    RhoOneAlignedSquareGNegTwoBoundaryResidual68 T g u ∨
    (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  have hfaces := T.rhoOne_exceptional_doubleZero_refined_faces
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hfaces
  rcases hfaces with ⟨_, _, _, _, h4, h3, _⟩
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * AR at hAclear
  obtain ⟨c', hc', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  have hcEq : c' = c := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst c'
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T.source.A T.source.B
      T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  rw [hbeta, hdelta, hzeta] at hlow
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR, AR, C0R]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hDrec : AR * BR / 3 + FR = DR := by
    dsimp only [FR, AR, BR, DR]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
    dsimp only [GR, ER, CR, AR, C0R, E0R]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) AR BR CR FR GR
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR :
      rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon) AR BR CR FR GR
        (ratFuncDerivation68 AR) (ratFuncDerivation68 BR)
        (ratFuncDerivation68 CR) (ratFuncDerivation68 FR)
        (ratFuncDerivation68 GR) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hsparseH := congrArg (ratFuncAtHahn46 T.root) hsparseR
  have hsparseH' :
      rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.epsilon)
        (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
        (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
        (ratFuncAtHahn46 T.root GR)
        (ratFuncAtHahn46 T.root (Differential.deriv AR))
        (ratFuncAtHahn46 T.root (Differential.deriv BR))
        (ratFuncAtHahn46 T.root (Differential.deriv CR))
        (ratFuncAtHahn46 T.root (Differential.deriv FR))
        (ratFuncAtHahn46 T.root (Differential.deriv GR)) =
      ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow,
      ratFuncAtHahn46_C, map_div₀, map_neg, map_ofNat, map_one] using hsparseH
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root AR).orderTop := by
    simpa only [AR] using hbounds.1
  have hAne : (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) ≠ 0 := by
    simpa only [AR] using P.2.2.1
  have hCRmap : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [CR, C0R, AR, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [FR, DR, AR, BR, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hERmap : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [ER, E0R, AR, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGRmap : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [GR, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hERmap, hCRmap]
    rw [map_mul, ratFuncAtHahn46_C]
  have h4R : rhoOneZeroLCubicDoubleZeroRefinedFour68 T.source.gamma
      ((ratFuncAtHahn46 T.root BR).coeff (1 : ℚ))
      ((ratFuncAtHahn46 T.root CR).coeff (0 : ℚ))
      ((ratFuncAtHahn46 T.root FR).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 T.root GR).coeff (-2 : ℚ)) = 0 := by
    rw [hCRmap, hFRmap, hGRmap]
    simpa only [BR] using h4
  have h3R : rhoOneZeroLCubicDoubleZeroRefinedThree68 T.source.gamma
      ((ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ))
      ((ratFuncAtHahn46 T.root BR).coeff (1 : ℚ))
      ((ratFuncAtHahn46 T.root CR).coeff (0 : ℚ))
      ((ratFuncAtHahn46 T.root FR).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 T.root GR).coeff (-2 : ℚ)) = 0 := by
    rw [hCRmap, hFRmap, hGRmap]
    simpa only [AR, BR] using h3
  have hBR : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
  have hFR : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root FR).orderTop := by rw [hFRmap]; exact hF
  have hGR : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root GR).orderTop := by rw [hGRmap]; exact hG
  have hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).orderTop := by
    dsimp only [AR]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdAco :
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ) =
        (-2 : k) * (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) := by
    dsimp only [AR]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
      T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num
  have hdB : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv BR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root BR
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBR)
  have hdC : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv CR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root CR hCR
  have hdF : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv FR)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 FR T.scale_order hFR
  have hdG : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 GR T.scale_order hGR
  have hcoeff6 := rhoOneMainTangentTerminalFourHahn_coeff_negSix_boundary68
    T.source.gamma T.source.epsilon
      (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
      (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
      (ratFuncAtHahn46 T.root GR)
      (ratFuncAtHahn46 T.root (Differential.deriv AR))
      (ratFuncAtHahn46 T.root (Differential.deriv BR))
      (ratFuncAtHahn46 T.root (Differential.deriv CR))
      (ratFuncAtHahn46 T.root (Differential.deriv FR))
      (ratFuncAtHahn46 T.root (Differential.deriv GR))
      hAH hBR hCR hFR hGR hdA hdB hdC hdF hdG hdAco
  have hterminal6 :
      (ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-6 : ℚ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [T.terminal_order]
      exact WithTop.coe_lt_coe.mpr (by norm_num))
  have hleft6 :
      (rhoOneMainTangentTerminalFourHahn68 T.source.gamma T.source.epsilon
        (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
        (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
        (ratFuncAtHahn46 T.root GR)
        (ratFuncAtHahn46 T.root (Differential.deriv AR))
        (ratFuncAtHahn46 T.root (Differential.deriv BR))
        (ratFuncAtHahn46 T.root (Differential.deriv CR))
        (ratFuncAtHahn46 T.root (Differential.deriv FR))
        (ratFuncAtHahn46 T.root (Differential.deriv GR))).coeff (-6 : ℚ) = 0 := by
    rw [← rhoOneMainTangentTerminalFourHahn_eq68, hsparseH']
    exact hterminal6
  have hprod :
      (ratFuncAtHahn46 T.root FR).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 T.root GR).coeff (-2 : ℚ) = 0 := by
    rw [hcoeff6, h4R, mul_zero, add_zero] at hleft6
    have ha : (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) ≠ 0 := hAne
    have hc89 : (8 / 9 : k) ≠ 0 := by norm_num
    rcases mul_eq_zero.mp hleft6 with habf | hg
    · rcases mul_eq_zero.mp habf with hab | hfz
      · rcases mul_eq_zero.mp hab with hc | ha0
        · exact (hc89 hc).elim
        · exact (ha ha0).elim
      · rw [hfz, zero_mul]
    · rw [hg, mul_zero]
  by_cases hf0 : (ratFuncAtHahn46 T.root FR).coeff (-1 : ℚ) = 0
  · have hsplit := T.rhoOne_exceptional_doubleZero_refined_fZero
      P hB hC hF hG hbeta hdelta hzeta h4 h3 (by
        dsimp only
        rw [← hFRmap]
        exact hf0)
    dsimp only at hsplit
    rcases hsplit with ⟨_, _, hF0, _, hGgain | hGboundary⟩
    · right
      right
      refine ⟨?_, hzeta⟩
      dsimp only [RhoOneAlignedSquareFinalOrderBox68]
      exact ⟨hB, hC, hF0, hGgain.1⟩
    · right
      left
      rcases hGboundary with ⟨hg, hB2, hb1, hS, hi4⟩
      have hFR0 : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root FR).orderTop := by rw [hFRmap]; exact hF0
      have hdF0 : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root (Differential.deriv FR)).orderTop :=
        ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root FR hFR0
      have hBR2 : (↑(2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB2
      have hcoeff5 :=
        rhoOneMainTangentTerminalFourHahn_coeff_negFive_gNegTwoBoundary68
          T.source.gamma T.source.epsilon
          (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
          (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
          (ratFuncAtHahn46 T.root GR)
          (ratFuncAtHahn46 T.root (Differential.deriv AR))
          (ratFuncAtHahn46 T.root (Differential.deriv BR))
          (ratFuncAtHahn46 T.root (Differential.deriv CR))
          (ratFuncAtHahn46 T.root (Differential.deriv FR))
          (ratFuncAtHahn46 T.root (Differential.deriv GR))
          hAH hBR2 hCR hFR0 hGR hdA hdB hdC hdF0 hdG hdAco
          (by rw [hCRmap]; exact hS)
      have hterminal5 :
          (ratFuncAtHahn46 T.root
            (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff
              (-5 : ℚ) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [T.terminal_order]
          exact WithTop.coe_lt_coe.mpr (by norm_num))
      have hleft5 :
          (rhoOneMainTangentTerminalFourHahn68
            T.source.gamma T.source.epsilon
            (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
            (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
            (ratFuncAtHahn46 T.root GR)
            (ratFuncAtHahn46 T.root (Differential.deriv AR))
            (ratFuncAtHahn46 T.root (Differential.deriv BR))
            (ratFuncAtHahn46 T.root (Differential.deriv CR))
            (ratFuncAtHahn46 T.root (Differential.deriv FR))
            (ratFuncAtHahn46 T.root (Differential.deriv GR))).coeff
              (-5 : ℚ) = 0 := by
        rw [← rhoOneMainTangentTerminalFourHahn_eq68, hsparseH']
        exact hterminal5
      rw [hcoeff5] at hleft5
      have hscalar : 3 * (ratFuncAtHahn46 T.root FR).coeff (0 : ℚ) +
          (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) *
            (ratFuncAtHahn46 T.root BR).coeff (2 : ℚ) = 0 := by
        have hc827 : (8 / 27 : k) ≠ 0 := by norm_num
        rcases mul_eq_zero.mp hleft5 with hab | hs
        · rcases mul_eq_zero.mp hab with hca | hg0
          · rcases mul_eq_zero.mp hca with hc | ha0
            · exact (hc827 hc).elim
            · exact (hAne ha0).elim
          · exact (hg (by rw [← hGRmap]; exact hg0)).elim
        · exact hs
      have hscalar' : 3 *
          (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (0 : ℚ) +
          (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ) *
            (ratFuncAtHahn46 T.root T.source.B).coeff (2 : ℚ) = 0 := by
        rw [← hFRmap]
        simpa only [AR, BR] using hscalar
      dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68]
      exact ⟨P, hbeta, hdelta, hzeta, hB2, hC, hF0, hG,
        (by rw [← hFRmap]; exact hf0), hg, hb1, hS,
        hscalar', hi4⟩
  · left
    have hg0 : (ratFuncAtHahn46 T.root GR).coeff (-2 : ℚ) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hf0
    have hGi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
      T.root GR (-2) hGR (by norm_num; exact hg0)
    norm_num at hGi
    change (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root GR).orderTop at hGi
    have hS0 : 2 * (ratFuncAtHahn46 T.root CR).coeff (0 : ℚ) +
        3 * T.source.gamma = 0 := by
      simp only [rhoOneZeroLCubicDoubleZeroRefinedFour68] at h4R
      rw [hg0] at h4R
      norm_num at h4R
      exact h4R.resolve_left hf0
    have hrel : 3 * (ratFuncAtHahn46 T.root FR).coeff (-1 : ℚ) =
        2 * (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) *
          (ratFuncAtHahn46 T.root BR).coeff (1 : ℚ) := by
      simp only [rhoOneZeroLCubicDoubleZeroRefinedThree68] at h3R
      rw [hg0] at h3R
      norm_num at h3R
      have hfac : (ratFuncAtHahn46 T.root FR).coeff (-1 : ℚ) *
          (3 * (ratFuncAtHahn46 T.root FR).coeff (-1 : ℚ) -
            2 * (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) *
              (ratFuncAtHahn46 T.root BR).coeff (1 : ℚ)) = 0 := by
        linear_combination h3R
      have hz := (mul_eq_zero.mp hfac).resolve_left hf0
      linear_combination hz
    have hbne : (ratFuncAtHahn46 T.root BR).coeff (1 : ℚ) ≠ 0 := by
      intro hb0
      rw [hb0, mul_zero] at hrel
      norm_num at hrel
      exact hf0 hrel
    have hS0' : 2 *
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ) +
        3 * T.source.gamma = 0 := by rw [← hCRmap]; exact hS0
    have hrel' : 3 *
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff (-1 : ℚ) =
        2 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ) *
          (ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ) := by
      rw [← hFRmap]
      simpa only [AR, BR] using hrel
    dsimp only [RhoOneAlignedSquareFNegOneBoundaryResidual68]
    exact ⟨P, hbeta, hdelta, hzeta, hB, hC, hF,
      (by rw [← hGRmap]; exact hGi),
      (by rw [← hFRmap]; exact hf0),
      (by rw [← hGRmap]; exact hg0), hS0',
      (by simpa only [BR] using hbne), hrel'⟩

end AlignedSquareBoundarySelectorsConsumer68

end Max11DegreeRoutes
