import Fable68ScaleTwoAlignedSquareGZeroChildNextScratch

/-! # The third unused rows on the refined `G[-1] = 0` children

The `G`-zero-child-next residual keeps the `G[-1] = 0` sibling as the
refined disjunction `BGainRefinedNext ∨ FGainRefinedNext`.  On that
sibling the exact next unused rows are the coefficient-three `I₄` row
and the coefficient-one `I₃` row, on both children:

* On the `B`-gain child (box `ord A ≥ -2`, `ord B ≥ 2`, `ord C ≥ 0`,
  `ord F ≥ 0`, `ord G ≥ 0`) the coefficient-three `I₄` row needs the
  four-combination jet on the `(2C+3γ)F` block and reads
  `4B[2]G[1] + 4B[3]G[0] + 2F[3]·(2C[0]+3γ) + 4C[1]F[2] + 4C[2]F[1] +
  4C[3]F[0] + 3εB[3] = 0`, while the coefficient-one `I₃` row is the
  first multi-combination `I₃` row of this lane: the `ABF` block
  carries the three combinations `A[-2]B[2]F[1] + A[-2]B[3]F[0] +
  A[-1]B[2]F[0]` and the row ties them to `6G[1]·(2C[0]+3γ) +
  12C[1]G[0] + 12F[0]F[1] + 9εC[1]` with no ground load.

* On the `F`-gain child (box `ord B ≥ 1`, `ord F ≥ 1`) the cube is no
  longer silent at coefficient three:
  `-4B[1]³ + 36B[1]G[2] + 36B[2]G[1] + 36B[3]G[0] + 18F[3]·(2C[0]+3γ)
  + 36C[1]F[2] + 36C[2]F[1] + 27εB[3] = 0`, and the coefficient-one
  `I₃` row reads `4A[-2]B[1]F[2] + 4A[-2]B[2]F[1] + 4A[-1]B[1]F[1] =
  6G[1]·(2C[0]+3γ) + 12C[1]G[0] + 9εC[1]`.

Both `I₃` rows are consumed at the Laurent level; the earlier `I₃`
rows of this lane were single-combination Hahn-level pinches.  On the
affine tail `2C[0]+3γ = 0` with the `C[1] = 0` face the new `B`-gain
`I₃` row degenerates to the scalar tie `A[-2]B[2]F[1] + A[-2]B[3]F[0]
+ A[-1]B[2]F[0] = 3F[0]F[1]`; this is recorded as a standalone
corollary and not wired into the packet, so the tail disjunction of
the imported refinement stays verbatim.  The nonzero `G[-1]` boundary
lane, the `C₂` face, and the quadratic rays remain literally inside
the imported derivative-next residual. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareGZeroChildThird68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareGZeroChildThirdHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The coefficient three integral jet above the lower face of a Laurent
product, restated locally for the `G`-zero-child-third lane. -/
theorem laurent_coeff_mul_lower_three_gZeroChildThird68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 3) =
      X.coeff m * Y.coeff (n + 3) +
        X.coeff (m + 1) * Y.coeff (n + 2) +
          X.coeff (m + 2) * Y.coeff (n + 1) +
            X.coeff (m + 3) * Y.coeff n := by
  let Xt : LaurentSeries k := X - HahnSeries.single m (X.coeff m)
  have hsm : (↑m : WithTop ℤ) ≤
      (HahnSeries.single m (X.coeff m) : LaurentSeries k).orderTop := by
    by_cases hx : X.coeff m = 0
    · simp [hx]
    · rw [HahnSeries.orderTop_single hx]
  have hXt0 : Xt.coeff m = 0 := by simp [Xt]
  have hXtBase : (↑m : WithTop ℤ) ≤ Xt.orderTop := by
    exact le_trans (by simpa using min_le_min hX hsm)
      HahnSeries.min_orderTop_le_orderTop_sub
  have hXt := laurent_orderTop_ge_succ_of_coeff_zero68 Xt m hXtBase hXt0
  have htail := laurent_coeff_mul_lower_two_gZeroChildNext68 Xt Y
    (m + 1) n hXt hY
  have htail' : (Xt * Y).coeff (m + n + 3) =
      Xt.coeff (m + 1) * Y.coeff (n + 2) +
        Xt.coeff (m + 2) * Y.coeff (n + 1) +
          Xt.coeff (m + 3) * Y.coeff n := by
    convert htail using 1 <;> ring
  have hXt1 : Xt.coeff (m + 1) = X.coeff (m + 1) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt2 : Xt.coeff (m + 2) = X.coeff (m + 2) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt3 : Xt.coeff (m + 3) = X.coeff (m + 3) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hlead :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Y).coeff
          (m + n + 3) = X.coeff m * Y.coeff (n + 3) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 3 - m = n + 3 := by omega
    rw [hi]
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by simp [Xt]
  calc
    (X * Y).coeff (m + n + 3) =
        ((HahnSeries.single m (X.coeff m) + Xt) * Y).coeff
          (m + n + 3) := by rw [← hXdec]
    _ = _ := by
      rw [add_mul, HahnSeries.coeff_add, hlead, htail', hXt1, hXt2, hXt3]
      ring

/-- The coefficient-three `I₄` row on the `B`-gain child: with
`ord B ≥ 2` the `BG` block carries two integral combinations, the
`(2C+3γ)F` block carries all four, and the cube stays silent. -/
theorem rhoOneGZeroChildThirdI4Load_bGain_coeff_three68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneGZeroChildI4LoadFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    4 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      2 * (ratFuncAtHahn46 root F).coeff (3 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      4 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff (3 : ℚ) = 0 := by
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 2 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G 0 hG
  have hC3g : (↑(0 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (3 * gamma) : LaurentSeries k).orderTop := by
    rw [HahnSeries.C_apply]
    by_cases hc0 : 3 * gamma = 0 <;> simp [hc0, HahnSeries.orderTop_single]
  have hSLord : (↑(0 : ℤ) : WithTop ℤ) ≤ SL.orderTop := by
    dsimp only [SL]
    have h2 : (↑(0 : ℤ) : WithTop ℤ) ≤ (2 * CL).orderTop := by
      rw [two_mul]
      exact le_trans (le_min hCL hCL)
        HahnSeries.min_orderTop_le_orderTop_add
    exact le_trans (le_min h2 hC3g)
      HahnSeries.min_orderTop_le_orderTop_add
  have hSF := laurent_coeff_mul_lower_three_gZeroChildThird68 SL FL 0 0
    hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower_succ68 BL Gser 2 0 hBL hGL
  norm_num at hBG
  have hBcubeOrder : (↑(6 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (3 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneGZeroChildI4LoadFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) BL CL FL Gser =
        HahnSeries.C i4 := by
    simpa only [rhoOneGZeroChildI4LoadFactored68, BL, CL, FL, Gser,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero,
      map_one, ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneGZeroChildI4LoadFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (3 : ℤ))
    hfactorL'
  simp only [HahnSeries.coeff_add] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc827 : (-8 / 27 : LaurentSeries k) =
      HahnSeries.C (-8 / 27 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc83 : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 3 =
      (-8 / 27 : k) * (BL ^ 3).coeff 3 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 3 =
      (8 / 3 : k) * (BL * Gser).coeff 3 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 3 =
      (4 / 3 : k) * (SL * FL).coeff 3 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 3 =
      (2 * epsilon) * BL.coeff 3 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (3 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hBcube, hBG, hSF, hright] at hc
  have hSL0 : SL.coeff (0 : ℤ) = 2 * CL.coeff (0 : ℤ) + 3 * gamma := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL1 : SL.coeff (1 : ℤ) = 2 * CL.coeff (1 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL2 : SL.coeff (2 : ℤ) = 2 * CL.coeff (2 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL3 : SL.coeff (3 : ℤ) = 2 * CL.coeff (3 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2, hSL3] at hc
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hC3 := ratFuncAtHahn46_coeff_int68 root C 3
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  norm_num at hB2 hB3 hC0 hC1 hC2 hC3 hF0 hF1 hF2 hF3 hG0 hG1
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB2, ← hB3, ← hC0, ← hC1, ← hC2, ← hC3, ← hF0, ← hF1, ← hF2,
    ← hF3, ← hG0, ← hG1] at hc
  linear_combination (3 / 2 : k) * hc

/-- The coefficient-three `I₄` row on the `F`-gain child: with
`ord B ≥ 1` and `ord F ≥ 1` the cube boundary `B[1]³` enters alongside
the three-combination `BG` and `(2C+3γ)F` jets. -/
theorem rhoOneGZeroChildThirdI4Load_fGain_coeff_three68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneGZeroChildI4LoadFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    -4 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) ^ 3 +
      36 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      18 * (ratFuncAtHahn46 root F).coeff (3 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      36 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      27 * epsilon * (ratFuncAtHahn46 root B).coeff (3 : ℚ) = 0 := by
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 1 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 1 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G 0 hG
  have hC3g : (↑(0 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (3 * gamma) : LaurentSeries k).orderTop := by
    rw [HahnSeries.C_apply]
    by_cases hc0 : 3 * gamma = 0 <;> simp [hc0, HahnSeries.orderTop_single]
  have hSLord : (↑(0 : ℤ) : WithTop ℤ) ≤ SL.orderTop := by
    dsimp only [SL]
    have h2 : (↑(0 : ℤ) : WithTop ℤ) ≤ (2 * CL).orderTop := by
      rw [two_mul]
      exact le_trans (le_min hCL hCL)
        HahnSeries.min_orderTop_le_orderTop_add
    exact le_trans (le_min h2 hC3g)
      HahnSeries.min_orderTop_le_orderTop_add
  have hSF := laurent_coeff_mul_lower_two_gZeroChildNext68 SL FL 0 1
    hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower_two_gZeroChildNext68 BL Gser 1 0
    hBL hGL
  norm_num at hBG
  have hBsqOrder : (↑(2 : ℤ) : WithTop ℤ) ≤ (BL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hBL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hBsqOrder' : (↑(2 : ℤ) : WithTop ℤ) ≤ (BL * BL).orderTop := by
    rw [← pow_two]
    exact hBsqOrder
  have hsqc := laurent_coeff_mul_lower68 BL BL 1 1 hBL hBL
  norm_num at hsqc
  have hcubec := laurent_coeff_mul_lower68 (BL * BL) BL 2 1 hBsqOrder' hBL
  norm_num at hcubec
  have hBcube : (BL ^ 3).coeff (3 : ℤ) = BL.coeff 1 ^ 3 := by
    have hpow : BL ^ 3 = BL * BL * BL := by ring
    rw [hpow, hcubec, hsqc]
    ring
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneGZeroChildI4LoadFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) BL CL FL Gser =
        HahnSeries.C i4 := by
    simpa only [rhoOneGZeroChildI4LoadFactored68, BL, CL, FL, Gser,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero,
      map_one, ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneGZeroChildI4LoadFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (3 : ℤ))
    hfactorL'
  simp only [HahnSeries.coeff_add] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc827 : (-8 / 27 : LaurentSeries k) =
      HahnSeries.C (-8 / 27 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc83 : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 3 =
      (-8 / 27 : k) * (BL ^ 3).coeff 3 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 3 =
      (8 / 3 : k) * (BL * Gser).coeff 3 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 3 =
      (4 / 3 : k) * (SL * FL).coeff 3 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 3 =
      (2 * epsilon) * BL.coeff 3 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (3 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hBcube, hBG, hSF, hright] at hc
  have hSL0 : SL.coeff (0 : ℤ) = 2 * CL.coeff (0 : ℤ) + 3 * gamma := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL1 : SL.coeff (1 : ℤ) = 2 * CL.coeff (1 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL2 : SL.coeff (2 : ℤ) = 2 * CL.coeff (2 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2] at hc
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  norm_num at hB1 hB2 hB3 hC0 hC1 hC2 hF1 hF2 hF3 hG0 hG1 hG2
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB1, ← hB2, ← hB3, ← hC0, ← hC1, ← hC2, ← hF1, ← hF2, ← hF3,
    ← hG0, ← hG1, ← hG2] at hc
  linear_combination (27 / 2 : k) * hc

/-- The coefficient-one `I₃` row on the `B`-gain child, consumed at the
Laurent level: the `ABF` block carries three integral combinations, the
`B²` blocks stay silent, and the row ties the boundary jets with no
ground load. -/
theorem rhoOneGZeroChildThirdI3Cap_bGain_coeff_one68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) -
      6 * (ratFuncAtHahn46 root G).coeff (1 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) -
      12 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) -
      12 * (ratFuncAtHahn46 root F).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) -
      9 * epsilon * (ratFuncAtHahn46 root C).coeff (1 : ℚ) = 0 := by
  let AL : LaurentSeries k := ratFuncAtLaurent46 root A
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hAcast : ((-2 : ℤ) : ℚ) = (-2 : ℚ) := by norm_num
  have hA' := hA
  rw [← hAcast] at hA'
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA'
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 2 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G 0 hG
  have hC3g : (↑(0 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (3 * gamma) : LaurentSeries k).orderTop := by
    rw [HahnSeries.C_apply]
    by_cases hc0 : 3 * gamma = 0 <;> simp [hc0, HahnSeries.orderTop_single]
  have hSLord : (↑(0 : ℤ) : WithTop ℤ) ≤ SL.orderTop := by
    dsimp only [SL]
    have h2 : (↑(0 : ℤ) : WithTop ℤ) ≤ (2 * CL).orderTop := by
      rw [two_mul]
      exact le_trans (le_min hCL hCL)
        HahnSeries.min_orderTop_le_orderTop_add
    exact le_trans (le_min h2 hC3g)
      HahnSeries.min_orderTop_le_orderTop_add
  have hABord : (↑(0 : ℤ) : WithTop ℤ) ≤ (AL * BL).orderTop := by
    have hidx : (0 : ℤ) = -2 + 2 := by norm_num
    rw [hidx, WithTop.coe_add]
    exact le_trans (add_le_add hAL hBL)
      HahnSeries.orderTop_add_le_mul
  have hABF := laurent_coeff_mul_lower_succ68 (AL * BL) FL 0 0
    hABord hFL
  norm_num at hABF
  have hAB0 := laurent_coeff_mul_lower68 AL BL (-2) 2 hAL hBL
  norm_num at hAB0
  have hAB1 := laurent_coeff_mul_lower_succ68 AL BL (-2) 2 hAL hBL
  norm_num at hAB1
  rw [hAB0, hAB1] at hABF
  have hSG := laurent_coeff_mul_lower_succ68 SL Gser 0 0 hSLord hGL
  norm_num at hSG
  have hBsqOrder : (↑(4 : ℤ) : WithTop ℤ) ≤ (BL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hBL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hBsq1 : (BL ^ 2).coeff (1 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBsqOrder)
  have hB2Cord : (↑(4 : ℤ) : WithTop ℤ) ≤ (BL ^ 2 * CL).orderTop := by
    have hidx : (4 : ℤ) = 4 + 0 := by norm_num
    rw [hidx, WithTop.coe_add]
    exact le_trans (add_le_add hBsqOrder hCL)
      HahnSeries.orderTop_add_le_mul
  have hB2C : (BL ^ 2 * CL).coeff (1 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB2Cord)
  have hFsq := laurent_coeff_mul_lower_succ68 FL FL 0 0 hFL hFL
  norm_num at hFsq
  have hF2 : (FL ^ 2).coeff (1 : ℤ) =
      FL.coeff 0 * FL.coeff 1 + FL.coeff 1 * FL.coeff 0 := by
    rw [pow_two, hFsq]
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) AL BL CL FL Gser = HahnSeries.C i3 := by
    simpa only [rhoOneI3CapFactored68, AL, BL, CL, FL, Gser,
      map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      map_zero, map_one, ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI3CapFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (1 : ℤ))
    hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc89 : (-8 / 9 : LaurentSeries k) =
      HahnSeries.C (-8 / 9 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc89' : (8 / 9 : LaurentSeries k) = HahnSeries.C (8 / 9 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc23 : (2 / 3 : LaurentSeries k) = HahnSeries.C (2 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hsc1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff (1 : ℤ) =
      (-8 / 9 : k) * (AL * BL * FL).coeff (1 : ℤ) := by
    have hform : (-8 / 9 : LaurentSeries k) * AL * BL * FL =
        HahnSeries.C (-8 / 9 : k) * (AL * BL * FL) := by
      rw [← hc89]
      ring
    rw [hform, hscale]
  have hsc2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff (1 : ℤ) =
      (8 / 9 : k) * (BL ^ 2 * CL).coeff (1 : ℤ) := by
    have hform : (8 / 9 : LaurentSeries k) * BL ^ 2 * CL =
        HahnSeries.C (8 / 9 : k) * (BL ^ 2 * CL) := by
      rw [← hc89']
      ring
    rw [hform, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff (1 : ℤ) =
      (4 / 3 : k) * (SL * Gser).coeff (1 : ℤ) := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff (1 : ℤ) =
      (4 / 3 : k) * (FL ^ 2).coeff (1 : ℤ) := by
    rw [hc43, hscale]
  have hsc5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma *
      BL ^ 2).coeff (1 : ℤ) =
      (2 / 3 * gamma : k) * (BL ^ 2).coeff (1 : ℤ) := by
    rw [hc23, ← map_mul, hscale]
  have hsc6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon *
      CL).coeff (1 : ℤ) = (2 * epsilon) * CL.coeff (1 : ℤ) := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hsc5, hsc6] at hc
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff (1 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hABF, hB2C, hSG, hF2, hBsq1, hright] at hc
  have hSL0 : SL.coeff (0 : ℤ) = 2 * CL.coeff (0 : ℤ) + 3 * gamma := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL1 : SL.coeff (1 : ℤ) = 2 * CL.coeff (1 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1] at hc
  have hA2 := ratFuncAtHahn46_coeff_int68 root A (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 root A (-1)
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  norm_num at hA2 hA1 hB2 hB3 hC0 hC1 hF0 hF1 hG0 hG1
  dsimp only [AL, BL, CL, FL, Gser] at hc
  rw [← hA2, ← hA1, ← hB2, ← hB3, ← hC0, ← hC1, ← hF0, ← hF1, ← hG0,
    ← hG1] at hc
  linear_combination (-9 / 2 : k) * hc

/-- The coefficient-one `I₃` row on the `F`-gain child, consumed at the
Laurent level: the `ABF` block carries the three combinations of the
shifted box `ord B ≥ 1`, `ord F ≥ 1`, and the `F²` block stays silent
alongside both `B²` blocks. -/
theorem rhoOneGZeroChildThirdI3Cap_fGain_coeff_one68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) -
      6 * (ratFuncAtHahn46 root G).coeff (1 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) -
      12 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) -
      9 * epsilon * (ratFuncAtHahn46 root C).coeff (1 : ℚ) = 0 := by
  let AL : LaurentSeries k := ratFuncAtLaurent46 root A
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hAcast : ((-2 : ℤ) : ℚ) = (-2 : ℚ) := by norm_num
  have hA' := hA
  rw [← hAcast] at hA'
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA'
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 1 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 1 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G 0 hG
  have hC3g : (↑(0 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (3 * gamma) : LaurentSeries k).orderTop := by
    rw [HahnSeries.C_apply]
    by_cases hc0 : 3 * gamma = 0 <;> simp [hc0, HahnSeries.orderTop_single]
  have hSLord : (↑(0 : ℤ) : WithTop ℤ) ≤ SL.orderTop := by
    dsimp only [SL]
    have h2 : (↑(0 : ℤ) : WithTop ℤ) ≤ (2 * CL).orderTop := by
      rw [two_mul]
      exact le_trans (le_min hCL hCL)
        HahnSeries.min_orderTop_le_orderTop_add
    exact le_trans (le_min h2 hC3g)
      HahnSeries.min_orderTop_le_orderTop_add
  have hABord : (↑(-1 : ℤ) : WithTop ℤ) ≤ (AL * BL).orderTop := by
    have hidx : (-1 : ℤ) = -2 + 1 := by norm_num
    rw [hidx, WithTop.coe_add]
    exact le_trans (add_le_add hAL hBL)
      HahnSeries.orderTop_add_le_mul
  have hABF := laurent_coeff_mul_lower_succ68 (AL * BL) FL (-1) 1
    hABord hFL
  norm_num at hABF
  have hABm1 := laurent_coeff_mul_lower68 AL BL (-2) 1 hAL hBL
  norm_num at hABm1
  have hAB0 := laurent_coeff_mul_lower_succ68 AL BL (-2) 1 hAL hBL
  norm_num at hAB0
  rw [hABm1, hAB0] at hABF
  have hSG := laurent_coeff_mul_lower_succ68 SL Gser 0 0 hSLord hGL
  norm_num at hSG
  have hBsqOrder : (↑(2 : ℤ) : WithTop ℤ) ≤ (BL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hBL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hBsq1 : (BL ^ 2).coeff (1 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBsqOrder)
  have hB2Cord : (↑(2 : ℤ) : WithTop ℤ) ≤ (BL ^ 2 * CL).orderTop := by
    have hidx : (2 : ℤ) = 2 + 0 := by norm_num
    rw [hidx, WithTop.coe_add]
    exact le_trans (add_le_add hBsqOrder hCL)
      HahnSeries.orderTop_add_le_mul
  have hB2C : (BL ^ 2 * CL).coeff (1 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB2Cord)
  have hFsqOrder : (↑(2 : ℤ) : WithTop ℤ) ≤ (FL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := FL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hFL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hF2 : (FL ^ 2).coeff (1 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hFsqOrder)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) AL BL CL FL Gser = HahnSeries.C i3 := by
    simpa only [rhoOneI3CapFactored68, AL, BL, CL, FL, Gser,
      map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      map_zero, map_one, ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI3CapFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (1 : ℤ))
    hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc89 : (-8 / 9 : LaurentSeries k) =
      HahnSeries.C (-8 / 9 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc89' : (8 / 9 : LaurentSeries k) = HahnSeries.C (8 / 9 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc23 : (2 / 3 : LaurentSeries k) = HahnSeries.C (2 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hsc1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff (1 : ℤ) =
      (-8 / 9 : k) * (AL * BL * FL).coeff (1 : ℤ) := by
    have hform : (-8 / 9 : LaurentSeries k) * AL * BL * FL =
        HahnSeries.C (-8 / 9 : k) * (AL * BL * FL) := by
      rw [← hc89]
      ring
    rw [hform, hscale]
  have hsc2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff (1 : ℤ) =
      (8 / 9 : k) * (BL ^ 2 * CL).coeff (1 : ℤ) := by
    have hform : (8 / 9 : LaurentSeries k) * BL ^ 2 * CL =
        HahnSeries.C (8 / 9 : k) * (BL ^ 2 * CL) := by
      rw [← hc89']
      ring
    rw [hform, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff (1 : ℤ) =
      (4 / 3 : k) * (SL * Gser).coeff (1 : ℤ) := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff (1 : ℤ) =
      (4 / 3 : k) * (FL ^ 2).coeff (1 : ℤ) := by
    rw [hc43, hscale]
  have hsc5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma *
      BL ^ 2).coeff (1 : ℤ) =
      (2 / 3 * gamma : k) * (BL ^ 2).coeff (1 : ℤ) := by
    rw [hc23, ← map_mul, hscale]
  have hsc6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon *
      CL).coeff (1 : ℤ) = (2 * epsilon) * CL.coeff (1 : ℤ) := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hsc5, hsc6] at hc
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff (1 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hABF, hB2C, hSG, hF2, hBsq1, hright] at hc
  have hSL0 : SL.coeff (0 : ℤ) = 2 * CL.coeff (0 : ℤ) + 3 * gamma := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL1 : SL.coeff (1 : ℤ) = 2 * CL.coeff (1 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1] at hc
  have hA2 := ratFuncAtHahn46_coeff_int68 root A (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 root A (-1)
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2' := ratFuncAtHahn46_coeff_int68 root F 2
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  norm_num at hA2 hA1 hB1 hB2 hC0 hC1 hF1 hF2' hG0 hG1
  dsimp only [AL, BL, CL, FL, Gser] at hc
  rw [← hA2, ← hA1, ← hB1, ← hB2, ← hC0, ← hC1, ← hF1, ← hF2', ← hG0,
    ← hG1] at hc
  linear_combination (-9 / 2 : k) * hc

/-- On the affine tail `2C[0]+3γ = 0` with the `C[1] = 0` face the new
`B`-gain `I₃` row degenerates to a scalar tie between the descended
`ABF` jet and the `F` boundary square.  Recorded as a scalar corollary;
the packet keeps the full row. -/
theorem rhoOneGZeroChildThird_bGain_affine_tail_tie68
    (gamma epsilon a2 a1 b2 b3 c0 c1 f0 f1 g0 g1 : k)
    (htie : 4 * a2 * b2 * f1 + 4 * a2 * b3 * f0 + 4 * a1 * b2 * f0 -
      6 * g1 * (2 * c0 + 3 * gamma) - 12 * c1 * g0 - 12 * f0 * f1 -
      9 * epsilon * c1 = 0)
    (hS0 : 2 * c0 + 3 * gamma = 0) (hc1 : c1 = 0) :
    a2 * b2 * f1 + a2 * b3 * f0 + a1 * b2 * f0 = 3 * f0 * f1 := by
  linear_combination (1 / 4 : k) * htie + (3 / 2 : k) * g1 * hS0 +
    (3 * g0 + (9 / 4 : k) * epsilon) * hc1

/-- The `B`-gain child refined through its third unused rows: the
imported refinement is kept verbatim, and the coefficient-three `I₄`
row and the coefficient-one `I₃` row are added globally. -/
def RhoOneGZeroChildBGainRefinedThird68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildBGainRefinedNext68 gamma epsilon A0R B0R C00R D0R E0R
      A B C F G ∧
    (4 * B.coeff (2 : ℚ) * G.coeff (1 : ℚ) +
        4 * B.coeff (3 : ℚ) * G.coeff (0 : ℚ) +
        2 * F.coeff (3 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        4 * C.coeff (1 : ℚ) * F.coeff (2 : ℚ) +
        4 * C.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        4 * C.coeff (3 : ℚ) * F.coeff (0 : ℚ) +
        3 * epsilon * B.coeff (3 : ℚ) = 0) ∧
    (4 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (3 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (2 : ℚ) * F.coeff (0 : ℚ) -
        6 * G.coeff (1 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) -
        12 * C.coeff (1 : ℚ) * G.coeff (0 : ℚ) -
        12 * F.coeff (0 : ℚ) * F.coeff (1 : ℚ) -
        9 * epsilon * C.coeff (1 : ℚ) = 0)

/-- The `F`-gain child refined through its third unused rows: the
imported refinement is kept verbatim, and the coefficient-three `I₄`
row (with the live cube boundary `B[1]³`) and the coefficient-one `I₃`
row are added globally. -/
def RhoOneGZeroChildFGainRefinedThird68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildFGainRefinedNext68 gamma epsilon A0R B0R C00R D0R E0R
      A B C F G ∧
    (-4 * B.coeff (1 : ℚ) ^ 3 +
        36 * B.coeff (1 : ℚ) * G.coeff (2 : ℚ) +
        36 * B.coeff (2 : ℚ) * G.coeff (1 : ℚ) +
        36 * B.coeff (3 : ℚ) * G.coeff (0 : ℚ) +
        18 * F.coeff (3 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        36 * C.coeff (1 : ℚ) * F.coeff (2 : ℚ) +
        36 * C.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        27 * epsilon * B.coeff (3 : ℚ) = 0) ∧
    (4 * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (1 : ℚ) * F.coeff (1 : ℚ) -
        6 * G.coeff (1 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) -
        12 * C.coeff (1 : ℚ) * G.coeff (0 : ℚ) -
        9 * epsilon * C.coeff (1 : ℚ) = 0)

/-- Source backwire: the derivative-next residual with its preserved
`G[-1] = 0` sibling refined child by child through the third unused
coefficient rows. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenThirdResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextResidual68
        T.root j T.source.gamma T.source.epsilon
        (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneGZeroChildBGainRefinedThird68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G ∨
         RhoOneGZeroChildFGainRefinedThird68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G)) := by
  dsimp only [RhoOneGZeroChildBGainRefinedThird68,
    RhoOneGZeroChildFGainRefinedThird68]
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenNextResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hprev
  rcases hprev with hres | ⟨hg, hG0, hchild⟩
  · exact Or.inl hres
  · right
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    have hCRraw : ratFuncAtHahn46 T.root CR =
        rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0) := by
      dsimp only [CR, AR, rhoOneCDefectHahn68]
      simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
    have hFRraw : ratFuncAtHahn46 T.root FR =
        rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D) := by
      dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
      simp only [map_sub, map_mul, ratFuncAtHahn46_C]
    have hGRraw : ratFuncAtHahn46 T.root GR =
        rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E)) := by
      dsimp only [GR, CR, AR, rhoOneTangentEDefectHahn68,
        rhoOneCDefectHahn68, rhoOneEDefectHahn68]
      simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
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
          simpa only [RatFunc.algebraMap_eq_C] using
            T.source.bracket_eq)
    rw [hbeta, hdelta, hzeta] at hi4raw hi3raw
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
    have hCH : (0 : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root CR).orderTop := by
      rw [hCRraw]
      exact hC
    have hFH : (0 : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root FR).orderTop := by
      rw [hFRraw]
      exact hF
    have hGH : (0 : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root GR).orderTop := by
      rw [hGRraw]
      exact hG0
    have hi4T : firstIntegralFour68 0 AR BR (AR ^ 2 / 3 + CR)
        (AR * BR / 3 + FR) (AR ^ 3 / 27 + AR * CR / 3 + GR)
        0 (RatFunc.C T.source.gamma) 0 (RatFunc.C T.source.epsilon)
        0 = RatFunc.C i4 := by
      rw [hCrec, hDrec, hErec]
      simpa only [AR, BR, RatFunc.algebraMap_eq_C, map_zero]
        using hi4raw
    have hload := firstIntegralFour_gZeroChild_load_factor68
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      AR BR CR FR GR (RatFunc.C i4) hi4T
    have hi3T : firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR)
        (AR * BR / 3 + FR) (AR ^ 3 / 27 + AR * CR / 3 + GR)
        0 (RatFunc.C T.source.gamma) 0 (RatFunc.C T.source.epsilon)
        0 = RatFunc.C i3 := by
      rw [hCrec, hDrec, hErec]
      simpa only [AR, BR, RatFunc.algebraMap_eq_C, map_zero]
        using hi3raw
    have hi3R := firstIntegralThree_cap_factor68
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      AR BR CR FR GR (RatFunc.C i3) hi3T
    refine ⟨hg, hG0, ?_⟩
    rcases hchild with hBgain | hFgain
    · left
      have hBgain' := hBgain
      dsimp only [RhoOneGZeroChildBGainRefinedNext68,
        RhoOneGZeroChildBGainRefined68] at hBgain'
      have hB2H : (↑(2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hBgain'.1.1.1
      have htie4 := rhoOneGZeroChildThirdI4Load_bGain_coeff_three68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hB2H hCH hFH hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
      have htie3 := rhoOneGZeroChildThirdI3Cap_bGain_coeff_one68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH hB2H hCH hFH hGH hi3R
      rw [hCRraw, hFRraw, hGRraw] at htie3
      simp only [AR, BR] at htie3
      exact ⟨hBgain, htie4, htie3⟩
    · right
      have hFgain' := hFgain
      dsimp only [RhoOneGZeroChildFGainRefinedNext68,
        RhoOneGZeroChildFGainRefined68] at hFgain'
      have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hB
      have hFH1 : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root FR).orderTop := by
        rw [hFRraw]
        exact hFgain'.1.1.1
      have htie4 := rhoOneGZeroChildThirdI4Load_fGain_coeff_three68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hBH hCH hFH1 hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
      have htie3 := rhoOneGZeroChildThirdI3Cap_fGain_coeff_one68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH hBH hCH hFH1 hGH hi3R
      rw [hCRraw, hFRraw, hGRraw] at htie3
      simp only [AR, BR] at htie3
      exact ⟨hFgain, htie4, htie3⟩

#print axioms laurent_coeff_mul_lower_three_gZeroChildThird68
#print axioms rhoOneGZeroChildThirdI4Load_bGain_coeff_three68
#print axioms rhoOneGZeroChildThirdI4Load_fGain_coeff_three68
#print axioms rhoOneGZeroChildThirdI3Cap_bGain_coeff_one68
#print axioms rhoOneGZeroChildThirdI3Cap_fGain_coeff_one68
#print axioms rhoOneGZeroChildThird_bGain_affine_tail_tie68
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenThirdResidual

end AlignedSquareGZeroChildThird68

end Max11DegreeRoutes
