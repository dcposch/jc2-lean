import Fable68ScaleTwoAlignedSquareGZeroChildScratch

/-! # The next unused rows on the refined `G[-1] = 0` children

The `G`-zero-child residual keeps the `G[-1] = 0` sibling as the refined
disjunction `BGainRefined ∨ FGainRefined`.  On that sibling the exact
next unused rows are the coefficient-zero `I₃` load row on the `B`-gain
child and the coefficient-two `I₄` row on both children:

* On the `B`-gain child (box `ord A ≥ -2`, `ord B ≥ 2`, `ord C ≥ 0`,
  `ord F ≥ 0`, `ord G ≥ 0`) the coefficient-zero `I₃` row is a load row:
  every surviving monomial pinches to a single boundary combination and
  `9·i3 = -8·A[-2]B[2]F[0] + 12·G[0]·(2C[0]+3γ) + 12·F[0]² + 18·ε·C[0]`.

* The coefficient-two `I₄` row is a genuine multi-combination Laurent
  jet.  On the `B`-gain child it reads
  `4B[2]G[0] + 2F[2]·(2C[0]+3γ) + 4C[1]F[1] + 4C[2]F[0] + 3εB[2] = 0`
  (the `(2C+3γ)F` block contributes all three combinations), while on
  the `F`-gain child (box `ord B ≥ 1`, `ord F ≥ 1`) it reads
  `4B[1]G[1] + 4B[2]G[0] + 2F[2]·(2C[0]+3γ) + 4C[1]F[1] + 3εB[2] = 0`
  (the `BG` block now contributes two combinations).

On the affine tail `2C[0]+3γ = 0` with the `F₀`-gain re-entry the new
load row pins the ground third integral to `i3 = -3εγ`; this scalar
consequence is recorded as a standalone corollary and not wired into
the packet, so the tail disjunction of the imported refinement stays
verbatim.  The nonzero `G[-1]` boundary lane, the `C₂` face, and the
quadratic rays remain literally inside the imported derivative-next
residual. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareGZeroChildNext68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareGZeroChildNextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The coefficient two integral jet above the lower face of a Laurent
product, restated locally for the `G`-zero-child-next lane. -/
theorem laurent_coeff_mul_lower_two_gZeroChildNext68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 2) =
      X.coeff m * Y.coeff (n + 2) +
        X.coeff (m + 1) * Y.coeff (n + 1) +
          X.coeff (m + 2) * Y.coeff n := by
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
  have htail := laurent_coeff_mul_lower_succ68 Xt Y (m + 1) n hXt hY
  have htail' : (Xt * Y).coeff (m + n + 2) =
      Xt.coeff (m + 1) * Y.coeff (n + 1) +
        Xt.coeff (m + 2) * Y.coeff n := by
    convert htail using 1 <;> ring
  have hXt1 : Xt.coeff (m + 1) = X.coeff (m + 1) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt2 : Xt.coeff (m + 2) = X.coeff (m + 2) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hlead :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Y).coeff
          (m + n + 2) = X.coeff m * Y.coeff (n + 2) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 2 - m = n + 2 := by omega
    rw [hi]
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by simp [Xt]
  calc
    (X * Y).coeff (m + n + 2) =
        ((HahnSeries.single m (X.coeff m) + Xt) * Y).coeff
          (m + n + 2) := by rw [← hXdec]
    _ = _ := by
      rw [add_mul, HahnSeries.coeff_add, hlead, htail', hXt1, hXt2]
      ring

/-- The coefficient-two `I₄` row on the `B`-gain child: with `ord B ≥ 2`
the `BG` block pinches to `B[2]G[0]`, the `(2C+3γ)F` block carries all
three integral combinations, and the cube stays silent. -/
theorem rhoOneGZeroChildNextI4Load_bGain_coeff_two68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneGZeroChildI4LoadFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    4 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      2 * (ratFuncAtHahn46 root F).coeff (2 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      4 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff (2 : ℚ) = 0 := by
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
  have hSF := laurent_coeff_mul_lower_two_gZeroChildNext68 SL FL 0 0
    hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower68 BL Gser 2 0 hBL hGL
  norm_num at hBG
  have hBcubeOrder : (↑(6 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (2 : ℤ) = 0 :=
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (2 : ℤ))
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
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 2 =
      (-8 / 27 : k) * (BL ^ 3).coeff 2 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 2 =
      (8 / 3 : k) * (BL * Gser).coeff 2 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 2 =
      (4 / 3 : k) * (SL * FL).coeff 2 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 2 =
      (2 * epsilon) * BL.coeff 2 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (2 : ℤ) = 0 := by
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
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  norm_num at hB2 hC0 hC1 hC2 hF0 hF1 hF2 hG0
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB2, ← hC0, ← hC1, ← hC2, ← hF0, ← hF1, ← hF2, ← hG0] at hc
  linear_combination (3 / 2 : k) * hc

/-- The coefficient-two `I₄` row on the `F`-gain child: with `ord B ≥ 1`
and `ord F ≥ 1` both the `BG` and the `(2C+3γ)F` blocks carry exactly
two integral combinations. -/
theorem rhoOneGZeroChildNextI4Load_fGain_coeff_two68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneGZeroChildI4LoadFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    4 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      2 * (ratFuncAtHahn46 root F).coeff (2 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      4 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff (2 : ℚ) = 0 := by
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
  have hSF := laurent_coeff_mul_lower_succ68 SL FL 0 1 hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower_succ68 BL Gser 1 0 hBL hGL
  norm_num at hBG
  have hBcubeOrder : (↑(3 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (2 : ℤ) = 0 :=
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (2 : ℤ))
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
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 2 =
      (-8 / 27 : k) * (BL ^ 3).coeff 2 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 2 =
      (8 / 3 : k) * (BL * Gser).coeff 2 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 2 =
      (4 / 3 : k) * (SL * FL).coeff 2 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 2 =
      (2 * epsilon) * BL.coeff 2 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (2 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hBcube, hBG, hSF, hright] at hc
  have hSL0 : SL.coeff (0 : ℤ) = 2 * CL.coeff (0 : ℤ) + 3 * gamma := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL1 : SL.coeff (1 : ℤ) = 2 * CL.coeff (1 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1] at hc
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  norm_num at hB1 hB2 hC0 hC1 hF1 hF2 hG0 hG1
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB1, ← hB2, ← hC0, ← hC1, ← hF1, ← hF2, ← hG0, ← hG1] at hc
  linear_combination (3 / 2 : k) * hc

/-- The coefficient-zero `I₃` row on the `B`-gain child: in the box
`ord A ≥ -2`, `ord B ≥ 2`, `ord C ≥ 0`, `ord F ≥ 0`, `ord G ≥ 0` every
surviving monomial pinches to a single boundary combination and the row
records the ground third-integral load. -/
theorem rhoOneI3CapFactored_gZeroChildNext_bGain_coeff_zero68
    (gamma epsilon i3 : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (0 : WithTop ℚ) ≤ G.orderTop)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    9 * i3 =
      -8 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (0 : ℚ) +
        12 * G.coeff (0 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        12 * F.coeff (0 : ℚ) ^ 2 + 18 * epsilon * C.coeff (0 : ℚ) := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (0 : WithTop ℚ) ≤ S.orderTop := by
    dsimp only [S]
    refine hahnOrderTop_add_nonneg46 _ _ ?_ (hahnOrderTop_C_nonneg46 _)
    rw [two_mul]
    exact hahnOrderTop_add_nonneg46 _ _ hC hC
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (0 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (0 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 0
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
  have hABFraw := lead (-8 / 9 : k) A B F C G 1 1 1 0 0
    (-2) 2 0 0 0 hA hB hF hC hG
  have hABF :
      (weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0).coeff
          (0 : ℚ) =
        (-8 / 9 : k) * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) *
          F.coeff (0 : ℚ) := by
    convert hABFraw using 1 <;> norm_num
  have hB2C := hz (-8 / 9 : k) B C A F G 2 1 0 0 0
    2 0 (-2) 0 0 hB hC hA hF hG (by norm_num)
  have hSGraw := lead (4 / 3 : k) S G A B F 1 1 0 0 0
    0 0 (-2) 2 0 hS' hG hA hB hF
  have hSG :
      (weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0).coeff
          (0 : ℚ) =
        (4 / 3 : k) * S.coeff (0 : ℚ) * G.coeff (0 : ℚ) := by
    convert hSGraw using 1 <;> norm_num
  have hF2raw := lead (4 / 3 : k) F A B C G 2 0 0 0 0
    0 (-2) 2 0 0 hF hA hB hC hG
  have hF2 :
      (weightedMonomial68 (4 / 3 : k) F A B C G 2 0 0 0 0).coeff
          (0 : ℚ) =
        (4 / 3 : k) * F.coeff (0 : ℚ) ^ 2 := by
    convert hF2raw using 1 <;> norm_num
  have hgammaB2 := hz (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0
    2 (-2) 0 0 0 hB hA hC hF hG (by norm_num)
  have hepsCraw := lead (2 * epsilon) C A B F G 1 0 0 0 0
    0 (-2) 2 0 0 hC hA hB hF hG
  have hepsC :
      (weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0).coeff
          (0 : ℚ) =
        2 * epsilon * C.coeff (0 : ℚ) := by
    convert hepsCraw using 1 <;> norm_num
  have hright : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (0 : ℚ) = i3 := by
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
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff (0 : ℚ)) hi3
  rw [hrewrite] at hc
  simp only [HahnSeries.coeff_add] at hc
  rw [hABF, hB2C, hSG, hF2, hgammaB2, hepsC, hright] at hc
  have hSco : S.coeff (0 : ℚ) = 2 * C.coeff (0 : ℚ) + 3 * gamma := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff (0 : ℚ) = 2 * C.coeff (0 : ℚ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hSco] at hc
  linear_combination (-9 : k) * hc

/-- On the affine tail `2C[0]+3γ = 0` with the `F₀`-gain re-entry the
new load row pins the ground third integral to `i3 = -3εγ`.  Recorded
as a scalar corollary; the packet keeps the full load row. -/
theorem rhoOneGZeroChildNext_bGain_affine_tail_load68
    (gamma epsilon i3 a2 b2 c0 f0 g0 : k)
    (htie : 9 * i3 = -8 * a2 * b2 * f0 +
      12 * g0 * (2 * c0 + 3 * gamma) + 12 * f0 ^ 2 + 18 * epsilon * c0)
    (hS0 : 2 * c0 + 3 * gamma = 0) (hf0 : f0 = 0) :
    i3 = -3 * epsilon * gamma := by
  linear_combination (1 / 9 : k) * htie +
    ((4 / 3 : k) * g0 + epsilon) * hS0 +
    (-(8 / 9 : k) * a2 * b2 + (4 / 3 : k) * f0) * hf0

/-- The `B`-gain child refined through its next unused rows: the
imported refinement is kept verbatim, the coefficient-two `I₄` row is
added globally, and the coefficient-zero `I₃` load row pins the ground
third integral. -/
def RhoOneGZeroChildBGainRefinedNext68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildBGainRefined68 gamma B C F ∧
    (4 * B.coeff (2 : ℚ) * G.coeff (0 : ℚ) +
        2 * F.coeff (2 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        4 * C.coeff (1 : ℚ) * F.coeff (1 : ℚ) +
        4 * C.coeff (2 : ℚ) * F.coeff (0 : ℚ) +
        3 * epsilon * B.coeff (2 : ℚ) = 0) ∧
    ∃ i3 : k,
      firstIntegralThree68 0 A0R B0R C00R D0R E0R (RatFunc.C (0 : k))
          (RatFunc.C gamma) (RatFunc.C (0 : k)) (RatFunc.C epsilon)
          (RatFunc.C (0 : k)) = RatFunc.C i3 ∧
      9 * i3 =
        -8 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (0 : ℚ) +
          12 * G.coeff (0 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
          12 * F.coeff (0 : ℚ) ^ 2 + 18 * epsilon * C.coeff (0 : ℚ)

/-- The `F`-gain child refined through its next unused row: the imported
refinement is kept verbatim and the coefficient-two `I₄` row is added
globally. -/
def RhoOneGZeroChildFGainRefinedNext68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildFGainRefined68 gamma epsilon A0R B0R C00R D0R E0R
      A B C F G ∧
    4 * B.coeff (1 : ℚ) * G.coeff (1 : ℚ) +
      4 * B.coeff (2 : ℚ) * G.coeff (0 : ℚ) +
      2 * F.coeff (2 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
      4 * C.coeff (1 : ℚ) * F.coeff (1 : ℚ) +
      3 * epsilon * B.coeff (2 : ℚ) = 0

/-- Source backwire: the derivative-next residual with its preserved
`G[-1] = 0` sibling refined child by child through the next unused
coefficient rows. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenNextResidual
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
        (RhoOneGZeroChildBGainRefinedNext68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G ∨
         RhoOneGZeroChildFGainRefinedNext68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G)) := by
  dsimp only [RhoOneGZeroChildBGainRefinedNext68,
    RhoOneGZeroChildFGainRefinedNext68]
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenResidual
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
    refine ⟨hg, hG0, ?_⟩
    rcases hchild with hBgain | hFgain
    · left
      have hBgain' := hBgain
      dsimp only [RhoOneGZeroChildBGainRefined68] at hBgain'
      have hB2H : (↑(2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hBgain'.1.1
      have htie4 := rhoOneGZeroChildNextI4Load_bGain_coeff_two68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hB2H hCH hFH hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
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
      have hi3Hraw := congrArg (ratFuncAtHahn46 T.root) hi3R
      have hi3H : rhoOneI3CapFactored68
          (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.epsilon)
          (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
          (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
          (ratFuncAtHahn46 T.root GR) = HahnSeries.C i3 := by
        simpa only [rhoOneI3CapFactored68, map_add, map_sub,
          map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero,
          map_one, RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C]
          using hi3Hraw
      have htie3 := rhoOneI3CapFactored_gZeroChildNext_bGain_coeff_zero68
        T.source.gamma T.source.epsilon i3
        (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
        (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
        (ratFuncAtHahn46 T.root GR) hAH hB2H hCH hFH hGH hi3H
      rw [hCRraw, hFRraw, hGRraw] at htie3
      simp only [AR, BR] at htie3
      have hi3source : firstIntegralThree68 0 T.source.A T.source.B
          T.source.C0 T.source.D T.source.E (RatFunc.C (0 : k))
          (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
          (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) =
          RatFunc.C i3 := by
        simpa only [RatFunc.algebraMap_eq_C, map_zero] using hi3raw
      exact ⟨hBgain, htie4, i3, hi3source, htie3⟩
    · right
      have hFgain' := hFgain
      dsimp only [RhoOneGZeroChildFGainRefined68] at hFgain'
      have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hB
      have hFH1 : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root FR).orderTop := by
        rw [hFRraw]
        exact hFgain'.1.1
      have htie4 := rhoOneGZeroChildNextI4Load_fGain_coeff_two68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hBH hCH hFH1 hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
      exact ⟨hFgain, htie4⟩

#print axioms laurent_coeff_mul_lower_two_gZeroChildNext68
#print axioms rhoOneGZeroChildNextI4Load_bGain_coeff_two68
#print axioms rhoOneGZeroChildNextI4Load_fGain_coeff_two68
#print axioms rhoOneI3CapFactored_gZeroChildNext_bGain_coeff_zero68
#print axioms rhoOneGZeroChildNext_bGain_affine_tail_load68
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenNextResidual

end AlignedSquareGZeroChildNext68

end Max11DegreeRoutes
