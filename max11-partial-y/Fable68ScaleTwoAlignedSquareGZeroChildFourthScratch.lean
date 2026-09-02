import Fable68ScaleTwoAlignedSquareGZeroChildThirdScratch

/-! # The fourth unused rows on the refined `G[-1] = 0` children

The `G`-zero-child-third residual keeps the `G[-1] = 0` sibling as the
refined disjunction `BGainRefinedThird ∨ FGainRefinedThird`.  On that
sibling the exact next unused rows are the coefficient-four `I₄` row
and the coefficient-two `I₃` row, on both children:

* On the `B`-gain child (box `ord A ≥ -2`, `ord B ≥ 2`, `ord C ≥ 0`,
  `ord F ≥ 0`, `ord G ≥ 0`) the coefficient-four `I₄` row needs the
  five-combination jet on the `(2C+3γ)F` block and reads
  `4B[2]G[2] + 4B[3]G[1] + 4B[4]G[0] + 2F[4]·(2C[0]+3γ) + 4C[1]F[3] +
  4C[2]F[2] + 4C[3]F[1] + 4C[4]F[0] + 3εB[4] = 0` (the cube stays
  silent), while the coefficient-two `I₃` row carries the six `ABF`
  combinations `A[-2]B[2]F[2] + A[-2]B[3]F[1] + A[-1]B[2]F[1] +
  A[-2]B[4]F[0] + A[-1]B[3]F[0] + A[0]B[2]F[0]` — the first row of the
  lane to see `A[0]` — against `6G[2]·(2C[0]+3γ) + 12C[1]G[1] +
  12C[2]G[0] + 12F[0]F[2] + 6F[1]² + 9εC[2]`, with both `B²` blocks
  still silent.

* On the `F`-gain child (box `ord B ≥ 1`, `ord F ≥ 1`) the cube
  boundary deepens to `3B[1]²B[2]`:
  `-12B[1]²B[2] + 36B[1]G[3] + 36B[2]G[2] + 36B[3]G[1] + 36B[4]G[0] +
  18F[4]·(2C[0]+3γ) + 36C[1]F[3] + 36C[2]F[2] + 36C[3]F[1] + 27εB[4] =
  0`, and the coefficient-two `I₃` row is the first `I₃` row of this
  child where the `B²C` and `γB²` blocks come alive, entering as the
  compact factored load `(4C[0]+3γ)·B[1]²`:
  `4A[-2]B[1]F[3] + 4A[-2]B[2]F[2] + 4A[-1]B[1]F[2] + 4A[-2]B[3]F[1] +
  4A[-1]B[2]F[1] + 4A[0]B[1]F[1] + (4C[0]+3γ)B[1]² =
  6G[2]·(2C[0]+3γ) + 12C[1]G[1] + 12C[2]G[0] + 6F[1]² + 9εC[2]`.

Both `I₃` rows are consumed at the Laurent level through the reusable
five-term coefficient-convolution lemma and its shorter siblings.  The
strongest scalar consequence of combining the new rows with all prior
child rows is a `G`-jet-free minor on the `B`-gain affine tail: on
`2C[0]+3γ = 0` with the `C[1] = 0` face, eliminating `4G[0]+3ε`
between the (imported) coefficient-two `I₄` row and the new
coefficient-two `I₃` row yields
`2B[2]·(A[-2]B[2]F[2] + A[-2]B[3]F[1] + A[-1]B[2]F[1] + A[-2]B[4]F[0]
+ A[-1]B[3]F[0] + A[0]B[2]F[0]) = 3B[2](2F[0]F[2]+F[1]²) − 6C[2]²F[0]`
— the whole `G` boundary jet leaves the new `I₃` row.  This is
recorded as a standalone corollary and not wired into the packet, so
the tail disjunction of the imported refinement stays verbatim.  Both
children and every sibling are preserved: the nonzero `G[-1]` boundary
lane, the `C₂` face, and the quadratic rays remain literally inside
the imported derivative-next residual.  NEXT_UNUSED_ROW: the
coefficient-five `I₄` row and the coefficient-three `I₃` row, on both
children. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareGZeroChildFourth68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareGZeroChildFourthHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The coefficient four integral jet above the lower face of a Laurent
product, restated locally for the `G`-zero-child-fourth lane. -/
theorem laurent_coeff_mul_lower_four_gZeroChildFourth68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 4) =
      X.coeff m * Y.coeff (n + 4) +
        X.coeff (m + 1) * Y.coeff (n + 3) +
          X.coeff (m + 2) * Y.coeff (n + 2) +
            X.coeff (m + 3) * Y.coeff (n + 1) +
              X.coeff (m + 4) * Y.coeff n := by
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
  have htail := laurent_coeff_mul_lower_three_gZeroChildThird68 Xt Y
    (m + 1) n hXt hY
  have htail' : (Xt * Y).coeff (m + n + 4) =
      Xt.coeff (m + 1) * Y.coeff (n + 3) +
        Xt.coeff (m + 2) * Y.coeff (n + 2) +
          Xt.coeff (m + 3) * Y.coeff (n + 1) +
            Xt.coeff (m + 4) * Y.coeff n := by
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
  have hXt4 : Xt.coeff (m + 4) = X.coeff (m + 4) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hlead :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Y).coeff
          (m + n + 4) = X.coeff m * Y.coeff (n + 4) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 4 - m = n + 4 := by omega
    rw [hi]
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by simp [Xt]
  calc
    (X * Y).coeff (m + n + 4) =
        ((HahnSeries.single m (X.coeff m) + Xt) * Y).coeff
          (m + n + 4) := by rw [← hXdec]
    _ = _ := by
      rw [add_mul, HahnSeries.coeff_add, hlead, htail', hXt1, hXt2, hXt3,
        hXt4]
      ring

/-- The coefficient-four `I₄` row on the `B`-gain child: with
`ord B ≥ 2` the `BG` block carries three integral combinations, the
`(2C+3γ)F` block carries all five, and the cube stays silent. -/
theorem rhoOneGZeroChildFourthI4Load_bGain_coeff_four68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneGZeroChildI4LoadFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    4 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      2 * (ratFuncAtHahn46 root F).coeff (4 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      4 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff (4 : ℚ) = 0 := by
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
  have hSF := laurent_coeff_mul_lower_four_gZeroChildFourth68 SL FL 0 0
    hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower_two_gZeroChildNext68 BL Gser 2 0
    hBL hGL
  norm_num at hBG
  have hBcubeOrder : (↑(6 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (4 : ℤ) = 0 :=
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (4 : ℤ))
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
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 4 =
      (-8 / 27 : k) * (BL ^ 3).coeff 4 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 4 =
      (8 / 3 : k) * (BL * Gser).coeff 4 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 4 =
      (4 / 3 : k) * (SL * FL).coeff 4 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 4 =
      (2 * epsilon) * BL.coeff 4 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (4 : ℤ) = 0 := by
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
  have hSL4 : SL.coeff (4 : ℤ) = 2 * CL.coeff (4 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2, hSL3, hSL4] at hc
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hB4 := ratFuncAtHahn46_coeff_int68 root B 4
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hC3 := ratFuncAtHahn46_coeff_int68 root C 3
  have hC4 := ratFuncAtHahn46_coeff_int68 root C 4
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  norm_num at hB2 hB3 hB4 hC0 hC1 hC2 hC3 hC4 hF0 hF1 hF2 hF3 hF4
  norm_num at hG0 hG1 hG2
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB2, ← hB3, ← hB4, ← hC0, ← hC1, ← hC2, ← hC3, ← hC4, ← hF0,
    ← hF1, ← hF2, ← hF3, ← hF4, ← hG0, ← hG1, ← hG2] at hc
  linear_combination (3 / 2 : k) * hc

/-- The coefficient-four `I₄` row on the `F`-gain child: with
`ord B ≥ 1` and `ord F ≥ 1` the cube boundary deepens to `3B[1]²B[2]`
alongside the four-combination `BG` and `(2C+3γ)F` jets. -/
theorem rhoOneGZeroChildFourthI4Load_fGain_coeff_four68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneGZeroChildI4LoadFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    -12 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) ^ 2 *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      18 * (ratFuncAtHahn46 root F).coeff (4 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      36 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      27 * epsilon * (ratFuncAtHahn46 root B).coeff (4 : ℚ) = 0 := by
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
  have hSF := laurent_coeff_mul_lower_three_gZeroChildThird68 SL FL 0 1
    hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower_three_gZeroChildThird68 BL Gser 1 0
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
  have hsq2 := laurent_coeff_mul_lower68 BL BL 1 1 hBL hBL
  norm_num at hsq2
  have hsq3 := laurent_coeff_mul_lower_succ68 BL BL 1 1 hBL hBL
  norm_num at hsq3
  have hcubec := laurent_coeff_mul_lower_succ68 (BL * BL) BL 2 1
    hBsqOrder' hBL
  norm_num at hcubec
  have hBcube : (BL ^ 3).coeff (4 : ℤ) =
      3 * BL.coeff 1 ^ 2 * BL.coeff 2 := by
    have hpow : BL ^ 3 = BL * BL * BL := by ring
    rw [hpow, hcubec, hsq2, hsq3]
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (4 : ℤ))
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
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 4 =
      (-8 / 27 : k) * (BL ^ 3).coeff 4 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 4 =
      (8 / 3 : k) * (BL * Gser).coeff 4 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 4 =
      (4 / 3 : k) * (SL * FL).coeff 4 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 4 =
      (2 * epsilon) * BL.coeff 4 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (4 : ℤ) = 0 := by
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
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hB4 := ratFuncAtHahn46_coeff_int68 root B 4
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hC3 := ratFuncAtHahn46_coeff_int68 root C 3
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hG3 := ratFuncAtHahn46_coeff_int68 root G 3
  norm_num at hB1 hB2 hB3 hB4 hC0 hC1 hC2 hC3 hF1 hF2 hF3 hF4
  norm_num at hG0 hG1 hG2 hG3
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB1, ← hB2, ← hB3, ← hB4, ← hC0, ← hC1, ← hC2, ← hC3, ← hF1,
    ← hF2, ← hF3, ← hF4, ← hG0, ← hG1, ← hG2, ← hG3] at hc
  linear_combination (27 / 2 : k) * hc

/-- The coefficient-two `I₃` row on the `B`-gain child, consumed at the
Laurent level: the `ABF` block carries six integral combinations — the
first appearance of `A[0]` in this lane — while both `B²` blocks stay
silent. -/
theorem rhoOneGZeroChildFourthI3Cap_bGain_coeff_two68
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
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) -
      6 * (ratFuncAtHahn46 root G).coeff (2 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) -
      12 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) -
      12 * (ratFuncAtHahn46 root F).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) -
      6 * (ratFuncAtHahn46 root F).coeff (1 : ℚ) ^ 2 -
      9 * epsilon * (ratFuncAtHahn46 root C).coeff (2 : ℚ) = 0 := by
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
  have hABF := laurent_coeff_mul_lower_two_gZeroChildNext68 (AL * BL) FL
    0 0 hABord hFL
  norm_num at hABF
  have hAB0 := laurent_coeff_mul_lower68 AL BL (-2) 2 hAL hBL
  norm_num at hAB0
  have hAB1 := laurent_coeff_mul_lower_succ68 AL BL (-2) 2 hAL hBL
  norm_num at hAB1
  have hAB2 := laurent_coeff_mul_lower_two_gZeroChildNext68 AL BL (-2) 2
    hAL hBL
  norm_num at hAB2
  rw [hAB0, hAB1, hAB2] at hABF
  have hSG := laurent_coeff_mul_lower_two_gZeroChildNext68 SL Gser 0 0
    hSLord hGL
  norm_num at hSG
  have hBsqOrder : (↑(4 : ℤ) : WithTop ℤ) ≤ (BL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hBL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hBsq2 : (BL ^ 2).coeff (2 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBsqOrder)
  have hB2Cord : (↑(4 : ℤ) : WithTop ℤ) ≤ (BL ^ 2 * CL).orderTop := by
    have hidx : (4 : ℤ) = 4 + 0 := by norm_num
    rw [hidx, WithTop.coe_add]
    exact le_trans (add_le_add hBsqOrder hCL)
      HahnSeries.orderTop_add_le_mul
  have hB2C : (BL ^ 2 * CL).coeff (2 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB2Cord)
  have hFsq := laurent_coeff_mul_lower_two_gZeroChildNext68 FL FL 0 0
    hFL hFL
  norm_num at hFsq
  have hF2 : (FL ^ 2).coeff (2 : ℤ) =
      FL.coeff 0 * FL.coeff 2 + FL.coeff 1 * FL.coeff 1 +
        FL.coeff 2 * FL.coeff 0 := by
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (2 : ℤ))
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
  have hsc1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff (2 : ℤ) =
      (-8 / 9 : k) * (AL * BL * FL).coeff (2 : ℤ) := by
    have hform : (-8 / 9 : LaurentSeries k) * AL * BL * FL =
        HahnSeries.C (-8 / 9 : k) * (AL * BL * FL) := by
      rw [← hc89]
      ring
    rw [hform, hscale]
  have hsc2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff (2 : ℤ) =
      (8 / 9 : k) * (BL ^ 2 * CL).coeff (2 : ℤ) := by
    have hform : (8 / 9 : LaurentSeries k) * BL ^ 2 * CL =
        HahnSeries.C (8 / 9 : k) * (BL ^ 2 * CL) := by
      rw [← hc89']
      ring
    rw [hform, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff (2 : ℤ) =
      (4 / 3 : k) * (SL * Gser).coeff (2 : ℤ) := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff (2 : ℤ) =
      (4 / 3 : k) * (FL ^ 2).coeff (2 : ℤ) := by
    rw [hc43, hscale]
  have hsc5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma *
      BL ^ 2).coeff (2 : ℤ) =
      (2 / 3 * gamma : k) * (BL ^ 2).coeff (2 : ℤ) := by
    rw [hc23, ← map_mul, hscale]
  have hsc6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon *
      CL).coeff (2 : ℤ) = (2 * epsilon) * CL.coeff (2 : ℤ) := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hsc5, hsc6] at hc
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff (2 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hABF, hB2C, hSG, hF2, hBsq2, hright] at hc
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
  have hA2 := ratFuncAtHahn46_coeff_int68 root A (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 root A (-1)
  have hA0 := ratFuncAtHahn46_coeff_int68 root A 0
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hB4 := ratFuncAtHahn46_coeff_int68 root B 4
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2' := ratFuncAtHahn46_coeff_int68 root F 2
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  norm_num at hA2 hA1 hA0 hB2 hB3 hB4 hC0 hC1 hC2 hF0 hF1 hF2'
  norm_num at hG0 hG1 hG2
  dsimp only [AL, BL, CL, FL, Gser] at hc
  rw [← hA2, ← hA1, ← hA0, ← hB2, ← hB3, ← hB4, ← hC0, ← hC1, ← hC2,
    ← hF0, ← hF1, ← hF2', ← hG0, ← hG1, ← hG2] at hc
  linear_combination (-9 / 2 : k) * hc

/-- The coefficient-two `I₃` row on the `F`-gain child, consumed at the
Laurent level: the `ABF` block carries the six combinations of the
shifted box `ord B ≥ 1`, `ord F ≥ 1`, and the `B²C` and `γB²` blocks
come alive for the first time, entering as the compact factored load
`(4C[0]+3γ)·B[1]²`. -/
theorem rhoOneGZeroChildFourthI3Cap_fGain_coeff_two68
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
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      (4 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) ^ 2 -
      6 * (ratFuncAtHahn46 root G).coeff (2 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) -
      12 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) -
      6 * (ratFuncAtHahn46 root F).coeff (1 : ℚ) ^ 2 -
      9 * epsilon * (ratFuncAtHahn46 root C).coeff (2 : ℚ) = 0 := by
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
  have hABF := laurent_coeff_mul_lower_two_gZeroChildNext68 (AL * BL) FL
    (-1) 1 hABord hFL
  norm_num at hABF
  have hABm1 := laurent_coeff_mul_lower68 AL BL (-2) 1 hAL hBL
  norm_num at hABm1
  have hAB0 := laurent_coeff_mul_lower_succ68 AL BL (-2) 1 hAL hBL
  norm_num at hAB0
  have hAB1 := laurent_coeff_mul_lower_two_gZeroChildNext68 AL BL (-2) 1
    hAL hBL
  norm_num at hAB1
  rw [hABm1, hAB0, hAB1] at hABF
  have hSG := laurent_coeff_mul_lower_two_gZeroChildNext68 SL Gser 0 0
    hSLord hGL
  norm_num at hSG
  have hBsqOrder : (↑(2 : ℤ) : WithTop ℤ) ≤ (BL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hBL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hsq2c := laurent_coeff_mul_lower68 BL BL 1 1 hBL hBL
  norm_num at hsq2c
  have hBsq2 : (BL ^ 2).coeff (2 : ℤ) = BL.coeff 1 * BL.coeff 1 := by
    rw [pow_two, hsq2c]
  have hB2C := laurent_coeff_mul_lower68 (BL ^ 2) CL 2 0 hBsqOrder hCL
  norm_num at hB2C
  have hFsq2c := laurent_coeff_mul_lower68 FL FL 1 1 hFL hFL
  norm_num at hFsq2c
  have hF2 : (FL ^ 2).coeff (2 : ℤ) = FL.coeff 1 * FL.coeff 1 := by
    rw [pow_two, hFsq2c]
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (2 : ℤ))
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
  have hsc1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff (2 : ℤ) =
      (-8 / 9 : k) * (AL * BL * FL).coeff (2 : ℤ) := by
    have hform : (-8 / 9 : LaurentSeries k) * AL * BL * FL =
        HahnSeries.C (-8 / 9 : k) * (AL * BL * FL) := by
      rw [← hc89]
      ring
    rw [hform, hscale]
  have hsc2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff (2 : ℤ) =
      (8 / 9 : k) * (BL ^ 2 * CL).coeff (2 : ℤ) := by
    have hform : (8 / 9 : LaurentSeries k) * BL ^ 2 * CL =
        HahnSeries.C (8 / 9 : k) * (BL ^ 2 * CL) := by
      rw [← hc89']
      ring
    rw [hform, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff (2 : ℤ) =
      (4 / 3 : k) * (SL * Gser).coeff (2 : ℤ) := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff (2 : ℤ) =
      (4 / 3 : k) * (FL ^ 2).coeff (2 : ℤ) := by
    rw [hc43, hscale]
  have hsc5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma *
      BL ^ 2).coeff (2 : ℤ) =
      (2 / 3 * gamma : k) * (BL ^ 2).coeff (2 : ℤ) := by
    rw [hc23, ← map_mul, hscale]
  have hsc6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon *
      CL).coeff (2 : ℤ) = (2 * epsilon) * CL.coeff (2 : ℤ) := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hsc5, hsc6] at hc
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff (2 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hABF, hB2C, hSG, hF2, hBsq2, hright] at hc
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
  have hA2 := ratFuncAtHahn46_coeff_int68 root A (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 root A (-1)
  have hA0 := ratFuncAtHahn46_coeff_int68 root A 0
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2' := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  norm_num at hA2 hA1 hA0 hB1 hB2 hB3 hC0 hC1 hC2 hF1 hF2' hF3
  norm_num at hG0 hG1 hG2
  dsimp only [AL, BL, CL, FL, Gser] at hc
  rw [← hA2, ← hA1, ← hA0, ← hB1, ← hB2, ← hB3, ← hC0, ← hC1, ← hC2,
    ← hF1, ← hF2', ← hF3, ← hG0, ← hG1, ← hG2] at hc
  linear_combination (-9 / 2 : k) * hc

/-- The strongest scalar consequence of combining the new rows with the
prior child rows: on the affine tail `2C[0]+3γ = 0` with the `C[1] = 0`
face, eliminating `4G[0]+3ε` between the coefficient-two `I₄` row and
the new coefficient-two `I₃` row leaves a `G`-jet-free minor tying the
descended six-combination `ABF` jet to the `F` boundary jets and the
`C[2]` defect.  Recorded as a standalone corollary; the packet keeps
the full rows. -/
theorem rhoOneGZeroChildFourth_bGain_affine_tail_minor68
    (gamma epsilon a2 a1 a0 b2 b3 b4 c0 c1 c2 f0 f1 f2 g0 g1 g2 : k)
    (htie4 : 4 * b2 * g0 + 2 * f2 * (2 * c0 + 3 * gamma) +
      4 * c1 * f1 + 4 * c2 * f0 + 3 * epsilon * b2 = 0)
    (htie3 : 4 * a2 * b2 * f2 + 4 * a2 * b3 * f1 + 4 * a1 * b2 * f1 +
      4 * a2 * b4 * f0 + 4 * a1 * b3 * f0 + 4 * a0 * b2 * f0 -
      6 * g2 * (2 * c0 + 3 * gamma) - 12 * c1 * g1 - 12 * c2 * g0 -
      12 * f0 * f2 - 6 * f1 ^ 2 - 9 * epsilon * c2 = 0)
    (hS0 : 2 * c0 + 3 * gamma = 0) (hc1 : c1 = 0) :
    2 * b2 * (a2 * b2 * f2 + a2 * b3 * f1 + a1 * b2 * f1 +
        a2 * b4 * f0 + a1 * b3 * f0 + a0 * b2 * f0) =
      3 * b2 * (2 * f0 * f2 + f1 ^ 2) - 6 * c2 ^ 2 * f0 := by
  linear_combination (b2 / 2 : k) * htie3 + (3 / 2 : k) * c2 * htie4 +
    (3 * b2 * g2 - 3 * c2 * f2) * hS0 +
    (6 * b2 * g1 - 6 * c2 * f1) * hc1

/-- The `B`-gain child refined through its fourth unused rows: the
imported refinement is kept verbatim, and the coefficient-four `I₄`
row and the coefficient-two `I₃` row are added globally. -/
def RhoOneGZeroChildBGainRefinedFourth68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildBGainRefinedThird68 gamma epsilon A0R B0R C00R D0R E0R
      A B C F G ∧
    (4 * B.coeff (2 : ℚ) * G.coeff (2 : ℚ) +
        4 * B.coeff (3 : ℚ) * G.coeff (1 : ℚ) +
        4 * B.coeff (4 : ℚ) * G.coeff (0 : ℚ) +
        2 * F.coeff (4 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        4 * C.coeff (1 : ℚ) * F.coeff (3 : ℚ) +
        4 * C.coeff (2 : ℚ) * F.coeff (2 : ℚ) +
        4 * C.coeff (3 : ℚ) * F.coeff (1 : ℚ) +
        4 * C.coeff (4 : ℚ) * F.coeff (0 : ℚ) +
        3 * epsilon * B.coeff (4 : ℚ) = 0) ∧
    (4 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (3 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (4 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (3 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (2 : ℚ) * F.coeff (0 : ℚ) -
        6 * G.coeff (2 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) -
        12 * C.coeff (1 : ℚ) * G.coeff (1 : ℚ) -
        12 * C.coeff (2 : ℚ) * G.coeff (0 : ℚ) -
        12 * F.coeff (0 : ℚ) * F.coeff (2 : ℚ) -
        6 * F.coeff (1 : ℚ) ^ 2 -
        9 * epsilon * C.coeff (2 : ℚ) = 0)

/-- The `F`-gain child refined through its fourth unused rows: the
imported refinement is kept verbatim, and the coefficient-four `I₄`
row (with the deepened cube boundary `3B[1]²B[2]`) and the
coefficient-two `I₃` row (with the live `(4C[0]+3γ)B[1]²` load) are
added globally. -/
def RhoOneGZeroChildFGainRefinedFourth68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildFGainRefinedThird68 gamma epsilon A0R B0R C00R D0R E0R
      A B C F G ∧
    (-12 * B.coeff (1 : ℚ) ^ 2 * B.coeff (2 : ℚ) +
        36 * B.coeff (1 : ℚ) * G.coeff (3 : ℚ) +
        36 * B.coeff (2 : ℚ) * G.coeff (2 : ℚ) +
        36 * B.coeff (3 : ℚ) * G.coeff (1 : ℚ) +
        36 * B.coeff (4 : ℚ) * G.coeff (0 : ℚ) +
        18 * F.coeff (4 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        36 * C.coeff (1 : ℚ) * F.coeff (3 : ℚ) +
        36 * C.coeff (2 : ℚ) * F.coeff (2 : ℚ) +
        36 * C.coeff (3 : ℚ) * F.coeff (1 : ℚ) +
        27 * epsilon * B.coeff (4 : ℚ) = 0) ∧
    (4 * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (1 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (3 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (1 : ℚ) * F.coeff (1 : ℚ) +
        (4 * C.coeff (0 : ℚ) + 3 * gamma) * B.coeff (1 : ℚ) ^ 2 -
        6 * G.coeff (2 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) -
        12 * C.coeff (1 : ℚ) * G.coeff (1 : ℚ) -
        12 * C.coeff (2 : ℚ) * G.coeff (0 : ℚ) -
        6 * F.coeff (1 : ℚ) ^ 2 -
        9 * epsilon * C.coeff (2 : ℚ) = 0)

/-- Source backwire: the derivative-next residual with its preserved
`G[-1] = 0` sibling refined child by child through the fourth unused
coefficient rows. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenFourthResidual
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
        (RhoOneGZeroChildBGainRefinedFourth68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G ∨
         RhoOneGZeroChildFGainRefinedFourth68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G)) := by
  dsimp only [RhoOneGZeroChildBGainRefinedFourth68,
    RhoOneGZeroChildFGainRefinedFourth68]
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenThirdResidual
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
      dsimp only [RhoOneGZeroChildBGainRefinedThird68,
        RhoOneGZeroChildBGainRefinedNext68,
        RhoOneGZeroChildBGainRefined68] at hBgain'
      have hB2H : (↑(2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hBgain'.1.1.1.1
      have htie4 := rhoOneGZeroChildFourthI4Load_bGain_coeff_four68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hB2H hCH hFH hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
      have htie3 := rhoOneGZeroChildFourthI3Cap_bGain_coeff_two68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH hB2H hCH hFH hGH hi3R
      rw [hCRraw, hFRraw, hGRraw] at htie3
      simp only [AR, BR] at htie3
      exact ⟨hBgain, htie4, htie3⟩
    · right
      have hFgain' := hFgain
      dsimp only [RhoOneGZeroChildFGainRefinedThird68,
        RhoOneGZeroChildFGainRefinedNext68,
        RhoOneGZeroChildFGainRefined68] at hFgain'
      have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hB
      have hFH1 : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root FR).orderTop := by
        rw [hFRraw]
        exact hFgain'.1.1.1.1
      have htie4 := rhoOneGZeroChildFourthI4Load_fGain_coeff_four68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hBH hCH hFH1 hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
      have htie3 := rhoOneGZeroChildFourthI3Cap_fGain_coeff_two68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH hBH hCH hFH1 hGH hi3R
      rw [hCRraw, hFRraw, hGRraw] at htie3
      simp only [AR, BR] at htie3
      exact ⟨hFgain, htie4, htie3⟩

#print axioms laurent_coeff_mul_lower_four_gZeroChildFourth68
#print axioms rhoOneGZeroChildFourthI4Load_bGain_coeff_four68
#print axioms rhoOneGZeroChildFourthI4Load_fGain_coeff_four68
#print axioms rhoOneGZeroChildFourthI3Cap_bGain_coeff_two68
#print axioms rhoOneGZeroChildFourthI3Cap_fGain_coeff_two68
#print axioms rhoOneGZeroChildFourth_bGain_affine_tail_minor68
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenFourthResidual

end AlignedSquareGZeroChildFourth68

end Max11DegreeRoutes
