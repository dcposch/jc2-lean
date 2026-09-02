import Fable68ScaleTwoAlignedSquareGZeroChildSixthScratch

/-! # The seventh unused rows on the refined `G[-1] = 0` children

The `G`-zero-child-sixth residual keeps the `G[-1] = 0` sibling as the
refined disjunction `BGainRefinedSixth ∨ FGainRefinedSixth`.  On that
sibling the exact next unused rows are the coefficient-seven `I₄` row
and the coefficient-five `I₃` row, on both children:

* On the `B`-gain child (box `ord A ≥ -2`, `ord B ≥ 2`, `ord C ≥ 0`,
  `ord F ≥ 0`, `ord G ≥ 0`) the cube boundary deepens to
  `(B³)[7] = 3B[2]²B[3]` and the `(2C+3γ)F` block needs the new
  eight-combination jet — the first row of the lane built on the
  eight-term convolution `lower_seven`:
  `-12B[2]²B[3] + 36B[2]G[5] + 36B[3]G[4] + 36B[4]G[3] + 36B[5]G[2] +
  36B[6]G[1] + 36B[7]G[0] + 18F[7]·(2C[0]+3γ) + 36C[1]F[6] +
  36C[2]F[5] + 36C[3]F[4] + 36C[4]F[3] + 36C[5]F[2] + 36C[6]F[1] +
  36C[7]F[0] + 27εB[7] = 0`, while the coefficient-five `I₃` row
  carries twenty-one `ABF` combinations — the first row of the lane to
  see `A[3]` (through `A[3]B[2]F[0]`) and `B[7]` (through
  `A[-2]B[7]F[0]`) — and the `B²C` and `γB²` blocks deepen to the load
  `4C[1]B[2]² + 2(4C[0]+3γ)B[2]B[3]`:
  `4·(A[-2]B[2]F[5] + A[-2]B[3]F[4] + A[-1]B[2]F[4] + A[-2]B[4]F[3] +
  A[-1]B[3]F[3] + A[0]B[2]F[3] + A[-2]B[5]F[2] + A[-1]B[4]F[2] +
  A[0]B[3]F[2] + A[1]B[2]F[2] + A[-2]B[6]F[1] + A[-1]B[5]F[1] +
  A[0]B[4]F[1] + A[1]B[3]F[1] + A[2]B[2]F[1] + A[-2]B[7]F[0] +
  A[-1]B[6]F[0] + A[0]B[5]F[0] + A[1]B[4]F[0] + A[2]B[3]F[0] +
  A[3]B[2]F[0]) + 4C[1]B[2]² + 2(4C[0]+3γ)B[2]B[3] =
  6G[5]·(2C[0]+3γ) + 12C[1]G[4] + 12C[2]G[3] + 12C[3]G[2] +
  12C[4]G[1] + 12C[5]G[0] + 12F[0]F[5] + 12F[1]F[4] + 12F[2]F[3] +
  9εC[5]`.

* On the `F`-gain child (box `ord B ≥ 1`, `ord F ≥ 1`) the cube
  boundary deepens to
  `(B³)[7] = 3B[1]²B[5] + 6B[1]B[2]B[4] + 3B[1]B[3]² + 3B[2]²B[3]`:
  `-12B[1]²B[5] - 24B[1]B[2]B[4] - 12B[1]B[3]² - 12B[2]²B[3] +
  36B[1]G[6] + 36B[2]G[5] + 36B[3]G[4] + 36B[4]G[3] + 36B[5]G[2] +
  36B[6]G[1] + 36B[7]G[0] + 18F[7]·(2C[0]+3γ) + 36C[1]F[6] +
  36C[2]F[5] + 36C[3]F[4] + 36C[4]F[3] + 36C[5]F[2] + 36C[6]F[1] +
  27εB[7] = 0`, and the coefficient-five `I₃` row carries the shifted
  twenty-one-combination `ABF` jet (also first seeing `A[3]`, through
  `A[3]B[1]F[1]`) together with the deepened `B²C` and `γB²` loads
  `4C[3]B[1]² + 8C[2]B[1]B[2] + 4C[1](2B[1]B[3]+B[2]²) +
  (4C[0]+3γ)(2B[1]B[4]+2B[2]B[3])`:
  `4·(A[-2]B[1]F[6] + A[-2]B[2]F[5] + A[-1]B[1]F[5] + A[-2]B[3]F[4] +
  A[-1]B[2]F[4] + A[0]B[1]F[4] + A[-2]B[4]F[3] + A[-1]B[3]F[3] +
  A[0]B[2]F[3] + A[1]B[1]F[3] + A[-2]B[5]F[2] + A[-1]B[4]F[2] +
  A[0]B[3]F[2] + A[1]B[2]F[2] + A[2]B[1]F[2] + A[-2]B[6]F[1] +
  A[-1]B[5]F[1] + A[0]B[4]F[1] + A[1]B[3]F[1] + A[2]B[2]F[1] +
  A[3]B[1]F[1]) + 4C[3]B[1]² + 8C[2]B[1]B[2] +
  4C[1](2B[1]B[3]+B[2]²) + (4C[0]+3γ)(2B[1]B[4]+2B[2]B[3]) =
  6G[5]·(2C[0]+3γ) + 12C[1]G[4] + 12C[2]G[3] + 12C[3]G[2] +
  12C[4]G[1] + 12C[5]G[0] + 12F[1]F[4] + 12F[2]F[3] + 9εC[5]`.

Both `I₄` rows are consumed at the Laurent level through the new
reusable eight-term coefficient-convolution lemma (built from the
imported `lower_six`) and the imported shorter siblings.  The
strongest scalar consequence of combining the new rows with all prior
child rows is again a `G`-jet-free and `ε`-free minor on the `B`-gain
affine tail: on `2C[0]+3γ = 0` with the `C[1] = 0` face, eliminating
`G[3]`, `G[2]`, `G[1]` and `G[0]` between the (imported)
coefficient-two through coefficient-five `I₄` rows and the new
coefficient-five `I₃` row yields
`4B[2]⁴·(ABF₂₁) = 6γB[2]⁵B[3] + 12B[2]⁴(F[0]F[5]+F[1]F[4]+F[2]F[3]) +
12C[2]²B[2]²(B[3]F[2]−B[2]F[3]) + 24C[2]C[3]B[2]²(B[3]F[1]−B[2]F[2]) +
12(2C[2]C[4]+C[3]²)B[2]²(B[3]F[0]−B[2]F[1]) +
12C[2]²B[2](B[2]B[4]−B[3]²)F[1] + 24C[2]C[3]B[2](B[2]B[4]−B[3]²)F[0] +
12(C[2]²(B[2]²B[5]−2B[2]B[3]B[4]+B[3]³) −
2B[2]³(C[2]C[5]+C[3]C[4]))F[0]` — the whole `G` boundary jet and the
ground constant `ε` again both leave the new `I₃` row, and the minor
stays `γ`-loaded through the `B²` block, now on the `B[2]B[3]`
boundary.  This is recorded as a standalone corollary and not wired
into the packet, so the tail disjunction of the imported refinement
stays verbatim.  Both children and every sibling are preserved: the
nonzero `G[-1]` boundary lane, the `C₂` face, and the quadratic rays
remain literally inside the imported derivative-next residual.
NEXT_UNUSED_ROW: the coefficient-eight `I₄` row and the
coefficient-six `I₃` row, on both children (the `B`-gain
`(2C+3γ)F` jet there needs the nine-term convolution — build
`lower_eight` from the new `lower_seven`). -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareGZeroChildSeventh68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareGZeroChildSeventhHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The coefficient seven integral jet above the lower face of a Laurent
product, built from the imported six-jet for the
`G`-zero-child-seventh lane. -/
theorem laurent_coeff_mul_lower_seven_gZeroChildSeventh68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 7) =
      X.coeff m * Y.coeff (n + 7) +
        X.coeff (m + 1) * Y.coeff (n + 6) +
          X.coeff (m + 2) * Y.coeff (n + 5) +
            X.coeff (m + 3) * Y.coeff (n + 4) +
              X.coeff (m + 4) * Y.coeff (n + 3) +
                X.coeff (m + 5) * Y.coeff (n + 2) +
                  X.coeff (m + 6) * Y.coeff (n + 1) +
                    X.coeff (m + 7) * Y.coeff n := by
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
  have htail := laurent_coeff_mul_lower_six_gZeroChildSixth68 Xt Y
    (m + 1) n hXt hY
  have htail' : (Xt * Y).coeff (m + n + 7) =
      Xt.coeff (m + 1) * Y.coeff (n + 6) +
        Xt.coeff (m + 2) * Y.coeff (n + 5) +
          Xt.coeff (m + 3) * Y.coeff (n + 4) +
            Xt.coeff (m + 4) * Y.coeff (n + 3) +
              Xt.coeff (m + 5) * Y.coeff (n + 2) +
                Xt.coeff (m + 6) * Y.coeff (n + 1) +
                  Xt.coeff (m + 7) * Y.coeff n := by
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
  have hXt5 : Xt.coeff (m + 5) = X.coeff (m + 5) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt6 : Xt.coeff (m + 6) = X.coeff (m + 6) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt7 : Xt.coeff (m + 7) = X.coeff (m + 7) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hlead :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Y).coeff
          (m + n + 7) = X.coeff m * Y.coeff (n + 7) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 7 - m = n + 7 := by omega
    rw [hi]
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by simp [Xt]
  calc
    (X * Y).coeff (m + n + 7) =
        ((HahnSeries.single m (X.coeff m) + Xt) * Y).coeff
          (m + n + 7) := by rw [← hXdec]
    _ = _ := by
      rw [add_mul, HahnSeries.coeff_add, hlead, htail', hXt1, hXt2, hXt3,
        hXt4, hXt5, hXt6, hXt7]
      ring

/-- The coefficient-seven `I₄` row on the `B`-gain child: with
`ord B ≥ 2` the cube boundary deepens to `(B³)[7] = 3B[2]²B[3]`, the
`BG` block carries six integral combinations and the `(2C+3γ)F` block
carries all eight — the first use of the eight-term convolution. -/
theorem rhoOneGZeroChildSeventhI4Load_bGain_coeff_seven68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneGZeroChildI4LoadFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    -12 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) ^ 2 *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (5 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (4 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (6 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (7 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      18 * (ratFuncAtHahn46 root F).coeff (7 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      36 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (6 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (5 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (6 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (7 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      27 * epsilon * (ratFuncAtHahn46 root B).coeff (7 : ℚ) = 0 := by
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
  have hSF := laurent_coeff_mul_lower_seven_gZeroChildSeventh68 SL FL 0 0
    hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower_five_gZeroChildFifth68 BL Gser 2 0
    hBL hGL
  norm_num at hBG
  have hBsqOrder : (↑(4 : ℤ) : WithTop ℤ) ≤ (BL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hBL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hBsqOrder' : (↑(4 : ℤ) : WithTop ℤ) ≤ (BL * BL).orderTop := by
    rw [← pow_two]
    exact hBsqOrder
  have hsqb := laurent_coeff_mul_lower68 BL BL 2 2 hBL hBL
  norm_num at hsqb
  have hsqb5 := laurent_coeff_mul_lower_succ68 BL BL 2 2 hBL hBL
  norm_num at hsqb5
  have hcubeb := laurent_coeff_mul_lower_succ68 (BL * BL) BL 4 2
    hBsqOrder' hBL
  norm_num at hcubeb
  have hBcube : (BL ^ 3).coeff (7 : ℤ) =
      3 * BL.coeff 2 ^ 2 * BL.coeff 3 := by
    have hpow : BL ^ 3 = BL * BL * BL := by ring
    rw [hpow, hcubeb, hsqb, hsqb5]
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (7 : ℤ))
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
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 7 =
      (-8 / 27 : k) * (BL ^ 3).coeff 7 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 7 =
      (8 / 3 : k) * (BL * Gser).coeff 7 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 7 =
      (4 / 3 : k) * (SL * FL).coeff 7 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 7 =
      (2 * epsilon) * BL.coeff 7 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (7 : ℤ) = 0 := by
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
  have hSL5 : SL.coeff (5 : ℤ) = 2 * CL.coeff (5 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL6 : SL.coeff (6 : ℤ) = 2 * CL.coeff (6 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL7 : SL.coeff (7 : ℤ) = 2 * CL.coeff (7 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2, hSL3, hSL4, hSL5, hSL6, hSL7] at hc
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hB4 := ratFuncAtHahn46_coeff_int68 root B 4
  have hB5 := ratFuncAtHahn46_coeff_int68 root B 5
  have hB6 := ratFuncAtHahn46_coeff_int68 root B 6
  have hB7 := ratFuncAtHahn46_coeff_int68 root B 7
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hC3 := ratFuncAtHahn46_coeff_int68 root C 3
  have hC4 := ratFuncAtHahn46_coeff_int68 root C 4
  have hC5 := ratFuncAtHahn46_coeff_int68 root C 5
  have hC6 := ratFuncAtHahn46_coeff_int68 root C 6
  have hC7 := ratFuncAtHahn46_coeff_int68 root C 7
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hF6 := ratFuncAtHahn46_coeff_int68 root F 6
  have hF7 := ratFuncAtHahn46_coeff_int68 root F 7
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hG3 := ratFuncAtHahn46_coeff_int68 root G 3
  have hG4 := ratFuncAtHahn46_coeff_int68 root G 4
  have hG5 := ratFuncAtHahn46_coeff_int68 root G 5
  norm_num at hB2 hB3 hB4 hB5 hB6 hB7 hC0 hC1 hC2 hC3 hC4 hC5 hC6 hC7
  norm_num at hF0 hF1 hF2 hF3 hF4 hF5 hF6 hF7 hG0 hG1 hG2 hG3 hG4 hG5
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB2, ← hB3, ← hB4, ← hB5, ← hB6, ← hB7, ← hC0, ← hC1, ← hC2,
    ← hC3, ← hC4, ← hC5, ← hC6, ← hC7, ← hF0, ← hF1, ← hF2, ← hF3,
    ← hF4, ← hF5, ← hF6, ← hF7, ← hG0, ← hG1, ← hG2, ← hG3, ← hG4,
    ← hG5] at hc
  linear_combination (27 / 2 : k) * hc

/-- The coefficient-seven `I₄` row on the `F`-gain child: with
`ord B ≥ 1` and `ord F ≥ 1` the cube boundary deepens to
`3B[1]²B[5] + 6B[1]B[2]B[4] + 3B[1]B[3]² + 3B[2]²B[3]` alongside the
seven-combination `BG` and `(2C+3γ)F` jets. -/
theorem rhoOneGZeroChildSeventhI4Load_fGain_coeff_seven68
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
        (ratFuncAtHahn46 root B).coeff (5 : ℚ) -
      24 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) -
      12 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) ^ 2 -
      12 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) ^ 2 *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (6 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (5 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (4 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (6 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
      36 * (ratFuncAtHahn46 root B).coeff (7 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
      18 * (ratFuncAtHahn46 root F).coeff (7 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) +
      36 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (6 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (5 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      36 * (ratFuncAtHahn46 root C).coeff (6 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      27 * epsilon * (ratFuncAtHahn46 root B).coeff (7 : ℚ) = 0 := by
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
  have hSF := laurent_coeff_mul_lower_six_gZeroChildSixth68 SL FL 0 1
    hSLord hFL
  norm_num at hSF
  have hBG := laurent_coeff_mul_lower_six_gZeroChildSixth68 BL Gser 1 0
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
  have hsq4 := laurent_coeff_mul_lower_two_gZeroChildNext68 BL BL 1 1
    hBL hBL
  norm_num at hsq4
  have hsq5 := laurent_coeff_mul_lower_three_gZeroChildThird68 BL BL 1 1
    hBL hBL
  norm_num at hsq5
  have hsq6 := laurent_coeff_mul_lower_four_gZeroChildFourth68 BL BL 1 1
    hBL hBL
  norm_num at hsq6
  have hcubec := laurent_coeff_mul_lower_four_gZeroChildFourth68 (BL * BL)
    BL 2 1 hBsqOrder' hBL
  norm_num at hcubec
  have hBcube : (BL ^ 3).coeff (7 : ℤ) =
      3 * BL.coeff 1 ^ 2 * BL.coeff 5 +
        6 * BL.coeff 1 * BL.coeff 2 * BL.coeff 4 +
        3 * BL.coeff 1 * BL.coeff 3 ^ 2 +
        3 * BL.coeff 2 ^ 2 * BL.coeff 3 := by
    have hpow : BL ^ 3 = BL * BL * BL := by ring
    rw [hpow, hcubec, hsq2, hsq3, hsq4, hsq5, hsq6]
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (7 : ℤ))
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
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 7 =
      (-8 / 27 : k) * (BL ^ 3).coeff 7 := by
    rw [hc827, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 7 =
      (8 / 3 : k) * (BL * Gser).coeff 7 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 7 =
      (4 / 3 : k) * (SL * FL).coeff 7 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 7 =
      (2 * epsilon) * BL.coeff 7 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hright : (HahnSeries.C i4 : LaurentSeries k).coeff (7 : ℤ) = 0 := by
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
  have hSL5 : SL.coeff (5 : ℤ) = 2 * CL.coeff (5 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL6 : SL.coeff (6 : ℤ) = 2 * CL.coeff (6 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2, hSL3, hSL4, hSL5, hSL6] at hc
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hB4 := ratFuncAtHahn46_coeff_int68 root B 4
  have hB5 := ratFuncAtHahn46_coeff_int68 root B 5
  have hB6 := ratFuncAtHahn46_coeff_int68 root B 6
  have hB7 := ratFuncAtHahn46_coeff_int68 root B 7
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hC3 := ratFuncAtHahn46_coeff_int68 root C 3
  have hC4 := ratFuncAtHahn46_coeff_int68 root C 4
  have hC5 := ratFuncAtHahn46_coeff_int68 root C 5
  have hC6 := ratFuncAtHahn46_coeff_int68 root C 6
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hF6 := ratFuncAtHahn46_coeff_int68 root F 6
  have hF7 := ratFuncAtHahn46_coeff_int68 root F 7
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hG3 := ratFuncAtHahn46_coeff_int68 root G 3
  have hG4 := ratFuncAtHahn46_coeff_int68 root G 4
  have hG5 := ratFuncAtHahn46_coeff_int68 root G 5
  have hG6 := ratFuncAtHahn46_coeff_int68 root G 6
  norm_num at hB1 hB2 hB3 hB4 hB5 hB6 hB7 hC0 hC1 hC2 hC3 hC4 hC5 hC6
  norm_num at hF1 hF2 hF3 hF4 hF5 hF6 hF7 hG0 hG1 hG2 hG3 hG4 hG5 hG6
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB1, ← hB2, ← hB3, ← hB4, ← hB5, ← hB6, ← hB7, ← hC0, ← hC1,
    ← hC2, ← hC3, ← hC4, ← hC5, ← hC6, ← hF1, ← hF2, ← hF3, ← hF4,
    ← hF5, ← hF6, ← hF7, ← hG0, ← hG1, ← hG2, ← hG3, ← hG4, ← hG5,
    ← hG6] at hc
  linear_combination (27 / 2 : k) * hc

/-- The coefficient-five `I₃` row on the `B`-gain child, consumed at
the Laurent level: the `ABF` block carries twenty-one integral
combinations — the first appearance of `A[3]` and `B[7]` in this
lane — while the `B²C` and `γB²` blocks deepen to the load
`4C[1]B[2]² + 2(4C[0]+3γ)B[2]B[3]`. -/
theorem rhoOneGZeroChildSeventhI3Cap_bGain_coeff_five68
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
        (ratFuncAtHahn46 root F).coeff (5 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (6 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (7 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (6 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (0 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) ^ 2 +
      2 * (4 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) -
      6 * (ratFuncAtHahn46 root G).coeff (5 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) -
      12 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (4 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (3 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (2 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) -
      12 * (ratFuncAtHahn46 root F).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (5 : ℚ) -
      12 * (ratFuncAtHahn46 root F).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) -
      12 * (ratFuncAtHahn46 root F).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) -
      9 * epsilon * (ratFuncAtHahn46 root C).coeff (5 : ℚ) = 0 := by
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
  have hABF := laurent_coeff_mul_lower_five_gZeroChildFifth68 (AL * BL)
    FL 0 0 hABord hFL
  norm_num at hABF
  have hAB0 := laurent_coeff_mul_lower68 AL BL (-2) 2 hAL hBL
  norm_num at hAB0
  have hAB1 := laurent_coeff_mul_lower_succ68 AL BL (-2) 2 hAL hBL
  norm_num at hAB1
  have hAB2 := laurent_coeff_mul_lower_two_gZeroChildNext68 AL BL (-2) 2
    hAL hBL
  norm_num at hAB2
  have hAB3 := laurent_coeff_mul_lower_three_gZeroChildThird68 AL BL (-2)
    2 hAL hBL
  norm_num at hAB3
  have hAB4 := laurent_coeff_mul_lower_four_gZeroChildFourth68 AL BL (-2)
    2 hAL hBL
  norm_num at hAB4
  have hAB5 := laurent_coeff_mul_lower_five_gZeroChildFifth68 AL BL (-2)
    2 hAL hBL
  norm_num at hAB5
  rw [hAB0, hAB1, hAB2, hAB3, hAB4, hAB5] at hABF
  have hSG := laurent_coeff_mul_lower_five_gZeroChildFifth68 SL Gser 0 0
    hSLord hGL
  norm_num at hSG
  have hBsqOrder : (↑(4 : ℤ) : WithTop ℤ) ≤ (BL ^ 2).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 2)
    have hdouble := nsmul_le_nsmul_right hBL 2
    norm_num at hdouble
    exact le_trans hdouble hp
  have hsqb := laurent_coeff_mul_lower68 BL BL 2 2 hBL hBL
  norm_num at hsqb
  have hBsq4 : (BL ^ 2).coeff (4 : ℤ) = BL.coeff 2 * BL.coeff 2 := by
    rw [pow_two, hsqb]
  have hsqb5 := laurent_coeff_mul_lower_succ68 BL BL 2 2 hBL hBL
  norm_num at hsqb5
  have hBsq5 : (BL ^ 2).coeff (5 : ℤ) =
      BL.coeff 2 * BL.coeff 3 + BL.coeff 3 * BL.coeff 2 := by
    rw [pow_two, hsqb5]
  have hB2C := laurent_coeff_mul_lower_succ68 (BL ^ 2) CL 4 0 hBsqOrder
    hCL
  norm_num at hB2C
  have hFsq := laurent_coeff_mul_lower_five_gZeroChildFifth68 FL FL 0 0
    hFL hFL
  norm_num at hFsq
  have hF2 : (FL ^ 2).coeff (5 : ℤ) =
      FL.coeff 0 * FL.coeff 5 + FL.coeff 1 * FL.coeff 4 +
        FL.coeff 2 * FL.coeff 3 + FL.coeff 3 * FL.coeff 2 +
          FL.coeff 4 * FL.coeff 1 + FL.coeff 5 * FL.coeff 0 := by
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (5 : ℤ))
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
  have hsc1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff (5 : ℤ) =
      (-8 / 9 : k) * (AL * BL * FL).coeff (5 : ℤ) := by
    have hform : (-8 / 9 : LaurentSeries k) * AL * BL * FL =
        HahnSeries.C (-8 / 9 : k) * (AL * BL * FL) := by
      rw [← hc89]
      ring
    rw [hform, hscale]
  have hsc2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff (5 : ℤ) =
      (8 / 9 : k) * (BL ^ 2 * CL).coeff (5 : ℤ) := by
    have hform : (8 / 9 : LaurentSeries k) * BL ^ 2 * CL =
        HahnSeries.C (8 / 9 : k) * (BL ^ 2 * CL) := by
      rw [← hc89']
      ring
    rw [hform, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff (5 : ℤ) =
      (4 / 3 : k) * (SL * Gser).coeff (5 : ℤ) := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff (5 : ℤ) =
      (4 / 3 : k) * (FL ^ 2).coeff (5 : ℤ) := by
    rw [hc43, hscale]
  have hsc5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma *
      BL ^ 2).coeff (5 : ℤ) =
      (2 / 3 * gamma : k) * (BL ^ 2).coeff (5 : ℤ) := by
    rw [hc23, ← map_mul, hscale]
  have hsc6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon *
      CL).coeff (5 : ℤ) = (2 * epsilon) * CL.coeff (5 : ℤ) := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hsc5, hsc6] at hc
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff (5 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hABF, hB2C, hSG, hF2, hBsq4, hBsq5, hright] at hc
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
  have hSL5 : SL.coeff (5 : ℤ) = 2 * CL.coeff (5 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2, hSL3, hSL4, hSL5] at hc
  have hA2 := ratFuncAtHahn46_coeff_int68 root A (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 root A (-1)
  have hA0 := ratFuncAtHahn46_coeff_int68 root A 0
  have hA1' := ratFuncAtHahn46_coeff_int68 root A 1
  have hA2' := ratFuncAtHahn46_coeff_int68 root A 2
  have hA3' := ratFuncAtHahn46_coeff_int68 root A 3
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hB4 := ratFuncAtHahn46_coeff_int68 root B 4
  have hB5 := ratFuncAtHahn46_coeff_int68 root B 5
  have hB6 := ratFuncAtHahn46_coeff_int68 root B 6
  have hB7 := ratFuncAtHahn46_coeff_int68 root B 7
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hC3 := ratFuncAtHahn46_coeff_int68 root C 3
  have hC4 := ratFuncAtHahn46_coeff_int68 root C 4
  have hC5 := ratFuncAtHahn46_coeff_int68 root C 5
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2' := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4' := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hG3 := ratFuncAtHahn46_coeff_int68 root G 3
  have hG4 := ratFuncAtHahn46_coeff_int68 root G 4
  have hG5 := ratFuncAtHahn46_coeff_int68 root G 5
  norm_num at hA2 hA1 hA0 hA1' hA2' hA3' hB2 hB3 hB4 hB5 hB6 hB7
  norm_num at hC0 hC1 hC2 hC3 hC4 hC5 hF0 hF1 hF2' hF3 hF4' hF5
  norm_num at hG0 hG1 hG2 hG3 hG4 hG5
  dsimp only [AL, BL, CL, FL, Gser] at hc
  rw [← hA2, ← hA1, ← hA0, ← hA1', ← hA2', ← hA3', ← hB2, ← hB3, ← hB4,
    ← hB5, ← hB6, ← hB7, ← hC0, ← hC1, ← hC2, ← hC3, ← hC4, ← hC5,
    ← hF0, ← hF1, ← hF2', ← hF3, ← hF4', ← hF5, ← hG0, ← hG1, ← hG2,
    ← hG3, ← hG4, ← hG5] at hc
  linear_combination (-9 / 2 : k) * hc

/-- The coefficient-five `I₃` row on the `F`-gain child, consumed at
the Laurent level: the `ABF` block carries the twenty-one combinations
of the shifted box `ord B ≥ 1`, `ord F ≥ 1` — also first seeing
`A[3]`, through `A[3]B[1]F[1]` — while the `B²C` and `γB²` blocks
deepen to the load `4C[3]B[1]² + 8C[2]B[1]B[2] +
4C[1](2B[1]B[3]+B[2]²) + (4C[0]+3γ)(2B[1]B[4]+2B[2]B[3])`. -/
theorem rhoOneGZeroChildSeventhI3Cap_fGain_coeff_five68
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
        (ratFuncAtHahn46 root F).coeff (6 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (5 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (5 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (6 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (-1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (0 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root A).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (1 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) ^ 2 +
      8 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root B).coeff (2 : ℚ) +
      4 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (2 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
            (ratFuncAtHahn46 root B).coeff (3 : ℚ) +
          (ratFuncAtHahn46 root B).coeff (2 : ℚ) ^ 2) +
      (4 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) *
        (2 * (ratFuncAtHahn46 root B).coeff (1 : ℚ) *
            (ratFuncAtHahn46 root B).coeff (4 : ℚ) +
          2 * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
            (ratFuncAtHahn46 root B).coeff (3 : ℚ)) -
      6 * (ratFuncAtHahn46 root G).coeff (5 : ℚ) *
        (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) -
      12 * (ratFuncAtHahn46 root C).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (4 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (3 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (3 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (2 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (4 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (1 : ℚ) -
      12 * (ratFuncAtHahn46 root C).coeff (5 : ℚ) *
        (ratFuncAtHahn46 root G).coeff (0 : ℚ) -
      12 * (ratFuncAtHahn46 root F).coeff (1 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (4 : ℚ) -
      12 * (ratFuncAtHahn46 root F).coeff (2 : ℚ) *
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) -
      9 * epsilon * (ratFuncAtHahn46 root C).coeff (5 : ℚ) = 0 := by
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
  have hABF := laurent_coeff_mul_lower_five_gZeroChildFifth68 (AL * BL)
    FL (-1) 1 hABord hFL
  norm_num at hABF
  have hABm1 := laurent_coeff_mul_lower68 AL BL (-2) 1 hAL hBL
  norm_num at hABm1
  have hAB0 := laurent_coeff_mul_lower_succ68 AL BL (-2) 1 hAL hBL
  norm_num at hAB0
  have hAB1 := laurent_coeff_mul_lower_two_gZeroChildNext68 AL BL (-2) 1
    hAL hBL
  norm_num at hAB1
  have hAB2 := laurent_coeff_mul_lower_three_gZeroChildThird68 AL BL (-2)
    1 hAL hBL
  norm_num at hAB2
  have hAB3 := laurent_coeff_mul_lower_four_gZeroChildFourth68 AL BL (-2)
    1 hAL hBL
  norm_num at hAB3
  have hAB4 := laurent_coeff_mul_lower_five_gZeroChildFifth68 AL BL (-2)
    1 hAL hBL
  norm_num at hAB4
  rw [hABm1, hAB0, hAB1, hAB2, hAB3, hAB4] at hABF
  have hSG := laurent_coeff_mul_lower_five_gZeroChildFifth68 SL Gser 0 0
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
  have hsq3c := laurent_coeff_mul_lower_succ68 BL BL 1 1 hBL hBL
  norm_num at hsq3c
  have hBsq3 : (BL ^ 2).coeff (3 : ℤ) =
      BL.coeff 1 * BL.coeff 2 + BL.coeff 2 * BL.coeff 1 := by
    rw [pow_two, hsq3c]
  have hsq4c := laurent_coeff_mul_lower_two_gZeroChildNext68 BL BL 1 1
    hBL hBL
  norm_num at hsq4c
  have hBsq4 : (BL ^ 2).coeff (4 : ℤ) =
      BL.coeff 1 * BL.coeff 3 + BL.coeff 2 * BL.coeff 2 +
        BL.coeff 3 * BL.coeff 1 := by
    rw [pow_two, hsq4c]
  have hsq5c := laurent_coeff_mul_lower_three_gZeroChildThird68 BL BL 1 1
    hBL hBL
  norm_num at hsq5c
  have hBsq5 : (BL ^ 2).coeff (5 : ℤ) =
      BL.coeff 1 * BL.coeff 4 + BL.coeff 2 * BL.coeff 3 +
        BL.coeff 3 * BL.coeff 2 + BL.coeff 4 * BL.coeff 1 := by
    rw [pow_two, hsq5c]
  have hB2C := laurent_coeff_mul_lower_three_gZeroChildThird68 (BL ^ 2)
    CL 2 0 hBsqOrder hCL
  norm_num at hB2C
  have hFsq5c := laurent_coeff_mul_lower_three_gZeroChildThird68 FL FL 1 1
    hFL hFL
  norm_num at hFsq5c
  have hF2 : (FL ^ 2).coeff (5 : ℤ) =
      FL.coeff 1 * FL.coeff 4 + FL.coeff 2 * FL.coeff 3 +
        FL.coeff 3 * FL.coeff 2 + FL.coeff 4 * FL.coeff 1 := by
    rw [pow_two, hFsq5c]
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (5 : ℤ))
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
  have hsc1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff (5 : ℤ) =
      (-8 / 9 : k) * (AL * BL * FL).coeff (5 : ℤ) := by
    have hform : (-8 / 9 : LaurentSeries k) * AL * BL * FL =
        HahnSeries.C (-8 / 9 : k) * (AL * BL * FL) := by
      rw [← hc89]
      ring
    rw [hform, hscale]
  have hsc2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff (5 : ℤ) =
      (8 / 9 : k) * (BL ^ 2 * CL).coeff (5 : ℤ) := by
    have hform : (8 / 9 : LaurentSeries k) * BL ^ 2 * CL =
        HahnSeries.C (8 / 9 : k) * (BL ^ 2 * CL) := by
      rw [← hc89']
      ring
    rw [hform, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff (5 : ℤ) =
      (4 / 3 : k) * (SL * Gser).coeff (5 : ℤ) := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff (5 : ℤ) =
      (4 / 3 : k) * (FL ^ 2).coeff (5 : ℤ) := by
    rw [hc43, hscale]
  have hsc5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma *
      BL ^ 2).coeff (5 : ℤ) =
      (2 / 3 * gamma : k) * (BL ^ 2).coeff (5 : ℤ) := by
    rw [hc23, ← map_mul, hscale]
  have hsc6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon *
      CL).coeff (5 : ℤ) = (2 * epsilon) * CL.coeff (5 : ℤ) := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hsc5, hsc6] at hc
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff (5 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hABF, hB2C, hSG, hF2, hBsq2, hBsq3, hBsq4, hBsq5, hright] at hc
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
  have hSL5 : SL.coeff (5 : ℤ) = 2 * CL.coeff (5 : ℤ) := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2, hSL3, hSL4, hSL5] at hc
  have hA2 := ratFuncAtHahn46_coeff_int68 root A (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 root A (-1)
  have hA0 := ratFuncAtHahn46_coeff_int68 root A 0
  have hA1' := ratFuncAtHahn46_coeff_int68 root A 1
  have hA2' := ratFuncAtHahn46_coeff_int68 root A 2
  have hA3' := ratFuncAtHahn46_coeff_int68 root A 3
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hB4 := ratFuncAtHahn46_coeff_int68 root B 4
  have hB5 := ratFuncAtHahn46_coeff_int68 root B 5
  have hB6 := ratFuncAtHahn46_coeff_int68 root B 6
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hC3 := ratFuncAtHahn46_coeff_int68 root C 3
  have hC4 := ratFuncAtHahn46_coeff_int68 root C 4
  have hC5 := ratFuncAtHahn46_coeff_int68 root C 5
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2' := ratFuncAtHahn46_coeff_int68 root F 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4' := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hF6 := ratFuncAtHahn46_coeff_int68 root F 6
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hG3 := ratFuncAtHahn46_coeff_int68 root G 3
  have hG4 := ratFuncAtHahn46_coeff_int68 root G 4
  have hG5 := ratFuncAtHahn46_coeff_int68 root G 5
  norm_num at hA2 hA1 hA0 hA1' hA2' hA3' hB1 hB2 hB3 hB4 hB5 hB6
  norm_num at hC0 hC1 hC2 hC3 hC4 hC5 hF1 hF2' hF3 hF4' hF5 hF6
  norm_num at hG0 hG1 hG2 hG3 hG4 hG5
  dsimp only [AL, BL, CL, FL, Gser] at hc
  rw [← hA2, ← hA1, ← hA0, ← hA1', ← hA2', ← hA3', ← hB1, ← hB2, ← hB3,
    ← hB4, ← hB5, ← hB6, ← hC0, ← hC1, ← hC2, ← hC3, ← hC4, ← hC5,
    ← hF1, ← hF2', ← hF3, ← hF4', ← hF5, ← hF6, ← hG0, ← hG1, ← hG2,
    ← hG3, ← hG4, ← hG5] at hc
  linear_combination (-9 / 2 : k) * hc

/-- The strongest scalar consequence of combining the new rows with the
prior child rows: on the affine tail `2C[0]+3γ = 0` with the `C[1] = 0`
face, eliminating `G[3]`, `G[2]`, `G[1]` and `G[0]` between the
imported coefficient-two through coefficient-five `I₄` rows and the
new coefficient-five `I₃` row leaves a `G`-jet-free and `ε`-free minor
tying the descended twenty-one-combination `ABF` jet to the `F`
boundary jets and the `C[2]`, `C[3]`, `C[4]`, `C[5]` defects — still
`γ`-loaded through the `B²` block, now on the `B[2]B[3]` boundary.
Recorded as a standalone corollary; the packet keeps the full rows. -/
theorem rhoOneGZeroChildSeventh_bGain_affine_tail_minor68
    (gamma epsilon a2 a1 a0 aP aQ aR b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4
      c5 f0 f1 f2 f3 f4 f5 g0 g1 g2 g3 g4 g5 : k)
    (htie2 : 4 * b2 * g0 + 2 * f2 * (2 * c0 + 3 * gamma) +
      4 * c1 * f1 + 4 * c2 * f0 + 3 * epsilon * b2 = 0)
    (htie3 : 4 * b2 * g1 + 4 * b3 * g0 + 2 * f3 * (2 * c0 + 3 * gamma) +
      4 * c1 * f2 + 4 * c2 * f1 + 4 * c3 * f0 + 3 * epsilon * b3 = 0)
    (htie4 : 4 * b2 * g2 + 4 * b3 * g1 + 4 * b4 * g0 +
      2 * f4 * (2 * c0 + 3 * gamma) + 4 * c1 * f3 + 4 * c2 * f2 +
      4 * c3 * f1 + 4 * c4 * f0 + 3 * epsilon * b4 = 0)
    (htie5 : 4 * b2 * g3 + 4 * b3 * g2 + 4 * b4 * g1 + 4 * b5 * g0 +
      2 * f5 * (2 * c0 + 3 * gamma) + 4 * c1 * f4 + 4 * c2 * f3 +
      4 * c3 * f2 + 4 * c4 * f1 + 4 * c5 * f0 + 3 * epsilon * b5 = 0)
    (hrow : 4 * a2 * b2 * f5 + 4 * a2 * b3 * f4 + 4 * a1 * b2 * f4 +
      4 * a2 * b4 * f3 + 4 * a1 * b3 * f3 + 4 * a0 * b2 * f3 +
      4 * a2 * b5 * f2 + 4 * a1 * b4 * f2 + 4 * a0 * b3 * f2 +
      4 * aP * b2 * f2 + 4 * a2 * b6 * f1 + 4 * a1 * b5 * f1 +
      4 * a0 * b4 * f1 + 4 * aP * b3 * f1 + 4 * aQ * b2 * f1 +
      4 * a2 * b7 * f0 + 4 * a1 * b6 * f0 + 4 * a0 * b5 * f0 +
      4 * aP * b4 * f0 + 4 * aQ * b3 * f0 + 4 * aR * b2 * f0 +
      4 * c1 * b2 ^ 2 + 2 * (4 * c0 + 3 * gamma) * b2 * b3 -
      6 * g5 * (2 * c0 + 3 * gamma) - 12 * c1 * g4 - 12 * c2 * g3 -
      12 * c3 * g2 - 12 * c4 * g1 - 12 * c5 * g0 - 12 * f0 * f5 -
      12 * f1 * f4 - 12 * f2 * f3 - 9 * epsilon * c5 = 0)
    (hS0 : 2 * c0 + 3 * gamma = 0) (hc1 : c1 = 0) :
    4 * b2 ^ 4 * (a2 * b2 * f5 + a2 * b3 * f4 + a1 * b2 * f4 +
        a2 * b4 * f3 + a1 * b3 * f3 + a0 * b2 * f3 +
        a2 * b5 * f2 + a1 * b4 * f2 + a0 * b3 * f2 + aP * b2 * f2 +
        a2 * b6 * f1 + a1 * b5 * f1 + a0 * b4 * f1 + aP * b3 * f1 +
        aQ * b2 * f1 + a2 * b7 * f0 + a1 * b6 * f0 + a0 * b5 * f0 +
        aP * b4 * f0 + aQ * b3 * f0 + aR * b2 * f0) =
      6 * gamma * b2 ^ 5 * b3 +
        12 * b2 ^ 4 * (f0 * f5 + f1 * f4 + f2 * f3) +
        12 * c2 ^ 2 * b2 ^ 2 * (b3 * f2 - b2 * f3) +
        24 * c2 * c3 * b2 ^ 2 * (b3 * f1 - b2 * f2) +
        12 * (2 * c2 * c4 + c3 ^ 2) * b2 ^ 2 * (b3 * f0 - b2 * f1) +
        12 * c2 ^ 2 * b2 * (b2 * b4 - b3 ^ 2) * f1 +
        24 * c2 * c3 * b2 * (b2 * b4 - b3 ^ 2) * f0 +
        12 * (c2 ^ 2 * (b2 ^ 2 * b5 - 2 * b2 * b3 * b4 + b3 ^ 3) -
          2 * b2 ^ 3 * (c2 * c5 + c3 * c4)) * f0 := by
  linear_combination (b2 ^ 4 : k) * hrow + 3 * c2 * b2 ^ 3 * htie5 +
    3 * b2 ^ 2 * (c3 * b2 - c2 * b3) * htie4 +
    3 * b2 * (c4 * b2 ^ 2 - c2 * b2 * b4 - c3 * b2 * b3 + c2 * b3 ^ 2) *
      htie3 +
    3 * (c5 * b2 ^ 3 - c2 * b2 ^ 2 * b5 - c3 * b2 ^ 2 * b4 -
      c4 * b2 ^ 2 * b3 + 2 * c2 * b2 * b3 * b4 + c3 * b2 * b3 ^ 2 -
      c2 * b3 ^ 3) * htie2 +
    (6 * b2 ^ 4 * g5 - 4 * b2 ^ 5 * b3 - 6 * c2 * b2 ^ 3 * f5 -
      6 * b2 ^ 2 * (c3 * b2 - c2 * b3) * f4 -
      6 * b2 * (c4 * b2 ^ 2 - c2 * b2 * b4 - c3 * b2 * b3 +
        c2 * b3 ^ 2) * f3 -
      6 * (c5 * b2 ^ 3 - c2 * b2 ^ 2 * b5 - c3 * b2 ^ 2 * b4 -
        c4 * b2 ^ 2 * b3 + 2 * c2 * b2 * b3 * b4 + c3 * b2 * b3 ^ 2 -
        c2 * b3 ^ 3) * f2) * hS0 +
    (12 * b2 ^ 4 * g4 - 4 * b2 ^ 6 - 12 * c2 * b2 ^ 3 * f4 -
      12 * b2 ^ 2 * (c3 * b2 - c2 * b3) * f3 -
      12 * b2 * (c4 * b2 ^ 2 - c2 * b2 * b4 - c3 * b2 * b3 +
        c2 * b3 ^ 2) * f2 -
      12 * (c5 * b2 ^ 3 - c2 * b2 ^ 2 * b5 - c3 * b2 ^ 2 * b4 -
        c4 * b2 ^ 2 * b3 + 2 * c2 * b2 * b3 * b4 + c3 * b2 * b3 ^ 2 -
        c2 * b3 ^ 3) * f1) * hc1

/-- The `B`-gain child refined through its seventh unused rows: the
imported refinement is kept verbatim, and the coefficient-seven `I₄`
row (with the deepened cube boundary `-12B[2]²B[3]`) and the
coefficient-five `I₃` row (with the deepened
`4C[1]B[2]² + 2(4C[0]+3γ)B[2]B[3]` load) are added globally. -/
def RhoOneGZeroChildBGainRefinedSeventh68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildBGainRefinedSixth68 gamma epsilon A0R B0R C00R D0R E0R
      A B C F G ∧
    (-12 * B.coeff (2 : ℚ) ^ 2 * B.coeff (3 : ℚ) +
        36 * B.coeff (2 : ℚ) * G.coeff (5 : ℚ) +
        36 * B.coeff (3 : ℚ) * G.coeff (4 : ℚ) +
        36 * B.coeff (4 : ℚ) * G.coeff (3 : ℚ) +
        36 * B.coeff (5 : ℚ) * G.coeff (2 : ℚ) +
        36 * B.coeff (6 : ℚ) * G.coeff (1 : ℚ) +
        36 * B.coeff (7 : ℚ) * G.coeff (0 : ℚ) +
        18 * F.coeff (7 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        36 * C.coeff (1 : ℚ) * F.coeff (6 : ℚ) +
        36 * C.coeff (2 : ℚ) * F.coeff (5 : ℚ) +
        36 * C.coeff (3 : ℚ) * F.coeff (4 : ℚ) +
        36 * C.coeff (4 : ℚ) * F.coeff (3 : ℚ) +
        36 * C.coeff (5 : ℚ) * F.coeff (2 : ℚ) +
        36 * C.coeff (6 : ℚ) * F.coeff (1 : ℚ) +
        36 * C.coeff (7 : ℚ) * F.coeff (0 : ℚ) +
        27 * epsilon * B.coeff (7 : ℚ) = 0) ∧
    (4 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (5 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (3 : ℚ) * F.coeff (4 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (2 : ℚ) * F.coeff (4 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (4 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (3 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (2 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (5 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (4 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (3 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (1 : ℚ) * B.coeff (2 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (6 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (5 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (4 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (1 : ℚ) * B.coeff (3 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (7 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (6 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (5 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (1 : ℚ) * B.coeff (4 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (2 : ℚ) * B.coeff (3 : ℚ) * F.coeff (0 : ℚ) +
        4 * A.coeff (3 : ℚ) * B.coeff (2 : ℚ) * F.coeff (0 : ℚ) +
        4 * C.coeff (1 : ℚ) * B.coeff (2 : ℚ) ^ 2 +
        2 * (4 * C.coeff (0 : ℚ) + 3 * gamma) * B.coeff (2 : ℚ) *
          B.coeff (3 : ℚ) -
        6 * G.coeff (5 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) -
        12 * C.coeff (1 : ℚ) * G.coeff (4 : ℚ) -
        12 * C.coeff (2 : ℚ) * G.coeff (3 : ℚ) -
        12 * C.coeff (3 : ℚ) * G.coeff (2 : ℚ) -
        12 * C.coeff (4 : ℚ) * G.coeff (1 : ℚ) -
        12 * C.coeff (5 : ℚ) * G.coeff (0 : ℚ) -
        12 * F.coeff (0 : ℚ) * F.coeff (5 : ℚ) -
        12 * F.coeff (1 : ℚ) * F.coeff (4 : ℚ) -
        12 * F.coeff (2 : ℚ) * F.coeff (3 : ℚ) -
        9 * epsilon * C.coeff (5 : ℚ) = 0)

/-- The `F`-gain child refined through its seventh unused rows: the
imported refinement is kept verbatim, and the coefficient-seven `I₄`
row (with the deepened cube boundary
`3B[1]²B[5] + 6B[1]B[2]B[4] + 3B[1]B[3]² + 3B[2]²B[3]`) and the
coefficient-five `I₃` row (with the deepened
`4C[3]B[1]² + 8C[2]B[1]B[2] + 4C[1](2B[1]B[3]+B[2]²) +
(4C[0]+3γ)(2B[1]B[4]+2B[2]B[3])` load) are added globally. -/
def RhoOneGZeroChildFGainRefinedSeventh68
    (gamma epsilon : k) (A0R B0R C00R D0R E0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneGZeroChildFGainRefinedSixth68 gamma epsilon A0R B0R C00R D0R E0R
      A B C F G ∧
    (-12 * B.coeff (1 : ℚ) ^ 2 * B.coeff (5 : ℚ) -
        24 * B.coeff (1 : ℚ) * B.coeff (2 : ℚ) * B.coeff (4 : ℚ) -
        12 * B.coeff (1 : ℚ) * B.coeff (3 : ℚ) ^ 2 -
        12 * B.coeff (2 : ℚ) ^ 2 * B.coeff (3 : ℚ) +
        36 * B.coeff (1 : ℚ) * G.coeff (6 : ℚ) +
        36 * B.coeff (2 : ℚ) * G.coeff (5 : ℚ) +
        36 * B.coeff (3 : ℚ) * G.coeff (4 : ℚ) +
        36 * B.coeff (4 : ℚ) * G.coeff (3 : ℚ) +
        36 * B.coeff (5 : ℚ) * G.coeff (2 : ℚ) +
        36 * B.coeff (6 : ℚ) * G.coeff (1 : ℚ) +
        36 * B.coeff (7 : ℚ) * G.coeff (0 : ℚ) +
        18 * F.coeff (7 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
        36 * C.coeff (1 : ℚ) * F.coeff (6 : ℚ) +
        36 * C.coeff (2 : ℚ) * F.coeff (5 : ℚ) +
        36 * C.coeff (3 : ℚ) * F.coeff (4 : ℚ) +
        36 * C.coeff (4 : ℚ) * F.coeff (3 : ℚ) +
        36 * C.coeff (5 : ℚ) * F.coeff (2 : ℚ) +
        36 * C.coeff (6 : ℚ) * F.coeff (1 : ℚ) +
        27 * epsilon * B.coeff (7 : ℚ) = 0) ∧
    (4 * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ) * F.coeff (6 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (5 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (1 : ℚ) * F.coeff (5 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (3 : ℚ) * F.coeff (4 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (2 : ℚ) * F.coeff (4 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (1 : ℚ) * F.coeff (4 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (4 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (3 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (2 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (1 : ℚ) * B.coeff (1 : ℚ) * F.coeff (3 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (5 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (4 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (3 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (1 : ℚ) * B.coeff (2 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (2 : ℚ) * B.coeff (1 : ℚ) * F.coeff (2 : ℚ) +
        4 * A.coeff (-2 : ℚ) * B.coeff (6 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (-1 : ℚ) * B.coeff (5 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (0 : ℚ) * B.coeff (4 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (1 : ℚ) * B.coeff (3 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (2 : ℚ) * B.coeff (2 : ℚ) * F.coeff (1 : ℚ) +
        4 * A.coeff (3 : ℚ) * B.coeff (1 : ℚ) * F.coeff (1 : ℚ) +
        4 * C.coeff (3 : ℚ) * B.coeff (1 : ℚ) ^ 2 +
        8 * C.coeff (2 : ℚ) * B.coeff (1 : ℚ) * B.coeff (2 : ℚ) +
        4 * C.coeff (1 : ℚ) *
          (2 * B.coeff (1 : ℚ) * B.coeff (3 : ℚ) +
            B.coeff (2 : ℚ) ^ 2) +
        (4 * C.coeff (0 : ℚ) + 3 * gamma) *
          (2 * B.coeff (1 : ℚ) * B.coeff (4 : ℚ) +
            2 * B.coeff (2 : ℚ) * B.coeff (3 : ℚ)) -
        6 * G.coeff (5 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) -
        12 * C.coeff (1 : ℚ) * G.coeff (4 : ℚ) -
        12 * C.coeff (2 : ℚ) * G.coeff (3 : ℚ) -
        12 * C.coeff (3 : ℚ) * G.coeff (2 : ℚ) -
        12 * C.coeff (4 : ℚ) * G.coeff (1 : ℚ) -
        12 * C.coeff (5 : ℚ) * G.coeff (0 : ℚ) -
        12 * F.coeff (1 : ℚ) * F.coeff (4 : ℚ) -
        12 * F.coeff (2 : ℚ) * F.coeff (3 : ℚ) -
        9 * epsilon * C.coeff (5 : ℚ) = 0)

/-- Source backwire: the derivative-next residual with its preserved
`G[-1] = 0` sibling refined child by child through the seventh unused
coefficient rows. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenSeventhResidual
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
        (RhoOneGZeroChildBGainRefinedSeventh68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G ∨
         RhoOneGZeroChildFGainRefinedSeventh68 T.source.gamma
           T.source.epsilon T.source.A T.source.B T.source.C0
           T.source.D T.source.E A B C F G)) := by
  dsimp only [RhoOneGZeroChildBGainRefinedSeventh68,
    RhoOneGZeroChildFGainRefinedSeventh68]
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenSixthResidual
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
      dsimp only [RhoOneGZeroChildBGainRefinedSixth68,
        RhoOneGZeroChildBGainRefinedFifth68,
        RhoOneGZeroChildBGainRefinedFourth68,
        RhoOneGZeroChildBGainRefinedThird68,
        RhoOneGZeroChildBGainRefinedNext68,
        RhoOneGZeroChildBGainRefined68] at hBgain'
      have hB2H : (↑(2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hBgain'.1.1.1.1.1.1.1
      have htie4 := rhoOneGZeroChildSeventhI4Load_bGain_coeff_seven68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hB2H hCH hFH hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
      have htie3 := rhoOneGZeroChildSeventhI3Cap_bGain_coeff_five68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH hB2H hCH hFH hGH hi3R
      rw [hCRraw, hFRraw, hGRraw] at htie3
      simp only [AR, BR] at htie3
      exact ⟨hBgain, htie4, htie3⟩
    · right
      have hFgain' := hFgain
      dsimp only [RhoOneGZeroChildFGainRefinedSixth68,
        RhoOneGZeroChildFGainRefinedFifth68,
        RhoOneGZeroChildFGainRefinedFourth68,
        RhoOneGZeroChildFGainRefinedThird68,
        RhoOneGZeroChildFGainRefinedNext68,
        RhoOneGZeroChildFGainRefined68] at hFgain'
      have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by
        simpa only [BR] using hB
      have hFH1 : (↑(1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root FR).orderTop := by
        rw [hFRraw]
        exact hFgain'.1.1.1.1.1.1.1
      have htie4 := rhoOneGZeroChildSeventhI4Load_fGain_coeff_seven68
        T.root T.source.gamma T.source.epsilon i4 BR CR FR GR
        hBH hCH hFH1 hGH hload
      rw [hCRraw, hFRraw, hGRraw] at htie4
      simp only [BR] at htie4
      have htie3 := rhoOneGZeroChildSeventhI3Cap_fGain_coeff_five68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH hBH hCH hFH1 hGH hi3R
      rw [hCRraw, hFRraw, hGRraw] at htie3
      simp only [AR, BR] at htie3
      exact ⟨hFgain, htie4, htie3⟩

#print axioms laurent_coeff_mul_lower_seven_gZeroChildSeventh68
#print axioms rhoOneGZeroChildSeventhI4Load_bGain_coeff_seven68
#print axioms rhoOneGZeroChildSeventhI4Load_fGain_coeff_seven68
#print axioms rhoOneGZeroChildSeventhI3Cap_bGain_coeff_five68
#print axioms rhoOneGZeroChildSeventhI3Cap_fGain_coeff_five68
#print axioms rhoOneGZeroChildSeventh_bGain_affine_tail_minor68
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenSeventhResidual

end AlignedSquareGZeroChildSeventh68

end Max11DegreeRoutes
