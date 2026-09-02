import Sol68ScaleTwoAlignedSquareTerminalGNonzeroScratch

/-! # Source-order adapter for the nonzero `G[-1]` terminal face -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGNonzeroSource68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGNonzeroSourceHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- At a simple local parameter, differentiation lowers a rational
function's Hahn order by at most one.  This is the exact pole-shift needed
for the `G[-1]` child. -/
theorem ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
    (a : k) (h0 : k[X]) (f : RatFunc k)
    (hscale :
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ))
    (hf : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a f).orderTop) :
    (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (Differential.deriv f)).orderTop := by
  let H : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let HH : HahnSeries ℚ k := ratFuncAtHahn46 a H
  let FH : HahnSeries ℚ k := ratFuncAtHahn46 a f
  let dHH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv H)
  let dFH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv f)
  have hHH : HH.orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    simpa only [HH, H] using hscale
  have hFH : (↑(-1 : ℚ) : WithTop ℚ) ≤ FH.orderTop := by
    simpa only [FH] using hf
  have hprod : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (H * f)).orderTop := by
    have hm := hahnOrderTop_mul_lower46 HH FH 1 (-1) hHH.ge hFH
    norm_num at hm
    simpa only [HH, FH, map_mul, HahnSeries.orderTop_mul] using hm
  have hdprod : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (Differential.deriv (H * f))).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a (H * f) hprod
  have hHnonneg : (0 : WithTop ℚ) ≤ HH.orderTop := by
    rw [hHH]
    norm_num
  have hdH : (0 : WithTop ℚ) ≤ dHH.orderTop := by
    exact ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a H hHnonneg
  have hdHf : (↑(-1 : ℚ) : WithTop ℚ) ≤ (dHH * FH).orderTop := by
    have hm := hahnOrderTop_mul_lower46 dHH FH 0 (-1) hdH hFH
    rw [HahnSeries.orderTop_mul]
    convert hm using 1 <;> norm_num
  have hsum : (↑(-1 : ℚ) : WithTop ℚ) ≤
      ((ratFuncAtHahn46 a (Differential.deriv (H * f))) -
        dHH * FH).orderTop := by
    rw [sub_eq_add_neg]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · exact le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hdprod
    · rw [HahnSeries.orderTop_neg]
      exact hdHf
  have hleibniz :
      ratFuncAtHahn46 a (Differential.deriv (H * f)) - dHH * FH =
        HH * dFH := by
    dsimp only [dHH, FH, HH, dFH]
    simp only [Derivation.leibniz, map_add, map_mul, smul_eq_mul]
    ring
  rw [hleibniz] at hsum
  change (↑(-2 : ℚ) : WithTop ℚ) ≤ dFH.orderTop
  cases hm : dFH.orderTop with
  | top => simp [hm]
  | coe q =>
      rw [HahnSeries.orderTop_mul, hHH, hm] at hsum
      have hq : (-1 : ℚ) ≤ 1 + q := by
        exact WithTop.coe_le_coe.mp (by
          simpa only [WithTop.coe_add] using hsum)
      exact WithTop.coe_le_coe.mpr (by linarith)

/-- Abstract terminal-row form of the `G[-1]` reduction. -/
theorem rhoOneMainTangentTerminal_gNonzero_quadraticWall68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG terminal : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ))
    (hAne : A.coeff (-2 : ℚ) ≠ 0)
    (hGne : G.coeff (-1 : ℚ) ≠ 0)
    (hi3 : rhoOneZeroLCubicDoubleZeroGZeroThree68 gamma
      (A.coeff (-2 : ℚ)) (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
      (F.coeff (0 : ℚ)) (G.coeff (-1 : ℚ)) = 0)
    (hrow : rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG = terminal)
    (hterminal : terminal.orderTop = (↑(-1 : ℚ) : WithTop ℚ)) :
    3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) ^ 2 +
      4 * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ) ^ 2 = 0 := by
  have hcoeff := rhoOneMainTangentTerminalFourHahn_coeff_negFive_gBox68
    gamma epsilon A B C F G dA dB dC dF dG
      hA hB hC hF hG hdA hdB hdC hdF hdG hdAco
  have hterminal5 : terminal.coeff (-5 : ℚ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hterminal]
      exact WithTop.coe_lt_coe.mpr (by norm_num))
  have hleft5 :
      (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
        A B C F G dA dB dC dF dG).coeff (-5 : ℚ) = 0 := by
    rw [← rhoOneMainTangentTerminalFourHahn_eq68, hrow]
    exact hterminal5
  rw [hcoeff] at hleft5
  have hface : F.coeff (0 : ℚ) *
        (2 * C.coeff (0 : ℚ) + 3 * gamma) +
      2 * B.coeff (1 : ℚ) * G.coeff (-1 : ℚ) = 0 := by
    rcases mul_eq_zero.mp hleft5 with hleft | hface
    · exfalso
      apply hAne
      rcases mul_eq_zero.mp hleft with hc | ha2
      · norm_num at hc
      · exact sq_eq_zero_iff.mp ha2
    · exact hface
  exact rhoOneDoubleZero_gNonzero_quadraticWall_of_terminal68
    _ _ _ _ _ _ hAne hGne hface hi3

end AlignedSquareTerminalGNonzeroSource68

end Max11DegreeRoutes
