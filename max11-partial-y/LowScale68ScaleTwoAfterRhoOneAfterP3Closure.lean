import LowScale68ScaleTwoAfterRhoOneAfterP3Residual

/-! # The row-zero obstruction on the final post-`p₃` residual

At the `(0,0,1,1,1)` box, the integrated coordinate `V` has unique leading
term `(2/9)C²`.  Consequently the weight `-4` row-zero coefficient is
`(4/9)D C²`.  The surviving residual makes both `C` and `D` nonzero, so this
closes the last post-`p₃` branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterP3Nonzero68

variable {k : Type*} [Field k] [CharZero k]

local instance afterP3NonzeroHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedIntegratedU68AfterP3
    (h A B C0 D E : k[X]) (L alpha beta gamma delta zeta : k) : k[X] :=
  C (4 / 9 : k) * B * C0 + C (4 / 9 : k) * A * D -
  C (4 / 27 : k) * h * A ^ 2 * B +
  C L * (C (7 / 6 : k) * E + C (7 / 72 : k) * h * B ^ 2 +
    C (7 / 36 : k) * A * C0 - C (35 / 1296 : k) * h * A ^ 3) +
  C alpha * D + C beta * (C (5 / 6 : k) * C0 -
    C (5 / 72 : k) * h * A ^ 2) + C ((2 / 3 : k) * gamma) * h * B +
  C ((1 / 2 : k) * delta) * h * A + C zeta * h

def localClearedIntegratedV68AfterP3
    (h A B C0 D E : k[X])
    (L alpha beta gamma delta epsilon eta : k) : k[X] :=
  C (2 / 9 : k) * C0 ^ 2 + C (4 / 9 : k) * h * B * D +
  C (4 / 9 : k) * h * A * E - C (4 / 27 : k) * h ^ 2 * A * B ^ 2 -
  C (4 / 27 : k) * h * A ^ 2 * C0 + C (5 / 243 : k) * h ^ 2 * A ^ 4 +
  C L * (C (7 / 36 : k) * h * B * C0 +
    C (7 / 36 : k) * h * A * D - C (35 / 432 : k) * h ^ 2 * A ^ 2 * B) +
  C alpha * h * E + C beta * (C (5 / 6 : k) * h * D -
    C (5 / 36 : k) * h ^ 2 * A * B) +
  C gamma * (C (2 / 3 : k) * h * C0 - C (1 / 9 : k) * h ^ 2 * A ^ 2) +
  C ((1 / 2 : k) * delta) * h ^ 2 * B +
  C ((1 / 3 : k) * epsilon) * h ^ 2 * A + C eta * h ^ 2

theorem algebraMap_localClearedIntegratedU68AfterP3
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta zeta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 = A)
    (hB : algebraMap k[X] (RatFunc k) B0 = B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      algebraMap k[X] (RatFunc k) h0 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      algebraMap k[X] (RatFunc k) h0 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      algebraMap k[X] (RatFunc k) h0 * E) :
    algebraMap k[X] (RatFunc k)
      (localClearedIntegratedU68AfterP3 h0 A0 B0 C00 D0 E0
        L alpha beta gamma delta zeta) =
      algebraMap k[X] (RatFunc k) h0 *
        integratedU68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C zeta) := by
  simp only [localClearedIntegratedU68AfterP3, integratedU68, map_add,
    map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem algebraMap_localClearedIntegratedV68AfterP3
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta epsilon eta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 = A)
    (hB : algebraMap k[X] (RatFunc k) B0 = B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      algebraMap k[X] (RatFunc k) h0 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      algebraMap k[X] (RatFunc k) h0 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      algebraMap k[X] (RatFunc k) h0 * E) :
    algebraMap k[X] (RatFunc k)
      (localClearedIntegratedV68AfterP3 h0 A0 B0 C00 D0 E0
        L alpha beta gamma delta epsilon eta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 *
        integratedV68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C eta) := by
  simp only [localClearedIntegratedV68AfterP3, integratedV68, map_add,
    map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem lowerRowZeroHahn68_coeff_neg4_afterP3
    (U D dE dV : HahnSeries ℚ k) (x : k)
    (hU : (↑(-1 : ℚ) : WithTop ℚ) ≤ U.orderTop)
    (hD : (↑(-1 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hdE : (↑(-2 : ℚ) : WithTop ℚ) ≤ dE.orderTop)
    (hdV : (↑(-3 : ℚ) : WithTop ℚ) ≤ dV.orderTop)
    (hdVco : dV.coeff (-3 : ℚ) = (-4 / 9 : k) * x ^ 2) :
    (U * dE - D * dV).coeff (-4 : ℚ) =
      (4 / 9 : k) * D.coeff (-1 : ℚ) * x ^ 2 := by
  have hUEord := hahnOrderTop_mul_lower46 U dE (-1) (-2) hU hdE
  have hUE : (U * dE).coeff (-4 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr (by norm_num : (-4 : ℚ) < -1 + -2)).trans_le
      hUEord
  have hDV := hahnCoeff_mul_at_lower46 D dV (-1) (-3) hD hdV
  norm_num at hDV
  simp only [HahnSeries.coeff_sub, hUE, hDV, hdVco, zero_sub]
  ring

theorem SquareConstantLIntegratedLocalRootData68.afterP3_rowZero_source_split
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    w.eval T.root = 0 ∨
      (p.coeff 1).eval T.root -
        (1 / 3 : k) * w.eval T.root * g.eval T.root = 0 := by
  let A0 := localClearedA68AfterP4 g u
  let B0 := localClearedB68AfterP3 g u v
  let C00 := localClearedC68AfterP3 h0 g u v w
  let D0 := localClearedD68AfterP3 h0 g u v w (p.coeff 1)
  let E0 := localClearedE68AfterP3 h0 g u v w (p.coeff 1) (p.coeff 0)
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterP3
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3 hp2
  let UR := integratedU68 (RatFunc.C l) T.source.A T.source.B
    T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
    (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
    (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta)
  let VR := integratedV68 (RatFunc.C l) T.source.A T.source.B
    T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
    (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
    (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
    (RatFunc.C T.source.eta)
  let U0 := localClearedIntegratedU68AfterP3 h0 A0 B0 C00 D0 E0 l
    T.source.alpha T.source.beta T.source.gamma T.source.delta T.source.zeta
  let V0 := localClearedIntegratedV68AfterP3 h0 A0 B0 C00 D0 E0 l
    T.source.alpha T.source.beta T.source.gamma T.source.delta
    T.source.epsilon T.source.eta
  have hU : algebraMap k[X] (RatFunc k) U0 =
      algebraMap k[X] (RatFunc k) h0 * UR := by
    exact algebraMap_localClearedIntegratedU68AfterP3 h0 A0 B0 C00 D0 E0
      T.source.A T.source.B T.source.C0 T.source.D T.source.E l
      T.source.alpha T.source.beta T.source.gamma T.source.delta T.source.zeta
      hA hB hC hD hE
  have hV : algebraMap k[X] (RatFunc k) V0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * VR := by
    exact algebraMap_localClearedIntegratedV68AfterP3 h0 A0 B0 C00 D0 E0
      T.source.A T.source.B T.source.C0 T.source.D T.source.E l
      T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.eta hA hB hC hD hE
  obtain ⟨c, hc, hsingle, hderiv⟩ := ratFuncAtHahn68_linearRoot_single_deriv
    h0 T.root T.scale_degree T.root_eq
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let UH := ratFuncAtHahn46 T.root UR
  let VH := ratFuncAtHahn46 T.root VR
  let dEH := ratFuncAtHahn46 T.root (Differential.deriv T.source.E)
  let dVH := ratFuncAtHahn46 T.root (Differential.deriv VR)
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0 C00
    T.source.C0 1 hc hsingle (by simpa only [pow_one] using hC)
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0 D0
    T.source.D 1 hc hsingle (by simpa only [pow_one] using hD)
  have hVco := localHahn_coeff_neg_of_cleared T.root c h0 V0 VR 2
    hc hsingle hV
  have hdVco := localHahn_deriv_coeff_neg_succ_of_cleared
    T.root c h0 V0 VR 2 hc hsingle hderiv hV
  have hUord := localHahn_orderTop_ge_of_cleared T.root h0 U0 UR 1
    T.scale_order (by simpa only [pow_one] using hU)
  have hDord := localHahn_orderTop_ge_of_cleared T.root h0 D0 T.source.D 1
    T.scale_order (by simpa only [pow_one] using hD)
  have hdEord := localHahn_deriv_orderTop_ge_of_cleared T.root h0 E0
    T.source.E 1 T.scale_order (by simpa only [pow_one] using hE)
  have hdVord := localHahn_deriv_orderTop_ge_of_cleared T.root h0 V0 VR 2
    T.scale_order hV
  norm_num at hCco hDco hVco hdVco
  have hVroot : V0.eval T.root = (2 / 9 : k) * C00.eval T.root ^ 2 := by
    simp [V0, localClearedIntegratedV68AfterP3, T.root_eq]
  have hVlead : VH.coeff (-2 : ℚ) =
      (2 / 9 : k) * CH.coeff (-1 : ℚ) ^ 2 := by
    rw [hVco, hVroot, hCco]
    field_simp [hc]
  have hdVlead : dVH.coeff (-3 : ℚ) =
      (-4 / 9 : k) * CH.coeff (-1 : ℚ) ^ 2 := by
    rw [hdVco, hVlead]
    ring
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hx := GCD369RatFuncDerivative (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C l) T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst l) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  have hrowR := hlow.2.2.2.2
  have hrowH := congrArg (ratFuncAtHahn46 T.root) hrowR
  have hrowH' : UH * dEH - DH * dVH = ratFuncAtHahn46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    dsimp only [UR, VR, UH, VH, CH, DH, dEH, dVH]
    simpa only [ratFuncDerivation46_apply, map_sub, map_mul] using hrowH
  have hterminal : (ratFuncAtHahn46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-4 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr (by norm_num : (-4 : ℚ) < -1)).trans_le
      (le_of_eq T.terminal_order.symm)
  have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff (-4 : ℚ)) hrowH'
  rw [hterminal] at hcoeff
  have hface := lowerRowZeroHahn68_coeff_neg4_afterP3 UH DH dEH dVH
    (CH.coeff (-1 : ℚ)) (by
      dsimp only [UH]
      convert hUord using 1 <;> norm_num) (by
      dsimp only [DH]
      convert hDord using 1 <;> norm_num) (by
      dsimp only [dEH]
      convert hdEord using 1 <;> norm_num) (by
      dsimp only [dVH]
      convert hdVord using 1 <;> norm_num) hdVlead
  rw [hface] at hcoeff
  have hprod : DH.coeff (-1 : ℚ) * CH.coeff (-1 : ℚ) ^ 2 = 0 := by
    have hfac : (4 / 9 : k) *
        (DH.coeff (-1 : ℚ) * CH.coeff (-1 : ℚ) ^ 2) = 0 := by
      linear_combination hcoeff
    exact (mul_eq_zero.mp hfac).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hprod with hDz | hCz
  · apply Or.inr
    rw [hDco] at hDz
    have hraw := (mul_eq_zero.mp hDz).resolve_left (inv_ne_zero hc)
    simpa [D0, localClearedD68AfterP3, T.root_eq] using hraw
  · apply Or.inl
    have hCzero : CH.coeff (-1 : ℚ) = 0 := eq_zero_of_pow_eq_zero hCz
    rw [hCco] at hCzero
    have hraw := (mul_eq_zero.mp hCzero).resolve_left (inv_ne_zero hc)
    simpa [C00, localClearedC68AfterP3, T.root_eq] using hraw

theorem SquareConstantLIntegratedLocalRootData68.afterP3_nonzeroResidual_impossible
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w)
    (hres : AfterP3NonzeroResidual68 T g u w) : False := by
  rcases hres with ⟨c, hc, hpack⟩
  dsimp only at hpack
  rcases hpack with ⟨hx, hlinear, hpoly⟩
  rcases T.afterP3_rowZero_source_split hp hH hp6 hp5 hp4 hp3 hp2 with
    hw | hd
  · have hx0 : c⁻¹ * w.eval T.root = 0 := by rw [hw, mul_zero]
    exact hx hx0
  · rw [hd, mul_zero, mul_zero, zero_add] at hlinear
    have hlx : l * (c⁻¹ * w.eval T.root) = 0 := by
      have hfac : (7 : k) * (l * (c⁻¹ * w.eval T.root)) = 0 := by
        linear_combination hlinear
      exact (mul_eq_zero.mp hfac).resolve_left (by norm_num)
    exact T.septic_ne_zero ((mul_eq_zero.mp hlx).resolve_right hx)

/-- The sole residual is impossible; hence the complete square-scale local
package in normalized bidegree `(6,8)` cannot occur. -/
theorem SquareConstantLIntegratedLocalRootData68.scaleTwo68_impossible
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) : False := by
  rcases T.afterP3_global_residual hp hH hp6 with
    ⟨g, u, v, w, hp5, hp4, hp3, hp2, hres⟩
  exact T.afterP3_nonzeroResidual_impossible
    hp hH hp6 hp5 hp4 hp3 hp2 hres

end AfterP3Nonzero68

end Max11DegreeRoutes
