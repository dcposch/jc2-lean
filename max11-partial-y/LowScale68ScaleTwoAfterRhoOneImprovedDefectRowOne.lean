import LowScale68ScaleTwoAfterRhoOneImprovedDefectNextRow

/-! # The decisive row-one face after the improved-defect descent

At the sharp post-rho-one box, the row-one differential identity has a
unique pole-seven contribution: `-2 C V'`.  Its coefficient excludes both
quadratic branches and forces a fourth scale factor into `p₄`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOneImprovedDefectRowOne68

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneImprovedDefectRowOneHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def afterRhoOneNextRowOneFace68 (a x : k) : k :=
  x * ((2 / 9 : k) * x ^ 2 - (4 / 27 : k) * a ^ 2 * x +
    (5 / 243 : k) * a ^ 4)

theorem lowerRowOneHahn68_coeff_neg7_afterRhoOneNext
    (L : k) (A B C0 D E S T U V dC dD dE dT dU dV : HahnSeries ℚ k)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-2 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (P : AfterRhoOneNextRowTwoBoundary68 L
      A B C0 D E S T U V dC dD dE dT dU dV) :
    (U * dD + 2 * T * dE - 2 * C0 * dV - D * dU).coeff (-7 : ℚ) =
      8 * C0.coeff (-2 : ℚ) * V.coeff (-4 : ℚ) := by
  have hCV := hahnCoeff_mul_at_lower46 C0 dV (-2) (-5) hC P.dv_order
  norm_num at hCV
  have hUDord := hahnOrderTop_mul_lower46 U dD (-3) (-3)
    P.u_order P.dd_order
  have hTEord := hahnOrderTop_mul_lower46 T dE (-3) (-3)
    P.t_order P.de_order
  have hDUord := hahnOrderTop_mul_lower46 D dU (-2) (-4)
    hD P.du_order
  have hzero (Z : HahnSeries ℚ k)
      (hZ : (↑(-6 : ℚ) : WithTop ℚ) ≤ Z.orderTop) :
      Z.coeff (-7 : ℚ) = 0 := by
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr (by norm_num)).trans_le hZ)
  have hUD : (U * dD).coeff (-7 : ℚ) = 0 :=
    hzero (U * dD) (by convert hUDord using 1 <;> norm_num)
  have hTE : (T * dE).coeff (-7 : ℚ) = 0 :=
    hzero (T * dE) (by convert hTEord using 1 <;> norm_num)
  have hDU : (D * dU).coeff (-7 : ℚ) = 0 :=
    hzero (D * dU) (by convert hDUord using 1 <;> norm_num)
  have hrewrite :
      U * dD + 2 * T * dE - 2 * C0 * dV - D * dU =
        U * dD + (T * dE + T * dE) -
          (C0 * dV + C0 * dV) - D * dU := by ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub,
    hUD, hTE, hCV, hDU, zero_add, add_zero]
  rw [P.dv_coeff]
  ring

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_rowOneFace
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    let a := (ratFuncAtHahn46 T0.root T0.source.A).coeff (-1 : ℚ)
    let x := (ratFuncAtHahn46 T0.root T0.source.C0).coeff (-2 : ℚ)
    afterRhoOneNextRowOneFace68 a x = 0 := by
  dsimp only
  let AH := ratFuncAtHahn46 T0.root T0.source.A
  let BH := ratFuncAtHahn46 T0.root T0.source.B
  let CH := ratFuncAtHahn46 T0.root T0.source.C0
  let DH := ratFuncAtHahn46 T0.root T0.source.D
  let EH := ratFuncAtHahn46 T0.root T0.source.E
  let SR := integratedS68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D (RatFunc.C T0.source.alpha)
    (RatFunc.C T0.source.beta) (RatFunc.C T0.source.delta)
  let TR := integratedT68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.epsilon)
  let UR := integratedU68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
    (RatFunc.C T0.source.zeta)
  let VR := integratedV68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
    (RatFunc.C T0.source.epsilon) (RatFunc.C T0.source.eta)
  let SH := ratFuncAtHahn46 T0.root SR
  let TH := ratFuncAtHahn46 T0.root TR
  let UH := ratFuncAtHahn46 T0.root UR
  let VH := ratFuncAtHahn46 T0.root VR
  let dCH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.C0)
  let dDH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.D)
  let dEH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.E)
  let dTH := ratFuncAtHahn46 T0.root (Differential.deriv TR)
  let dUH := ratFuncAtHahn46 T0.root (Differential.deriv UR)
  let dVH := ratFuncAtHahn46 T0.root (Differential.deriv VR)
  have P := T0.afterRhoOneNextRowTwoBoundary hp hH hp6 hp5 hp4 hp3
  dsimp only at P
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T0.coordinateOrderBoundsAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
  have hconst (z : k) : ratFuncDerivation68 (RatFunc.C z) = 0 := by
    have hz := GCD369RatFuncDerivative (C z : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hz
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C l) T0.source.A T0.source.B
      T0.source.C0 T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
      (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
      (RatFunc.C T0.source.zeta) (RatFunc.C T0.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst l) (hconst T0.source.alpha) (hconst T0.source.beta)
      (hconst T0.source.gamma) (hconst T0.source.delta)
      (hconst T0.source.epsilon) (hconst T0.source.zeta)
      (hconst T0.source.eta) T0.source.bracket_eq
  have hrowR := hlow.2.2.2.1
  have hrowH := congrArg (ratFuncAtHahn46 T0.root) hrowR
  have hrowH' : UH * dDH + 2 * TH * dEH - 2 * CH * dVH - DH * dUH = 0 := by
    dsimp only [AH, BH, CH, DH, EH, SR, TR, UR, VR, SH, TH, UH, VH,
      dCH, dDH, dEH, dTH, dUH, dVH]
    simpa only [ratFuncDerivation46_apply, map_add, map_sub, map_mul,
      map_ofNat, map_zero] using hrowH
  have hcoeff := congrArg
    (fun z : HahnSeries ℚ k => z.coeff (-7 : ℚ)) hrowH'
  simp only [HahnSeries.coeff_zero] at hcoeff
  have hface := lowerRowOneHahn68_coeff_neg7_afterRhoOneNext
    l AH BH CH DH EH SH TH UH VH dCH dDH dEH dTH dUH dVH
      (by simpa only [CH] using hC) (by simpa only [DH] using hD) P
  rw [hface, P.v_coeff] at hcoeff
  have hscalar : (8 : k) ≠ 0 := by norm_num
  have hface0 : CH.coeff (-2 : ℚ) *
      ((2 / 9 : k) * CH.coeff (-2 : ℚ) ^ 2 -
        (4 / 27 : k) * AH.coeff (-1 : ℚ) ^ 2 * CH.coeff (-2 : ℚ) +
        (5 / 243 : k) * AH.coeff (-1 : ℚ) ^ 4) = 0 := by
    have hcoeff' : (8 : k) *
        (CH.coeff (-2 : ℚ) *
          ((2 / 9 : k) * CH.coeff (-2 : ℚ) ^ 2 -
            (4 / 27 : k) * AH.coeff (-1 : ℚ) ^ 2 *
              CH.coeff (-2 : ℚ) +
            (5 / 243 : k) * AH.coeff (-1 : ℚ) ^ 4)) = 0 := by
      linear_combination hcoeff
    exact (mul_eq_zero.mp hcoeff').resolve_left hscalar
  simpa only [afterRhoOneNextRowOneFace68, AH, CH] using hface0

theorem afterRhoOne_firstBranch_rowOne_impossible
    (a x : k) (ha : a ≠ 0) (hx : 3 * x - a ^ 2 = 0)
    (hrow : afterRhoOneNextRowOneFace68 a x = 0) : False := by
  have hx' : x = a ^ 2 / 3 := by linear_combination (1 / 3 : k) * hx
  rw [hx', afterRhoOneNextRowOneFace68] at hrow
  have hpow : a ^ 6 = 0 := by
    have hfactor : (-1 / 729 : k) ≠ 0 := by norm_num
    apply (mul_eq_zero.mp ?_).resolve_left hfactor
    linear_combination hrow
  exact ha (eq_zero_of_pow_eq_zero hpow)

theorem afterRhoOne_secondBranch_rowOne_impossible
    (a x : k) (ha : a ≠ 0) (hx : 9 * x - 2 * a ^ 2 = 0)
    (hrow : afterRhoOneNextRowOneFace68 a x = 0) : False := by
  have hx' : x = 2 * a ^ 2 / 9 := by linear_combination (1 / 9 : k) * hx
  rw [hx', afterRhoOneNextRowOneFace68] at hrow
  have hpow : a ^ 6 = 0 := by
    have hfactor : (-2 / 6561 : k) ≠ 0 := by norm_num
    apply (mul_eq_zero.mp ?_).resolve_left hfactor
    linear_combination hrow
  exact ha (eq_zero_of_pow_eq_zero hpow)

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOne_rowOne_forces_p4
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    h0 ^ 4 ∣ p.coeff 4 := by
  have hthree := T0.afterRhoOneNext_face hp hH hp6 hp5 hp4 hp3
  have hrow := T0.afterRhoOneNext_rowOneFace hp hH hp6 hp5 hp4 hp3
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T0.coordinateInitialPacketAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
  let a : k := c⁻¹ * u.eval T0.root
  let x : k := (c ^ 2)⁻¹ * (p.coeff 2).eval T0.root
  dsimp only at hthree hrow
  rw [hAco, hCco] at hthree hrow
  change a * (3 * x - a ^ 2) * (9 * x - 2 * a ^ 2) = 0 at hthree
  change afterRhoOneNextRowOneFace68 a x = 0 at hrow
  by_cases ha : a = 0
  · have ha' : c⁻¹ * u.eval T0.root = 0 := by simpa only [a] using ha
    have huroot : u.eval T0.root = 0 :=
      (mul_eq_zero.mp ha').resolve_left (inv_ne_zero hc)
    obtain ⟨w, huw⟩ := linearPolynomial_dvd_of_eval_eq_zero
      h0 u T0.root T0.scale_degree T0.root_eq huroot
    refine ⟨w, ?_⟩
    rw [hp4, huw]
    ring
  · have hprod : (3 * x - a ^ 2) * (9 * x - 2 * a ^ 2) = 0 := by
      have hthree' : a * ((3 * x - a ^ 2) * (9 * x - 2 * a ^ 2)) = 0 := by
        simpa only [mul_assoc] using hthree
      exact (mul_eq_zero.mp hthree').resolve_left ha
    rcases mul_eq_zero.mp hprod with hx | hx
    · exact (afterRhoOne_firstBranch_rowOne_impossible a x ha hx hrow).elim
    · exact (afterRhoOne_secondBranch_rowOne_impossible a x ha hx hrow).elim

/-- Original-data checkpoint after the decisive row-one exclusion. -/
theorem SquareConstantLIntegratedLocalRootData68.afterRhoOne_rowOne_global_descend
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ p.coeff 4 ∧
      h0 ^ 2 ∣ p.coeff 3 := by
  rcases T0.afterRhoOne_next_divisibilities hp hH hp6 with
    ⟨⟨g, hp5⟩, ⟨u, hp4⟩, ⟨v, hp3⟩⟩
  refine ⟨⟨g, hp5⟩, ?_, ⟨v, hp3⟩⟩
  exact T0.afterRhoOne_rowOne_forces_p4 hp hH hp6 hp5 hp4 hp3

end AfterRhoOneImprovedDefectRowOne68

#print axioms lowerRowOneHahn68_coeff_neg7_afterRhoOneNext
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_rowOneFace
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOne_rowOne_forces_p4
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOne_rowOne_global_descend

end Max11DegreeRoutes
