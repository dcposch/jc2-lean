import LowScale68ScaleTwoIntegratedBoundary

/-! # Final two first-box local rows for the `(6,8)` scale-two branch

This module transports the last two rows of the literal integrated Keller
system to the finite-place Hahn field.  At the first Newton boundary the
Keller terminal has no contribution: its order is `-1`, whereas the last
homogeneous row occurs at exponent `-66`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LocalRowOneZero68

variable {k : Type*} [Field k] [CharZero k]

local instance localRowOneZeroHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The fourth scalar local row is unconditional for every actual
square-source local package. -/
theorem SquareConstantLIntegratedLocalRootData68.topRowOne_zero
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowOne68
        ((ratFuncAtHahn46 T0.root T0.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.E).coeff (-30 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T0.root T0.source.A
  let BH := ratFuncAtHahn46 T0.root T0.source.B
  let CH := ratFuncAtHahn46 T0.root T0.source.C0
  let DH := ratFuncAtHahn46 T0.root T0.source.D
  let EH := ratFuncAtHahn46 T0.root T0.source.E
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
  let TH := ratFuncAtHahn46 T0.root TR
  let UH := ratFuncAtHahn46 T0.root UR
  let VH := ratFuncAtHahn46 T0.root VR
  let dDH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.D)
  let dEH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.E)
  let dUH := ratFuncAtHahn46 T0.root (Differential.deriv UR)
  let dVH := ratFuncAtHahn46 T0.root (Differential.deriv VR)
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T0.coordinateOrderBounds hp hH hp6
  obtain ⟨hdA, hdB, hdC, hdD, hdE⟩ :=
    T0.coordinateDerivativeOrderBounds hp hH hp6
  obtain ⟨hdAco, hdBco, hdCco, hdDco, hdEco⟩ :=
    T0.coordinateDerivativeInitialCoeffs hp hH hp6
  have hboundary :=
    T0.integratedLocalRowTwoBoundaryData hp hH hp6
  dsimp only at hboundary
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hx := GCD369RatFuncDerivative (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
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
    dsimp only [AH, BH, CH, DH, EH, TR, UR, VR, TH, UH, VH, dDH, dEH,
      dUH, dVH]
    simpa only [ratFuncDerivation46_apply, map_add, map_sub, map_mul,
      map_ofNat, map_zero] using hrowH
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-61 : ℚ)) hrowH'
  simp only [HahnSeries.coeff_zero] at hcoeff
  have hface := lowerRowOneHahn68_coeff_neg61
    AH BH CH DH EH TH UH VH dDH dEH dUH dVH hC hD
      hboundary.t_order hboundary.u_order hboundary.v_order hdD hdE
      hboundary.du_order hboundary.dv_order hboundary.t_coeff
      hboundary.u_coeff hboundary.v_coeff hdDco hdEco
      hboundary.du_coeff hboundary.dv_coeff
  rw [hface] at hcoeff
  have hfactor : (40 / 243 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- Exact first-box extraction of the last homogeneous one-form row. -/
theorem lowerRowZeroHahn68_coeff_neg66
    (A B C0 D E U V dE dV : HahnSeries ℚ k)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hUord : (↑(-35 : ℚ) : WithTop ℚ) ≤ U.orderTop)
    (hdE : (↑(-31 : ℚ) : WithTop ℚ) ≤ dE.orderTop)
    (hdV : (↑(-41 : ℚ) : WithTop ℚ) ≤ dV.orderTop)
    (hUco : U.coeff (-35 : ℚ) =
      (4 / 9 : k) * B.coeff (-15 : ℚ) * C0.coeff (-20 : ℚ) +
      (4 / 9 : k) * A.coeff (-10 : ℚ) * D.coeff (-25 : ℚ) -
      (4 / 27 : k) * A.coeff (-10 : ℚ) ^ 2 * B.coeff (-15 : ℚ))
    (hVco : V.coeff (-40 : ℚ) =
      (2 / 9 : k) * C0.coeff (-20 : ℚ) ^ 2 +
      (4 / 9 : k) * B.coeff (-15 : ℚ) * D.coeff (-25 : ℚ) +
      (4 / 9 : k) * A.coeff (-10 : ℚ) * E.coeff (-30 : ℚ) -
      (4 / 27 : k) * A.coeff (-10 : ℚ) * B.coeff (-15 : ℚ) ^ 2 -
      (4 / 27 : k) * A.coeff (-10 : ℚ) ^ 2 * C0.coeff (-20 : ℚ) +
      (5 / 243 : k) * A.coeff (-10 : ℚ) ^ 4)
    (hdEco : dE.coeff (-31 : ℚ) =
      (-30 : k) * E.coeff (-30 : ℚ))
    (hdVco : dV.coeff (-41 : ℚ) =
      (-40 : k) * V.coeff (-40 : ℚ)) :
    (U * dE - D * dV).coeff (-66 : ℚ) =
      (40 / 243 : k) * topRowZero68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ)) := by
  have hUE := hahnCoeff_mul_at_lower46 U dE (-35) (-31) hUord hdE
  have hDV := hahnCoeff_mul_at_lower46 D dV (-25) (-41) hD hdV
  norm_num at hUE hDV
  simp only [HahnSeries.coeff_sub, hUE, hDV]
  rw [hdEco, hdVco, hUco, hVco]
  simp only [topRowZero68]
  ring

/-- The Keller terminal has order `-1`, so the last first-box row at
exponent `-66` also vanishes. -/
theorem SquareConstantLIntegratedLocalRootData68.topRowZero_zero
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowZero68
        ((ratFuncAtHahn46 T0.root T0.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.E).coeff (-30 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T0.root T0.source.A
  let BH := ratFuncAtHahn46 T0.root T0.source.B
  let CH := ratFuncAtHahn46 T0.root T0.source.C0
  let DH := ratFuncAtHahn46 T0.root T0.source.D
  let EH := ratFuncAtHahn46 T0.root T0.source.E
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
  let UH := ratFuncAtHahn46 T0.root UR
  let VH := ratFuncAtHahn46 T0.root VR
  let dEH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.E)
  let dVH := ratFuncAtHahn46 T0.root (Differential.deriv VR)
  let terminalH := ratFuncAtHahn46 T0.root
    (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T0.coordinateOrderBounds hp hH hp6
  obtain ⟨hdA, hdB, hdC, hdD, hdE⟩ :=
    T0.coordinateDerivativeOrderBounds hp hH hp6
  obtain ⟨hdAco, hdBco, hdCco, hdDco, hdEco⟩ :=
    T0.coordinateDerivativeInitialCoeffs hp hH hp6
  have hboundary :=
    T0.integratedLocalRowTwoBoundaryData hp hH hp6
  dsimp only at hboundary
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hx := GCD369RatFuncDerivative (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
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
  have hrowR := hlow.2.2.2.2
  have hrowH := congrArg (ratFuncAtHahn46 T0.root) hrowR
  have hrowH' : UH * dEH - DH * dVH = terminalH := by
    dsimp only [AH, BH, CH, DH, EH, UR, VR, UH, VH, dEH, dVH,
      terminalH]
    simpa only [ratFuncDerivation46_apply, map_sub, map_mul] using hrowH
  have hterminal : terminalH.coeff (-66 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [T0.terminal_order]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-66 : ℚ)) hrowH'
  rw [hterminal] at hcoeff
  have hface := lowerRowZeroHahn68_coeff_neg66
    AH BH CH DH EH UH VH dEH dVH hD hboundary.u_order
      hdE hboundary.dv_order hboundary.u_coeff
      hboundary.v_coeff hdEco hboundary.dv_coeff
  rw [hface] at hcoeff
  have hfactor : (40 / 243 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- All five local first-box rows therefore place the sextic initial form
on the unique depressed cubic-core locus. -/
theorem SquareConstantLIntegratedLocalRootData68.localCubicCore
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    let a := (ratFuncAtHahn46 T0.root T0.source.A).coeff (-10 : ℚ)
    let b := (ratFuncAtHahn46 T0.root T0.source.B).coeff (-15 : ℚ)
    let c := (ratFuncAtHahn46 T0.root T0.source.C0).coeff (-20 : ℚ)
    let d := (ratFuncAtHahn46 T0.root T0.source.D).coeff (-25 : ℚ)
    let e := (ratFuncAtHahn46 T0.root T0.source.E).coeff (-30 : ℚ)
    b = 0 ∧ d = 0 ∧ c = a ^ 2 / 3 ∧ e = a ^ 3 / 27 := by
  dsimp only
  apply topRows_cubicCore68
  · exact T0.topRowFour_zero hp hH hp6
  · exact T0.topRowThree_zero hp hH hp6
  · exact T0.topRowTwo_zero hp hH hp6
  · exact T0.topRowOne_zero hp hH hp6
  · exact T0.topRowZero_zero hp hH hp6

/-- In source coordinates the five-row elimination forces the next sextic
coefficient to vanish at the simple zero of the scale.  Equivalently,
`h0` divides `p.coeff 5`; this is the exact input for the next, smaller
Newton box. -/
theorem SquareConstantLIntegratedLocalRootData68.source_p5_root_zero
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    (p.coeff 5).eval T0.root = 0 := by
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T0.coordinateInitialCoeffs hp hH hp6
  have hb := (T0.localCubicCore hp hH hp6).1
  have hBroot :
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)).eval
          T0.root =
        (5 / 27 : k) * (p.coeff 5).eval T0.root ^ 3 := by
    simp [localClearedB68, T0.root_eq]
  rw [hb, hBroot] at hBco
  field_simp [hc] at hBco
  norm_num at hBco
  exact hBco

/-- Polynomial form of the first-box descent: the linear square root of
the leading coefficient divides the next sextic coefficient. -/
theorem SquareConstantLIntegratedLocalRootData68.source_scale_dvd_p5
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    h0 ∣ p.coeff 5 := by
  let a := T0.root
  have hp5root : (p.coeff 5).IsRoot a := by
    dsimp only [a]
    exact T0.source_p5_root_zero hp hH hp6
  have hlinearRoot : X - C a ∣ p.coeff 5 :=
    Polynomial.dvd_iff_isRoot.mpr hp5root
  obtain ⟨c, hc, d, hlinear⟩ :=
    Polynomial.natDegree_eq_one.mp T0.scale_degree
  have hca : c * a + d = 0 := by
    dsimp only [a]
    simpa [← hlinear] using T0.root_eq
  have hd : d = -(c * a) := by
    linear_combination hca
  have hfactor : h0 = C c * (X - C a) := by
    calc
      h0 = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h0 ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

end LocalRowOneZero68

#print axioms SquareConstantLIntegratedLocalRootData68.topRowOne_zero
#print axioms lowerRowZeroHahn68_coeff_neg66
#print axioms SquareConstantLIntegratedLocalRootData68.topRowZero_zero
#print axioms SquareConstantLIntegratedLocalRootData68.localCubicCore
#print axioms SquareConstantLIntegratedLocalRootData68.source_p5_root_zero
#print axioms SquareConstantLIntegratedLocalRootData68.source_scale_dvd_p5

end Max11DegreeRoutes
