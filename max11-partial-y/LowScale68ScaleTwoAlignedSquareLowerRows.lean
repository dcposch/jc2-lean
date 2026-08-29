import LowScale68ScaleTwoAlignedSquareRowTwo

/-! # Lower zero-septic rows and the first aligned square descent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareLowerRows68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareLowerRowsHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The fourth scalar local row on the aligned zero-septic chamber. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowOne_zero
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0)
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
  let TR := integratedT68 (RatFunc.C 0) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.epsilon)
  let UR := integratedU68 (RatFunc.C 0) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
    (RatFunc.C T0.source.zeta)
  let VR := integratedV68 (RatFunc.C 0) T0.source.A T0.source.B
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
  obtain ⟨hA, hB, hC, hD, hE⟩ := T0.coordinateOrderBounds hp hH hp6
  obtain ⟨hdA, hdB, hdC, hdD, hdE⟩ :=
    T0.coordinateDerivativeOrderBounds hp hH hp6
  obtain ⟨hdAco, hdBco, hdCco, hdDco, hdEco⟩ :=
    T0.coordinateDerivativeInitialCoeffs hp hH hp6
  have hboundary := T0.integratedLocalRowTwoBoundaryData hp hH hp6
  dsimp only at hboundary
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hx := GCD369RatFuncDerivative (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T0.source.A T0.source.B
      T0.source.C0 T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
      (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
      (RatFunc.C T0.source.zeta) (RatFunc.C T0.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T0.source.alpha) (hconst T0.source.beta)
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

/-- The terminal has order `-1`, so it makes no contribution to the fifth
first-box row at exponent `-66`, also when the septic is zero. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowZero_zero
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0)
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
  let UR := integratedU68 (RatFunc.C 0) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
    (RatFunc.C T0.source.zeta)
  let VR := integratedV68 (RatFunc.C 0) T0.source.A T0.source.B
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
  obtain ⟨hA, hB, hC, hD, hE⟩ := T0.coordinateOrderBounds hp hH hp6
  obtain ⟨hdA, hdB, hdC, hdD, hdE⟩ :=
    T0.coordinateDerivativeOrderBounds hp hH hp6
  obtain ⟨hdAco, hdBco, hdCco, hdDco, hdEco⟩ :=
    T0.coordinateDerivativeInitialCoeffs hp hH hp6
  have hboundary := T0.integratedLocalRowTwoBoundaryData hp hH hp6
  dsimp only at hboundary
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hx := GCD369RatFuncDerivative (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T0.source.A T0.source.B
      T0.source.C0 T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
      (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
      (RatFunc.C T0.source.zeta) (RatFunc.C T0.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T0.source.alpha) (hconst T0.source.beta)
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

/-- All five zero-septic first-box rows lie on the unique depressed cubic
core. -/
theorem SquareZeroLIntegratedLocalRootData68.localCubicCore
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0)
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

/-- The cubic-core packet forces the next sextic source coefficient to
vanish at the simple zero of the scale. -/
theorem SquareZeroLIntegratedLocalRootData68.source_p5_root_zero
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0)
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

/-- First genuine aligned-square descent: the linear square root divides
the next sextic source coefficient. -/
theorem SquareZeroLIntegratedLocalRootData68.source_scale_dvd_p5
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0)
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

end AlignedSquareLowerRows68

end Max11DegreeRoutes
