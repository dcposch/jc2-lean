import LowScale68ScaleTwoAlignedSquareDescent

/-! # The zero-septic row-two boundary

This transports the derivative initial forms and the four integrated
coordinate clearings to the aligned square-core local package.  No step uses
nonvanishing of the septic coefficient.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRowTwo68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRowTwoHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Exact derivative boundary coefficients in the zero-septic box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateDerivativeInitialCoeffs
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff
        (-11 : ℚ) =
      (-10 : k) * (ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.B)).coeff
        (-16 : ℚ) =
      (-15 : k) * (ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.C0)).coeff
        (-21 : ℚ) =
      (-20 : k) * (ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.D)).coeff
        (-26 : ℚ) =
      (-25 : k) * (ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.E)).coeff
        (-31 : ℚ) =
      (-30 : k) * (ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ) := by
  obtain ⟨c, hc, hsingle, hderiv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0 (localClearedA68 h0 (p.coeff 5) (p.coeff 4))
      T.source.A 10 hc hsingle hderiv hA using 1 <;> norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 hc hsingle hderiv hB using 1 <;> norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 hc hsingle hderiv hC using 1 <;> norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 hc hsingle hderiv hD using 1 <;>
      norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30 hc
        hsingle hderiv hE using 1 <;> norm_num

/-- Exact derivative Newton-box order bounds in the zero-septic box. -/
theorem SquareZeroLIntegratedLocalRootData68.coordinateDerivativeOrderBounds
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    (↑(-11 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.A)).orderTop ∧
    (↑(-16 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.B)).orderTop ∧
    (↑(-21 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.C0)).orderTop ∧
    (↑(-26 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.D)).orderTop ∧
    (↑(-31 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.E)).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) T.source.A 10
      T.scale_order hA using 1 <;> norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 T.scale_order hB using 1 <;> norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 T.scale_order hC using 1 <;> norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 T.scale_order hD using 1 <;>
      norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30
      T.scale_order hE using 1 <;> norm_num

/-- The four integrated coordinate clearings furnish the complete boundary
packet needed by the third scalar row, now with `L=0`. -/
theorem SquareZeroLIntegratedLocalRootData68.integratedLocalRowTwoBoundaryData
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    let AH := ratFuncAtHahn46 T0.root T0.source.A
    let BH := ratFuncAtHahn46 T0.root T0.source.B
    let CH := ratFuncAtHahn46 T0.root T0.source.C0
    let DH := ratFuncAtHahn46 T0.root T0.source.D
    let EH := ratFuncAtHahn46 T0.root T0.source.E
    let SR := integratedS68 (RatFunc.C 0) T0.source.A T0.source.B
      T0.source.C0 T0.source.D (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.delta)
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
    let SH := ratFuncAtHahn46 T0.root SR
    let TH := ratFuncAtHahn46 T0.root TR
    let UH := ratFuncAtHahn46 T0.root UR
    let VH := ratFuncAtHahn46 T0.root VR
    let dTH := ratFuncAtHahn46 T0.root (Differential.deriv TR)
    let dUH := ratFuncAtHahn46 T0.root (Differential.deriv UR)
    let dVH := ratFuncAtHahn46 T0.root (Differential.deriv VR)
    IntegratedLocalRowTwoBoundaryData68
      AH BH CH DH EH SH TH UH VH dTH dUH dVH := by
  dsimp only
  let A0 := localClearedA68 h0 (p.coeff 5) (p.coeff 4)
  let B0 := localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
  let C00 := localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
    (p.coeff 2)
  let D0 := localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1)
  let E0 := localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1) (p.coeff 0)
  let SR := integratedS68 (RatFunc.C 0) T0.source.A T0.source.B
    T0.source.C0 T0.source.D (RatFunc.C T0.source.alpha)
    (RatFunc.C T0.source.beta) (RatFunc.C T0.source.delta)
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
  let S0 := localClearedIntegratedS68 h0 A0 B0 C00 D0 0
    T0.source.alpha T0.source.beta T0.source.delta
  let T00 := localClearedIntegratedT68 h0 A0 B0 C00 D0 E0 0
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
  let U0 := localClearedIntegratedU68 h0 A0 B0 C00 D0 E0 0
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
    T0.source.zeta
  let V0 := localClearedIntegratedV68 h0 A0 B0 C00 D0 E0 0
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
    T0.source.epsilon T0.source.eta
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T0.source.clearedCoordinates hp T0.scale_ne_zero hH hp6
  change algebraMap k[X] (RatFunc k) A0 = _ at hA
  change algebraMap k[X] (RatFunc k) B0 = _ at hB
  change algebraMap k[X] (RatFunc k) C00 = _ at hC
  change algebraMap k[X] (RatFunc k) D0 = _ at hD
  change algebraMap k[X] (RatFunc k) E0 = _ at hE
  have hS : algebraMap k[X] (RatFunc k) S0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 25 * SR := by
    exact algebraMap_localClearedIntegratedS68 h0 A0 B0 C00 D0
      T0.source.A T0.source.B T0.source.C0 T0.source.D 0
      T0.source.alpha T0.source.beta T0.source.delta hA hB hC hD
  have hT : algebraMap k[X] (RatFunc k) T00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 30 * TR := by
    exact algebraMap_localClearedIntegratedT68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E 0
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
      hA hB hC hD hE
  have hU : algebraMap k[X] (RatFunc k) U0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 35 * UR := by
    exact algebraMap_localClearedIntegratedU68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E 0
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
      T0.source.zeta hA hB hC hD hE
  have hV : algebraMap k[X] (RatFunc k) V0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 40 * VR := by
    exact algebraMap_localClearedIntegratedV68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E 0
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
      T0.source.epsilon T0.source.eta hA hB hC hD hE
  obtain ⟨c, hc, hsingle, hderiv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T0.root T0.scale_degree T0.root_eq
  have hAco := localHahn_coeff_neg_of_cleared T0.root c h0 A0
    T0.source.A 10 hc hsingle hA
  have hBco := localHahn_coeff_neg_of_cleared T0.root c h0 B0
    T0.source.B 15 hc hsingle hB
  have hCco := localHahn_coeff_neg_of_cleared T0.root c h0 C00
    T0.source.C0 20 hc hsingle hC
  have hDco := localHahn_coeff_neg_of_cleared T0.root c h0 D0
    T0.source.D 25 hc hsingle hD
  have hEco := localHahn_coeff_neg_of_cleared T0.root c h0 E0
    T0.source.E 30 hc hsingle hE
  have hSco := localHahn_coeff_neg_of_cleared T0.root c h0 S0
    SR 25 hc hsingle hS
  have hTco := localHahn_coeff_neg_of_cleared T0.root c h0 T00
    TR 30 hc hsingle hT
  have hUco := localHahn_coeff_neg_of_cleared T0.root c h0 U0
    UR 35 hc hsingle hU
  have hVco := localHahn_coeff_neg_of_cleared T0.root c h0 V0
    VR 40 hc hsingle hV
  have hSord := localHahn_orderTop_ge_of_cleared T0.root h0 S0 SR
    25 T0.scale_order hS
  have hTord := localHahn_orderTop_ge_of_cleared T0.root h0 T00 TR
    30 T0.scale_order hT
  have hUord := localHahn_orderTop_ge_of_cleared T0.root h0 U0 UR
    35 T0.scale_order hU
  have hVord := localHahn_orderTop_ge_of_cleared T0.root h0 V0 VR
    40 T0.scale_order hV
  have hdTord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    T00 TR 30 T0.scale_order hT
  have hdUord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    U0 UR 35 T0.scale_order hU
  have hdVord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    V0 VR 40 T0.scale_order hV
  have hdTco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 T00 TR 30 hc hsingle hderiv hT
  have hdUco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 U0 UR 35 hc hsingle hderiv hU
  have hdVco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 V0 VR 40 hc hsingle hderiv hV
  have hSroot : S0.eval T0.root =
      (4 / 3 : k) * D0.eval T0.root +
        (4 / 9 : k) * A0.eval T0.root * B0.eval T0.root := by
    simp [S0, localClearedIntegratedS68, T0.root_eq]
  have hTroot : T00.eval T0.root =
      (4 / 3 : k) * E0.eval T0.root +
      (2 / 9 : k) * B0.eval T0.root ^ 2 +
      (4 / 9 : k) * A0.eval T0.root * C00.eval T0.root -
      (4 / 81 : k) * A0.eval T0.root ^ 3 := by
    simp [T00, localClearedIntegratedT68, T0.root_eq]
  have hUroot : U0.eval T0.root =
      (4 / 9 : k) * B0.eval T0.root * C00.eval T0.root +
      (4 / 9 : k) * A0.eval T0.root * D0.eval T0.root -
      (4 / 27 : k) * A0.eval T0.root ^ 2 * B0.eval T0.root := by
    simp [U0, localClearedIntegratedU68, T0.root_eq]
  have hVroot : V0.eval T0.root =
      (2 / 9 : k) * C00.eval T0.root ^ 2 +
      (4 / 9 : k) * B0.eval T0.root * D0.eval T0.root +
      (4 / 9 : k) * A0.eval T0.root * E0.eval T0.root -
      (4 / 27 : k) * A0.eval T0.root * B0.eval T0.root ^ 2 -
      (4 / 27 : k) * A0.eval T0.root ^ 2 * C00.eval T0.root +
      (5 / 243 : k) * A0.eval T0.root ^ 4 := by
    simp [V0, localClearedIntegratedV68, T0.root_eq]
  dsimp only [SR, TR, UR, VR] at hSco hTco hUco hVco hSord hTord hUord
  dsimp only [SR, TR, UR, VR] at hVord hdTord hdUord hdVord hdTco hdUco
  dsimp only [SR, TR, UR, VR] at hdVco
  norm_num at hAco hBco hCco hDco hEco hSco hTco hUco hVco
  refine {
    s_order := by simpa using hSord
    t_order := by simpa using hTord
    u_order := by simpa using hUord
    v_order := by simpa using hVord
    dt_order := by convert hdTord using 1 <;> norm_num
    du_order := by convert hdUord using 1 <;> norm_num
    dv_order := by convert hdVord using 1 <;> norm_num
    s_coeff := ?_
    t_coeff := ?_
    u_coeff := ?_
    v_coeff := ?_
    dt_coeff := by convert hdTco using 1 <;> norm_num
    du_coeff := by convert hdUco using 1 <;> norm_num
    dv_coeff := by convert hdVco using 1 <;> norm_num }
  · simp only [map_zero]
    rw [hSco, hSroot, hAco, hBco, hDco]
    field_simp [hc]
  · simp only [map_zero]
    rw [hTco, hTroot, hAco, hBco, hCco, hEco]
    field_simp [hc]
  · simp only [map_zero]
    rw [hUco, hUroot, hAco, hBco, hCco, hDco]
    field_simp [hc]
  · simp only [map_zero]
    rw [hVco, hVroot, hAco, hBco, hCco, hDco, hEco]
    field_simp [hc]

/-- The literal lower differential row forces the third scalar face to
vanish in the zero-septic box. -/
theorem SquareZeroLIntegratedLocalRootData68.topRowTwo_zero
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowTwo68
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
  let SR := integratedS68 (RatFunc.C 0) T0.source.A T0.source.B
    T0.source.C0 T0.source.D (RatFunc.C T0.source.alpha)
    (RatFunc.C T0.source.beta) (RatFunc.C T0.source.delta)
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
  have hboundary := T0.integratedLocalRowTwoBoundaryData hp hH hp6
  dsimp only at hboundary
  obtain ⟨hA, hB, hC, hD, hE⟩ := T0.coordinateOrderBounds hp hH hp6
  obtain ⟨hdA, hdB, hdC, hdD, hdE⟩ :=
    T0.coordinateDerivativeOrderBounds hp hH hp6
  obtain ⟨hdAco, hdBco, hdCco, hdDco, hdEco⟩ :=
    T0.coordinateDerivativeInitialCoeffs hp hH hp6
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
  have hrowR := hlow.2.2.1
  have hrowH := congrArg (ratFuncAtHahn46 T0.root) hrowR
  have hrowH' :
      UH * dCH + 2 * TH * dDH + 3 * SH * dEH - 3 * BH * dVH -
        2 * CH * dUH - DH * dTH = 0 := by
    dsimp only [AH, BH, CH, DH, EH, SR, TR, UR, VR, SH, TH, UH, VH,
      dCH, dDH, dEH, dTH, dUH, dVH]
    simpa only [ratFuncDerivation46_apply, map_add, map_sub, map_mul,
      map_ofNat, map_zero] using hrowH
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-56 : ℚ)) hrowH'
  simp only [HahnSeries.coeff_zero] at hcoeff
  have hface := lowerRowTwoHahn68_coeff_neg56
    AH BH CH DH EH SH TH UH VH dCH dDH dEH dTH dUH dVH
      hB hC hD hE hboundary.s_order hboundary.t_order hboundary.u_order
      hboundary.v_order hdC hdD hdE hboundary.dt_order hboundary.du_order
      hboundary.dv_order hboundary.s_coeff hboundary.t_coeff
      hboundary.u_coeff hboundary.v_coeff hdCco hdDco hdEco
      hboundary.dt_coeff hboundary.du_coeff hboundary.dv_coeff
  rw [hface] at hcoeff
  have hfactor : (40 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

end AlignedSquareRowTwo68

end Max11DegreeRoutes
