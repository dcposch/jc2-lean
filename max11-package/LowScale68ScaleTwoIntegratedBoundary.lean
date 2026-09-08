import LowScale68ScaleTwoLocalDerivativeRowTwo

/-! # Integrated boundary data for the `(6,8)` scale-two branch

This module clears the local denominators of the four integrated octic
coordinates `S,T,U,V` at exponents `25,30,35,40`, extracts their boundary
coefficients and derivatives, and closes the third local scalar row.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section IntegratedClearings68

variable {k : Type*} [Field k] [CharZero k]

local instance integratedBoundaryHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedIntegratedS68 (h A B C0 D : k[X])
    (L alpha beta delta : k) : k[X] :=
  C (4 / 3 : k) * D + C (4 / 9 : k) * A * B +
  C L * (C (7 / 6 : k) * C0 * h ^ 5 +
    C (7 / 72 : k) * A ^ 2 * h ^ 5) +
  C alpha * B * h ^ 10 + C ((5 / 6 : k) * beta) * A * h ^ 15 +
  C delta * h ^ 25

def localClearedIntegratedT68 (h A B C0 D E : k[X])
    (L alpha beta gamma epsilon : k) : k[X] :=
  C (4 / 3 : k) * E + C (2 / 9 : k) * B ^ 2 +
  C (4 / 9 : k) * A * C0 - C (4 / 81 : k) * A ^ 3 +
  C L * (C (7 / 6 : k) * D * h ^ 5 +
    C (7 / 36 : k) * A * B * h ^ 5) +
  C alpha * C0 * h ^ 10 + C ((5 / 6 : k) * beta) * B * h ^ 15 +
  C ((2 / 3 : k) * gamma) * A * h ^ 20 + C epsilon * h ^ 30

def localClearedIntegratedU68 (h A B C0 D E : k[X])
    (L alpha beta gamma delta zeta : k) : k[X] :=
  C (4 / 9 : k) * B * C0 + C (4 / 9 : k) * A * D -
  C (4 / 27 : k) * A ^ 2 * B +
  C L * (C (7 / 6 : k) * E * h ^ 5 +
    C (7 / 72 : k) * B ^ 2 * h ^ 5 +
    C (7 / 36 : k) * A * C0 * h ^ 5 -
    C (35 / 1296 : k) * A ^ 3 * h ^ 5) +
  C alpha * D * h ^ 10 +
  C beta * (C (5 / 6 : k) * C0 * h ^ 15 -
    C (5 / 72 : k) * A ^ 2 * h ^ 15) +
  C ((2 / 3 : k) * gamma) * B * h ^ 20 +
  C ((1 / 2 : k) * delta) * A * h ^ 25 + C zeta * h ^ 35

def localClearedIntegratedV68 (h A B C0 D E : k[X])
    (L alpha beta gamma delta epsilon eta : k) : k[X] :=
  C (2 / 9 : k) * C0 ^ 2 + C (4 / 9 : k) * B * D +
  C (4 / 9 : k) * A * E - C (4 / 27 : k) * A * B ^ 2 -
  C (4 / 27 : k) * A ^ 2 * C0 + C (5 / 243 : k) * A ^ 4 +
  C L * (C (7 / 36 : k) * B * C0 * h ^ 5 +
    C (7 / 36 : k) * A * D * h ^ 5 -
    C (35 / 432 : k) * A ^ 2 * B * h ^ 5) +
  C alpha * E * h ^ 10 +
  C beta * (C (5 / 6 : k) * D * h ^ 15 -
    C (5 / 36 : k) * A * B * h ^ 15) +
  C gamma * (C (2 / 3 : k) * C0 * h ^ 20 -
    C (1 / 9 : k) * A ^ 2 * h ^ 20) +
  C ((1 / 2 : k) * delta) * B * h ^ 25 +
  C ((1 / 3 : k) * epsilon) * A * h ^ 30 + C eta * h ^ 40

theorem algebraMap_localClearedIntegratedS68
    (h0 A0 B0 C00 D0 : k[X]) (A B C0 D : RatFunc k)
    (L alpha beta delta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 10 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 15 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 20 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 25 * D) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedS68 h0 A0 B0 C00 D0 L alpha beta delta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 25 *
        integratedS68 (RatFunc.C L) A B C0 D (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C delta) := by
  simp only [localClearedIntegratedS68, integratedS68, map_add, map_mul,
    map_pow, map_div₀, map_ofNat, RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD]
  ring

theorem algebraMap_localClearedIntegratedT68
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma epsilon : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 10 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 15 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 20 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 25 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 30 * E) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedT68 h0 A0 B0 C00 D0 E0
          L alpha beta gamma epsilon) =
      (algebraMap k[X] (RatFunc k) h0) ^ 30 *
        integratedT68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) := by
  simp only [localClearedIntegratedT68, integratedT68, map_add, map_sub,
    map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem algebraMap_localClearedIntegratedU68
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta zeta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 10 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 15 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 20 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 25 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 30 * E) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedU68 h0 A0 B0 C00 D0 E0
          L alpha beta gamma delta zeta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 35 *
        integratedU68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C zeta) := by
  simp only [localClearedIntegratedU68, integratedU68, map_add, map_sub,
    map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem algebraMap_localClearedIntegratedV68
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta epsilon eta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 10 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 15 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 20 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 25 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 30 * E) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedV68 h0 A0 B0 C00 D0 E0
          L alpha beta gamma delta epsilon eta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 40 *
        integratedV68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C eta) := by
  simp only [localClearedIntegratedV68, integratedV68, map_add, map_sub,
    map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

/-- The four explicit clearings furnish the complete integrated boundary
package required by the local row-two extractor. -/
theorem SquareConstantLIntegratedLocalRootData68.integratedLocalRowTwoBoundaryData
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
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
  let S0 := localClearedIntegratedS68 h0 A0 B0 C00 D0 l
    T0.source.alpha T0.source.beta T0.source.delta
  let T00 := localClearedIntegratedT68 h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
  let U0 := localClearedIntegratedU68 h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
    T0.source.zeta
  let V0 := localClearedIntegratedV68 h0 A0 B0 C00 D0 E0 l
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
      T0.source.A T0.source.B T0.source.C0 T0.source.D l
      T0.source.alpha T0.source.beta T0.source.delta hA hB hC hD
  have hT : algebraMap k[X] (RatFunc k) T00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 30 * TR := by
    exact algebraMap_localClearedIntegratedT68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
      hA hB hC hD hE
  have hU : algebraMap k[X] (RatFunc k) U0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 35 * UR := by
    exact algebraMap_localClearedIntegratedU68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
      T0.source.zeta hA hB hC hD hE
  have hV : algebraMap k[X] (RatFunc k) V0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 40 * VR := by
    exact algebraMap_localClearedIntegratedV68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
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
  dsimp only [SR, TR, UR, VR] at hSco hTco hUco hVco hSord hTord hUord hVord hdTord hdUord hdVord hdTco hdUco hdVco
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
  · rw [hSco, hSroot, hAco, hBco, hDco]
    field_simp [hc]
  · rw [hTco, hTroot, hAco, hBco, hCco, hEco]
    field_simp [hc]
  · rw [hUco, hUroot, hAco, hBco, hCco, hDco]
    field_simp [hc]
  · rw [hVco, hVroot, hAco, hBco, hCco, hDco, hEco]
    field_simp [hc]

/-- The third scalar local row is now unconditional for every actual
square-source local package. -/
theorem SquareConstantLIntegratedLocalRootData68.topRowTwo_zero
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowTwo68
        ((ratFuncAtHahn46 T0.root T0.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.E).coeff (-30 : ℚ)) = 0 := by
  apply T0.topRowTwo_zero_of_integratedBoundary hp hH hp6
  exact T0.integratedLocalRowTwoBoundaryData hp hH hp6

/-! ## Start of the fourth local row -/

/-- Reusable local coefficient extraction for row one.  The remaining
source transport uses the same integrated boundary package already proved
above. -/
theorem lowerRowOneHahn68_coeff_neg61
    (A B C0 D E T U V dD dE dU dV : HahnSeries ℚ k)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hTord : (↑(-30 : ℚ) : WithTop ℚ) ≤ T.orderTop)
    (hUord : (↑(-35 : ℚ) : WithTop ℚ) ≤ U.orderTop)
    (hVord : (↑(-40 : ℚ) : WithTop ℚ) ≤ V.orderTop)
    (hdD : (↑(-26 : ℚ) : WithTop ℚ) ≤ dD.orderTop)
    (hdE : (↑(-31 : ℚ) : WithTop ℚ) ≤ dE.orderTop)
    (hdU : (↑(-36 : ℚ) : WithTop ℚ) ≤ dU.orderTop)
    (hdV : (↑(-41 : ℚ) : WithTop ℚ) ≤ dV.orderTop)
    (hTco : T.coeff (-30 : ℚ) =
      (4 / 3 : k) * E.coeff (-30 : ℚ) +
      (2 / 9 : k) * B.coeff (-15 : ℚ) ^ 2 +
      (4 / 9 : k) * A.coeff (-10 : ℚ) * C0.coeff (-20 : ℚ) -
      (4 / 81 : k) * A.coeff (-10 : ℚ) ^ 3)
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
    (hdDco : dD.coeff (-26 : ℚ) =
      (-25 : k) * D.coeff (-25 : ℚ))
    (hdEco : dE.coeff (-31 : ℚ) =
      (-30 : k) * E.coeff (-30 : ℚ))
    (hdUco : dU.coeff (-36 : ℚ) =
      (-35 : k) * U.coeff (-35 : ℚ))
    (hdVco : dV.coeff (-41 : ℚ) =
      (-40 : k) * V.coeff (-40 : ℚ)) :
    (U * dD + 2 * T * dE - 2 * C0 * dV - D * dU).coeff (-61 : ℚ) =
      (40 / 243 : k) * topRowOne68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ)) := by
  have hUD := hahnCoeff_mul_at_lower46 U dD (-35) (-26) hUord hdD
  have hTE := hahnCoeff_mul_at_lower46 T dE (-30) (-31) hTord hdE
  have hCV := hahnCoeff_mul_at_lower46 C0 dV (-20) (-41) hC hdV
  have hDU := hahnCoeff_mul_at_lower46 D dU (-25) (-36) hD hdU
  norm_num at hUD hTE hCV hDU
  have hrewrite : U * dD + 2 * T * dE - 2 * C0 * dV - D * dU =
      U * dD + (T * dE + T * dE) - (C0 * dV + C0 * dV) - D * dU := by
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub, hUD, hTE, hCV,
    hDU]
  rw [hdDco, hdEco, hdUco, hdVco, hTco, hUco, hVco]
  simp only [topRowOne68]
  ring

end IntegratedClearings68

#print axioms algebraMap_localClearedIntegratedS68
#print axioms algebraMap_localClearedIntegratedT68
#print axioms algebraMap_localClearedIntegratedU68
#print axioms algebraMap_localClearedIntegratedV68
#print axioms SquareConstantLIntegratedLocalRootData68.integratedLocalRowTwoBoundaryData
#print axioms SquareConstantLIntegratedLocalRootData68.topRowTwo_zero
#print axioms lowerRowOneHahn68_coeff_neg61

end Max11DegreeRoutes
