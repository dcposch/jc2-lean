import LowScale68ScaleTwoAfterRhoOneImprovedDefect

/-! # The next differential row after the improved-defect face

At the sharp box `(A,B,C,D,E)=(1,1,2,2,2)`, the integrated octic
coordinates have box `(S,T,U,V)=(2,3,3,4)`.  The leading coefficient of
the literal row-two Jacobian equation occurs at exponent `-6`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOneImprovedDefectNextRow68

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneImprovedDefectNextRowHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-! ## Sharp integrated denominator clearings -/

def localSharpIntegratedS68 (h A B C0 D : k[X])
    (L alpha beta delta : k) : k[X] :=
  C (4 / 3 : k) * D + C (4 / 9 : k) * A * B +
  C L * (C (7 / 6 : k) * C0 + C (7 / 72 : k) * A ^ 2) +
  C alpha * B * h + C ((5 / 6 : k) * beta) * A * h + C delta * h ^ 2

def localSharpIntegratedT68 (h A B C0 D E : k[X])
    (L alpha beta gamma epsilon : k) : k[X] :=
  C (4 / 3 : k) * E * h + C (2 / 9 : k) * B ^ 2 * h +
  C (4 / 9 : k) * A * C0 - C (4 / 81 : k) * A ^ 3 +
  C L * (C (7 / 6 : k) * D * h + C (7 / 36 : k) * A * B * h) +
  C alpha * C0 * h + C ((5 / 6 : k) * beta) * B * h ^ 2 +
  C ((2 / 3 : k) * gamma) * A * h ^ 2 + C epsilon * h ^ 3

def localSharpIntegratedU68 (h A B C0 D E : k[X])
    (L alpha beta gamma delta zeta : k) : k[X] :=
  C (4 / 9 : k) * B * C0 + C (4 / 9 : k) * A * D -
  C (4 / 27 : k) * A ^ 2 * B +
  C L * (C (7 / 6 : k) * E * h + C (7 / 72 : k) * B ^ 2 * h +
    C (7 / 36 : k) * A * C0 - C (35 / 1296 : k) * A ^ 3) +
  C alpha * D * h +
  C beta * (C (5 / 6 : k) * C0 * h - C (5 / 72 : k) * A ^ 2 * h) +
  C ((2 / 3 : k) * gamma) * B * h ^ 2 +
  C ((1 / 2 : k) * delta) * A * h ^ 2 + C zeta * h ^ 3

def localSharpIntegratedV68 (h A B C0 D E : k[X])
    (L alpha beta gamma delta epsilon eta : k) : k[X] :=
  C (2 / 9 : k) * C0 ^ 2 + C (4 / 9 : k) * B * D * h +
  C (4 / 9 : k) * A * E * h - C (4 / 27 : k) * A * B ^ 2 * h -
  C (4 / 27 : k) * A ^ 2 * C0 + C (5 / 243 : k) * A ^ 4 +
  C L * (C (7 / 36 : k) * B * C0 * h +
    C (7 / 36 : k) * A * D * h - C (35 / 432 : k) * A ^ 2 * B * h) +
  C alpha * E * h ^ 2 +
  C beta * (C (5 / 6 : k) * D * h ^ 2 -
    C (5 / 36 : k) * A * B * h ^ 2) +
  C gamma * (C (2 / 3 : k) * C0 * h ^ 2 -
    C (1 / 9 : k) * A ^ 2 * h ^ 2) +
  C ((1 / 2 : k) * delta) * B * h ^ 3 +
  C ((1 / 3 : k) * epsilon) * A * h ^ 3 + C eta * h ^ 4

theorem algebraMap_localSharpIntegratedS68
    (h0 A0 B0 C00 D0 : k[X]) (A B C0 D : RatFunc k)
    (L alpha beta delta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      algebraMap k[X] (RatFunc k) h0 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      algebraMap k[X] (RatFunc k) h0 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * D) :
    algebraMap k[X] (RatFunc k)
        (localSharpIntegratedS68 h0 A0 B0 C00 D0 L alpha beta delta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 *
        integratedS68 (RatFunc.C L) A B C0 D (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C delta) := by
  simp only [localSharpIntegratedS68, integratedS68, map_add, map_mul,
    map_pow, map_div₀, map_ofNat, RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD]
  ring

theorem algebraMap_localSharpIntegratedT68
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma epsilon : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      algebraMap k[X] (RatFunc k) h0 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      algebraMap k[X] (RatFunc k) h0 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * E) :
    algebraMap k[X] (RatFunc k)
        (localSharpIntegratedT68 h0 A0 B0 C00 D0 E0
          L alpha beta gamma epsilon) =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 *
        integratedT68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) := by
  simp only [localSharpIntegratedT68, integratedT68, map_add, map_sub,
    map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem algebraMap_localSharpIntegratedU68
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta zeta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      algebraMap k[X] (RatFunc k) h0 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      algebraMap k[X] (RatFunc k) h0 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * E) :
    algebraMap k[X] (RatFunc k)
        (localSharpIntegratedU68 h0 A0 B0 C00 D0 E0
          L alpha beta gamma delta zeta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 *
        integratedU68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C zeta) := by
  simp only [localSharpIntegratedU68, integratedU68, map_add, map_sub,
    map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem algebraMap_localSharpIntegratedV68
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta epsilon eta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      algebraMap k[X] (RatFunc k) h0 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      algebraMap k[X] (RatFunc k) h0 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * E) :
    algebraMap k[X] (RatFunc k)
        (localSharpIntegratedV68 h0 A0 B0 C00 D0 E0
          L alpha beta gamma delta epsilon eta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 *
        integratedV68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C eta) := by
  simp only [localSharpIntegratedV68, integratedV68, map_add, map_sub,
    map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

/-! ## Boundary packet and literal row-two coefficient -/

structure AfterRhoOneNextRowTwoBoundary68
    (L : k) (A B C0 D E S T U V dC dD dE dT dU dV : HahnSeries ℚ k) : Prop where
  s_order : (↑(-2 : ℚ) : WithTop ℚ) ≤ S.orderTop
  t_order : (↑(-3 : ℚ) : WithTop ℚ) ≤ T.orderTop
  u_order : (↑(-3 : ℚ) : WithTop ℚ) ≤ U.orderTop
  v_order : (↑(-4 : ℚ) : WithTop ℚ) ≤ V.orderTop
  dc_order : (↑(-3 : ℚ) : WithTop ℚ) ≤ dC.orderTop
  dd_order : (↑(-3 : ℚ) : WithTop ℚ) ≤ dD.orderTop
  de_order : (↑(-3 : ℚ) : WithTop ℚ) ≤ dE.orderTop
  dt_order : (↑(-4 : ℚ) : WithTop ℚ) ≤ dT.orderTop
  du_order : (↑(-4 : ℚ) : WithTop ℚ) ≤ dU.orderTop
  dv_order : (↑(-5 : ℚ) : WithTop ℚ) ≤ dV.orderTop
  t_coeff : T.coeff (-3 : ℚ) =
    (4 / 9 : k) * A.coeff (-1 : ℚ) * C0.coeff (-2 : ℚ) -
      (4 / 81 : k) * A.coeff (-1 : ℚ) ^ 3
  u_coeff : U.coeff (-3 : ℚ) =
    (4 / 9 : k) * B.coeff (-1 : ℚ) * C0.coeff (-2 : ℚ) +
      (4 / 9 : k) * A.coeff (-1 : ℚ) * D.coeff (-2 : ℚ) -
      (4 / 27 : k) * A.coeff (-1 : ℚ) ^ 2 * B.coeff (-1 : ℚ) +
      (7 / 36 : k) * A.coeff (-1 : ℚ) * C0.coeff (-2 : ℚ) *
        L - (35 / 1296 : k) * A.coeff (-1 : ℚ) ^ 3 * L
  v_coeff : V.coeff (-4 : ℚ) =
    (2 / 9 : k) * C0.coeff (-2 : ℚ) ^ 2 -
      (4 / 27 : k) * A.coeff (-1 : ℚ) ^ 2 * C0.coeff (-2 : ℚ) +
      (5 / 243 : k) * A.coeff (-1 : ℚ) ^ 4
  dc_coeff : dC.coeff (-3 : ℚ) = (-2 : k) * C0.coeff (-2 : ℚ)
  dd_coeff : dD.coeff (-3 : ℚ) = (-2 : k) * D.coeff (-2 : ℚ)
  de_coeff : dE.coeff (-3 : ℚ) = (-2 : k) * E.coeff (-2 : ℚ)
  dt_coeff : dT.coeff (-4 : ℚ) = (-3 : k) * T.coeff (-3 : ℚ)
  du_coeff : dU.coeff (-4 : ℚ) = (-3 : k) * U.coeff (-3 : ℚ)
  dv_coeff : dV.coeff (-5 : ℚ) = (-4 : k) * V.coeff (-4 : ℚ)

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNextRowTwoBoundary
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
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
    AfterRhoOneNextRowTwoBoundary68 l
      AH BH CH DH EH SH TH UH VH dCH dDH dEH dTH dUH dVH := by
  dsimp only
  let A0 := localClearedA68AfterRhoOne h0 g u
  let B0 := localClearedB68AfterRhoOneNext h0 g u v
  let C00 := localClearedC68AfterRhoOneNext h0 g u v (p.coeff 2)
  let D0 := localClearedD68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1)
  let E0 := localClearedE68AfterRhoOneNext h0 g u v (p.coeff 2) (p.coeff 1)
    (p.coeff 0)
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
  let S0 := localSharpIntegratedS68 h0 A0 B0 C00 D0 l
    T0.source.alpha T0.source.beta T0.source.delta
  let T00 := localSharpIntegratedT68 h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
  let U0 := localSharpIntegratedU68 h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
    T0.source.zeta
  let V0 := localSharpIntegratedV68 h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
    T0.source.epsilon T0.source.eta
  obtain ⟨hA, hB, hC, hD, hE⟩ := T0.source.clearedCoordinatesAfterRhoOneNext
    hp T0.scale_ne_zero hH hp6 hp5 hp4 hp3
  change algebraMap k[X] (RatFunc k) A0 = _ at hA
  change algebraMap k[X] (RatFunc k) B0 = _ at hB
  change algebraMap k[X] (RatFunc k) C00 = _ at hC
  change algebraMap k[X] (RatFunc k) D0 = _ at hD
  change algebraMap k[X] (RatFunc k) E0 = _ at hE
  have hA' : algebraMap k[X] (RatFunc k) A0 =
      algebraMap k[X] (RatFunc k) h0 * T0.source.A := by simpa using hA
  have hB' : algebraMap k[X] (RatFunc k) B0 =
      algebraMap k[X] (RatFunc k) h0 * T0.source.B := by simpa using hB
  have hS : algebraMap k[X] (RatFunc k) S0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * SR := by
    exact algebraMap_localSharpIntegratedS68 h0 A0 B0 C00 D0
      T0.source.A T0.source.B T0.source.C0 T0.source.D l
      T0.source.alpha T0.source.beta T0.source.delta hA' hB' hC hD
  have hT : algebraMap k[X] (RatFunc k) T00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * TR := by
    exact algebraMap_localSharpIntegratedT68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
      hA' hB' hC hD hE
  have hU : algebraMap k[X] (RatFunc k) U0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * UR := by
    exact algebraMap_localSharpIntegratedU68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
      T0.source.zeta hA' hB' hC hD hE
  have hV : algebraMap k[X] (RatFunc k) V0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * VR := by
    exact algebraMap_localSharpIntegratedV68 h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
      T0.source.epsilon T0.source.eta hA' hB' hC hD hE
  obtain ⟨c, hc, hsingle, hderiv⟩ := ratFuncAtHahn68_linearRoot_single_deriv
    h0 T0.root T0.scale_degree T0.root_eq
  have hAco := localHahn_coeff_neg_of_cleared T0.root c h0 A0
    T0.source.A 1 hc hsingle hA
  have hBco := localHahn_coeff_neg_of_cleared T0.root c h0 B0
    T0.source.B 1 hc hsingle hB
  have hCco := localHahn_coeff_neg_of_cleared T0.root c h0 C00
    T0.source.C0 2 hc hsingle hC
  have hDco := localHahn_coeff_neg_of_cleared T0.root c h0 D0
    T0.source.D 2 hc hsingle hD
  have hEco := localHahn_coeff_neg_of_cleared T0.root c h0 E0
    T0.source.E 2 hc hsingle hE
  have hTco := localHahn_coeff_neg_of_cleared T0.root c h0 T00 TR 3
    hc hsingle hT
  have hUco := localHahn_coeff_neg_of_cleared T0.root c h0 U0 UR 3
    hc hsingle hU
  have hVco := localHahn_coeff_neg_of_cleared T0.root c h0 V0 VR 4
    hc hsingle hV
  have hSord := localHahn_orderTop_ge_of_cleared T0.root h0 S0 SR 2
    T0.scale_order hS
  have hTord := localHahn_orderTop_ge_of_cleared T0.root h0 T00 TR 3
    T0.scale_order hT
  have hUord := localHahn_orderTop_ge_of_cleared T0.root h0 U0 UR 3
    T0.scale_order hU
  have hVord := localHahn_orderTop_ge_of_cleared T0.root h0 V0 VR 4
    T0.scale_order hV
  have hdCord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0 C00
    T0.source.C0 2 T0.scale_order hC
  have hdDord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0 D0
    T0.source.D 2 T0.scale_order hD
  have hdEord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0 E0
    T0.source.E 2 T0.scale_order hE
  have hdTord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0 T00 TR 3
    T0.scale_order hT
  have hdUord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0 U0 UR 3
    T0.scale_order hU
  have hdVord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0 V0 VR 4
    T0.scale_order hV
  have hdCco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 C00 T0.source.C0 2 hc hsingle hderiv hC
  have hdDco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 D0 T0.source.D 2 hc hsingle hderiv hD
  have hdEco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 E0 T0.source.E 2 hc hsingle hderiv hE
  have hdTco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 T00 TR 3 hc hsingle hderiv hT
  have hdUco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 U0 UR 3 hc hsingle hderiv hU
  have hdVco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 V0 VR 4 hc hsingle hderiv hV
  have hTroot : T00.eval T0.root =
      (4 / 9 : k) * A0.eval T0.root * C00.eval T0.root -
      (4 / 81 : k) * A0.eval T0.root ^ 3 := by
    simp [T00, localSharpIntegratedT68, T0.root_eq]
  have hUroot : U0.eval T0.root =
      (4 / 9 : k) * B0.eval T0.root * C00.eval T0.root +
      (4 / 9 : k) * A0.eval T0.root * D0.eval T0.root -
      (4 / 27 : k) * A0.eval T0.root ^ 2 * B0.eval T0.root +
      l * ((7 / 36 : k) * A0.eval T0.root * C00.eval T0.root -
        (35 / 1296 : k) * A0.eval T0.root ^ 3) := by
    simp [U0, localSharpIntegratedU68, T0.root_eq]
  have hVroot : V0.eval T0.root =
      (2 / 9 : k) * C00.eval T0.root ^ 2 -
      (4 / 27 : k) * A0.eval T0.root ^ 2 * C00.eval T0.root +
      (5 / 243 : k) * A0.eval T0.root ^ 4 := by
    simp [V0, localSharpIntegratedV68, T0.root_eq]
  dsimp only [SR, TR, UR, VR] at hTco hUco hVco hSord hTord hUord hVord hdTord hdUord hdVord hdTco hdUco hdVco
  norm_num at hAco hBco hCco hDco hEco hTco hUco hVco
  refine {
    s_order := by simpa using hSord
    t_order := by simpa using hTord
    u_order := by simpa using hUord
    v_order := by simpa using hVord
    dc_order := by convert hdCord using 1 <;> norm_num
    dd_order := by convert hdDord using 1 <;> norm_num
    de_order := by convert hdEord using 1 <;> norm_num
    dt_order := by convert hdTord using 1 <;> norm_num
    du_order := by convert hdUord using 1 <;> norm_num
    dv_order := by convert hdVord using 1 <;> norm_num
    t_coeff := ?_
    u_coeff := ?_
    v_coeff := ?_
    dc_coeff := by convert hdCco using 1 <;> norm_num
    dd_coeff := by convert hdDco using 1 <;> norm_num
    de_coeff := by convert hdEco using 1 <;> norm_num
    dt_coeff := by convert hdTco using 1 <;> norm_num
    du_coeff := by convert hdUco using 1 <;> norm_num
    dv_coeff := by convert hdVco using 1 <;> norm_num }
  · rw [hTco, hTroot, hAco, hCco]
    field_simp [hc]
  · rw [hUco, hUroot, hAco, hBco, hCco, hDco]
    field_simp [hc]
    ring
  · rw [hVco, hVroot, hAco, hCco]
    field_simp [hc]

def afterRhoOneNextDifferentialFace68 (L a b x d : k) : k :=
  (40 / 9 : k) * b * x ^ 2 + (4 / 3 : k) * a * d * x -
    (64 / 27 : k) * a ^ 2 * b * x + (4 / 81 : k) * a ^ 3 * d +
    (20 / 81 : k) * a ^ 4 * b + (7 / 9 : k) * L * a * x ^ 2 -
    (35 / 324 : k) * L * a ^ 3 * x

theorem lowerRowTwoHahn68_coeff_neg6_afterRhoOneNext
    (L : k) (A B C0 D E S T U V dC dD dE dT dU dV : HahnSeries ℚ k)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-2 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (P : AfterRhoOneNextRowTwoBoundary68 L
      A B C0 D E S T U V dC dD dE dT dU dV) :
    (U * dC + 2 * T * dD + 3 * S * dE - 3 * B * dV -
      2 * C0 * dU - D * dT).coeff (-6 : ℚ) =
      afterRhoOneNextDifferentialFace68 L (A.coeff (-1 : ℚ))
        (B.coeff (-1 : ℚ)) (C0.coeff (-2 : ℚ))
        (D.coeff (-2 : ℚ)) := by
  have hUC := hahnCoeff_mul_at_lower46 U dC (-3) (-3) P.u_order P.dc_order
  have hTD := hahnCoeff_mul_at_lower46 T dD (-3) (-3) P.t_order P.dd_order
  have hBV := hahnCoeff_mul_at_lower46 B dV (-1) (-5) hB P.dv_order
  have hCU := hahnCoeff_mul_at_lower46 C0 dU (-2) (-4) hC P.du_order
  have hDT := hahnCoeff_mul_at_lower46 D dT (-2) (-4) hD P.dt_order
  norm_num at hUC hTD hBV hCU hDT
  have hSEord := hahnOrderTop_mul_lower46 S dE (-2) (-3)
    P.s_order P.de_order
  have hSE : (S * dE).coeff (-6 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr (by norm_num : (-6 : ℚ) < -2 + -3)).trans_le
      hSEord
  have hrewrite :
      U * dC + 2 * T * dD + 3 * S * dE - 3 * B * dV -
          2 * C0 * dU - D * dT =
        U * dC + (T * dD + T * dD) +
          (S * dE + S * dE + S * dE) -
          (B * dV + B * dV + B * dV) -
          (C0 * dU + C0 * dU) - D * dT := by ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub,
    hUC, hTD, hSE, hBV, hCU, hDT, add_zero, zero_add]
  rw [P.dc_coeff, P.dd_coeff, P.dt_coeff, P.du_coeff, P.dv_coeff,
    P.t_coeff, P.u_coeff, P.v_coeff]
  simp only [afterRhoOneNextDifferentialFace68]
  ring

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_differentialFace
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    let AH := ratFuncAtHahn46 T0.root T0.source.A
    let BH := ratFuncAtHahn46 T0.root T0.source.B
    let CH := ratFuncAtHahn46 T0.root T0.source.C0
    let DH := ratFuncAtHahn46 T0.root T0.source.D
    afterRhoOneNextDifferentialFace68 l (AH.coeff (-1 : ℚ))
      (BH.coeff (-1 : ℚ)) (CH.coeff (-2 : ℚ))
      (DH.coeff (-2 : ℚ)) = 0 := by
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
    (fun z : HahnSeries ℚ k => z.coeff (-6 : ℚ)) hrowH'
  simp only [HahnSeries.coeff_zero] at hcoeff
  have hface := lowerRowTwoHahn68_coeff_neg6_afterRhoOneNext
    l AH BH CH DH EH SH TH UH VH dCH dDH dEH dTH dUH dVH
      (by simpa only [BH] using hB) (by simpa only [CH] using hC)
      (by simpa only [DH] using hD) P
  rw [hface] at hcoeff
  exact hcoeff

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_differentialFaceAtScaleSingle
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T0.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c) :
    afterRhoOneNextDifferentialFace68 l (c⁻¹ * u.eval T0.root)
      (c⁻¹ * (v.eval T0.root -
        (2 / 3 : k) * u.eval T0.root * g.eval T0.root))
      ((c ^ 2)⁻¹ * (p.coeff 2).eval T0.root)
      ((c ^ 2)⁻¹ * (-(1 / 3 : k) * (p.coeff 2).eval T0.root *
        g.eval T0.root)) = 0 := by
  have hface := T0.afterRhoOneNext_differentialFace
    hp hH hp6 hp5 hp4 hp3
  obtain ⟨hAco, hBco, hCco, hDco, hEco⟩ :=
    T0.coordinateInitialPacketAtScaleSingleAfterRhoOneNext
      hp hH hp6 hp5 hp4 hp3 hc hsingle
  dsimp only at hface
  rw [hAco, hBco, hCco, hDco] at hface
  exact hface

theorem afterRhoOne_firstBranch_differential_elimination
    (L a b x d : k) (ha : a ≠ 0)
    (hx : 3 * x - a ^ 2 = 0)
    (hb : 512 * b + 119 * L * a = 0)
    (hface : afterRhoOneNextDifferentialFace68 L a b x d = 0) :
    3072 * d + 385 * L * a ^ 2 = 0 := by
  have hx' : x = a ^ 2 / 3 := by linear_combination (1 / 3 : k) * hx
  have hb' : b = -(119 / 512 : k) * L * a := by
    linear_combination (1 / 512 : k) * hb
  rw [hx', hb'] at hface
  have hfac : a ^ 3 *
      ((40 / 81 : k) * d + (1925 / 31104 : k) * L * a ^ 2) = 0 := by
    rw [afterRhoOneNextDifferentialFace68] at hface
    linear_combination hface
  have hinner := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 3 ha)
  linear_combination (31104 / 5 : k) * hinner

theorem afterRhoOne_secondBranch_differential_elimination
    (L a b x d : k) (ha : a ≠ 0)
    (hx : 9 * x - 2 * a ^ 2 = 0)
    (hd : 4608 * d - 1536 * a * b + 77 * L * a ^ 2 = 0)
    (hface : afterRhoOneNextDifferentialFace68 L a b x d = 0) :
    1024 * b + 161 * L * a = 0 := by
  have hx' : x = 2 * a ^ 2 / 9 := by linear_combination (1 / 9 : k) * hx
  have hd' : d = (1 / 3 : k) * a * b - (77 / 4608 : k) * L * a ^ 2 := by
    linear_combination (1 / 4608 : k) * hd
  rw [hx', hd'] at hface
  have hfac : a ^ 4 *
      ((40 / 729 : k) * b + (805 / 93312 : k) * L * a) = 0 := by
    rw [afterRhoOneNextDifferentialFace68] at hface
    linear_combination hface
  have hinner := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 4 ha)
  linear_combination (93312 / 5 : k) * hinner

theorem SquareConstantLIntegratedLocalRootData68.firstBranchImprovedNextRows
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T0.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c)
    (ha : c⁻¹ * u.eval T0.root ≠ 0)
    (hx : 3 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T0.root) -
      (c⁻¹ * u.eval T0.root) ^ 2 = 0)
    (hb : 512 * (c⁻¹ * (v.eval T0.root -
        (2 / 3 : k) * u.eval T0.root * g.eval T0.root)) +
      119 * l * (c⁻¹ * u.eval T0.root) = 0) :
    ∃ w : k[X],
      localClearedFirstDefect68 h0 g u v (p.coeff 2) = h0 * w ∧
      3072 * ((c ^ 2)⁻¹ * (-(1 / 3 : k) *
          (p.coeff 2).eval T0.root * g.eval T0.root)) +
        385 * l * (c⁻¹ * u.eval T0.root) ^ 2 = 0 ∧
      2097152 * (c⁻¹ * w.eval T0.root) -
        740733 * l ^ 2 * (c⁻¹ * u.eval T0.root) = 0 := by
  let a : k := c⁻¹ * u.eval T0.root
  let b : k := c⁻¹ * (v.eval T0.root -
    (2 / 3 : k) * u.eval T0.root * g.eval T0.root)
  let x : k := (c ^ 2)⁻¹ * (p.coeff 2).eval T0.root
  let d : k := (c ^ 2)⁻¹ * (-(1 / 3 : k) *
    (p.coeff 2).eval T0.root * g.eval T0.root)
  have hdiff := T0.afterRhoOneNext_differentialFaceAtScaleSingle
    hp hH hp6 hp5 hp4 hp3 hc hsingle
  change afterRhoOneNextDifferentialFace68 l a b x d = 0 at hdiff
  have hdrel := afterRhoOne_firstBranch_differential_elimination
    l a b x d (by simpa only [a] using ha)
      (by simpa only [a, x] using hx) (by simpa only [a, b] using hb) hdiff
  obtain ⟨w, hFw, htrans⟩ := T0.firstBranchImprovedThreeRow
    hp hH hp6 hp5 hp4 hp3 hc hsingle hx hb
  change afterRhoOneFirstBranchTransverse68 l a d
    (c⁻¹ * w.eval T0.root) = 0 at htrans
  have hd' : d = -(385 / 3072 : k) * l * a ^ 2 := by
    linear_combination (1 / 3072 : k) * hdrel
  rw [hd'] at htrans
  have hfac : a ^ 3 *
      ((-8 / 243 : k) * (c⁻¹ * w.eval T0.root) +
        (246911 / 21233664 : k) * l ^ 2 * a) = 0 := by
    rw [afterRhoOneFirstBranchTransverse68] at htrans
    linear_combination htrans
  have hinner := (mul_eq_zero.mp hfac).resolve_left
    (pow_ne_zero 3 (by simpa only [a] using ha))
  refine ⟨w, hFw, ?_, ?_⟩
  · simpa only [d, a] using hdrel
  · change 2097152 * (c⁻¹ * w.eval T0.root) -
      740733 * l ^ 2 * a = 0
    linear_combination (-63700992 : k) * hinner

theorem SquareConstantLIntegratedLocalRootData68.secondBranchImprovedNextRows
    {p q : k[X][X]} {j l c : k} {h0 H g u v : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hc : c ≠ 0)
    (hsingle : ratFuncAtHahn46 T0.root
        (algebraMap k[X] (RatFunc k) h0) = HahnSeries.single (1 : ℚ) c)
    (ha : c⁻¹ * u.eval T0.root ≠ 0)
    (hx : 9 * ((c ^ 2)⁻¹ * (p.coeff 2).eval T0.root) -
      2 * (c⁻¹ * u.eval T0.root) ^ 2 = 0)
    (hd : 4608 * ((c ^ 2)⁻¹ * (-(1 / 3 : k) *
        (p.coeff 2).eval T0.root * g.eval T0.root)) -
      1536 * (c⁻¹ * u.eval T0.root) *
        (c⁻¹ * (v.eval T0.root -
          (2 / 3 : k) * u.eval T0.root * g.eval T0.root)) +
      77 * l * (c⁻¹ * u.eval T0.root) ^ 2 = 0) :
    ∃ w : k[X],
      localClearedSecondDefect68 h0 g u v (p.coeff 2) = h0 * w ∧
      1024 * (c⁻¹ * (v.eval T0.root -
          (2 / 3 : k) * u.eval T0.root * g.eval T0.root)) +
        161 * l * (c⁻¹ * u.eval T0.root) = 0 ∧
      9216 * ((c ^ 2)⁻¹ * (-(1 / 3 : k) *
          (p.coeff 2).eval T0.root * g.eval T0.root)) +
        637 * l * (c⁻¹ * u.eval T0.root) ^ 2 = 0 ∧
      1048576 * (c⁻¹ * u.eval T0.root) *
          (c⁻¹ * w.eval T0.root) -
        28311552 * ((c ^ 2)⁻¹ * ((1 / 36 : k) *
          (p.coeff 2).eval T0.root * g.eval T0.root ^ 2)) +
        326781 * l ^ 2 * (c⁻¹ * u.eval T0.root) ^ 2 = 0 := by
  let a : k := c⁻¹ * u.eval T0.root
  let b : k := c⁻¹ * (v.eval T0.root -
    (2 / 3 : k) * u.eval T0.root * g.eval T0.root)
  let x : k := (c ^ 2)⁻¹ * (p.coeff 2).eval T0.root
  let d : k := (c ^ 2)⁻¹ * (-(1 / 3 : k) *
    (p.coeff 2).eval T0.root * g.eval T0.root)
  let e : k := (c ^ 2)⁻¹ * ((1 / 36 : k) *
    (p.coeff 2).eval T0.root * g.eval T0.root ^ 2)
  have hdiff := T0.afterRhoOneNext_differentialFaceAtScaleSingle
    hp hH hp6 hp5 hp4 hp3 hc hsingle
  change afterRhoOneNextDifferentialFace68 l a b x d = 0 at hdiff
  have hbrel := afterRhoOne_secondBranch_differential_elimination
    l a b x d (by simpa only [a] using ha)
      (by simpa only [a, x] using hx) (by simpa only [a, b, d] using hd) hdiff
  have hdrel : 9216 * d + 637 * l * a ^ 2 = 0 := by
    linear_combination 2 * hd + 3 * a * hbrel
  obtain ⟨w, hGw, htrans⟩ := T0.secondBranchImprovedThreeRow
    hp hH hp6 hp5 hp4 hp3 hc hsingle hx hd
  change afterRhoOneSecondBranchTransverse68 l a b e
    (c⁻¹ * w.eval T0.root) = 0 at htrans
  have hb' : b = -(161 / 1024 : k) * l * a := by
    linear_combination (1 / 1024 : k) * hbrel
  rw [hb'] at htrans
  have hfac : a ^ 2 *
      ((8 / 729 : k) * a * (c⁻¹ * w.eval T0.root) -
        (8 / 27 : k) * e + (12103 / 3538944 : k) * l ^ 2 * a ^ 2) = 0 := by
    rw [afterRhoOneSecondBranchTransverse68] at htrans
    linear_combination htrans
  have hinner := (mul_eq_zero.mp hfac).resolve_left
    (pow_ne_zero 2 (by simpa only [a] using ha))
  refine ⟨w, hGw, ?_, ?_, ?_⟩
  · simpa only [a, b] using hbrel
  · simpa only [a, d] using hdrel
  · change 1048576 * a * (c⁻¹ * w.eval T0.root) -
      28311552 * e + 326781 * l ^ 2 * a ^ 2 = 0
    linear_combination (95551488 : k) * hinner

#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_differentialFace
#print axioms SquareConstantLIntegratedLocalRootData68.firstBranchImprovedNextRows
#print axioms SquareConstantLIntegratedLocalRootData68.secondBranchImprovedNextRows

end AfterRhoOneImprovedDefectNextRow68

end Max11DegreeRoutes
