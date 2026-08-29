import LowScale68ScaleTwoRhoOneComponentSplit

/-! # The third local row at the uniform `rho = 1` box

The two first-integral faces leave one degree-ten affine component.  This
module extracts the next literal differential row.  Its initial coefficient
is the scalar polynomial `topRowTwo68`; consequently the remaining source
packet acquires a third exact equation.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RhoOneNoncubicNext68

variable {k : Type*} [Field k] [CharZero k]

local instance rhoOneNextHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-! ## The abstract coefficient calculation -/

theorem lowerRowTwoHahn68_coeff_neg12_rhoOne
    (A B C0 D E S T U V dC dD dE dT dU dV : HahnSeries ℚ k)
    (hB : (↑(-3 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hSord : (↑(-5 : ℚ) : WithTop ℚ) ≤ S.orderTop)
    (hTord : (↑(-6 : ℚ) : WithTop ℚ) ≤ T.orderTop)
    (hUord : (↑(-7 : ℚ) : WithTop ℚ) ≤ U.orderTop)
    (hVord : (↑(-8 : ℚ) : WithTop ℚ) ≤ V.orderTop)
    (hdC : (↑(-5 : ℚ) : WithTop ℚ) ≤ dC.orderTop)
    (hdD : (↑(-6 : ℚ) : WithTop ℚ) ≤ dD.orderTop)
    (hdE : (↑(-7 : ℚ) : WithTop ℚ) ≤ dE.orderTop)
    (hdT : (↑(-7 : ℚ) : WithTop ℚ) ≤ dT.orderTop)
    (hdU : (↑(-8 : ℚ) : WithTop ℚ) ≤ dU.orderTop)
    (hdV : (↑(-9 : ℚ) : WithTop ℚ) ≤ dV.orderTop)
    (hSco : S.coeff (-5 : ℚ) =
      (4 / 3 : k) * D.coeff (-5 : ℚ) +
        (4 / 9 : k) * A.coeff (-2 : ℚ) * B.coeff (-3 : ℚ))
    (hTco : T.coeff (-6 : ℚ) =
      (4 / 3 : k) * E.coeff (-6 : ℚ) +
      (2 / 9 : k) * B.coeff (-3 : ℚ) ^ 2 +
      (4 / 9 : k) * A.coeff (-2 : ℚ) * C0.coeff (-4 : ℚ) -
      (4 / 81 : k) * A.coeff (-2 : ℚ) ^ 3)
    (hUco : U.coeff (-7 : ℚ) =
      (4 / 9 : k) * B.coeff (-3 : ℚ) * C0.coeff (-4 : ℚ) +
      (4 / 9 : k) * A.coeff (-2 : ℚ) * D.coeff (-5 : ℚ) -
      (4 / 27 : k) * A.coeff (-2 : ℚ) ^ 2 * B.coeff (-3 : ℚ))
    (hVco : V.coeff (-8 : ℚ) =
      (2 / 9 : k) * C0.coeff (-4 : ℚ) ^ 2 +
      (4 / 9 : k) * B.coeff (-3 : ℚ) * D.coeff (-5 : ℚ) +
      (4 / 9 : k) * A.coeff (-2 : ℚ) * E.coeff (-6 : ℚ) -
      (4 / 27 : k) * A.coeff (-2 : ℚ) * B.coeff (-3 : ℚ) ^ 2 -
      (4 / 27 : k) * A.coeff (-2 : ℚ) ^ 2 * C0.coeff (-4 : ℚ) +
      (5 / 243 : k) * A.coeff (-2 : ℚ) ^ 4)
    (hdCco : dC.coeff (-5 : ℚ) = (-4 : k) * C0.coeff (-4 : ℚ))
    (hdDco : dD.coeff (-6 : ℚ) = (-5 : k) * D.coeff (-5 : ℚ))
    (hdEco : dE.coeff (-7 : ℚ) = (-6 : k) * E.coeff (-6 : ℚ))
    (hdTco : dT.coeff (-7 : ℚ) = (-6 : k) * T.coeff (-6 : ℚ))
    (hdUco : dU.coeff (-8 : ℚ) = (-7 : k) * U.coeff (-7 : ℚ))
    (hdVco : dV.coeff (-9 : ℚ) = (-8 : k) * V.coeff (-8 : ℚ)) :
    (U * dC + 2 * T * dD + 3 * S * dE - 3 * B * dV -
      2 * C0 * dU - D * dT).coeff (-12 : ℚ) =
      (8 / 81 : k) * topRowTwo68 (A.coeff (-2 : ℚ))
        (B.coeff (-3 : ℚ)) (C0.coeff (-4 : ℚ))
        (D.coeff (-5 : ℚ)) (E.coeff (-6 : ℚ)) := by
  have hUC := hahnCoeff_mul_at_lower46 U dC (-7) (-5) hUord hdC
  have hTD := hahnCoeff_mul_at_lower46 T dD (-6) (-6) hTord hdD
  have hSE := hahnCoeff_mul_at_lower46 S dE (-5) (-7) hSord hdE
  have hBV := hahnCoeff_mul_at_lower46 B dV (-3) (-9) hB hdV
  have hCU := hahnCoeff_mul_at_lower46 C0 dU (-4) (-8) hC hdU
  have hDT := hahnCoeff_mul_at_lower46 D dT (-5) (-7) hD hdT
  norm_num at hUC hTD hSE hBV hCU hDT
  have hrewrite :
      U * dC + 2 * T * dD + 3 * S * dE - 3 * B * dV -
          2 * C0 * dU - D * dT =
        U * dC + (T * dD + T * dD) +
          (S * dE + S * dE + S * dE) -
          (B * dV + B * dV + B * dV) -
          (C0 * dU + C0 * dU) - D * dT := by ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub, hUC, hTD, hSE,
    hBV, hCU, hDT]
  rw [hdCco, hdDco, hdEco, hdTco, hdUco, hdVco, hSco, hTco, hUco,
    hVco]
  simp only [topRowTwo68]
  ring

/-! ## Denominator clearings for the four integrated coordinates -/

def localClearedIntegratedS68RhoOne (h A B C0 D : k[X])
    (L alpha beta delta : k) : k[X] :=
  C (4 / 3 : k) * D + C (4 / 9 : k) * A * B +
  C L * (C (7 / 6 : k) * C0 * h + C (7 / 72 : k) * A ^ 2 * h) +
  C alpha * B * h ^ 2 + C ((5 / 6 : k) * beta) * A * h ^ 3 +
  C delta * h ^ 5

def localClearedIntegratedT68RhoOne (h A B C0 D E : k[X])
    (L alpha beta gamma epsilon : k) : k[X] :=
  C (4 / 3 : k) * E + C (2 / 9 : k) * B ^ 2 +
  C (4 / 9 : k) * A * C0 - C (4 / 81 : k) * A ^ 3 +
  C L * (C (7 / 6 : k) * D * h + C (7 / 36 : k) * A * B * h) +
  C alpha * C0 * h ^ 2 + C ((5 / 6 : k) * beta) * B * h ^ 3 +
  C ((2 / 3 : k) * gamma) * A * h ^ 4 + C epsilon * h ^ 6

def localClearedIntegratedU68RhoOne (h A B C0 D E : k[X])
    (L alpha beta gamma delta zeta : k) : k[X] :=
  C (4 / 9 : k) * B * C0 + C (4 / 9 : k) * A * D -
  C (4 / 27 : k) * A ^ 2 * B +
  C L * (C (7 / 6 : k) * E * h + C (7 / 72 : k) * B ^ 2 * h +
    C (7 / 36 : k) * A * C0 * h - C (35 / 1296 : k) * A ^ 3 * h) +
  C alpha * D * h ^ 2 +
  C beta * (C (5 / 6 : k) * C0 * h ^ 3 -
    C (5 / 72 : k) * A ^ 2 * h ^ 3) +
  C ((2 / 3 : k) * gamma) * B * h ^ 4 +
  C ((1 / 2 : k) * delta) * A * h ^ 5 + C zeta * h ^ 7

def localClearedIntegratedV68RhoOne (h A B C0 D E : k[X])
    (L alpha beta gamma delta epsilon eta : k) : k[X] :=
  C (2 / 9 : k) * C0 ^ 2 + C (4 / 9 : k) * B * D +
  C (4 / 9 : k) * A * E - C (4 / 27 : k) * A * B ^ 2 -
  C (4 / 27 : k) * A ^ 2 * C0 + C (5 / 243 : k) * A ^ 4 +
  C L * (C (7 / 36 : k) * B * C0 * h +
    C (7 / 36 : k) * A * D * h - C (35 / 432 : k) * A ^ 2 * B * h) +
  C alpha * E * h ^ 2 +
  C beta * (C (5 / 6 : k) * D * h ^ 3 -
    C (5 / 36 : k) * A * B * h ^ 3) +
  C gamma * (C (2 / 3 : k) * C0 * h ^ 4 -
    C (1 / 9 : k) * A ^ 2 * h ^ 4) +
  C ((1 / 2 : k) * delta) * B * h ^ 5 +
  C ((1 / 3 : k) * epsilon) * A * h ^ 6 + C eta * h ^ 8

theorem algebraMap_localClearedIntegratedS68RhoOne
    (h0 A0 B0 C00 D0 : k[X]) (A B C0 D : RatFunc k)
    (L alpha beta delta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * D) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedS68RhoOne h0 A0 B0 C00 D0
          L alpha beta delta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 *
        integratedS68 (RatFunc.C L) A B C0 D (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C delta) := by
  simp only [localClearedIntegratedS68RhoOne, integratedS68, map_add,
    map_mul, map_pow, map_div₀, map_ofNat, RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD]
  ring

theorem algebraMap_localClearedIntegratedT68RhoOne
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma epsilon : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * E) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedT68RhoOne h0 A0 B0 C00 D0 E0
          L alpha beta gamma epsilon) =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 *
        integratedT68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) := by
  simp only [localClearedIntegratedT68RhoOne, integratedT68, map_add,
    map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem algebraMap_localClearedIntegratedU68RhoOne
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta zeta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * E) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedU68RhoOne h0 A0 B0 C00 D0 E0
          L alpha beta gamma delta zeta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 7 *
        integratedU68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C zeta) := by
  simp only [localClearedIntegratedU68RhoOne, integratedU68, map_add,
    map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

theorem algebraMap_localClearedIntegratedV68RhoOne
    (h0 A0 B0 C00 D0 E0 : k[X]) (A B C0 D E : RatFunc k)
    (L alpha beta gamma delta epsilon eta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * D)
    (hE : algebraMap k[X] (RatFunc k) E0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * E) :
    algebraMap k[X] (RatFunc k)
        (localClearedIntegratedV68RhoOne h0 A0 B0 C00 D0 E0
          L alpha beta gamma delta epsilon eta) =
      (algebraMap k[X] (RatFunc k) h0) ^ 8 *
        integratedV68 (RatFunc.C L) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C eta) := by
  simp only [localClearedIntegratedV68RhoOne, integratedV68, map_add,
    map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
    RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD, hE]
  ring

/-! ## Source specialization -/

/-- The literal third lower row at the uniform rho-one box. -/
theorem SquareConstantLIntegratedLocalRootData68.topRowTwoRhoOne_zero
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    topRowTwo68
        ((ratFuncAtHahn46 T0.root T0.source.A).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.B).coeff (-3 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.C0).coeff (-4 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.D).coeff (-5 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.E).coeff (-6 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T0.root T0.source.A
  let BH := ratFuncAtHahn46 T0.root T0.source.B
  let CH := ratFuncAtHahn46 T0.root T0.source.C0
  let DH := ratFuncAtHahn46 T0.root T0.source.D
  let EH := ratFuncAtHahn46 T0.root T0.source.E
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C00 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
  let E0 := localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
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
  let S0 := localClearedIntegratedS68RhoOne h0 A0 B0 C00 D0 l
    T0.source.alpha T0.source.beta T0.source.delta
  let T00 := localClearedIntegratedT68RhoOne h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
  let U0 := localClearedIntegratedU68RhoOne h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
    T0.source.zeta
  let V0 := localClearedIntegratedV68RhoOne h0 A0 B0 C00 D0 E0 l
    T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
    T0.source.epsilon T0.source.eta
  obtain ⟨hA, hBclear, hCclear, hDclear, hEclear⟩ :=
    T0.source.clearedCoordinatesRhoOne hp T0.scale_ne_zero hH hp6 hp5 hp4
  change algebraMap k[X] (RatFunc k) A0 = _ at hA
  change algebraMap k[X] (RatFunc k) B0 = _ at hBclear
  change algebraMap k[X] (RatFunc k) C00 = _ at hCclear
  change algebraMap k[X] (RatFunc k) D0 = _ at hDclear
  change algebraMap k[X] (RatFunc k) E0 = _ at hEclear
  have hS : algebraMap k[X] (RatFunc k) S0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * SR := by
    exact algebraMap_localClearedIntegratedS68RhoOne h0 A0 B0 C00 D0
      T0.source.A T0.source.B T0.source.C0 T0.source.D l
      T0.source.alpha T0.source.beta T0.source.delta
      hA hBclear hCclear hDclear
  have hT : algebraMap k[X] (RatFunc k) T00 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * TR := by
    exact algebraMap_localClearedIntegratedT68RhoOne h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.epsilon
      hA hBclear hCclear hDclear hEclear
  have hU : algebraMap k[X] (RatFunc k) U0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 7 * UR := by
    exact algebraMap_localClearedIntegratedU68RhoOne h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
      T0.source.zeta hA hBclear hCclear hDclear hEclear
  have hV : algebraMap k[X] (RatFunc k) V0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 8 * VR := by
    exact algebraMap_localClearedIntegratedV68RhoOne h0 A0 B0 C00 D0 E0
      T0.source.A T0.source.B T0.source.C0 T0.source.D T0.source.E l
      T0.source.alpha T0.source.beta T0.source.gamma T0.source.delta
      T0.source.epsilon T0.source.eta
      hA hBclear hCclear hDclear hEclear
  obtain ⟨c, hc, hsingle, hderiv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T0.root T0.scale_degree T0.root_eq
  have hAco := localHahn_coeff_neg_of_cleared T0.root c h0 A0
    T0.source.A 2 hc hsingle hA
  have hBco := localHahn_coeff_neg_of_cleared T0.root c h0 B0
    T0.source.B 3 hc hsingle hBclear
  have hCco := localHahn_coeff_neg_of_cleared T0.root c h0 C00
    T0.source.C0 4 hc hsingle hCclear
  have hDco := localHahn_coeff_neg_of_cleared T0.root c h0 D0
    T0.source.D 5 hc hsingle hDclear
  have hEco := localHahn_coeff_neg_of_cleared T0.root c h0 E0
    T0.source.E 6 hc hsingle hEclear
  have hSco := localHahn_coeff_neg_of_cleared T0.root c h0 S0 SR
    5 hc hsingle hS
  have hTco := localHahn_coeff_neg_of_cleared T0.root c h0 T00 TR
    6 hc hsingle hT
  have hUco := localHahn_coeff_neg_of_cleared T0.root c h0 U0 UR
    7 hc hsingle hU
  have hVco := localHahn_coeff_neg_of_cleared T0.root c h0 V0 VR
    8 hc hsingle hV
  have hSord := localHahn_orderTop_ge_of_cleared T0.root h0 S0 SR
    5 T0.scale_order hS
  have hTord := localHahn_orderTop_ge_of_cleared T0.root h0 T00 TR
    6 T0.scale_order hT
  have hUord := localHahn_orderTop_ge_of_cleared T0.root h0 U0 UR
    7 T0.scale_order hU
  have hVord := localHahn_orderTop_ge_of_cleared T0.root h0 V0 VR
    8 T0.scale_order hV
  have hdTord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    T00 TR 6 T0.scale_order hT
  have hdUord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    U0 UR 7 T0.scale_order hU
  have hdVord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    V0 VR 8 T0.scale_order hV
  have hdTco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 T00 TR 6 hc hsingle hderiv hT
  have hdUco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 U0 UR 7 hc hsingle hderiv hU
  have hdVco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 V0 VR 8 hc hsingle hderiv hV
  have hdCord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    C00 T0.source.C0 4 T0.scale_order hCclear
  have hdDord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    D0 T0.source.D 5 T0.scale_order hDclear
  have hdEord := localHahn_deriv_orderTop_ge_of_cleared T0.root h0
    E0 T0.source.E 6 T0.scale_order hEclear
  have hdCco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 C00 T0.source.C0 4 hc hsingle hderiv hCclear
  have hdDco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 D0 T0.source.D 5 hc hsingle hderiv hDclear
  have hdEco := localHahn_deriv_coeff_neg_succ_of_cleared
    T0.root c h0 E0 T0.source.E 6 hc hsingle hderiv hEclear
  have hSroot : S0.eval T0.root =
      (4 / 3 : k) * D0.eval T0.root +
        (4 / 9 : k) * A0.eval T0.root * B0.eval T0.root := by
    simp [S0, localClearedIntegratedS68RhoOne, T0.root_eq]
  have hTroot : T00.eval T0.root =
      (4 / 3 : k) * E0.eval T0.root +
      (2 / 9 : k) * B0.eval T0.root ^ 2 +
      (4 / 9 : k) * A0.eval T0.root * C00.eval T0.root -
      (4 / 81 : k) * A0.eval T0.root ^ 3 := by
    simp [T00, localClearedIntegratedT68RhoOne, T0.root_eq]
  have hUroot : U0.eval T0.root =
      (4 / 9 : k) * B0.eval T0.root * C00.eval T0.root +
      (4 / 9 : k) * A0.eval T0.root * D0.eval T0.root -
      (4 / 27 : k) * A0.eval T0.root ^ 2 * B0.eval T0.root := by
    simp [U0, localClearedIntegratedU68RhoOne, T0.root_eq]
  have hVroot : V0.eval T0.root =
      (2 / 9 : k) * C00.eval T0.root ^ 2 +
      (4 / 9 : k) * B0.eval T0.root * D0.eval T0.root +
      (4 / 9 : k) * A0.eval T0.root * E0.eval T0.root -
      (4 / 27 : k) * A0.eval T0.root * B0.eval T0.root ^ 2 -
      (4 / 27 : k) * A0.eval T0.root ^ 2 * C00.eval T0.root +
      (5 / 243 : k) * A0.eval T0.root ^ 4 := by
    simp [V0, localClearedIntegratedV68RhoOne, T0.root_eq]
  dsimp only [SR, TR, UR, VR] at hSco hTco hUco hVco hSord hTord hUord hVord hdTord hdUord hdVord hdTco hdUco hdVco
  norm_num at hAco hBco hCco hDco hEco hSco hTco hUco hVco
  have hSco' : SH.coeff (-5 : ℚ) =
      (4 / 3 : k) * DH.coeff (-5 : ℚ) +
        (4 / 9 : k) * AH.coeff (-2 : ℚ) * BH.coeff (-3 : ℚ) := by
    dsimp only [AH, BH, DH, SH]
    rw [hSco, hSroot, hAco, hBco, hDco]
    field_simp [hc]
  have hTco' : TH.coeff (-6 : ℚ) =
      (4 / 3 : k) * EH.coeff (-6 : ℚ) +
      (2 / 9 : k) * BH.coeff (-3 : ℚ) ^ 2 +
      (4 / 9 : k) * AH.coeff (-2 : ℚ) * CH.coeff (-4 : ℚ) -
      (4 / 81 : k) * AH.coeff (-2 : ℚ) ^ 3 := by
    dsimp only [AH, BH, CH, EH, TH]
    rw [hTco, hTroot, hAco, hBco, hCco, hEco]
    field_simp [hc]
  have hUco' : UH.coeff (-7 : ℚ) =
      (4 / 9 : k) * BH.coeff (-3 : ℚ) * CH.coeff (-4 : ℚ) +
      (4 / 9 : k) * AH.coeff (-2 : ℚ) * DH.coeff (-5 : ℚ) -
      (4 / 27 : k) * AH.coeff (-2 : ℚ) ^ 2 * BH.coeff (-3 : ℚ) := by
    dsimp only [AH, BH, CH, DH, UH]
    rw [hUco, hUroot, hAco, hBco, hCco, hDco]
    field_simp [hc]
  have hVco' : VH.coeff (-8 : ℚ) =
      (2 / 9 : k) * CH.coeff (-4 : ℚ) ^ 2 +
      (4 / 9 : k) * BH.coeff (-3 : ℚ) * DH.coeff (-5 : ℚ) +
      (4 / 9 : k) * AH.coeff (-2 : ℚ) * EH.coeff (-6 : ℚ) -
      (4 / 27 : k) * AH.coeff (-2 : ℚ) * BH.coeff (-3 : ℚ) ^ 2 -
      (4 / 27 : k) * AH.coeff (-2 : ℚ) ^ 2 * CH.coeff (-4 : ℚ) +
      (5 / 243 : k) * AH.coeff (-2 : ℚ) ^ 4 := by
    dsimp only [AH, BH, CH, DH, EH, VH]
    rw [hVco, hVroot, hAco, hBco, hCco, hDco, hEco]
    field_simp [hc]
  obtain ⟨hAord, hBord, hCord, hDord, hEord⟩ :=
    T0.coordinateOrderBoundsRhoOne hp hH hp6 hp5 hp4
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
    (fun x : HahnSeries ℚ k => x.coeff (-12 : ℚ)) hrowH'
  simp only [HahnSeries.coeff_zero] at hcoeff
  have hface := lowerRowTwoHahn68_coeff_neg12_rhoOne
    AH BH CH DH EH SH TH UH VH dCH dDH dEH dTH dUH dVH
      hBord hCord hDord hEord
      (by dsimp only [SH, SR]; convert hSord using 1 <;> norm_num)
      (by dsimp only [TH, TR]; convert hTord using 1 <;> norm_num)
      (by dsimp only [UH, UR]; convert hUord using 1 <;> norm_num)
      (by dsimp only [VH, VR]; convert hVord using 1 <;> norm_num)
      (by dsimp only [dCH]; convert hdCord using 1 <;> norm_num)
      (by dsimp only [dDH]; convert hdDord using 1 <;> norm_num)
      (by dsimp only [dEH]; convert hdEord using 1 <;> norm_num)
      (by dsimp only [dTH, TR]; convert hdTord using 1 <;> norm_num)
      (by dsimp only [dUH, UR]; convert hdUord using 1 <;> norm_num)
      (by dsimp only [dVH, VR]; convert hdVord using 1 <;> norm_num)
      hSco' hTco' hUco' hVco'
      (by dsimp only [dCH, CH]; convert hdCco using 1 <;> norm_num)
      (by dsimp only [dDH, DH]; convert hdDco using 1 <;> norm_num)
      (by dsimp only [dEH, EH]; convert hdEco using 1 <;> norm_num)
      (by dsimp only [dTH, TH, TR]; convert hdTco using 1 <;> norm_num)
      (by dsimp only [dUH, UH, UR]; convert hdUco using 1 <;> norm_num)
      (by dsimp only [dVH, VH, VR]; convert hdVco using 1 <;> norm_num)
  rw [hface] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

def rhoOneResidualTwo68 (t v z : k) : k :=
  topRowTwo68 (rhoOneInitialA68 v z) (rhoOneInitialB68 t v z)
    (rhoOneInitialC68 t v z) (rhoOneInitialD68 t v z)
    (rhoOneInitialE68 t v z)

def rhoOneAffineTwo68 (T V : k) : k := rhoOneResidualTwo68 T V 1

/-- The old degree-ten packet plus the exact third differential row. -/
def RhoOneNoncubicThreeRowPacket68
    {p q : k[X][X]} {j l : k} {h0 : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (g u : k[X]) : Prop :=
  ∃ c t v z : k, c ≠ 0 ∧
    ratFuncAtHahn46 T0.root (algebraMap k[X] (RatFunc k) h0) =
      HahnSeries.single (1 : ℚ) c ∧
    t = (c ^ 3)⁻¹ * (p.coeff 3).eval T0.root ∧
    v = (c ^ 2)⁻¹ * u.eval T0.root ∧
    z = c⁻¹ * g.eval T0.root ∧ z ≠ 0 ∧
    rhoOneNoncubicVPolynomial68 (v / z ^ 2) = 0 ∧
    rhoOneAffineFour68 (t / z ^ 3) (v / z ^ 2) = 0 ∧
    rhoOneAffineThree68 (t / z ^ 3) (v / z ^ 2) = 0 ∧
    rhoOneAffineTwo68 (t / z ^ 3) (v / z ^ 2) = 0

theorem rhoOneResidualTwo68_normalize (t v z : k) (hz : z ≠ 0) :
    rhoOneResidualTwo68 t v z =
      z ^ 11 * rhoOneAffineTwo68 (t / z ^ 3) (v / z ^ 2) := by
  simp only [rhoOneResidualTwo68, rhoOneAffineTwo68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68,
    rhoOneInitialE68, topRowTwo68]
  field_simp [hz]

/-- The actual source noncubic packet maps to the strictly smaller
three-equation residual packet. -/
theorem SquareConstantLIntegratedLocalRootData68.rhoOneNoncubic_nextRow
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hpacket : RhoOneNoncubicSourcePacket68 T0 g u) :
    RhoOneNoncubicThreeRowPacket68 T0 g u := by
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hP, h4, h3⟩ := hpacket
  have h2 := T0.topRowTwoRhoOne_zero hp hH hp6 hp5 hp4
  have hAform : (ratFuncAtHahn46 T0.root T0.source.A).coeff (-2 : ℚ) =
      rhoOneInitialA68 v z := by
    obtain ⟨hAc, hBc, hCc, hDc, hEc⟩ :=
      T0.source.clearedCoordinatesRhoOne hp T0.scale_ne_zero hH hp6 hp5 hp4
    have hAco := localHahn_coeff_neg_of_cleared T0.root c h0
      (localClearedA68RhoOne g u) T0.source.A 2 hc hsingle hAc
    have hAco' : (ratFuncAtHahn46 T0.root T0.source.A).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * (localClearedA68RhoOne g u).eval T0.root := by
      convert hAco using 1 <;> norm_num
    rw [hAco']
    simp only [rhoOneInitialA68, hv, hzdef, localClearedA68RhoOne]
    simp
    field_simp [hc]
  have hBform : (ratFuncAtHahn46 T0.root T0.source.B).coeff (-3 : ℚ) =
      rhoOneInitialB68 t v z := by
    obtain ⟨hAc, hBc, hCc, hDc, hEc⟩ :=
      T0.source.clearedCoordinatesRhoOne hp T0.scale_ne_zero hH hp6 hp5 hp4
    have hBco := localHahn_coeff_neg_of_cleared T0.root c h0
      (localClearedB68RhoOne g u (p.coeff 3)) T0.source.B 3 hc hsingle hBc
    have hBco' : (ratFuncAtHahn46 T0.root T0.source.B).coeff (-3 : ℚ) =
        (c ^ 3)⁻¹ * (localClearedB68RhoOne g u (p.coeff 3)).eval T0.root := by
      convert hBco using 1 <;> norm_num
    rw [hBco']
    simp only [rhoOneInitialB68, ht, hv, hzdef, localClearedB68RhoOne]
    simp
    field_simp [hc]
  have hCform : (ratFuncAtHahn46 T0.root T0.source.C0).coeff (-4 : ℚ) =
      rhoOneInitialC68 t v z := by
    obtain ⟨hAc, hBc, hCc, hDc, hEc⟩ :=
      T0.source.clearedCoordinatesRhoOne hp T0.scale_ne_zero hH hp6 hp5 hp4
    have hCco := localHahn_coeff_neg_of_cleared T0.root c h0
      (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2))
      T0.source.C0 4 hc hsingle hCc
    have hCco' : (ratFuncAtHahn46 T0.root T0.source.C0).coeff (-4 : ℚ) =
        (c ^ 4)⁻¹ * (localClearedC68RhoOne h0 g u (p.coeff 3)
          (p.coeff 2)).eval T0.root := by
      convert hCco using 1 <;> norm_num
    rw [hCco']
    simp only [rhoOneInitialC68, ht, hv, hzdef, localClearedC68RhoOne]
    simp [T0.root_eq]
    field_simp [hc]
  have hDform : (ratFuncAtHahn46 T0.root T0.source.D).coeff (-5 : ℚ) =
      rhoOneInitialD68 t v z := by
    obtain ⟨hAc, hBc, hCc, hDc, hEc⟩ :=
      T0.source.clearedCoordinatesRhoOne hp T0.scale_ne_zero hH hp6 hp5 hp4
    have hDco := localHahn_coeff_neg_of_cleared T0.root c h0
      (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1))
      T0.source.D 5 hc hsingle hDc
    have hDco' : (ratFuncAtHahn46 T0.root T0.source.D).coeff (-5 : ℚ) =
        (c ^ 5)⁻¹ * (localClearedD68RhoOne h0 g u (p.coeff 3)
          (p.coeff 2) (p.coeff 1)).eval T0.root := by
      convert hDco using 1 <;> norm_num
    rw [hDco']
    simp only [rhoOneInitialD68, ht, hv, hzdef, localClearedD68RhoOne]
    simp [T0.root_eq]
    field_simp [hc]
  have hEform : (ratFuncAtHahn46 T0.root T0.source.E).coeff (-6 : ℚ) =
      rhoOneInitialE68 t v z := by
    obtain ⟨hAc, hBc, hCc, hDc, hEc⟩ :=
      T0.source.clearedCoordinatesRhoOne hp T0.scale_ne_zero hH hp6 hp5 hp4
    have hEco := localHahn_coeff_neg_of_cleared T0.root c h0
      (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
        (p.coeff 0)) T0.source.E 6 hc hsingle hEc
    have hEco' : (ratFuncAtHahn46 T0.root T0.source.E).coeff (-6 : ℚ) =
        (c ^ 6)⁻¹ * (localClearedE68RhoOne h0 g u (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0)).eval T0.root := by
      convert hEco using 1 <;> norm_num
    rw [hEco']
    simp only [rhoOneInitialE68, ht, hv, hzdef, localClearedE68RhoOne]
    simp [T0.root_eq]
    field_simp [hc]
  rw [hAform, hBform, hCform, hDform, hEform] at h2
  change rhoOneResidualTwo68 t v z = 0 at h2
  have h2aff : rhoOneAffineTwo68 (t / z ^ 3) (v / z ^ 2) = 0 := by
    rw [rhoOneResidualTwo68_normalize t v z hz] at h2
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 11 hz)
  exact ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hP, h4, h3, h2aff⟩

end RhoOneNoncubicNext68

#print axioms lowerRowTwoHahn68_coeff_neg12_rhoOne
#print axioms algebraMap_localClearedIntegratedS68RhoOne
#print axioms algebraMap_localClearedIntegratedT68RhoOne
#print axioms algebraMap_localClearedIntegratedU68RhoOne
#print axioms algebraMap_localClearedIntegratedV68RhoOne
#print axioms SquareConstantLIntegratedLocalRootData68.topRowTwoRhoOne_zero
#print axioms rhoOneResidualTwo68_normalize
#print axioms SquareConstantLIntegratedLocalRootData68.rhoOneNoncubic_nextRow

end Max11DegreeRoutes
