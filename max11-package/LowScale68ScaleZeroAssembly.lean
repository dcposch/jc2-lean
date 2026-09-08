import LowScale68Expansion

/-! # Source assembly for the scale-zero `(6,8)` branch

This module closes the formal transport from a literal normalized
source with constant leading core to the exact polynomial lower system.  The
remaining mathematical input is isolated as exclusion of that lower system.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section SourceScaleZeroAssembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 4000000

/-- Generic last mile from a depressed rational Keller bracket, polynomial
representatives of its sextic coefficients, and a nonzero ground terminal to
the exact polynomial lower system. -/
theorem depressedSourceData_exists_integratedPolynomialLowerSystem68
    (A B C0 D E L P Q R S T U V : RatFunc k)
    (A0 B0 C00 D0 E0 : k[X]) (terminal : k)
    (hterminal : terminal ≠ 0)
    (hA0 : algebraMap k[X] (RatFunc k) A0 = A)
    (hB0 : algebraMap k[X] (RatFunc k) B0 = B)
    (hC0 : algebraMap k[X] (RatFunc k) C00 = C0)
    (hD0 : algebraMap k[X] (RatFunc k) D0 = D)
    (hE0 : algebraMap k[X] (RatFunc k) E0 = E)
    (hbracket : differentialJacobian ratFuncDerivation68
        (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) = C (RatFunc.C terminal)) :
    ∃ (l alpha beta gamma delta epsilon zeta eta : k),
      terminal ≠ 0 ∧
      IntegratedPolynomialLowerSystem68 l alpha beta gamma delta epsilon zeta
        eta terminal A0 B0 C00 D0 E0 := by
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta,
      hL, hP, hQ, hR, hS, hT, hU, hV⟩ :=
    depressedCoefficients_integrate_over_ground68
      L P Q R S T U V A B C0 D E (RatFunc.C terminal) hbracket
  have hintegrated := hbracket
  rw [hL, hP, hQ, hR, hS, hT, hU, hV] at hintegrated
  rw [hL] at hintegrated
  simp only [RatFunc.algebraMap_eq_C] at hintegrated
  refine ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta,
    hterminal, ?_⟩
  apply integratedRationalLowerSystem_polynomialLowerSystem68
      (A := A) (B := B) (C0 := C0) (D := D) (E := E)
      (A0 := A0) (B0 := B0) (C00 := C00) (D0 := D0) (E0 := E0)
      (l := l) (alpha := alpha) (beta := beta) (gamma := gamma)
      (delta := delta) (epsilon := epsilon) (zeta := zeta) (eta := eta)
      (terminal := terminal)
  · exact hA0
  · exact hB0
  · exact hC0
  · exact hD0
  · exact hE0
  · exact hintegrated

/-- A literal normalized `(6,8)` Keller source whose common leading core has
degree zero produces polynomial depressed coefficients satisfying the exact
five-row integrated lower system, with nonzero terminal constant. -/
theorem normalized68ScaleZero_exists_integratedPolynomialLowerSystem
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 0) :
    ∃ (l alpha beta gamma delta epsilon zeta eta terminal : k)
        (A B C0 D E : k[X]),
      terminal ≠ 0 ∧
      IntegratedPolynomialLowerSystem68 l alpha beta gamma delta epsilon zeta
        eta terminal A B C0 D E := by
  rcases hsource with
    ⟨hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by
    simpa only [q] using hq8
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hcne : c ≠ 0 := by
    intro hzero
    apply hHne
    rw [← hc, hzero, C_0]
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c
    (by norm_num : 0 < 2)
  have htne : t ≠ 0 := by
    intro hzero
    apply hcne
    rw [← ht, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  have hHsquare : H = (C t : k[X]) ^ 2 := by
    rw [← hc, ← C_pow, ht]
  have hp6t : p.coeff 6 = (C t : k[X]) ^ 6 := by
    rw [hp6', hHsquare]
    ring
  have hq8t : q.coeff 8 = (C t : k[X]) ^ 8 := by
    rw [hq8', hHsquare]
    ring
  let scale : RatFunc k := RatFunc.C t
  let r0 : k[X] := C ((6 * t ^ 5) ⁻¹) * p.coeff 5
  let r : RatFunc k := algebraMap k[X] (RatFunc k) r0
  have hscale : scale ≠ 0 := by
    intro hzero
    apply htne
    apply RatFunc.C_injective
    simpa only [scale, map_zero] using hzero
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = scale ^ 6 := by
    rw [hp6t, map_pow]
    simp only [scale, RatFunc.algebraMap_C]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 8) = scale ^ 8 := by
    rw [hq8t, map_pow]
    simp only [scale, RatFunc.algebraMap_C]
  have hr : r = sexticDepressionR68 scale
      (algebraMap k[X] (RatFunc k) (p.coeff 5)) := by
    dsimp only [r, r0, scale]
    exact (sexticDepressionR68_constantScale_eq_algebraMap p t).symm
  let a5 := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b7 := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 := algebraMap k[X] (RatFunc k) (q.coeff 0)
  let A := depressedA68 scale r a5 a4
  let B := depressedB68 scale r a5 a4 a3
  let C0 := depressedC68 scale r a5 a4 a3 a2
  let D := depressedD68 scale r a5 a4 a3 a2 a1
  let E := depressedE68 scale r a5 a4 a3 a2 a1 a0
  let L := depressedL68 scale r b7
  let P1 := depressedP68 scale r b7 b6
  let Q1 := depressedQ68 scale r b7 b6 b5
  let R1 := depressedR68 scale r b7 b6 b5 b4
  let S1 := depressedS68 scale r b7 b6 b5 b4 b3
  let T1 := depressedT68 scale r b7 b6 b5 b4 b3 b2
  let U1 := depressedU68 scale r b7 b6 b5 b4 b3 b2 b1
  let V1 := depressedV68 scale r b7 b6 b5 b4 b3 b2 b1 b0
  have hpDep : affineDepress68 scale r (sourceToRatFunc68 p) =
      depressedSextic68 A B C0 D E := by
    simpa only [A, B, C0, D, E, a5, a4, a3, a2, a1, a0] using
      affineDepress_sourceSextic68 p scale r hp hscale hpTop hr
  have hqDep : affineDepress68 scale r (sourceToRatFunc68 q) =
      depressedOctic68 L P1 Q1 R1 S1 T1 U1 V1 := by
    simpa only [L, P1, Q1, R1, S1, T1, U1, V1,
      b7, b6, b5, b4, b3, b2, b1, b0] using
      affineDepress_sourceOctic68 q scale r hq hscale hqTop
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let terminal : k := j / t
  have hterminal : terminal ≠ 0 := div_ne_zero hj htne
  have hbracket0 := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j scale r hscale hDsrc
  rw [hpDep, hqDep] at hbracket0
  have hbracket : differentialJacobian ratFuncDerivation68
      (depressedSextic68 A B C0 D E)
      (depressedOctic68 L P1 Q1 R1 S1 T1 U1 V1) =
        C (RatFunc.C terminal) := by
    simpa only [scale, terminal, map_div₀, RatFunc.algebraMap_eq_C] using
      hbracket0
  have hpDepConstant : affineDepress68 (RatFunc.C t)
      (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 p) =
        depressedSextic68 A B C0 D E := by
    simpa only [scale, r] using hpDep
  obtain ⟨A0, B0, C00, D0, E0, hA0, hB0, hC00, hD0, hE0⟩ :=
    constantScale_depressedSextic68_polynomialRepresentatives
      p t r0 htne A B C0 D E hpDepConstant
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta,
      hterminal', hsystem⟩ :=
    depressedSourceData_exists_integratedPolynomialLowerSystem68
      A B C0 D E L P1 Q1 R1 S1 T1 U1 V1 A0 B0 C00 D0 E0 terminal
      hterminal hA0 hB0 hC00 hD0 hE0 hbracket
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, terminal,
    A0, B0, C00, D0, E0, hterminal', hsystem⟩

/-- The single remaining endgame assertion after the source assembly above. -/
def IntegratedPolynomialLowerSystem68Exclusion : Prop :=
  ∀ (l alpha beta gamma delta epsilon zeta eta terminal : k)
      (A B C0 D E : k[X]),
    terminal ≠ 0 →
    IntegratedPolynomialLowerSystem68 l alpha beta gamma delta epsilon zeta
      eta terminal A B C0 D E → False

/-- A verifier-clean source exclusion adapter: all source normalization,
depression, descent, and denominator removal are discharged; only the
intrinsic polynomial lower-system exclusion is assumed. -/
theorem normalized68ScaleZero_impossible_of_lowerSystem_exclusion
    (hexclude : IntegratedPolynomialLowerSystem68Exclusion (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 0) : False := by
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, terminal,
      A, B, C0, D, E, hterminal, hsystem⟩ :=
    normalized68ScaleZero_exists_integratedPolynomialLowerSystem hsource
  exact hexclude l alpha beta gamma delta epsilon zeta eta terminal
    A B C0 D E hterminal hsystem

/-- The unresolved scale-two branch plus the isolated intrinsic polynomial
endgame gives the complete normalized low-scale `(6,8)` route. -/
def PlaneKellerNormalized68ScaleTwoRoute : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) k) (H : k[X]),
    Normalized68LeadingCoreSource P Q H 2 → PlanePairGenerates P Q

theorem planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo
    (hexclude : IntegratedPolynomialLowerSystem68Exclusion (k := k))
    (hscaleTwo : PlaneKellerNormalized68ScaleTwoRoute (k := k)) :
    PlaneKellerNormalized68LowScaleRoute (K := k) := by
  intro P Q H n hn hsource
  rcases hn with rfl | rfl
  · exact (normalized68ScaleZero_impossible_of_lowerSystem_exclusion
      hexclude hsource).elim
  · exact hscaleTwo P Q H hsource

end SourceScaleZeroAssembly68

#print axioms normalized68ScaleZero_exists_integratedPolynomialLowerSystem
#print axioms depressedSourceData_exists_integratedPolynomialLowerSystem68
#print axioms normalized68ScaleZero_impossible_of_lowerSystem_exclusion
#print axioms planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo

end Max11DegreeRoutes
