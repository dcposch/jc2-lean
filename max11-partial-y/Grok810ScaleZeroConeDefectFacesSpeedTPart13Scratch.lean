import Grok810ScaleZeroConeDefectFacesSpeedTPart10Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart12Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Scale-zero faces and residual -/

section DefectFacesClosed810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Source-facing packet: `ξ`, `μ`, and `ο` are ground constants on the
free core, and every unique weighted face named above is empty. -/
theorem normalized810ScaleZero_defectFaces_closed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hcXi, hxi, hcMu, hmu, hcOm, hom⟩ :=
    normalized810ScaleZero_defectPolynomials_eq_C hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hdeg, hxi, hmu, hom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hAmax
    exact xi_A7_impossible_of_A_maximal l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hAmax hxi
  · intro hBleads
    exact omicron_B5_impossible_of_B_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hBleads hom
  · intro hCleads
    exact mu_C03_impossible_of_C0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hCleads hmu
  · intro hDleads
    exact omicron_D03_impossible_of_D0_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hDleads hom
  · intro hEleads
    exact mu_E02_impossible_of_E0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hEleads hmu
  · intro hFleads
    exact xi_F02_impossible_of_F0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hFleads hxi
  · intro hconst
    exact degreeZeroPrimitivePolynomial810_false_of_constant_core l beta
      gamma delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0
      hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2.1 hconst.2.2.2.2.2.1 hconst.2.2.2.2.2.2 hder

set_option maxHeartbeats 64000000 in
/-- Remaining cones after every unique weighted `ξ`/`μ`/`ο` face named
above.  Unique-`G₀` of degree one with vanishing `G₀`-linear
coefficients of `ξ`, `μ`, and `ο` (CAS: those coefficients reduce to
`(1/2) ε`, `(3/4) γ`, and `(3/8) ζ` when the other letters vanish) is
the next comparison, together with the pair-ratio ties in which no
load-free face strictly leads.  The unused first integrals `κ` and `ν`
are available on that unique-`G₀` chamber. -/
theorem normalized810ScaleZero_coneDefectFacesResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hxi, hmu, hom, hAmax, hBleads, hCleads, hDleads, hEleads,
      hFleads, _hconst⟩ :=
    normalized810ScaleZero_defectFaces_closed hsource
  exact ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hxi, hmu, hom, hAmax, hBleads, hCleads, hDleads, hEleads, hFleads⟩

set_option maxHeartbeats 64000000 in
/-- Glue of the two constant faces through the defect-face residual: the
scale-zero source is empty once the named leftover cones are excluded.
Neither leftover cone is claimed empty here. -/
theorem normalized810ScaleZero_impossible_of_defectFacesResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
          cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta
                epsilon zeta eta theta A B C0 D0 E0 F0 G0) =
            Polynomial.C (j / t) ∧
          (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneDefectFacesResidual hsource)

end DefectFacesClosed810




end Max11DegreeRoutes
