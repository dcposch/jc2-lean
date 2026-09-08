import Grok610ScaleZeroConeCascadePart27Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitive610_eq_integratedPrimitive
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta theta iota : F) :
    degreeZeroPrimitive610 L A B C0 D0 E0
        (integratedP610 A alpha)
        (integratedQ610 L A B beta)
        (integratedR610 L A B C0 alpha gamma)
        (integratedS610 L A B C0 D0 alpha beta delta)
        (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
        (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta)
        (integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon eta)
        (integratedW610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
          theta)
        (integratedX610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
          eta iota) =
      degreeZeroIntegratedPrimitive610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta := by
  obtain ⟨halpha, hbeta, _hgamma, hdelta, hepsilon, hzeta, heta, htheta,
      _hiota⟩ :=
    integratedResiduals610 L A B C0 D0 E0 alpha beta gamma delta epsilon
      zeta eta theta iota
  simp only [degreeZeroPrimitive610, degreeZeroIntegratedPrimitive610]
  rw [halpha, hbeta, hdelta, hepsilon, hzeta, heta, htheta]

end PrimitivePolynomial610

end Max11DegreeRoutes
