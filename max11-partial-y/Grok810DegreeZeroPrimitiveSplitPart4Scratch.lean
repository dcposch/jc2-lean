import Grok810DegreeZeroPrimitiveSplitPart101Scratch

/-! # SPEED: theorems of `Grok810DegreeZeroPrimitiveScratch`, part 4 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxRecDepth 8000000

section DegreeZeroPrimitive810

variable {F : Type*} [Field F] [CharZero F]

section DerivativeCertificate

variable {k : Type*} [Field k] [Algebra k F]

/-- Lane Z2: on the residual-constant locus, `dρ = 0` if and only if the
degree-zero Jacobian coefficient vanishes. -/
theorem rhoResidual810_deriv_eq_zero_iff_row
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0)
    (hkappa : d (kappaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (hmu : d (muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (hnu : d (nuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (hxi : d (xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (homicron : d (omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0) :
    d (rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 ↔
      W0 * d G0 - F0 * d X0 = 0 := by
  rw [rhoResidual810_deriv_eq_row d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hkappa
    hmu hnu hxi homicron]


end DerivativeCertificate

end DegreeZeroPrimitive810

end Max11DegreeRoutes

end
