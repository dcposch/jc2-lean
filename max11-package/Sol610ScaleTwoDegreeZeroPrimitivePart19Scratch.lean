import Sol610ScaleTwoDegreeZeroPrimitivePart18Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

section DifferentialCertificate

variable {k : Type*} [Field k] [Algebra k F]

theorem degreeZeroPrimitive610_deriv_eq_row
    (d : Derivation k F F)
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (heta : d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0) = 0)
    (hkappa : d (kappaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0)
    (hlambda : d (lambdaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0)
    (hmu : d (muResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0) :
    d (degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0) =
      W0 * d E0 - D0 * d X0 := by
  rw [degreeZeroPrimitive610_deriv_identity d L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0]
  rw [hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta,
    hiota, hkappa, hlambda, hmu]
  ring

end DifferentialCertificate

end DegreeZeroPrimitive610

end Max11DegreeRoutes
