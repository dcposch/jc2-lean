import Fable810ScaleZeroFourteenthDefectPart29Scratch

/-! Part 30 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroFourteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-- The same row integrates: if the degree-`8`, degree-`7`, degree-`6`,
degree-`5`, degree-`4`, and degree-`2` Jacobian rows vanish, `L` is
constant, and the residuals `α, β, γ, δ, ε, ζ, η, θ, ι` are constant,
then the next residual `ο` is a differential constant. -/
theorem scaleZero_omicronResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
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
    (hrow8 : (9 : F) * L * d G0 + (8 : F) * P * d F0 +
        (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A -
        F0 * d P - (2 : F) * E0 * d Q -
        (3 : F) * D0 * d R - (4 : F) * C0 * d S0 -
        (5 : F) * B * d T0 - (6 : F) * A * d U0 -
        (8 : F) * d W0 = 0)
    (hrow7 : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0)
    (hrow6 : (7 : F) * Q * d G0 + (6 : F) * R * d F0 +
        (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        W0 * d A -
        F0 * d R - (2 : F) * E0 * d S0 -
        (3 : F) * D0 * d T0 - (4 : F) * C0 * d U0 -
        (5 : F) * B * d V0 - (6 : F) * A * d W0 = 0)
    (hrow5 : (6 : F) * R * d G0 + (5 : F) * S0 * d F0 +
        (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + W0 * d B -
        F0 * d S0 - (2 : F) * E0 * d T0 -
        (3 : F) * D0 * d U0 - (4 : F) * C0 * d V0 -
        (5 : F) * B * d W0 - (6 : F) * A * d X0 = 0)
    (hrow4 : (5 : F) * S0 * d G0 + (4 : F) * T0 * d F0 +
        (3 : F) * U0 * d E0 + (2 : F) * V0 * d D0 +
        W0 * d C0 -
        F0 * d T0 - (2 : F) * E0 * d U0 -
        (3 : F) * D0 * d V0 - (4 : F) * C0 * d W0 -
        (5 : F) * B * d X0 = 0)
    (hrow : (3 : F) * U0 * d G0 + (2 : F) * V0 * d F0 +
        W0 * d E0 -
        F0 * d V0 - (2 : F) * E0 * d W0 -
        (3 : F) * D0 * d X0 = 0) :
    d (omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 :=
  omicronResidual810_deriv_zero d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hrow8
    hrow7 hrow6 hrow5 hrow4 hrow


end ScaleZeroFourteenthDefect810
end Max11DegreeRoutes
end
