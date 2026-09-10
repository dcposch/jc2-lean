import Grok810ScaleZeroQuarticSigmaLadderPart59Scratch

/-! Part 60 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticParityCorner810


set_option maxHeartbeats 64000000 in
theorem quarticParityCorner_BDF_zero_impossible {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hB : B = 0) (hD : D = 0) (hF : F = 0) (hl : l = 0)
    (hbeta : beta = 0) (hdelta : delta = 0) (hzeta : zeta = 0)
    (htheta : theta = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) : False := by
  subst hB; subst hD; subst hF; subst hl; subst hbeta; subst hdelta
  subst hzeta; subst htheta
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810,
    rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero, sub_self, derivative_zero] at hder
  exact hjdiv (by simpa using (Polynomial.C_eq_zero.mp hder.symm))


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_allZero
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t))
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    False := by
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  exact quarticADominant_allLettersZero_impossible (j := j) (t := t)
    l beta gamma delta epsilon zeta eta theta A B C D E F G
    hApos hBz hCz hDz hEz hFz hGz hjdiv hder


end QuarticParityCorner810
end Max11DegreeRoutes
end
