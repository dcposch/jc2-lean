import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart15pScratch

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section CubicADominant610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in

theorem normalized610ScaleZero_cubicADominantResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C D E : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
            eta theta A B C D E) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      CubicRatioConeA610 A B C D E := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg⟩ :=
    normalized610ScaleZero_cubicResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, ?_⟩
  cases cubicSupportCone610_of A B C D E with

  | coneA h => exact h
  | coneB h =>
    exact (cubicCone_B_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneC h =>
    exact (cubicCone_C_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneD h =>
    exact (cubicCone_D_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hjdiv hder).elim
  | coneE h =>
    exact (cubicCone_E_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneAB h =>
    exact (cubicCone_AB_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneAC h =>
    exact (cubicCone_AC_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneAD h =>
    exact (cubicCone_AD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneAE h =>
    exact (cubicCone_AE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneBC h =>
    exact (cubicCone_BC_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBD h =>
    exact (cubicCone_BD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBE h =>
    exact (cubicCone_BE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneCD h =>
    exact (cubicCone_CD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneCE h =>
    exact (cubicCone_CE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h homiDeg).elim
  | coneDE h =>
    exact (cubicCone_DE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneABC h =>
    exact (cubicCone_ABC_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABD h =>
    exact (cubicCone_ABD_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABE h =>
    exact (cubicCone_ABE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneACD h =>
    exact (cubicCone_ACD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hmuDeg).elim
  | coneACE h =>
    exact (cubicCone_ACE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h homiDeg).elim
  | coneADE h =>
    exact (cubicCone_ADE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBCD h =>
    exact (cubicCone_BCD_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneBCE h =>
    exact (cubicCone_BCE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBDE h =>
    exact (cubicCone_BDE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hmuDeg).elim
  | coneCDE h =>
    exact (cubicCone_CDE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneABCD h =>
    exact (cubicCone_ABCD_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABCE h =>
    exact (cubicCone_ABCE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABDE h =>
    exact (cubicCone_ABDE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneACDE h =>
    exact (cubicCone_ACDE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBCDE h =>
    exact (cubicCone_BCDE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABCDE h =>
    exact (cubicCone_ABCDE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | allConst h =>
    exact (cubicCone_allConstant_impossible (j := j) (t := t) l alpha
        beta delta epsilon zeta eta theta A B C D E h.1 h.2.1 h.2.2.1
        h.2.2.2.1 h.2.2.2.2 hjdiv hder).elim

end CubicADominant610

end Max11DegreeRoutes

end
