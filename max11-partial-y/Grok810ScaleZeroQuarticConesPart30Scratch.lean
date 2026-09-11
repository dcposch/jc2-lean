import Grok810ScaleZeroQuarticKillsSpeedReflSplitPart2Scratch
import Grok810ScaleZeroQuarticKillsSpeedReflSplitPart3Scratch
import Grok810ScaleZeroQuarticMultiKillsPart04Scratch
import Grok810ScaleZeroQuarticMultiKillsPart08Scratch
import Grok810ScaleZeroQuarticMultiKillsPart23Scratch
import Grok810ScaleZeroQuarticMultiKillsPart27Scratch
import Grok810ScaleZeroQuarticMultiKillsPart47Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitPart3Scratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitPart3Scratch
import Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitPart1Scratch
import Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitPart3Scratch
import Grok810ScaleZeroQuarticMultiKills4Part11Scratch
import Grok810ScaleZeroQuarticMultiKills4Part23Scratch
import Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitPart3Scratch
import Grok810ScaleZeroQuarticMultiKills5Scratch
import Grok810ScaleZeroQuarticMultiKills6Part18Scratch
import Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegSplitPart23Scratch
import Grok810ScaleZeroQuarticConesPart29Scratch

/-! # Part 30 of `Grok810ScaleZeroQuarticConesScratch`.

One declaration split out of `Grok810ScaleZeroQuarticConesScratch`; statements are byte-identical.
-/

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
set_option maxHeartbeats 64000000

section QuarticADominant810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
theorem normalized810ScaleZero_quarticADominantResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 ∧
      (
        QuarticRatioConeA810 A B C D E F G ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg⟩ :=
    normalized810ScaleZero_quarticResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  cases quarticSupportCone810_of A B C D E F G with
  | coneA h => exact Or.inl h
  | coneB h =>
    exact (quarticCone_B_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneC h =>
    exact (quarticCone_C_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneD h =>
    exact (quarticCone_D_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h homiDeg).elim
  | coneE h =>
    exact (quarticCone_E_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneF h =>
    exact (quarticCone_F_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneG h =>
    exact (quarticCone_G_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hpiDeg).elim
  | coneAB h =>
    exact (quarticCone_AB_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneAC h =>
    exact (quarticCone_AC_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneAD h =>
    exact (quarticCone_AD_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneAE h =>
    exact (quarticCone_AE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneAF h =>
    exact (quarticCone_AF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneAG h =>
    exact (quarticCone_AG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hpiDeg).elim
  | coneBC h =>
    exact (quarticCone_BC_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneBD h =>
    exact (quarticCone_BD_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneBE h =>
    exact (quarticCone_BE_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBF h =>
    exact (quarticCone_BF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneBG h =>
    exact (quarticCone_BG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCD h =>
    exact (quarticCone_CD_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneCE h =>
    exact (quarticCone_CE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneCF h =>
    exact (quarticCone_CF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCG h =>
    exact (quarticCone_CG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneDE h =>
    exact (quarticCone_DE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneDF h =>
    exact (quarticCone_DF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneDG h =>
    exact (quarticCone_DG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hnuDeg).elim
  | coneEF h =>
    exact (quarticCone_EF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneEG h =>
    exact (quarticCone_EG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneFG h =>
    exact (quarticCone_FG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneABC h =>
    exact (quarticCone_ABC_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABD h =>
    exact (quarticCone_ABD_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABE h =>
    exact (quarticCone_ABE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneABF h =>
    exact (quarticCone_ABF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneABG h =>
    exact (quarticCone_ABG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneACD h =>
    exact (quarticCone_ACD_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hnuDeg).elim
  | coneACE h =>
    exact (quarticCone_ACE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneACF h =>
    exact (quarticCone_ACF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneACG h =>
    exact (quarticCone_ACG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneADE h =>
    exact (quarticCone_ADE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneADF h =>
    exact (quarticCone_ADF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h homiDeg).elim
  | coneADG h =>
    exact (quarticCone_ADG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneAEF h =>
    exact (quarticCone_AEF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneAEG h =>
    exact (quarticCone_AEG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneAFG h =>
    exact (quarticCone_AFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneBCD h =>
    exact (quarticCone_BCD_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCE h =>
    exact (quarticCone_BCE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneBCF h =>
    exact (quarticCone_BCF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCG h =>
    exact (quarticCone_BCG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hnuDeg).elim
  | coneBDE h =>
    exact (quarticCone_BDE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hnuDeg).elim
  | coneBDF h =>
    exact (quarticCone_BDF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneBDG h =>
    exact (quarticCone_BDG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneBEF h =>
    exact (quarticCone_BEF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneBEG h =>
    exact (quarticCone_BEG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneBFG h =>
    exact (quarticCone_BFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCDE h =>
    exact (quarticCone_CDE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCDF h =>
    exact (quarticCone_CDF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCDG h =>
    exact (quarticCone_CDG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneCEF h =>
    exact (quarticCone_CEF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCEG h =>
    exact (quarticCone_CEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneCFG h =>
    exact (quarticCone_CFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneDEF h =>
    exact (quarticCone_DEF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneDEG h =>
    exact (quarticCone_DEG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneDFG h =>
    exact (quarticCone_DFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneEFG h =>
    exact (quarticCone_EFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneABCD h =>
    exact (quarticCone_ABCD_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCE h =>
    exact (quarticCone_ABCE_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCF h =>
    exact (quarticCone_ABCF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCG h =>
    exact (quarticCone_ABCG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABDE h =>
    exact (quarticCone_ABDE_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABDF h =>
    exact (quarticCone_ABDF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABDG h =>
    exact (quarticCone_ABDG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABEF h =>
    exact (quarticCone_ABEF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneABEG h =>
    exact (quarticCone_ABEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABFG h =>
    exact (quarticCone_ABFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneACDE h =>
    exact (quarticCone_ACDE_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneACDF h =>
    exact (quarticCone_ACDF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneACDG h =>
    exact (quarticCone_ACDG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hxiDeg).elim
  | coneACEF h =>
    exact (quarticCone_ACEF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneACEG h =>
    exact (quarticCone_ACEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneACFG h =>
    exact (quarticCone_ACFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneADEF h =>
    exact (quarticCone_ADEF_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneADEG h =>
    exact (quarticCone_ADEG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneADFG h =>
    exact (quarticCone_ADFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hnuDeg).elim
  | coneAEFG h =>
    exact (quarticCone_AEFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hmuDeg).elim
  | coneBCDE h =>
    exact (quarticCone_BCDE_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCDF h =>
    exact (quarticCone_BCDF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCDG h =>
    exact (quarticCone_BCDG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCEF h =>
    exact (quarticCone_BCEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCEG h =>
    exact (quarticCone_BCEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCFG h =>
    exact (quarticCone_BCFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBDEF h =>
    exact (quarticCone_BDEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBDEG h =>
    exact (quarticCone_BDEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBDFG h =>
    exact (quarticCone_BDFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBEFG h =>
    exact (quarticCone_BEFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCDEF h =>
    exact (quarticCone_CDEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneCDEG h =>
    exact (quarticCone_CDEG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCDFG h =>
    exact (quarticCone_CDFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneCEFG h =>
    exact (quarticCone_CEFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneDEFG h =>
    exact (quarticCone_DEFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneABCDE h =>
    exact (quarticCone_ABCDE_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCDF h =>
    exact (quarticCone_ABCDF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCDG h =>
    exact (quarticCone_ABCDG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCEF h =>
    exact (quarticCone_ABCEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCEG h =>
    exact (quarticCone_ABCEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCFG h =>
    exact (quarticCone_ABCFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABDEF h =>
    exact (quarticCone_ABDEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABDEG h =>
    exact (quarticCone_ABDEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABDFG h =>
    exact (quarticCone_ABDFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABEFG h =>
    exact (quarticCone_ABEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneACDEF h =>
    exact (quarticCone_ACDEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneACDEG h =>
    exact (quarticCone_ACDEG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneACDFG h =>
    exact (quarticCone_ACDFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneACEFG h =>
    exact (quarticCone_ACEFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneADEFG h =>
    exact (quarticCone_ADEFG_impossible l beta gamma delta epsilon zeta eta theta
        A B C D E F G h hkapDeg).elim
  | coneBCDEF h =>
    exact (quarticCone_BCDEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCDEG h =>
    exact (quarticCone_BCDEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCDFG h =>
    exact (quarticCone_BCDFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCEFG h =>
    exact (quarticCone_BCEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBDEFG h =>
    exact (quarticCone_BDEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneCDEFG h =>
    exact (quarticCone_CDEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCDEF h =>
    exact (quarticCone_ABCDEF_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCDEG h =>
    exact (quarticCone_ABCDEG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCDFG h =>
    exact (quarticCone_ABCDFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCEFG h =>
    exact (quarticCone_ABCEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABDEFG h =>
    exact (quarticCone_ABDEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneACDEFG h =>
    exact (quarticCone_ACDEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneBCDEFG h =>
    exact (quarticCone_BCDEFG_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h hxiDeg hmuDeg homiDeg
        hkapDeg hnuDeg hpiDeg hjdiv hder).elim
  | coneABCDEFG h => exact (Or.inr h)
  | allConst h =>
    exact (quarticCone_allConstant_impossible (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G h.1 h.2.1 h.2.2.1 h.2.2.2.1
        h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 hjdiv hder).elim

#print axioms quarticC810_add
#print axioms degreeZeroKappaPolynomial810_eq_quartic
#print axioms degreeZeroMuPolynomial810_eq_quartic
#print axioms degreeZeroNuPolynomial810_eq_quartic
#print axioms degreeZeroXiPolynomial810_eq_quartic
#print axioms degreeZeroOmicronPolynomial810_eq_quartic
#print axioms degreeZeroPiPolynomial810_eq_quartic
#print axioms degreeZeroPrimitivePolynomial810_eq_quartic
#print axioms normalized810ScaleZero_quarticResidual
#print axioms normalized810ScaleZero_quarticADominantResidual

end QuarticADominant810

end Max11DegreeRoutes
