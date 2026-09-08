import Grok610ScaleZeroCubicADominantPart28Scratch
import Grok610ScaleZeroCubicADominantPart33Scratch
import Grok610ScaleZeroCubicADominantPart38Scratch
import Grok610ScaleZeroCubicADominantPart43Scratch
import Grok610ScaleZeroCubicADominantPart57Scratch
import Grok610ScaleZeroCubicADominantPart62Scratch
import Grok610ScaleZeroCubicADominantPart67Scratch
import Grok610ScaleZeroCubicADominantPart72Scratch
import Grok610ScaleZeroCubicADominantPart77Scratch
import Grok610ScaleZeroCubicADominantPart82Scratch
import Grok610ScaleZeroCubicADominantPart102Scratch
import Grok610ScaleZeroCubicADominantPart107Scratch
import Grok610ScaleZeroCubicADominantPart112Scratch
import Grok610ScaleZeroCubicADominantPart145Scratch

open scoped Polynomial.Bivariate
noncomputable section
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

section CubicAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Honest leftover of Stage B+C: the source is still on `R = {A}`,
none of the 13 empty σ-argmin cones, and not the all-constant cell.
The `{C,D}` refinement and the balanced cell are not yet closed in Lean
(`N₁` rest bounds did not finish under `compute_degree`+`omega`).
Load-compete chambers after `l = 0` likewise remain. -/
theorem normalized610ScaleZero_cubicADominantResidual2
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
          A B C D E).natDegree = 0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      CubicRatioConeA610 A B C D E ∧
      ¬ CubicSigmaConeB610 A B C D E ∧
      ¬ CubicSigmaConeC610 A B C D E ∧
      ¬ CubicSigmaConeD610 A B C D E ∧
      ¬ CubicSigmaConeE610 A B C D E ∧
      ¬ CubicSigmaConeBC610 A B C D E ∧
      ¬ CubicSigmaConeBD610 A B C D E ∧
      ¬ CubicSigmaConeBE610 A B C D E ∧
      ¬ CubicSigmaConeCE610 A B C D E ∧
      ¬ CubicSigmaConeDE610 A B C D E ∧
      ¬ CubicSigmaConeBCD610 A B C D E ∧
      ¬ CubicSigmaConeBCE610 A B C D E ∧
      ¬ CubicSigmaConeBDE610 A B C D E ∧
      ¬ CubicSigmaConeCDE610 A B C D E ∧
      ¬ (B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA⟩ :=
    normalized610ScaleZero_cubicADominantResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
    ?notB, ?notC, ?notD, ?notE, ?notBC, ?notBD, ?notBE, ?notCE, ?notDE,
    ?notBCD, ?notBCE, ?notBDE, ?notCDE, ?notZero⟩
  · intro h; exact cubicSigmaCone_B_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_C_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hlamDeg
  · intro h; exact cubicSigmaCone_D_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hlamDeg
  · intro h; exact cubicSigmaCone_E_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hlamDeg
  · intro h; exact cubicSigmaCone_BC_impossible (j := j) (t := t) l alpha
      beta delta epsilon zeta eta theta A B C D E h hlamDeg hkapDeg hmuDeg
      homiDeg hjdiv hder
  · intro h; exact cubicSigmaCone_BD_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_BE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_CE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h homiDeg
  · intro h; exact cubicSigmaCone_DE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_BCD_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h homiDeg
  · intro h; exact cubicSigmaCone_BCE_impossible (j := j) (t := t) l alpha
      beta delta epsilon zeta eta theta A B C D E h hlamDeg hkapDeg hmuDeg
      homiDeg hjdiv hder
  · intro h; exact cubicSigmaCone_BDE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h homiDeg
  · intro h; exact cubicSigmaCone_CDE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicADominant_allLettersZero_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hconeA.1 h.1 h.2.1
      h.2.2.1 h.2.2.2 hjdiv hder

end CubicAssembly610

end Max11DegreeRoutes
