import Grok610ScaleZeroCubicLoadWallsPart201Scratch
import Grok610ScaleZeroCubicLoadWallsPart202Scratch

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
set_option maxRecDepth 100000000

section CubicLoadWallsClosure610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
theorem normalized610ScaleZero_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) : False := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand,
      hdBand, hzBand, htBand, hexh⟩ :=
    normalized610ScaleZero_cubicResidual8 hsource
  rcases hexh with hCD | ⟨hBCDE, hwall⟩
  · exact cubicLoadSigmaCone_CD_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hCD hl0 hbBand hdBand hzBand
      htBand hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_wall_impossible (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hBCDE hl0 hwall
      hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder

end CubicLoadWallsClosure610

end Max11DegreeRoutes
