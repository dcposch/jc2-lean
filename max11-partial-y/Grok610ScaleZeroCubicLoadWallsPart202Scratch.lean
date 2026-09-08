import Grok610ScaleZeroCubicLoadWallsPart181Scratch
import Grok610ScaleZeroCubicLoadWallsPart182Scratch
import Grok610ScaleZeroCubicLoadWallsPart183Scratch
import Grok610ScaleZeroCubicLoadWallsPart184Scratch

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

section CubicLoadWallsAssembly610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCDE_wall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree ∨
      9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree ∨
      7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  rcases hwall with hbeq | hdeq | hzeq | hteq
  · exact cubicLoadSigmaCone_BCDE_betaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hbeq
      hlam hkap hmu homi hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_deltaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hdeq
      hlam hkap hmu homi hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_zetaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hzeq
      hlam hkap hmu homi hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_thetaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hteq
      hlam hkap hmu homi hjdiv hder

end CubicLoadWallsAssembly610

end Max11DegreeRoutes
