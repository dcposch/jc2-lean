import Grok810ScaleZeroQuarticTowerSpeedTPart101Scratch
import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # BCDEFG12 chamber, part 1

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, load-free chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestFree1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (23 / 8192 : k) • (A * B ^ 5)
  + (-(5 / 512 : k)) • (A * B ^ 3 * E)
  + (-(125 / 2048 : k)) • (B ^ 4 * D)
  + (-(265 / 2048 : k)) • (B ^ 3 * C ^ 2)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, load-free chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestFree2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (-(5 / 16 : k)) • (B * E * G)
  + (-(5 / 16 : k)) • (B * F ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, load-free chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestFree3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (C * D * G)
  + (-(5 / 8 : k)) • (C * E * F)
  + (-(5 / 16 : k)) • (D ^ 2 * F)
  + (-(5 / 16 : k)) • (D * E ^ 2)
  + (-(15 / 512 : k)) • (A * B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestL1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (693 / 1048576 * l : k) • (A ^ 6 * C)
  + (-(315 / 2097152 * l : k)) • (A ^ 5 * B ^ 2)
  + (315 / 131072 * l : k) • (A ^ 5 * E)
  + (-(315 / 262144 * l : k)) • (A ^ 4 * B * D)
  + (2205 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  + (315 / 32768 * l : k) • (A ^ 4 * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestL2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(81 / 131072 * l : k)) • (A ^ 3 * B ^ 2 * C)
  + (-(45 / 8192 * l : k)) • (A ^ 3 * B * F)
  + (225 / 8192 * l : k) • (A ^ 3 * C * E)
  + (-(45 / 16384 * l : k)) • (A ^ 3 * D ^ 2)
  + (-(45 / 524288 * l : k)) • (A ^ 2 * B ^ 4)
  + (-(45 / 16384 * l : k)) • (A ^ 2 * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestL3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 4096 * l : k)) • (A ^ 2 * B * C * D)
  + (9 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  + (27 / 256 * l : k) • (A ^ 2 * C * G)
  + (-(27 / 1024 * l : k)) • (A ^ 2 * D * F)
  + (81 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  + (-(27 / 4096 * l : k)) • (A * B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 4; at most six monomials. -/
def bandAuxBCDEFG12RestL4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 2048 * l : k)) • (A * B ^ 2 * C ^ 2)
  + (-(9 / 512 * l : k)) • (A * B ^ 2 * G)
  + (9 / 32 * l : k) • (A * E * G)
  + (-(9 / 128 * l : k)) • (A * F ^ 2)
  + (-(567 / 16384 * l : k)) • (B ^ 4 * C)
  + (27 / 512 * l : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 5; at most six monomials. -/
def bandAuxBCDEFG12RestL5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (-(9 / 64 * l : k)) • (B * D * G)
  + (-(9 / 32 * l : k)) • (B * E * F)
  + (63 / 4096 * l : k) • (C ^ 4)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 6; at most six monomials. -/
def bandAuxBCDEFG12RestL6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 128 * l : k)) • (C ^ 2 * G)
  + (-(9 / 32 * l : k)) • (C * D * F)
  + (-(9 / 64 * l : k)) • (C * E ^ 2)
  + (-(9 / 64 * l : k)) • (D ^ 2 * E)
  + (9 / 16 * l : k) • (G ^ 2)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestBeta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 131072 * beta : k) • (A ^ 5 * C)
  + (-(35 / 65536 * beta : k)) • (A ^ 4 * B ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 4 * E)
  + (-(35 / 8192 * beta : k)) • (A ^ 3 * B * D)
  + (175 / 16384 * beta : k) • (A ^ 3 * C ^ 2)
  + (-(7 / 16384 * beta : k)) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestBeta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (A ^ 2 * C * E)
  + (-(21 / 2048 * beta : k)) • (A ^ 2 * D ^ 2)
  + (49 / 32768 * beta : k) • (A * B ^ 4)
  + (-(7 / 1024 * beta : k)) • (A * B ^ 2 * E)
  + (7 / 128 * beta : k) • (A * E ^ 2)
  + (-(7 / 128 * beta : k)) • (B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestBeta3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(91 / 1024 * beta : k)) • (B ^ 2 * C ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  + (-(7 / 16 * beta : k)) • (F ^ 2)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 4; at most six monomials. -/
def bandAuxBCDEFG12RestBeta4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 64 * beta : k)) • (A * D * F)
  + (-(21 / 1024 * beta : k)) • (A ^ 2 * B * F)
  + (35 / 1024 * beta : k) • (A ^ 3 * G)
  + (7 / 32 * beta : k) • (A * C * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, gamma chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestGamma1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 256 * gamma : k)) • (B ^ 3 * C)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  + (-(3 / 4 * gamma : k)) • (E * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, delta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestDelta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 4096 * delta : k) • (A ^ 4 * C)
  + (-(15 / 8192 * delta : k)) • (A ^ 3 * B ^ 2)
  + (15 / 512 * delta : k) • (A ^ 3 * E)
  + (-(15 / 1024 * delta : k)) • (A ^ 2 * B * D)
  + (45 / 2048 * delta : k) • (A ^ 2 * C ^ 2)
  + (-(5 / 1024 * delta : k)) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, delta chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestDelta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (A * C * E)
  + (-(5 / 128 * delta : k)) • (A * D ^ 2)
  + (-(135 / 4096 * delta : k)) • (B ^ 4)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • (C ^ 3)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, delta chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestDelta3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 8 * delta : k)) • (D * F)
  + (-(5 / 16 * delta : k)) • (E ^ 2)
  + (-(5 / 64 * delta : k)) • (A * B * F)
  + (15 / 128 * delta : k) • (A ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, epsilon chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestEpsilon1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  + (-(1 / 2 * epsilon : k)) • (C * F)
  + (-(1 / 2 * epsilon : k)) • (D * E)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, zeta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestZeta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 * zeta : k) • (A ^ 3 * C)
  + (-(3 / 512 * zeta : k)) • (A ^ 2 * B ^ 2)
  + (3 / 32 * zeta : k) • (A ^ 2 * E)
  + (-(3 / 64 * zeta : k)) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  + (-(3 / 8 * zeta : k)) • (B * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, zeta chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestZeta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 8 * zeta : k)) • (C * E)
  + (-(3 / 16 * zeta : k)) • (D ^ 2)
  + (3 / 128 * zeta : k) • (A * C ^ 2)
  + (3 / 8 * zeta : k) • (A * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, eta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestEta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * eta : k) • (B ^ 3)
  + (-(1 / 4 * eta : k)) • (B * E)
  + (-(1 / 4 * eta : k)) • (C * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, theta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestTheta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * theta : k) • (A ^ 2 * C)
  + (-(1 / 64 * theta : k)) • (A * B ^ 2)
  + (1 / 4 * theta : k) • (A * E)
  + (-(1 / 8 * theta : k)) • (B * D)
  + (-(1 / 16 * theta : k)) • (C ^ 2)
  + (1 / 1 * theta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- The tower auxiliary whose cost-four-s load-free face cancels. -/
def degreeZeroBandAuxBCDEFG12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (1 / 4 : k) • (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G))

set_option maxHeartbeats 64000000 in
/-- The auxiliary with its five pure-A load monomials removed. -/
def bandAuxBCDEFG12Rest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 6

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12KappaFace810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3) +
    (-15 / 128 : k) • (B * C ^ 2) +
    (5 / 16 : k) • (B * G) +
    (5 / 16 : k) • (C * F) +
    (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12KappaRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * l : k) • (A ^ 5) +
    (45 / 8192 * l : k) • (A ^ 3 * C) +
    (-9 / 16384 * l : k) • (A ^ 2 * B ^ 2) +
    (27 / 1024 * l : k) • (A ^ 2 * E) +
    (-9 / 512 * l : k) • (A * B * D) +
    (9 / 1024 * l : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12KappaRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * l : k) • (A * G) +
    (-63 / 1024 * l : k) • (B ^ 2 * C) +
    (9 / 64 * l : k) • (B * F) +
    (9 / 64 * l : k) • (C * E) +
    (9 / 128 * l : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12KappaRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * beta : k) • (A ^ 4) +
    (21 / 1024 * beta : k) • (A ^ 2 * C) +
    (7 / 1024 * beta : k) • (A * B ^ 2) +
    (7 / 64 * beta : k) • (A * E) +
    (-7 / 64 * beta : k) • (B * D) +
    (-7 / 128 * beta : k) • (C ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 8 * beta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12KappaRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 16 * gamma : k) • (B * C) +
    (3 / 4 * gamma : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12KappaRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * delta : k) • (A ^ 3) +
    (5 / 64 * delta : k) • (A * C) +
    (-15 / 128 * delta : k) • (B ^ 2) +
    (5 / 8 * delta : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 2 * epsilon : k) • (D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12KappaRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * zeta : k) • (A ^ 2) +
    (3 / 8 * zeta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (B)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (A)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12KappaRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12KappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 9

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12MuFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C) +
    (-5 / 64 : k) • (A * B * F) +
    (-5 / 128 : k) • (A * D ^ 2) +
    (-5 / 128 : k) • (C ^ 3) +
    (5 / 16 : k) • (C * G) +
    (5 / 32 : k) • (E ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12MuRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • (B ^ 4) +
    (-15 / 128 : k) • (B ^ 2 * E) +
    (-15 / 64 : k) • (B * C * D) +
    (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12MuRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-45 / 262144 * l : k) • (A ^ 4 * B) +
    (-9 / 8192 * l : k) • (A ^ 3 * D) +
    (-9 / 8192 * l : k) • (A ^ 2 * B * C) +
    (-9 / 1024 * l : k) • (A ^ 2 * F) +
    (63 / 8192 * l : k) • (A * B ^ 3) +
    (-9 / 512 * l : k) • (A * B * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12MuRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-9 / 512 * l : k) • (A * C * D) +
    (-63 / 1024 * l : k) • (B ^ 2 * D) +
    (-63 / 1024 * l : k) • (B * C ^ 2) +
    (9 / 64 * l : k) • (B * G) +
    (9 / 64 * l : k) • (C * F) +
    (9 / 64 * l : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12MuRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 8192 * beta : k) • (A ^ 3 * B) +
    (-7 / 1024 * beta : k) • (A ^ 2 * D) +
    (7 / 512 * beta : k) • (A * B * C) +
    (-7 / 64 * beta : k) • (A * F) +
    (21 / 1024 * beta : k) • (B ^ 3) +
    (-7 / 64 * beta : k) • (B * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12MuRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 64 * beta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12MuRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * gamma : k) • (A * B ^ 2) +
    (-3 / 16 * gamma : k) • (B * D) +
    (-3 / 32 * gamma : k) • (C ^ 2) +
    (3 / 4 * gamma : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12MuRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 1024 * delta : k) • (A ^ 2 * B) +
    (-5 / 64 * delta : k) • (A * D) +
    (-15 / 64 * delta : k) • (B * C) +
    (5 / 8 * delta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12MuRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 8 * epsilon : k) • (B ^ 2) +
    (1 / 2 * epsilon : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12MuRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 64 * zeta : k) • (A * B) +
    (3 / 8 * zeta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12MuRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12MuRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (B)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12MuRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12MuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 12

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12XiFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E) +
    (15 / 256 : k) • (A * B * C * D) +
    (-5 / 64 : k) • (A * D * F) +
    (-15 / 128 : k) • (C ^ 2 * E) +
    (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 2048 : k) • (A * B ^ 4) +
    (55 / 1024 : k) • (B ^ 3 * D) +
    (45 / 512 : k) • (B ^ 2 * C ^ 2) +
    (-5 / 64 : k) • (B ^ 2 * G) +
    (-25 / 128 : k) • (B * C * F) +
    (-25 / 128 : k) • (B * D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12XiRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (C * D ^ 2) +
    (5 / 32 : k) • (F ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-45 / 262144 * l : k) • (A ^ 4 * D) +
    (9 / 16384 * l : k) • (A ^ 3 * B * C) +
    (-9 / 8192 * l : k) • (A ^ 3 * F) +
    (-9 / 16384 * l : k) • (A ^ 2 * B ^ 3) +
    (9 / 4096 * l : k) • (A ^ 2 * B * E) +
    (-9 / 8192 * l : k) • (A ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (171 / 8192 * l : k) • (A * B ^ 2 * D) +
    (9 / 1024 * l : k) • (A * B * C ^ 2) +
    (-9 / 512 * l : k) • (A * C * F) +
    (-9 / 512 * l : k) • (A * D * E) +
    (63 / 2048 * l : k) • (B ^ 3 * C) +
    (-45 / 1024 * l : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12XiRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-27 / 256 * l : k) • (B * C * E) +
    (-27 / 512 * l : k) • (B * D ^ 2) +
    (-63 / 1024 * l : k) • (C ^ 2 * D) +
    (9 / 64 * l : k) • (D * G) +
    (9 / 64 * l : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 8192 * beta : k) • (A ^ 3 * D) +
    (7 / 2048 * beta : k) • (A ^ 2 * B * C) +
    (-7 / 1024 * beta : k) • (A ^ 2 * F) +
    (-7 / 1024 * beta : k) • (A * B ^ 3) +
    (7 / 256 * beta : k) • (A * B * E) +
    (7 / 512 * beta : k) • (A * C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12XiRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (49 / 1024 * beta : k) • (B ^ 2 * D) +
    (7 / 128 * beta : k) • (B * C ^ 2) +
    (-7 / 64 * beta : k) • (C * F) +
    (-7 / 64 * beta : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12XiRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * gamma : k) • (A * B * D) +
    (3 / 32 * gamma : k) • (B ^ 2 * C) +
    (-3 / 32 * gamma : k) • (B * F) +
    (-3 / 16 * gamma : k) • (C * E) +
    (-3 / 32 * gamma : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 1024 * delta : k) • (A ^ 2 * D) +
    (5 / 128 * delta : k) • (A * B * C) +
    (-5 / 64 * delta : k) • (A * F) +
    (5 / 128 * delta : k) • (B ^ 3) +
    (-5 / 32 * delta : k) • (B * E) +
    (-15 / 64 * delta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12XiRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • (A * B ^ 2) +
    (-3 / 16 * epsilon : k) • (B * D) +
    (-1 / 8 * epsilon : k) • (C ^ 2) +
    (1 / 2 * epsilon : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def bcdefg12XiRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 64 * zeta : k) • (A * D) +
    (-3 / 16 * zeta : k) • (B * C) +
    (3 / 8 * zeta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12XiRest11810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 16 * eta : k) • (B ^ 2) +
    (1 / 4 * eta : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12XiRest12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12XiRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12XiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 15

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12PiFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4) +
    (-45 / 512 : k) • (A * B ^ 2 * C ^ 2) +
    (5 / 64 : k) • (A * B ^ 2 * G) +
    (5 / 32 : k) • (A * B * C * F) +
    (5 / 16 : k) • (A * B * D * E) +
    (5 / 32 : k) • (A * C * D ^ 2) +
    (-5 / 16 : k) • (A * F ^ 2) +
    (15 / 256 : k) • (C ^ 4) +
    (-5 / 16 : k) • (C ^ 2 * G) +
    (-5 / 8 : k) • (C * E ^ 2) +
    (5 / 4 : k) • (G ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (A * B ^ 3 * D) +
    (-35 / 256 : k) • (B ^ 4 * C) +
    (25 / 128 : k) • (B ^ 3 * F) +
    (45 / 64 : k) • (B ^ 2 * C * E) +
    (45 / 128 : k) • (B ^ 2 * D ^ 2) +
    (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12PiRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 8 : k) • (B * D * G) +
    (-15 / 16 : k) • (B * E * F) +
    (-15 / 16 : k) • (C * D * F) +
    (-5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 131072 * l : k) • (A ^ 4 * B * C) +
    (-45 / 32768 * l : k) • (A ^ 4 * F) +
    (-3 / 32768 * l : k) • (A ^ 3 * B ^ 3) +
    (9 / 4096 * l : k) • (A ^ 3 * B * E) +
    (9 / 4096 * l : k) • (A ^ 3 * C * D) +
    (-27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2) +
    (-27 / 1024 * l : k) • (A ^ 2 * C * F) +
    (9 / 512 * l : k) • (A ^ 2 * D * E) +
    (-189 / 4096 * l : k) • (A * B ^ 3 * C) +
    (63 / 1024 * l : k) • (A * B ^ 2 * F) +
    (9 / 128 * l : k) • (A * B * C * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 256 * l : k) • (A * B * D ^ 2) +
    (9 / 256 * l : k) • (A * C ^ 2 * D) +
    (-9 / 64 * l : k) • (A * E * F) +
    (-63 / 4096 * l : k) • (B ^ 5) +
    (63 / 512 * l : k) • (B ^ 3 * E) +
    (189 / 512 * l : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 512 * l : k) • (B * C ^ 3) +
    (-9 / 32 * l : k) • (B * C * G) +
    (-27 / 64 * l : k) • (B * D * F) +
    (-9 / 32 * l : k) • (B * E ^ 2) +
    (-27 / 128 * l : k) • (C ^ 2 * F) +
    (-9 / 16 * l : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12PiRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 32 * l : k) • (D ^ 3) +
    (9 / 8 * l : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 4096 * beta : k) • (A ^ 3 * B * C) +
    (-7 / 1024 * beta : k) • (A ^ 3 * F) +
    (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3) +
    (7 / 512 * beta : k) • (A ^ 2 * B * E) +
    (7 / 512 * beta : k) • (A ^ 2 * C * D) +
    (-21 / 256 * beta : k) • (A * B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 256 * beta : k) • (A * B * C ^ 2) +
    (-7 / 64 * beta : k) • (A * C * F) +
    (7 / 32 * beta : k) • (A * D * E) +
    (-63 / 512 * beta : k) • (B ^ 3 * C) +
    (21 / 128 * beta : k) • (B ^ 2 * F) +
    (7 / 16 * beta : k) • (B * C * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def bcdefg12PiRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * beta : k) • (B * D ^ 2) +
    (7 / 32 * beta : k) • (C ^ 2 * D) +
    (-7 / 8 * beta : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 32 * gamma : k) • (A * B ^ 2 * C) +
    (3 / 16 * gamma : k) • (A * D ^ 2) +
    (-15 / 256 * gamma : k) • (B ^ 4) +
    (3 / 8 * gamma : k) • (B ^ 2 * E) +
    (3 / 4 * gamma : k) • (B * C * D) +
    (1 / 8 * gamma : k) • (C ^ 3)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12PiRest11810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 4 * gamma : k) • (D * F) +
    (-3 / 4 * gamma : k) • (E ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 * delta : k) • (A ^ 2 * B * C) +
    (-5 / 128 * delta : k) • (A ^ 2 * F) +
    (-15 / 256 * delta : k) • (A * B ^ 3) +
    (5 / 32 * delta : k) • (A * B * E) +
    (5 / 32 * delta : k) • (A * C * D) +
    (15 / 32 * delta : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def bcdefg12PiRest13810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 32 * delta : k) • (B * C ^ 2) +
    (-5 / 8 * delta : k) • (C * F) +
    (-5 / 4 * delta : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12PiRest14810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * epsilon : k) • (A * B * D) +
    (1 / 2 * epsilon : k) • (B ^ 2 * C) +
    (-1 / 2 * epsilon : k) • (B * F) +
    (-1 * epsilon : k) • (C * E) +
    (-1 / 2 * epsilon : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12PiRest15810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * zeta : k) • (A * B * C) +
    (-3 / 8 * zeta : k) • (A * F) +
    (5 / 32 * zeta : k) • (B ^ 3) +
    (-3 / 4 * zeta : k) • (B * E) +
    (-3 / 4 * zeta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12PiRest16810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 16 * eta : k) • (A * B ^ 2) +
    (-1 / 2 * eta : k) • (B * D) +
    (-1 / 4 * eta : k) • (C ^ 2) +
    (2 * eta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12PiRest17810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 4 * theta : k) • (B * C) +
    (1 * theta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12PiRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12PiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 18

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The polynomial face of N2 on BCDEFG12. -/
def bcdefg12N2Face
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (-15 / 64 : k) • (B * C * E)
  + (-15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestLF0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  + (-15 / 128 : k) • (B ^ 2 * F)
  + (-15 / 128 : k) • (B * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestLF0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestLF0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestL0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • (A ^ 6)
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  + (-9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 8192 * l : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestL0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N2RestL0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestL0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestL1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 32768 * l : k) • (B ^ 4)
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  + (-9 / 512 * l : k) • (A * B * F)
  + (-9 / 1024 * l : k) • (A * D ^ 2)
  + (-63 / 1024 * l : k) • (B ^ 2 * E)
  + (-63 / 512 * l : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestL1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N2RestL1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestL1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestL2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-21 / 1024 * l : k) • (C ^ 3)
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • (E ^ 2)
  + (-9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (9 / 512 * l : k) • (A * C * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestL2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N2RestL2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestL2]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestBeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • (A ^ 5)
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestBeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N2RestBeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestBeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestBeta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 64 * beta : k) • (B * F)
  + (-7 / 64 * beta : k) • (C * E)
  + (-7 / 128 * beta : k) • (D ^ 2)
  + (-7 / 1024 * beta : k) • (A * C ^ 2)
  + (7 / 64 * beta : k) • (A * G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestBeta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N2RestBeta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestBeta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestGamma0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 128 * gamma : k) • (B ^ 3)
  + (-3 / 16 * gamma : k) • (B * E)
  + (-3 / 16 * gamma : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestGamma0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestGamma0]
  compute_degree
  omega

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 19

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestDelta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • (A ^ 4)
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (-15 / 64 * delta : k) • (B * D)
  + (-15 / 128 * delta : k) • (C ^ 2)
  + (5 / 8 * delta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestDelta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N2RestDelta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestDelta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestDelta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestDelta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N2RestDelta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestDelta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestEpsilon0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • (F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestEpsilon0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestEpsilon0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestZeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * zeta : k) • (A ^ 3)
  + (-15 / 128 * zeta : k) • (B ^ 2)
  + (3 / 8 * zeta : k) • (E)
  + (3 / 64 * zeta : k) • (A * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestZeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst zeta
    simp only [bcdefg12N2RestZeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestZeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestEta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestEta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestEta0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestTheta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * theta : k) • (A ^ 2)
  + (1 / 8 * theta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestTheta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst theta
    simp only [bcdefg12N2RestTheta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestTheta0]
    compute_degree
    omega

end Max11DegreeRoutes
