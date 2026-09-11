import Grok810ScaleZeroQuarticTowerSpeedTPart01Scratch

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
