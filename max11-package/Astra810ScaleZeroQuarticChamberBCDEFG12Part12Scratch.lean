import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

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
