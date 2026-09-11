import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

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
