import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

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
