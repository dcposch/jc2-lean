import Astra810ScaleZeroQuarticChamberBCDEFG12Part08Scratch

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
