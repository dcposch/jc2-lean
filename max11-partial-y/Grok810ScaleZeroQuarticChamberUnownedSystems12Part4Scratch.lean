import Mathlib

/-! # Unowned multi-carrier systems, part 12/15

4 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
Singular-lifted top-coefficient system.  Every load column of every row
carries an exact rational Farkas verdict (`dominated`, `dominated-hnc` or
a named band).
Untracked working note.
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

section QuarticChamberUnownedSystems12810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` leaf 6: the 7 face rows force `f ^ 2 * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCDEFG7L6810_cert
    (a b c d e f g : k)
    (hr0 : (5 / 512 : k) * a * b ^ 3 + (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * b * g + (5 / 16 : k) * c * f = 0)
    (hr1 : (15 / 512 : k) * a * b ^ 2 * c + (-5 / 64 : k) * a * b * f + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr2 : (-5 / 4096 : k) * a ^ 2 * b ^ 3 + (15 / 1024 : k) * a * b * c ^ 2 + (-5 / 128 : k) * a * b * g + (-5 / 128 : k) * a * c * f = 0)
    (hr3 : (-15 / 2048 : k) * a * b ^ 4 + (45 / 512 : k) * b ^ 2 * c ^ 2 + (-5 / 64 : k) * b ^ 2 * g + (-25 / 128 : k) * b * c * f + (5 / 32 : k) * f ^ 2 = 0)
    (hr4 : (-5 / 65536 : k) * a ^ 3 * b ^ 3 + (15 / 16384 : k) * a ^ 2 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 2 * b * g + (-5 / 2048 : k) * a ^ 2 * c * f = 0)
    (hr5 : (15 / 4096 : k) * a ^ 2 * b ^ 4 + (-45 / 512 : k) * a * b ^ 2 * c ^ 2 + (5 / 64 : k) * a * b ^ 2 * g + (5 / 32 : k) * a * b * c * f + (-5 / 16 : k) * a * f ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr6 : (-5 / 65536 : k) * a ^ 4 * b ^ 3 + (15 / 16384 : k) * a ^ 3 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 3 * b * g + (-5 / 2048 : k) * a ^ 3 * c * f = 0)
    (hFc : (f : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : f ^ 2 * g ^ 2 = 0 := by
    linear_combination ((99 / 1120 : k) * a * b ^ 3 * c ^ 2 + (1011 / 14000 : k) * a * b ^ 3 * g + (-594 / 875 : k) * a * b ^ 2 * c * f + (3267 / 7000 : k) * a * b * f ^ 2 + (2761 / 3500 : k) * b * c ^ 2 * g + (1872 / 875 : k) * b * g ^ 2 + (-33 / 70 : k) * c * f * g) * hr0 + ((33 / 280 : k) * b ^ 2 * c ^ 3 + (-2411 / 1750 : k) * b ^ 2 * c * g + (-792 / 875 : k) * b * c ^ 2 * f + (187 / 70 : k) * b * f * g + (1089 / 1750 : k) * c * f ^ 2) * hr1 + ((11 / 70 : k) * a * b ^ 2 * c ^ 2 + (-131 / 1750 : k) * a * b ^ 2 * g + (-1056 / 875 : k) * a * b * c * f + (726 / 875 : k) * a * f ^ 2 + (66 / 125 : k) * c ^ 2 * g + (2696 / 875 : k) * g ^ 2) * hr3 + ((11 / 140 : k) * b ^ 2 * c ^ 2 + (-599 / 1750 : k) * b ^ 2 * g + (-528 / 875 : k) * b * c * f + (363 / 875 : k) * f ^ 2) * hr5
  exact (mul_ne_zero (pow_ne_zero 2 hFc) (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems12810

end Max11DegreeRoutes
