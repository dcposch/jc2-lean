import Mathlib

/-! # Unowned multi-carrier systems, part 14/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems14810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDEFG` / `CG·DD·CCC` leaf 10: the 5 face rows force `d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCDEFG102L10810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr2 : (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr3 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr4 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hDc : (d : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : d * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * c * d) * hr0 + ((18 / 55 : k) * d) * hr1 + ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * hr2
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems14810

end Max11DegreeRoutes
