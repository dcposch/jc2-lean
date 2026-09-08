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
/-- The Singular-lifted certificate of chamber `CDEFG` / `CG·EE·CCC` leaf 2: the 3 face rows force `e * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDEFG34L2810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g + (5 / 32 : k) * e ^ 2 = 0)
    (hr1 : (-15 / 128 : k) * c ^ 2 * e + (5 / 16 : k) * e * g = 0)
    (hr2 : (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (-5 / 8 : k) * c * e ^ 2 + (5 / 4 : k) * g ^ 2 = 0)
    (hEc : (e : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : e * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * c * e) * hr0 + ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * hr1 + ((18 / 55 : k) * e) * hr2
  exact (mul_ne_zero hEc (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems12810

end Max11DegreeRoutes
