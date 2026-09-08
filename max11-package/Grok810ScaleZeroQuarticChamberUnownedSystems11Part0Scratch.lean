import Mathlib

/-! # Unowned multi-carrier systems, part 11/15

3 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems11810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CDEFG` / `CG·DD·CCC` leaf 3: the 10 face rows force `d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDEFG28L3810_cert
    (a b c d e f g : k)
    (hr0 : (5 / 16 : k) * c * f + (5 / 16 : k) * d * e = 0)
    (hr1 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr2 : (-5 / 128 : k) * a * c * f + (-5 / 128 : k) * a * d * e + (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr3 : (-5 / 64 : k) * a * d * f + (-15 / 128 : k) * c ^ 2 * e + (-15 / 128 : k) * c * d ^ 2 + (5 / 16 : k) * e * g = 0)
    (hr4 : (-5 / 2048 : k) * a ^ 2 * c * f + (-5 / 2048 : k) * a ^ 2 * d * e + (15 / 1024 : k) * a * c ^ 2 * d + (-5 / 128 : k) * a * d * g = 0)
    (hr5 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr6 : (-5 / 2048 : k) * a ^ 3 * c * f + (-5 / 2048 : k) * a ^ 3 * d * e + (15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (-5 / 256 : k) * a ^ 2 * d * g = 0)
    (hr7 : (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr8 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr9 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hDc : (d : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : d * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * c * d) * hr1 + ((18 / 55 : k) * d) * hr5 + ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * hr7
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems11810

end Max11DegreeRoutes
