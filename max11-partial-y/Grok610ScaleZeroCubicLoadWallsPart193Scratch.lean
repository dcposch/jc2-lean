import Grok610ScaleZeroCubicLoadWallsPart188Scratch

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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronChamberCD610_of_alpha_eq_zero
    (epsilon eta : k) (A C D E : k[X]) :
    omicronChamberCD610 0 epsilon eta A C D E =
      (-(5 / 27 : k)) • (C ^ 2 * E) +
        (-(5 / 27 : k)) • (C * D ^ 2) +
        (-(1 / 9 * epsilon : k)) • C ^ 2 +
        (1 / 3 * eta : k) • E := by
  unfold omicronChamberCD610
  have hAD2 : (-(2 / 27 * (0 : k) : k)) • (A * D ^ 2) = 0 := by
    have hz : (2 / 27 * (0 : k) : k) = 0 := by ring
    rw [hz, neg_zero, zero_smul]
  have hC3 : (-(4 / 81 * (0 : k) : k)) • C ^ 3 = 0 := by
    have hz : (4 / 81 * (0 : k) : k) = 0 := by ring
    rw [hz, neg_zero, zero_smul]
  have hE2 : ((2 / 9 * (0 : k) : k)) • E ^ 2 = 0 := by
    have hz : (2 / 9 * (0 : k) : k) = 0 := by ring
    rw [hz, zero_smul]
  rw [hAD2, hC3, hE2]
  abel

end CubicLoadCDChamber610

end Max11DegreeRoutes
