import Grok610ScaleZeroCubicLoadWallsPart186Scratch

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

theorem degreeZeroKappaCubic610_eq_chamber
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      kappaChamberCD610 alpha epsilon C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  simp only [degreeZeroKappaCubic610, kappaChamberCD610, hpow2, hpow3,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    neg_zero]
  all_goals module

end CubicLoadCDChamber610

end Max11DegreeRoutes
