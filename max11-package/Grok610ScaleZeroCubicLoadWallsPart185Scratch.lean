import Grok610ScaleZeroCubicLoadMultiScratch
import Max11SpeedReflectDegLibScratch

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

theorem degreeZeroLambdaCubicNoSigmaCD610_eq_chamberRest
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaCD610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      lambdaChamberRestCD610 alpha epsilon eta A C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  simp only [degreeZeroLambdaCubicNoSigmaCD610, lambdaChamberRestCD610,
    hpow2, hpow3, hpow4, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, neg_zero]
  all_goals module

end CubicLoadCDChamber610

end Max11DegreeRoutes
