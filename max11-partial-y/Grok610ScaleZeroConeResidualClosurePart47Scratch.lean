import Grok610ScaleZeroConeResidualClosurePart07Scratch
import Grok610ScaleZeroConeResidualClosurePart36Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section UniqueC0Cone610

variable {k : Type*} [Field k] [CharZero k]

theorem uniqueC0_cubicCoefficient610_natDegree_eq_zero
    (l beta : k) {A B : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0) :
    (uniqueC0_cubicCoefficient610 l beta A B).natDegree = 0 := by
  have hA' : ((419904 / 2239488 * l : k) • A).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ A).trans hA.le
  have hB' : ((414720 / 2239488 : k) • B).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ B).trans hB.le
  have hc : (C (-(36288 / 559872 * beta : k)) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((419904 / 2239488 * l : k) • A +
      (414720 / 2239488 : k) • B +
      C (-(36288 / 559872 * beta : k))).natDegree = 0
  exact natDegree_eq_zero_of_le_zero610 <|
    (natDegree_add_le _ _).trans <| max_le
      ((natDegree_add_le _ _).trans (max_le hA' hB')) hc.le

end UniqueC0Cone610

end Max11DegreeRoutes
