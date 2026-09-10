import Fable810ScaleZeroFourteenthDefectPart26Scratch

/-! Part 27 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroFourteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-- At scale zero the common core is constant, so the leading octic
coefficient of the degree-`2` row is a differential constant. -/
theorem scaleZero_fifteenthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : k)) -
      ((p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  have hrow :=
    fableScaleZero_fifteenthCoefficientJacobianRow_raw_810 hp hq hjac
  simpa using hrow


end ScaleZeroFourteenthDefect810
end Max11DegreeRoutes
end
