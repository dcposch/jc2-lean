import Fable810ScaleZeroThirteenthDefectPart22Scratch

/-! Part 23 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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

section ScaleZeroThirteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-! ## Degree-`4` source Jacobian row -/

/-- Source-facing degree-`3` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_fourteenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : k)) -
      ((p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp8, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using fableScaleZero_fourteenthCoefficientJacobianRow_raw_810 hp hq hjac


end ScaleZeroThirteenthDefect810
end Max11DegreeRoutes
end
