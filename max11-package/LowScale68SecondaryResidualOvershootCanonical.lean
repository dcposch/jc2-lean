import LowScale68SecondaryLargeGapResidual
import LowScale68SecondaryResidualLoadZeroEndgame

/-! # Canonical expanded wrapper for residual overshoot `n < g+h`

On a canonical expanded source `IntegratedPolynomialLowerSystem68`, the
open residual overshoot chamber `2g < n < 3g` and `n < g+h` exposes the
Jacobian load of I4 at degree `8n`.  The already-checked extraction
`maximalExpandedIntegratedPolynomialLowerSystem_residualOvershoot_loadL_eq_zero68`
forces `l = 0`.  The residual load-zero endgame then excludes the whole
strip `2g < n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 4000000 in
/-- The residual overshoot chamber `2g < n < 3g` and `n < g+h` is empty
on a canonical expanded source: I4 forces `l = 0`, and the tracked
`l = 0` endgame then excludes `2g < n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualOvershoot_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n ∧ n < 3 * g)
    (hover :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      n < g + h) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  have hl0 :=
    maximalExpandedIntegratedPolynomialLowerSystem_residualOvershoot_loadL_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hchamber hover
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl0 (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualOvershoot_impossible68

end Max11DegreeRoutes
