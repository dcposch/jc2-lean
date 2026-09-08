import Sol68LaterDeepLowerOpenDoubleClosureAssemblyScratch
import LowScale68SecondaryLaterDeepLowerOpenMiddleFiveSumRowTwo
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighZeta
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighBalancedSixToSeven

/-! # Exact five-sum reduction on the surviving non-double child

On the wall `g+h=5n`, the already assembled double closure forces the middle
child `h<2g`.  The five-sum row-two theorem then supplies `delta=0`, all four
nonzero residual edges, and the ordinary discriminant.  Arithmetic forces
both high inequalities, so the high zeta selector applies.  Its balanced
branch is impossible and its `2h=7n` branch contradicts the strict-open
window.  The exact residual is therefore the right seven wall `3g=7n`
(with `3h=8n`) or `zeta=0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleFiveSumReduction68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_reduced68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall :
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
      g + h = 5 * n) :
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
    h < 2 * g ∧ delta = 0 ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧
      ((3 * g = 7 * n ∧ 3 * h = 8 * n) ∨ zeta = 0) := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change g + h = 5 * n at hwall
  have hmiddle :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_forces_middle68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change h < 2 * g at hmiddle
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSumOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hwall)
  change delta = 0 ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 at ordinary
  have hhigh : 5 * n < 2 * h ∧ 5 * n < 3 * g := by omega
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighStrict_zetaSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hhigh)
  change (2 * h = 3 * g ∧ 2 * h < 7 * n) ∨
      2 * h = 7 * n ∨ 3 * g = 7 * n ∨ zeta = 0 at selector
  have residual : (3 * g = 7 * n ∧ 3 * h = 8 * n) ∨ zeta = 0 := by
    rcases selector with hbalanced | hsevenH | hsevenG | hzeta
    · have hbelowSeven : 3 * g < 7 * n := by
        rw [← hbalanced.1]
        exact hbalanced.2
      exact False.elim
        (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighBalancedBelowSeven_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
            using hmiddle)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
            using hhigh)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
            using And.intro hbalanced.1 hbelowSeven))
    · exfalso
      omega
    · left
      exact ⟨hsevenG, by omega⟩
    · exact Or.inr hzeta
  exact ⟨hmiddle, ordinary.1, ordinary.2.1, ordinary.2.2.1,
    ordinary.2.2.2.1, ordinary.2.2.2.2.1, ordinary.2.2.2.2.2,
    residual⟩

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_reduced68

end LaterDeepLowerOpenMiddleFiveSumReduction68

end Max11DegreeRoutes
