import Sol68LaterDeepLowerOpenDoubleExactFiveAssemblyScratch
import Sol68LaterDeepLowerOpenDoubleSevenWallRowZeroClosureScratch
import Fable68LaterDeepStrictHighBelowSevenBranchesScratch
import Fable68LaterDeepStrictHighAboveSevenEndgameScratch
import LowScale68SecondaryLaterDeepLowerOpenMiddleSelector
import LowScale68SecondaryLaterDeepThreeRadiusDoubleRowZero
import LowScale68SecondaryLaterDeepThreeRadiusMiddleBalancedRowOne
import LowScale68SecondaryLaterDeepThreeRadiusMiddleRight

/-! # Closure assembly for the later-deep lower-open double child

The exact-five assembly first forces strict high.  The strict-high child is
then exhausted by the comparison of `3g` with `7n`: the below-seven and
above-seven Fable closures delete the strict sides, while row zero deletes
the equality wall.  Consequently the immediate later-deep selector retains
only its non-double sibling `h < 2g`; the existing middle packet is returned
unchanged.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleClosureAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_impossible68
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
    (hdouble :
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
      2 * g ≤ h) : False := by
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
  change 2 * g ≤ h at hdouble
  have hstrictHigh :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_forces_strictHigh68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
  change 5 * n < 3 * g at hstrictHigh
  rcases lt_trichotomy (3 * g) (7 * n) with hbelow | hwall | habove
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighBelowSeven_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
          using hdouble)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
          using hstrictHigh)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hbelow)
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_inconsistent68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
          using hdouble)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighAboveSeven_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
          using hdouble)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove)

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_forces_middle68
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
      3 * n < 2 * g ∧ 2 * g < 5 * n) :
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
    h < 2 * g := by
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
  change h < 2 * g
  by_contra hnot
  have hdouble : 2 * g ≤ h := by omega
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hdouble)

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_middleResidual68
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
      3 * n < 2 * g ∧ 2 * g < 5 * n) :
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
    h < 2 * g ∧ l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧
      ((g + h < 5 * n ∧
          Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0) ∨
        (g + h = 5 * n ∧
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                d.coeff (5 * n - h)) +
              3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h) = 0) ∧
          (8 / 3 : k) *
                (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
                  ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
              (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (5 * n < g + h ∧ delta = 0 ∧
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                d.coeff (5 * n - h)) +
              3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h) = 0))) := by
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
  have hmiddle :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_forces_middle68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change h < 2 * g at hmiddle
  have packet :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧ _
    at packet
  exact ⟨hmiddle, packet⟩

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadius_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      2 * g = 3 * n) : False := by
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
  change 2 * g = 3 * n at hwall
  by_cases hmiddle : h < 2 * g
  · have selector :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleRowTwoSelector68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
          using hmiddle)
    change (2 * h = 3 * g ∨ 3 * g < 2 * h) ∧ _ at selector
    rcases selector.1 with hbalanced | hright
    · exact
        maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleBalanced_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
            using hbalanced)
    · exact
        maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleRight_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
            using And.intro hmiddle hright)
  · have hdouble : 2 * g ≤ h := by omega
    exact
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusDouble_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
          using hdouble)

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParent_forces_openMiddle68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
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
    3 * n < 2 * g ∧ 2 * g < 5 * n ∧ h < 2 * g := by
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
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  have parent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParentAfterThreeRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change 3 * n ≤ 2 * g ∧ 2 * g < 5 * n ∧ _ at parent
  have hlower : 3 * n < 2 * g := by
    apply lt_of_le_of_ne parent.1
    intro heq
    exact
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadius_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using heq.symm)
  have hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n :=
    ⟨hlower, parent.2.1⟩
  have hmiddle :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_forces_middle68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  exact ⟨hopen.1, hopen.2, by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle⟩

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_forces_middle68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_middleResidual68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadius_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParent_forces_openMiddle68

end LaterDeepLowerOpenDoubleClosureAssembly68

end Max11DegreeRoutes
