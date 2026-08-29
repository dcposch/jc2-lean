import LowScale68SecondaryLaterDeepFiveRadiusTerminalEndgame

/-! # Parent residual assembly below the eliminated five-radius wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Once the endpoint `2g=5n` is deleted, both remaining children of the
closed lower window enter the same translated residual system.  This is the
common source-facing packet for the wall `2g=3n` and the open interval. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParentResidualEntry68
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
    3 * n ≤ 2 * g ∧ 2 * g < 5 * n ∧
      l = 0 ∧ beta = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < secondaryResidualGap68 n d ee := by
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
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  have split :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerResidualSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧ _ at split
  obtain ⟨hl, hthree, hone, hcases⟩ := split
  rcases hcases with hwall3 | hopen | hwall5
  · have entry :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusResidualEntry68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall3.1)
    change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < secondaryResidualGap68 n d ee at entry
    exact ⟨by omega, by omega, hl, entry.2.1, hthree, hone,
      entry.2.2.1, entry.2.2.2.1, entry.2.2.2.2.1,
      entry.2.2.2.2.2.1, entry.2.2.2.2.2.2⟩
  · exact ⟨by omega, hopen.2.1, hl, hopen.2.2.1, hthree, hone,
      hopen.2.2.2.1, hopen.2.2.2.2.1, hopen.2.2.2.2.2.1,
      hopen.2.2.2.2.2.2.1, hopen.2.2.2.2.2.2.2⟩
  · exact (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEndgame68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall5.1)).elim

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParentResidualEntry68

end LaterDeepLowerParentAssembly68

end Max11DegreeRoutes
