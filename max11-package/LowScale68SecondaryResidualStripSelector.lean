import LowScale68SecondaryResidualLeftLoadWindow
import LowScale68SecondaryResidualHalfRadiusI4Wall
import LowScale68SecondaryResidualRowTwoLoadDominance
import LowScale68SecondaryResidualSumLoadWall
import LowScale68SecondaryResidualOvershootCanonical

/-! # Canonical selector for the residual strip `2g < n < 3g`

The five tracked impossibility theorems already close every comparison of
`2h` and `g+h` against `n` inside the strict residual strip.  This module
packages that partition: Nat trichotomy on `2h` versus `n`, and after
`n < 2h` a second trichotomy on `g+h` versus `n`.  The common hypotheses
are exactly the union of the imported wrappers: the canonical source, the
strip `2g < n < 3g`, `g < h`, and the selected residual degree bounds.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Exhaustive arithmetic -/

/-- Residual-strip comparisons of `2h` and `g+h` against `n`. -/
theorem residualStripSelector_cases (n g h : ℕ) :
    2 * h < n ∨
      2 * h = n ∨
        (n < 2 * h ∧ g + h < n) ∨
          g + h = n ∨
            n < g + h := by
  rcases lt_trichotomy (2 * h) n with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr (Or.inl heq)
  · rcases lt_trichotomy (g + h) n with hwin | hwall | hover
    · exact Or.inr (Or.inr (Or.inl ⟨hgt, hwin⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hwall)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hover)))

theorem residualStripSelector_sumWall (n g h : ℕ) (hsum : g + h = n) :
    h = n - g := by
  omega

/-! ## Canonical expanded wrapper -/

set_option maxHeartbeats 4000000 in
/-- The strict residual strip `2g < n < 3g` is empty on a canonical
expanded source, once the selected residual gap satisfies `g < h` and the
selected residual degree bounds required by the imported wrappers. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualStripSelector_impossible68
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
    (hgh :
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
      g < h)
    (hmiddle :
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h)
    : False := by
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
  have hchamber' : 2 * g < n ∧ n < 3 * g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber
  have hgh' : g < h := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hgh
  have hmiddle' : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle
  rcases residualStripSelector_cases n g h with
    hleft | hhalf | hdom | hsum | hover
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_residualLeftLoadWindow_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hchamber (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
            And.intro hgh' hleft)
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusI4Wall_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          hchamber'.1)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          hchamber'.2)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
          hhalf)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
          hmiddle')
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_residualRowTwoLoadDominance_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hchamber (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdom)
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_residualSumLoadWall_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hchamber (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
            residualStripSelector_sumWall n g h hsum)
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_residualOvershoot_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hchamber (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hover)

set_option maxHeartbeats 4000000 in
/-- The strict complementary strip is unconditionally empty on a canonical
expanded source.  The residual gap inequality and its degree bounds are
derived internally from the first-face strict drops. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualStrictStrip_impossible68
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
      2 * g < n ∧ n < 3 * g) :
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
  change 2 * g < n ∧ n < 3 * g at hchamber
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_residualStripSelector_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hgh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hbounds)

#print axioms residualStripSelector_cases
#print axioms residualStripSelector_sumWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualStripSelector_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualStrictStrip_impossible68

end Max11DegreeRoutes
