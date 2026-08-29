import LowScale68SecondaryLargeGapTransport
import LowScale68SecondaryLargeGapAlphaCancellation

/-! # Canonical closure of the (6,8) large-gap load-zero chamber `n < 2g` and `g < n`

The transport module supplies
`maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZero_impossible_of_rowOneCutoff68`
on `n < 2g` and `g < n`, once the cubic row-one load sits strictly below
`12n-3g-1`.  Exact alpha-core cancellation
`cubicLoadRowOnePolynomial68_degree_lt_largeGap_of_gap_lt_radius`
discharges that cutoff after `l = 0` throughout `g < n`.  The residual-gap
packet is unpacked only to obtain `l = 0` and the first-face residual
degree bounds needed by the cutoff.  The complementary walls `g = n` and
`2g = n`, and the strip `2g < n`, are not claimed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroClosure68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- On the canonical expanded system, the full large-gap load-zero chamber
`n < 2g` and `g < n` is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZero_impossible68
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
      n < 2 * g ∧ g < n) :
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
  change n < 2 * g ∧ g < n at hchamber
  have hgap :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.2)
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h at hgap
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg0 : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hcdeg : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - g := le_of_lt hgap.2.2.1
  have heLoad : ee.natDegree ≤ 6 * n - g := le_of_lt hgap.2.2.2.1
  have hDload :
      ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have hload1 :=
    cubicLoadRowOnePolynomial68_degree_lt_largeGap_of_gap_lt_radius
      0 alpha beta gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g
      (by omega) hg0 rfl hchamber.2 hA hB hcdeg hDload heLoad
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZero_impossible_of_rowOneCutoff68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hload1)

end LargeGapLoadZeroClosure68

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZero_impossible68

end Max11DegreeRoutes
