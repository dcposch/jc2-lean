import LowScale68SecondaryLargeGapLoadZeroFacePart03Scratch

/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-- The canonical expanded system on `n < 2g` and `g < n` has genuine
strict degree drop in both residual coordinates. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualDrops68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g)
    (hgap :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
      ee.natDegree < 6 * n - g := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n < 2 * g at hlarge
  change g < n at hgap
  change l = 0 ∧
    (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop :=
    maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  exact ⟨hclass.1,
    firstSecondaryResidualDegreeDrops68_of_largeGapLoadZero Ae Be De ee n g
      hn hg hlarge hgap hA hB hD he hclass.2.2 hclass.2.1⟩

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
