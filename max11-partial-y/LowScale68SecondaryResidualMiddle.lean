import LowScale68SecondaryResidualExtraction

/-! # The actual `(6,8)` middle residual face

This module connects the abstract middle-face classifier to the canonical
expanded polynomial lower system.  It assumes only the explicit degree-gap
selection data `g<h<2g`; proving that the residual tropical screen selects
this face or one of the endpoint faces is the next step.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualMiddle68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 4000000 in
/-- If the actual expanded lower system enters the middle residual face in
`3g<n`, its two new residual coefficients are nonzero and its leading
`A,B,c` coefficients satisfy the exact discriminant relation. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddle68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (h : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g < n)
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
      g < h)
    (hh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      h < 2 * g)
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
        Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
        (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0)) :
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
    d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 := by
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
  change 3 * g < n at hsmall
  change g < h at hgh
  change h < 2 * g at hh
  change d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
    Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
    (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) at hmiddle
  change d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
      3 * ce.coeff (4 * n - g) ^ 2 = 0
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have hx := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  exact polynomialSecondaryResidualBetweenFace68_classify
    l beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h
    hg hgh hh hsmall hA hB hc hmiddle.1 hmiddle.2.1
    hmiddle.2.2.1 hmiddle.2.2.2.1 hmiddle.2.2.2.2 hi4c hi3c

end SecondaryResidualMiddle68

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddle68

end Max11DegreeRoutes
