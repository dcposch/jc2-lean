import LowScale68SecondaryLaterDeepThreeRadiusZeroResidualLoadAssembly

/-! # Source deletion of the zero residual leaf on `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusZeroResidualSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 6000000 in
/-- The exact I4 and row-one equations exclude the identically-zero
translated residual pair on the three-radius wall. -/
theorem threeRadius_zeroResidual_impossible68
    (alpha gamma delta epsilon zeta eta i4 : k) (A B c : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨
      c.coeff (4 * n - g) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B)) 0 = C i4)
    (hrow : secondaryResidualRowOnePolynomial68 A B c 0 0 +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B)) 0 = 0) : False := by
  have hb := threeRadiusZeroResidualI4_forces_B_top_zero68
    gamma delta epsilon zeta i4 A B c n g hn hwall hA hB hc hi4
  have hindex : 0 < 3 * n - g := by omega
  have hBlt := natDegree_lt_of_le_of_coeff_eq_zero68
    B (3 * n - g) hindex hB hb
  have hcne : c.coeff (4 * n - g) ≠ 0 :=
    hsupport.resolve_left (not_ne_iff.mpr hb)
  have hload :=
    cubicLoadRowOnePolynomial68_degree_lt_threeRadiusZeroResidual
      alpha gamma delta epsilon zeta eta A B c n g hn hwall hA hBlt hc
  have hres :=
    secondaryResidualRowOnePolynomial68_coeff_threeRadiusZeroResidual
      A B c n g hn hwall hA hBlt hc
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrow
  rw [coeff_add, hres, coeff_eq_zero_of_natDegree_lt hload, add_zero,
    coeff_zero] at hcoeff
  have hcast : (((4 * n - g : ℕ) : k)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hcast)
    (pow_ne_zero 3 hcne)) hcoeff

set_option maxHeartbeats 12000000 in
/-- Source-facing exact selector on `2g=3n`, with the zero residual leaf
removed.  The surviving edge is either the ordinary middle face or the
ordinary double-invariant face. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusNonzeroResidualSelector68
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
      2 * g = 3 * n) :
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
    l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧
      ((h < 2 * g ∧
          SecondaryResidualBetweenFace68
            (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
            (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
            (ee.coeff (6 * n - h))) ∨
        (2 * g ≤ h ∧
          ThreeRadiusResidualDoubleInvariantFace68
            (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
            (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
            (ee.coeff (6 * n - 2 * g)))) := by
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
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusResidualSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧ _
    at selector
  refine ⟨selector.1, selector.2.1, selector.2.2.1,
    selector.2.2.2.1, selector.2.2.2.2.1,
    selector.2.2.2.2.2.1, ?_⟩
  rcases selector.2.2.2.2.2.2 with hzero | hpacket
  · have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have secondary :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
      ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
      ee.natDegree ≤ 6 * n - g ∧ _ at secondary
    have hn : 0 < n := by simpa only [n] using core.1
    have hA : Ae.natDegree ≤ 2 * n := by
      have hAe : Ae.natDegree = 2 * n := by
        simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
      omega
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    have hd0 : d = 0 := hzero.1
    have he0 : ee = 0 := hzero.2
    obtain ⟨i4, hi4⟩ := hsys.firstFour
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    have hi4c := hi4e
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, selector.1, selector.2.1, hd0, he0] at hi4c
    have hi4zero : cubicFirstIntegralFourPolynomial68
        0 0 gamma delta epsilon zeta Ae Be ce
          ((1 / 3 : k) • (Ae * Be)) 0 = C i4 := by
      simpa only [add_zero] using hi4c
    have h1e : lowerRowOnePolynomial68
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Ce De Ee = 0 := by
      dsimp only [Ae, Be, Ce, De, Ee]
      rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
        ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
        hsys.rowOne, map_zero, zero_mul]
    rw [hCrec, hDrec, hErec] at h1e
    have hrow := polynomialSecondaryResidualRowOne68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h1e
    rw [selector.1, selector.2.1, hd0, he0] at hrow
    have hrowzero : secondaryResidualRowOnePolynomial68 Ae Be ce 0 0 +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be)) 0 = 0 := by
      simpa only [add_zero] using hrow
    exact (threeRadius_zeroResidual_impossible68
      alpha gamma delta epsilon zeta eta i4 Ae Be ce n g hn hwall hA
      secondary.2.1 secondary.2.2.1 selector.2.2.2.2.2.1
      hi4zero hrowzero).elim
  · exact hpacket

#print axioms threeRadius_zeroResidual_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusNonzeroResidualSelector68

end LaterDeepThreeRadiusZeroResidualSource68

end Max11DegreeRoutes
