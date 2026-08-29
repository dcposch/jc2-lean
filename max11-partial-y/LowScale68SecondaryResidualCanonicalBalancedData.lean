import LowScale68SecondaryResidualCanonicalBalanced
import LowScale68SecondaryResidualRowTwoBalanced

/-! # Canonical balanced residual data for row one

From an actual expanded polynomial lower system in the chamber `3*g<n`,
the selected residual gap is balanced, the middle-face scalars are
attained and nonzero, and the cubic invariant lies strictly below the
cubic face.  This packages exactly the residual data consumed by the
balanced row-one coefficient; it does not mention row-one polynomials
or row-one loads.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section CanonicalBalancedData68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Residual data on the balanced wall `2*h=3*g` needed to read the cubic
face of residual row one. -/
structure CanonicalBalancedResidualData68
    (A B c d e : k[X]) (n g h : ℕ) : Prop where
  hg : 0 < g
  hgh : g < h
  hh : h < 2 * g
  hsmall : 3 * g < n
  hbalanced : 2 * h = 3 * g
  hA : A.natDegree ≤ 2 * n
  hB : B.natDegree ≤ 3 * n - g
  hcdeg : c.natDegree ≤ 4 * n - g
  hd : d.natDegree ≤ 5 * n - h
  he : e.natDegree ≤ 6 * n - h
  ha0 : A.coeff (2 * n) ≠ 0
  hb0 : B.coeff (3 * n - g) ≠ 0
  hc0 : c.coeff (4 * n - g) ≠ 0
  hd0 : d.coeff (5 * n - h) ≠ 0
  he0 : e.coeff (6 * n - h) ≠ 0
  hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
    (3 : k) * c.coeff (4 * n - g) ^ 2 = 0
  hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
    c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0
  hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
    (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0
  hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
    10 * n - 3 * g

set_option maxHeartbeats 8000000 in
/-- The actual maximal expanded lower system in `3*g<n` supplies the
canonical balanced residual data. -/
theorem canonicalBalancedResidualData68_of_system
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
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
      3 * g < n) :
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
    CanonicalBalancedResidualData68 Ae Be ce d ee n g h := by
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
  change 3 * g < n at hsmall
  change CanonicalBalancedResidualData68 Ae Be ce d ee n g h
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
  have hcdeg : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 2 * g < n by omega))
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt n g d ee hsmall
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hbalanced : 2 * h = 3 * g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
      residualCanonicalSelectedGap_eq_balanced68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  have hh : h < 2 * g := by omega
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have ha0 : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondarySmallGapBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 2 * g < n by omega))
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hsupport := hboundary.2.2
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    rintro ⟨hd0, he0⟩
    have hh0 : h = 6 * n + 1 := by
      simp only [h, secondaryResidualGap68, polynomialGap68, hd0, he0,
        ↓reduceIte, min_self]
    omega
  have hattained : d.coeff (5 * n - h) ≠ 0 ∨
      ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using secondaryResidualGap68_boundary_attained n d ee
      hdbase hebase hnotboth
  have hface :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddleFace68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hbounds)
  change SecondaryResidualBetweenFace68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) at hface
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) ha0 hsupport hattained hface
  have hb0 : Be.coeff (3 * n - g) ≠ 0 := hclass.1
  have hc0 : ce.coeff (4 * n - g) ≠ 0 := hclass.2.1
  have hd0 : d.coeff (5 * n - h) ≠ 0 := hclass.2.2.1
  have he0 : ee.coeff (6 * n - h) ≠ 0 := hclass.2.2.2.1
  have hdisc : Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
      (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 := hclass.2.2.2.2
  have hinc : Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
      ce.coeff (4 * n - g) * d.coeff (5 * n - h) = 0 := hface.four
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
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
  have hQ :
      (residualBalancedIncidenceQ68 Be ce d ee).natDegree <
        9 * n - 3 * g := by
    have hq :=
      secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace
        l beta gamma delta epsilon zeta i4 Ae Be ce d ee n g h
        hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2 hi4c
    simpa [residualBalancedIncidenceQ68,
      secondaryResidualIncidenceDefectPolynomial68] using hq
  have hload :
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 3 * g - 1 :=
    cubicLoadRowTwoPolynomial68_degree_lt_cubicFace
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
      hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
  have hsum := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  have hrel := residualRowTwo_add_load_eq_zero_imp_balancedRelation68
    Ae Be ce d ee
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hg hgh hh hsmall hbalanced hA hB hcdeg hbounds.1 hbounds.2
    hQ hdisc hload hsum
  have hD : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have hload3 := secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace
    l beta gamma delta epsilon zeta Ae Be ce
    ((1 / 3 : k) • (Ae * Be) + d) ee n g h hg hgh hsmall
    hA hB hcdeg hD hbounds.2
  have hsplit := hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  have hI3eq :
      secondaryResidualInvariantThreePolynomial68 Ae Be ce d ee =
        C i3 - secondaryLoadInvariantThreePolynomial68
          l beta gamma delta epsilon zeta Ae Be ce
            ((1 / 3 : k) • (Ae * Be) + d) ee :=
    eq_sub_iff_add_eq.mpr hsplit
  have hI3 :
      (secondaryResidualInvariantThreePolynomial68 Ae Be ce d ee).natDegree <
        10 * n - 3 * g := by
    rw [hI3eq]
    compute_degree
    omega
  exact ⟨hg, hgh, hh, hsmall, hbalanced, hA, hB, hcdeg, hbounds.1,
    hbounds.2, ha0, hb0, hc0, hd0, he0, hdisc, hinc, hrel, hI3⟩

end CanonicalBalancedData68

#print axioms canonicalBalancedResidualData68_of_system

end Max11DegreeRoutes
