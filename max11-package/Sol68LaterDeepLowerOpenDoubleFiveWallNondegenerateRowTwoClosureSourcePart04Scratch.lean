import Sol68LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSourcePart03Scratch

/-! # Row-two closure of the nondegenerate double-five tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallNondegenerate_inconsistent68
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
      2 * g ≤ h)
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
      3 * g = 5 * n)
    (hnondegenerate :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ce.coeff (4 * n - g) ≠ 0) : False := by
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
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  let a := Ae.coeff (2 * n)
  let b := Be.coeff (3 * n - g)
  let c := ce.coeff (4 * n - g)
  let de := d.coeff (5 * n - 2 * g)
  let e := ee.coeff (6 * n - 2 * g)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change c ≠ 0 at hnondegenerate
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ (de ≠ 0 ∨ e ≠ 0) ∧
      LaterDeepLowerOpenDoubleFiveWallScalarPacket68
        (n : k) a b c de e delta at selector
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _
    at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have ha : a ≠ 0 := by
    dsimp only [a]
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
    have ht := bounds.1
    change d.natDegree ≤ 5 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have hDtr : Dtr.natDegree ≤ 5 * n - g := by
    simp only [Dtr]
    compute_degree
    omega
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at h2e
  have hrowPoly := polynomialSecondaryResidualRowTwo68
    0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee h2e
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) hrowPoly
  rw [coeff_add, coeff_zero,
    secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
      Ae Be ce d ee n g hn hwall hA secondary.2.1 secondary.2.2.1 hd2 he2,
    cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
      alpha gamma delta epsilon zeta eta Ae Be ce Dtr ee n g hn hwall
      hA secondary.2.1 secondary.2.2.1 hDtr he2] at hcoeff
  have hrowTwo : (8 / 27 : k) * (n : k) *
        (a * b ^ 3 + 9 * a * b * e + 9 * a * c * de - 18 * b * c ^ 2) +
      (2 / 3 : k) * (n : k) * delta * a ^ 3 = 0 := by
    simpa only [a, b, c, de, e] using hcoeff
  have refined := laterDeepLowerOpenDoubleFiveWallScalarPacket68_refine
    (n : k) a b c de e delta ha (Or.inr hnondegenerate)
    selector.2.1 selector.2.2
  have hdisc : a * b ^ 2 = c ^ 2 := by
    rcases refined with hdeg | hnon
    · exact False.elim (hnondegenerate hdeg.1)
    · exact hnon.2
  exact laterDeepLowerOpenDoubleFiveWall_nondegenerate_rowTwo_inconsistent68
    (n : k) a b c de e delta (Nat.cast_ne_zero.mpr hn.ne') ha
    hnondegenerate hdisc selector.2.2 hrowTwo

end LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68
end Max11DegreeRoutes
