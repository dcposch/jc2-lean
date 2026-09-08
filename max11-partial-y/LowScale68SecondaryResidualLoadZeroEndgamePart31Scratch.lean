import LowScale68SecondaryResidualLoadZeroEndgamePart30Scratch

/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

set_option maxHeartbeats 6000000 in
theorem residualCanonicalSelectedGap_eq_balanced68_of_l_eq_zero
    (alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      2 * g < n) :
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
    2 * h = 3 * g := by
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
  change 2 * g < n at hsmall
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
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
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
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
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSelect68_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  obtain ⟨h', hgh', hh', hb0, hc0, hd0', he0', hdisc'⟩ := hsel
  change g < h' at hgh'
  change h' < 2 * g at hh'
  change Be.coeff (3 * n - g) ≠ 0 at hb0
  change ce.coeff (4 * n - g) ≠ 0 at hc0
  change d.coeff (5 * n - h') ≠ 0 at hd0'
  change ee.coeff (6 * n - h') ≠ 0 at he0'
  change Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
    3 * ce.coeff (4 * n - g) ^ 2 = 0 at hdisc'
  have hdne : d ≠ 0 := fun hz => by
    rw [hz, coeff_zero] at hd0'
    exact hd0' rfl
  have hh : h < 2 * g := by
    have hgapd : polynomialGap68 n 5 d ≤ h' := by
      have hgap : polynomialGap68 n 5 d = 5 * n - d.natDegree := by
        simp [polynomialGap68, hdne]
      rw [hgap]
      have hle : 5 * n - h' ≤ d.natDegree := by
        by_contra hnot
        have hz : d.coeff (5 * n - h') = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        exact hd0' hz
      omega
    exact (le_trans (Nat.min_le_left _ _) hgapd).trans_lt hh'
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := fun hboth => hdne hboth.1
  have hattained : d.coeff (5 * n - h) ≠ 0 ∨
      ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using secondaryResidualGap68_boundary_attained n d ee
      hdbase hebase hnotboth
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
  have hi4e : firstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hface :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddleFace68_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
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
    (ee.coeff (6 * n - h)) (by simpa only [n, Ae] using
      (maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
        0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys).2.2.2.2.2) (Or.inl hb0) hattained hface
  have hQ :
      (residualIncidenceQ68 Be ce d ee).natDegree < 9 * n - 3 * g := by
    have hq :=
      secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace_of_l_eq_zero
        beta gamma delta epsilon zeta i4 Ae Be ce d ee n g h
        hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2 hi4c
    simpa [residualIncidenceQ68,
      secondaryResidualIncidenceDefectPolynomial68] using hq
  have hload :
      (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 3 * g - 1 :=
    cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
      hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
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
        (integratedSPolynomial68 0 alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
  exact residualSelectedGap_eq_balanced68_of_rowTwoSystem_of_l_eq_zero
    alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
    hg hgh hh hsmall hA hB hcdeg hbounds.1 hbounds.2 hQ hload hrowTwo
    hclass.2.2.2.2 hb0 hc0 hclass.2.2.1 hclass.2.2.2.1

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
