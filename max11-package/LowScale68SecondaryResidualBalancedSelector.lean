import LowScale68SecondaryResidualSelector
import LowScale68SecondaryResidualRowTwoFaces
import LowScale68SecondaryResidualRowTwoSystem

/-! # Selected residual gap is balanced: `2h = 3g`

The residual first one-form plus a strictly lower load cannot vanish in
either strict Newton chamber.

* Left chamber `2h < 3g`: the `d*e` face at `11*n-2*h-1` has coefficient
  `(8/3)*(11*n-2*h)*d_top*e_top`.
* Right chamber `3g < 2h`: the middle-face discriminant collapses the
  `B,c` core at `11*n-3*g-1` to `(32/81)*(11*n-3*g)*a*b^3`.

Both scalars are nonzero in characteristic zero.  The load cutoff
`natDegree < 11*n-3*g-1` is already below the cubic face, hence also below
the left face whenever `2h < 3g`.  Trichotomy therefore forces `2h = 3g`.

The `Q` degree cutoff and load degree cutoff are parameters of the abstract
trichotomy and are discharged by the residual-descent module downstream.  The row-two vanishing `residual + load = 0` is the checked
system-bridge shape.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualBalancedSelector68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Residual plus a strictly lower load cannot contribute at `idx`. -/
theorem residualRowTwo_coeff_eq_zero_of_loadCutoff68
    (A B c d e load : k[X]) (idx : ℕ)
    (hload : load.natDegree < idx)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff idx = 0 := by
  have h := congrArg (fun p : k[X] => p.coeff idx) hsum
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload,
    add_zero] at h
  exact h

/-- Middle-face discriminant and a nonzero `c` force `a ≠ 0`. -/
theorem residualDisc_imp_leadingA_ne_zero68 (a b c : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) (hc : c ≠ 0) :
    a ≠ 0 := by
  intro ha
  have h3c : (3 : k) * c ^ 2 = 0 := by
    simpa [ha] using hdisc
  exact (mul_ne_zero (by norm_num : (3 : k) ≠ 0) (pow_ne_zero 2 hc)) h3c

set_option maxHeartbeats 2000000 in
/-- The left chamber `2h < 3g` is incompatible with residual-plus-load
vanishing under the cubic-face load cutoff. -/
theorem residualRowTwo_not_leftChamber68
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    False := by
  have hidx : 11 * n - 3 * g - 1 < 11 * n - 2 * h - 1 := by omega
  have hload' : load.natDegree < 11 * n - 2 * h - 1 := hload.trans hidx
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e load (11 * n - 2 * h - 1) hload' hsum
  exact residualRowTwo_leftChamber_ne_zero68 A B c d e n g h hg hgh hh hsmall
    hleft hA hB hc hd he hQ hd0 he0 hcoeff0

set_option maxHeartbeats 2000000 in
/-- The right chamber `3g < 2h` is incompatible with residual-plus-load
vanishing under the cubic-face load cutoff. -/
theorem residualRowTwo_not_rightChamber68
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0) :
    False := by
  have ha0 := residualDisc_imp_leadingA_ne_zero68
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    hdisc hc0
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e load (11 * n - 3 * g - 1) hload hsum
  exact residualRowTwo_rightChamber_ne_zero68 A B c d e n g h hg hgh hh hsmall
    hright hA hB hc hd he hQ hdisc ha0 hb0 hcoeff0

set_option maxHeartbeats 2000000 in
/-- Abstract trichotomy: under the restated cutoffs, the selected gap is
balanced. -/
theorem residualSelectedGap_eq_balanced68
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    2 * h = 3 * g := by
  rcases lt_trichotomy (2 * h) (3 * g) with hleft | heq | hright
  · exact (residualRowTwo_not_leftChamber68 A B c d e load n g h hg hgh hh
      hsmall hleft hA hB hc hd he hQ hload hsum hd0 he0).elim
  · exact heq
  · exact (residualRowTwo_not_rightChamber68 A B c d e load n g h hg hgh hh
      hsmall hright hA hB hc hd he hQ hload hsum hdisc hb0 hc0).elim

set_option maxHeartbeats 2000000 in
/-- The same trichotomy, with residual-plus-load discharged by the checked
row-two system bridge. -/
theorem residualSelectedGap_eq_balanced68_of_rowTwoSystem
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload :
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
          11 * n - 3 * g - 1)
    (hrowTwo :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta A B C0 D0)
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D0 E0) B C0 D0 E0 = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    2 * h = 3 * g := by
  have hsum := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta A B c d e hrowTwo
  exact residualSelectedGap_eq_balanced68 A B c d e
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e)
    n g h hg hgh hh hsmall hA hB hc hd he hQ hload hsum hdisc hb0 hc0 hd0 he0

set_option maxHeartbeats 6000000 in
/-- Canonical specialization: the selected residual gap of a maximal
expanded polynomial lower system is balanced, given the restated `Q` and
load cutoffs. -/
theorem residualCanonicalSelectedGap_eq_balanced68
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
      3 * g < n)
    (hQ :
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
      (residualIncidenceQ68 Be ce d ee).natDegree < 9 * n - 3 * g)
    (hload :
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
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 3 * g - 1) :
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
  change 3 * g < n at hsmall
  change (residualIncidenceQ68 Be ce d ee).natDegree < 9 * n - 3 * g at hQ
  change (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
        11 * n - 3 * g - 1 at hload
  change 2 * h = 3 * g
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
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
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
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddle68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          And.intro hbounds.1 (And.intro hbounds.2
            (And.intro hb0 (And.intro hc0 hattained))))
  change d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
      3 * ce.coeff (4 * n - g) ^ 2 = 0 at hclass
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
  exact residualSelectedGap_eq_balanced68_of_rowTwoSystem
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
    hg hgh hh hsmall hA hB hcdeg hbounds.1 hbounds.2 hQ hload hrowTwo
    hclass.2.2 hb0 hc0 hclass.1 hclass.2.1

end SecondaryResidualBalancedSelector68

#print axioms residualRowTwo_coeff_eq_zero_of_loadCutoff68
#print axioms residualDisc_imp_leadingA_ne_zero68
#print axioms residualRowTwo_not_leftChamber68
#print axioms residualRowTwo_not_rightChamber68
#print axioms residualSelectedGap_eq_balanced68
#print axioms residualSelectedGap_eq_balanced68_of_rowTwoSystem
#print axioms residualCanonicalSelectedGap_eq_balanced68

end Max11DegreeRoutes
