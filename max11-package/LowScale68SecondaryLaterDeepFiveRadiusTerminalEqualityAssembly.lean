import LowScale68SecondaryLaterDeepFiveRadiusTerminalEqualityFaceAlgebra

/-! # Source-level finite selector on the terminal equality wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalEqualityAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 48000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

structure FiveRadiusTerminalEqualityScalarSelector68
    (a b c d e : k) : Prop where
  cases :
    (c = 0 ∧ d = 0 ∧ 9 * e = b ^ 2) ∨
    (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
      6 * c * d = -(b ^ 3) ∧ 18 * e = 5 * b ^ 2)

set_option maxHeartbeats 3000000 in
theorem fiveRadiusTerminalEqualityFace68_classify
    (a b c d e : k) (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0)
    (hattained : d ≠ 0 ∨ e ≠ 0)
    (hface : FiveRadiusTerminalEqualityFace68 a b c d e) :
    b ≠ 0 ∧ FiveRadiusTerminalEqualityScalarSelector68 a b c d e := by
  have hb : b ≠ 0 := by
    rcases hsupport with hb | hc
    · exact hb
    · intro hb0
      have hd0 : d = 0 := by
        have h := hface.four
        rw [hb0] at h
        have hcd : c * d = 0 := by linear_combination (1 / 9 : k) * h
        exact (mul_eq_zero.mp hcd).resolve_left hc
      have he0 : e = 0 := by
        have h := hface.three
        rw [hb0] at h
        have hce : c * e = 0 := by linear_combination (1 / 3 : k) * h
        exact (mul_eq_zero.mp hce).resolve_left hc
      exact hattained.elim (fun hd ↦ hd hd0) (fun he ↦ he he0)
  refine ⟨hb, ⟨?_⟩⟩
  by_cases hc0 : c = 0
  · left
    have hd0 : d = 0 := by
      have h := hface.three
      rw [hc0] at h
      have hab : a * b ≠ 0 := mul_ne_zero ha hb
      have habd : a * b * d = 0 := by linear_combination -h
      exact (mul_eq_zero.mp habd).resolve_left hab
    refine ⟨hc0, hd0, ?_⟩
    have h := hface.four
    rw [hc0, hd0] at h
    have hprod : b * (9 * e - b ^ 2) = 0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hb)
  · right
    have hdisc0 : c * (a * b ^ 2 - c ^ 2) = 0 := by
      linear_combination hface.rowOne
    have hdisc : c ^ 2 = a * b ^ 2 := by
      have hz := (mul_eq_zero.mp hdisc0).resolve_left hc0
      exact (sub_eq_zero.mp hz).symm
    have hdiscEq : c ^ 2 - a * b ^ 2 = 0 := sub_eq_zero.mpr hdisc
    have hdprod : (2 * c) * (b ^ 3 + 6 * c * d) = 0 := by
      linear_combination
        c * hface.four - (3 * b) * hface.three + (3 * d) * hdiscEq
    have h2c : (2 : k) * c ≠ 0 := mul_ne_zero (by norm_num) hc0
    have hdrel0 : b ^ 3 + 6 * c * d = 0 :=
      (mul_eq_zero.mp hdprod).resolve_left h2c
    have hdrel : 6 * c * d = -(b ^ 3) := by
      linear_combination hdrel0
    have heprod : b * (18 * e - 5 * b ^ 2) = 0 := by
      linear_combination 2 * hface.four - 3 * hdrel0
    have herel : 18 * e = 5 * b ^ 2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp heprod).resolve_left hb)
    exact ⟨hc0, hdisc, hdrel, herel⟩

/-- Full source-facing refinement of the terminal selector.  All strict
terminal leaves are absent; the equality wall satisfies an exact finite
two-family scalar selector. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalScalarSelector68
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
      2 * g = 5 * n) :
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
    h = 5 * n ∧
      d.natDegree ≤ 0 ∧ ee.natDegree ≤ n ∧ zeta = 0 ∧
      FiveRadiusTerminalEqualityFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff 0) (ee.coeff n) ∧
      Be.coeff (3 * n - g) ≠ 0 ∧
      FiveRadiusTerminalEqualityScalarSelector68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff 0) (ee.coeff n) := by
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
  have terminalEq :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEquality68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      h = 5 * n ∧ (d.coeff 0 ≠ 0 ∨ ee.coeff n ≠ 0)
      at terminalEq
  have heqh : h = 5 * n := terminalEq.2.2.2.2.2.2.2.1
  have hddeg : d.natDegree ≤ 0 := by
    have := terminalEq.2.2.2.2.1
    omega
  have hedeg : ee.natDegree ≤ n := by
    have := terminalEq.2.2.2.2.2.1
    omega
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hwall' : 2 * g = 5 * n := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, terminalEq.1, terminalEq.2.1, terminalEq.2.2.1] at hi4c
  have hzeta := cubicFirstIntegralFourPolynomial68_forces_zeta_of_fiveRadiusWall_above
    gamma epsilon zeta i4 Ae Be ce d ee n g (5 * n) hn hwall'
      (by omega) hA ha secondary.2.1 secondary.2.2.1
      (by omega) (by omega)
      (by simpa only [heqh] using hi4c)
  have hi40 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    simpa only [hzeta] using hi4c
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, terminalEq.1, terminalEq.2.1, terminalEq.2.2.1, hzeta] at hi3c
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
  rw [terminalEq.1, terminalEq.2.1, terminalEq.2.2.1, hzeta] at hrow
  have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
    alpha gamma epsilon 0 eta i3 Ae Be ce d ee hi3c hrow
  have hface := polynomialFiveRadiusTerminalEqualityFace68
    gamma epsilon i4 i3 Ae Be ce d ee n g hn hwall' hA
      secondary.2.1 secondary.2.2.1 hddeg hedeg hi40 hi3c hreduced
  have hclass := fiveRadiusTerminalEqualityFace68_classify
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff 0) (ee.coeff n) ha
    terminalEq.2.2.2.2.2.2.1 terminalEq.2.2.2.2.2.2.2.2 hface
  exact ⟨heqh, hddeg, hedeg, hzeta, hface, hclass.1, hclass.2⟩

#print axioms fiveRadiusTerminalEqualityFace68_classify
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalScalarSelector68

end LaterDeepFiveRadiusTerminalEqualityAssembly68

end Max11DegreeRoutes
