import LowScale68SecondaryLaterDeepFiveRadiusTerminalRowZeroAlgebra

/-! # Source closure of the terminal equality wall `2g = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 48000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The complete later-deep five-radius wall is empty.  Strict terminal
leaves were removed by I4/row one; on the equality leaf the exact row-zero
coefficient contradicts both scalar families left by I4/I3/row one. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEndgame68
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
      2 * g = 5 * n) : False := by
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
  have base :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEquality68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      h = 5 * n ∧ (d.coeff 0 ≠ 0 ∨ ee.coeff n ≠ 0) at base
  have scalar :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalScalarSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change h = 5 * n ∧ d.natDegree ≤ 0 ∧ ee.natDegree ≤ n ∧
      zeta = 0 ∧
      FiveRadiusTerminalEqualityFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff 0) (ee.coeff n) ∧
      Be.coeff (3 * n - g) ≠ 0 ∧
      FiveRadiusTerminalEqualityScalarSelector68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff 0) (ee.coeff n) at scalar
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
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 :
      secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
        C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa using hsplit0.symm.trans h0e
  rw [base.1, base.2.1, base.2.2.1, scalar.2.2.2.1] at hsum0
  have hloadEq := cubicLoadRowZeroPolynomial68_terminalEquality
    alpha gamma epsilon eta Ae Be ce d ee
  rw [hloadEq] at hsum0
  let idx := 13 * n - 3 * g - 1
  have hidx : idx ≠ 59 := by
    dsimp [idx]
    omega
  have hterm :
      (C terminal * (60 * (X ^ 59 : k[X]))).coeff idx = 0 := by
    simp [coeff_C_mul, coeff_X_pow, hidx]
  have hloadLow := fiveRadiusTerminalRowZeroLoad68_degree_lt
    gamma epsilon Ae Be ce d ee n g hn hwall' hA
      secondary.2.1 secondary.2.2.1 scalar.2.1 scalar.2.2.1
  have htailLow := fiveRadiusTerminalRowZeroTail68_degree_lt
    Ae Be ce d ee n g hn hwall' hA secondary.2.1 secondary.2.2.1
      scalar.2.1 scalar.2.2.1
  have hcoreCoeff := fiveRadiusTerminalRowZeroCore68_coeff
    Ae Be ce d ee n g hn hwall' hA secondary.2.1 secondary.2.2.1
      scalar.2.1 scalar.2.2.1
  have hresCoeff :
      (secondaryResidualRowZeroPolynomial68 Ae Be ce d ee).coeff idx =
        (8 / 27 : k) * (n : k) * Ae.coeff (2 * n) *
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) * ee.coeff n) -
            Ae.coeff (2 * n) * ce.coeff (4 * n - g) * d.coeff 0 +
            Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2) := by
    rw [secondaryResidualRowZeroPolynomial68_terminalEqualitySplit,
      coeff_add, coeff_eq_zero_of_natDegree_lt htailLow, add_zero]
    simpa only [idx] using hcoreCoeff
  have hz := congrArg (fun p : k[X] => p.coeff idx) hsum0
  rw [coeff_add, hresCoeff, coeff_eq_zero_of_natDegree_lt hloadLow,
    add_zero, hterm] at hz
  have hnK : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpref : (8 / 27 : k) * (n : k) * Ae.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hnK) ha
  have hzero :
      -(Ae.coeff (2 * n) * Be.coeff (3 * n - g) * ee.coeff n) -
        Ae.coeff (2 * n) * ce.coeff (4 * n - g) * d.coeff 0 +
        Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 = 0 :=
    (mul_eq_zero.mp hz).resolve_left hpref
  exact fiveRadiusTerminalEqualityScalarSelector68_rowZero_impossible
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff 0) (ee.coeff n) ha
    scalar.2.2.2.2.2.1 scalar.2.2.2.2.2.2 (by linear_combination hzero)

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEndgame68

end LaterDeepFiveRadiusTerminalEndgame68

end Max11DegreeRoutes
