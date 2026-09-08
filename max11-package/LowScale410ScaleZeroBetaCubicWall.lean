import LowScale410ScaleZeroNonzeroBetaCone

/-!
# The explicit nonzero-beta cubic wall

This file studies the smallest algebraic survivor of the nonzero-beta
Newton packet,

`5 A^3 - 24 A C0 - 4 B^2 = 0`.

No later load is set to zero.  The wall forces an exact three-face degree
tie, removes beta completely from the second invariant, reduces the first
beta core to a three-term quartic, and adds an independent terminal Newton
constraint.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section BetaCubicWall410

variable {k : Type*} [Field k] [CharZero k]

/-- The first beta core after reduction modulo the cubic beta wall. -/
def betaCubicReducedTwoCore410 (A C0 : k[X]) : k[X] :=
  -(55 : k) • A ^ 4 + (240 : k) • (A ^ 2 * C0) +
    (192 : k) • C0 ^ 2

theorem betaTwoCorePolynomial410_eq_reduced_of_cubicWall
    (A B C0 : k[X])
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    betaTwoCorePolynomial410 A B C0 =
      betaCubicReducedTwoCore410 A C0 := by
  simp only [betaOneCorePolynomial410, betaTwoCorePolynomial410,
    betaCubicReducedTwoCore410, Polynomial.smul_eq_C_mul] at hwall ⊢
  push_cast at hwall ⊢
  simp only [Polynomial.C_neg, Polynomial.C_ofNat] at hwall ⊢
  linear_combination 12 * A * hwall

/-- The pure beta contribution to the terminal row, defined directly by
specializing the load remainders. -/
def betaPureTerminalPolynomial410
    (beta : k) (A B C0 : k[X]) : k[X] :=
  betaWallWRemainder410 beta 0 0 0 0 A B C0 * derivative C0 -
    B * derivative (betaWallZRemainder410 beta 0 0 0 0 A B C0)

/-- The contribution of all loads strictly after beta to the terminal row.
It contains `gamma`, `delta`, `zeta`, `eta`, and `theta`, but no beta. -/
def betaLaterTerminalPolynomial410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  betaWallWRemainder410 0 gamma delta zeta theta A B C0 * derivative C0 -
    B * derivative (betaWallZRemainder410 0 gamma delta zeta eta A B C0)

/-- Exact beta/later split of the terminal load remainder. -/
theorem betaWallLoadRow410_eq_beta_add_later
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    betaWallWRemainder410 beta gamma delta zeta theta A B C0 *
          derivative C0 -
        B * derivative
          (betaWallZRemainder410 beta gamma delta zeta eta A B C0) =
      betaPureTerminalPolynomial410 beta A B C0 +
        betaLaterTerminalPolynomial410 gamma delta zeta eta theta A B C0 := by
  have hC (x : k) : Polynomial.C x = x • (1 : k[X]) := by
    simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]
  have hW :
      betaWallWRemainder410 beta gamma delta zeta theta A B C0 =
        betaWallWRemainder410 beta 0 0 0 0 A B C0 +
          betaWallWRemainder410 0 gamma delta zeta theta A B C0 := by
    simp only [betaWallWRemainder410, hC]
    module
  have hZ :
      betaWallZRemainder410 beta gamma delta zeta eta A B C0 =
        betaWallZRemainder410 beta 0 0 0 0 A B C0 +
          betaWallZRemainder410 0 gamma delta zeta eta A B C0 := by
    simp only [betaWallZRemainder410]
    module
  rw [hW, hZ, Polynomial.derivative_add]
  simp only [betaPureTerminalPolynomial410,
    betaLaterTerminalPolynomial410]
  ring

/-- The full terminal row is the zero-load row plus the beta face plus all
strictly later faces.  The cancelling loads `alpha`, `epsilon`, and `iota`
do not occur. -/
theorem lowerRow410_eq_zeroLoad_add_beta_add_later
    (alpha beta gamma delta epsilon zeta eta theta iota : k)
    (A B C0 : k[X]) :
    lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
          iota A B C0) B C0 =
      lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
          (zeroLoadZPolynomial410 A B C0) B C0 +
        betaPureTerminalPolynomial410 beta A B C0 +
          betaLaterTerminalPolynomial410 gamma delta zeta eta theta
            A B C0 := by
  rw [lowerRow410_eq_zeroLoad_add_remainder,
    betaWallLoadRow410_eq_beta_add_later]
  abel

/-- On the cubic wall beta disappears identically from the second
invariant; this is the exact remaining constant-fiber equation there. -/
theorem firstIntegralOne410_eq_zero_add_later_of_betaCubicWall
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    firstIntegralOnePolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
        betaLoadOneRest410 gamma delta zeta eta theta A B C0 := by
  rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
    loadCorrectionOnePolynomial410_eq_beta_add_rest,
    betaLoadOnePolynomial410_eq_core, hwall, mul_zero, smul_zero, zero_add]

private def threeDegreeTieBeta410 (d1 d2 d3 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
    (d2 = m ∧ d3 = m)

private theorem threeTerm_degree_tie_beta410
    (P Q R : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hR : R ≠ 0)
    (hsum : P + Q + R = 0) :
    threeDegreeTieBeta410 P.natDegree Q.natDegree R.natDegree
      (max P.natDegree (max Q.natDegree R.natDegree)) := by
  let m := max P.natDegree (max Q.natDegree R.natDegree)
  have hP_le : P.natDegree ≤ m := by dsimp [m]; omega
  have hQ_le : Q.natDegree ≤ m := by dsimp [m]; omega
  have hR_le : R.natDegree ≤ m := by dsimp [m]; omega
  have htop : P.natDegree = m ∨ Q.natDegree = m ∨ R.natDegree = m := by
    dsimp [m]
    omega
  have hcoeff : P.coeff m + Q.coeff m + R.coeff m = 0 := by
    have := congrArg (fun S : k[X] => S.coeff m) hsum
    simpa only [coeff_add, coeff_zero] using this
  by_contra hnot
  change ¬ threeDegreeTieBeta410 P.natDegree Q.natDegree R.natDegree m
    at hnot
  rcases htop with hPm | hQm | hRm
  · have hQlt : Q.natDegree < m := by
      have : Q.natDegree ≠ m := by
        intro h; exact hnot (Or.inl ⟨hPm, h⟩)
      omega
    have hRlt : R.natDegree < m := by
      have : R.natDegree ≠ m := by
        intro h; exact hnot (Or.inr (Or.inl ⟨hPm, h⟩))
      omega
    rw [show P.coeff m = P.leadingCoeff by rw [← hPm, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt hQlt,
      coeff_eq_zero_of_natDegree_lt hRlt, add_zero, add_zero] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP) hcoeff
  · have hPlt : P.natDegree < m := by
      have : P.natDegree ≠ m := by
        intro h; exact hnot (Or.inl ⟨h, hQm⟩)
      omega
    have hRlt : R.natDegree < m := by
      have : R.natDegree ≠ m := by
        intro h; exact hnot (Or.inr (Or.inr ⟨hQm, h⟩))
      omega
    rw [coeff_eq_zero_of_natDegree_lt hPlt,
      show Q.coeff m = Q.leadingCoeff by rw [← hQm, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt hRlt, zero_add, add_zero] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hQ) hcoeff
  · have hPlt : P.natDegree < m := by
      have : P.natDegree ≠ m := by
        intro h; exact hnot (Or.inr (Or.inl ⟨h, hRm⟩))
      omega
    have hQlt : Q.natDegree < m := by
      have : Q.natDegree ≠ m := by
        intro h; exact hnot (Or.inr (Or.inr ⟨h, hRm⟩))
      omega
    rw [coeff_eq_zero_of_natDegree_lt hPlt,
      coeff_eq_zero_of_natDegree_lt hQlt,
      show R.coeff m = R.leadingCoeff by rw [← hRm, coeff_natDegree],
      zero_add, zero_add] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hR) hcoeff

/-- Exact Newton selector intrinsic to the cubic wall.  If `C0 = 0`, the
wall is the binomial ray `3 deg A = 2 deg B`.  Otherwise at least two of
`3 deg A`, `deg A + deg C0`, and `2 deg B` attain the common maximum. -/
theorem betaCubicWall_degree_split
    (A B C0 : k[X]) (hB : B ≠ 0)
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    (C0 = 0 ∧ 3 * A.natDegree = 2 * B.natDegree) ∨
      (C0 ≠ 0 ∧
        threeDegreeTieBeta410 (3 * A.natDegree)
          (A.natDegree + C0.natDegree) (2 * B.natDegree)
          (max (3 * A.natDegree)
            (max (A.natDegree + C0.natDegree) (2 * B.natDegree)))) := by
  have hA : A ≠ 0 := by
    intro hA0
    have hB2 : B ^ 2 = 0 := by
      simpa [betaOneCorePolynomial410, hA0] using hwall
    exact hB (eq_zero_of_pow_eq_zero hB2)
  by_cases hC : C0 = 0
  · left
    refine ⟨hC, ?_⟩
    have hbinomial : (5 : k) • A ^ 3 = (4 : k) • B ^ 2 := by
      simpa [betaOneCorePolynomial410, hC, sub_eq_zero] using hwall
    have hleft : ((5 : k) • A ^ 3).natDegree = 3 * A.natDegree := by
      rw [natDegree_smul _ (by norm_num : (5 : k) ≠ 0), natDegree_pow]
    have hright : ((4 : k) • B ^ 2).natDegree = 2 * B.natDegree := by
      rw [natDegree_smul _ (by norm_num : (4 : k) ≠ 0), natDegree_pow]
    rw [← hleft, ← hright, hbinomial]
  · right
    refine ⟨hC, ?_⟩
    have hsum :
        (5 : k) • A ^ 3 + (-(24 : k)) • (A * C0) +
            (-(4 : k)) • B ^ 2 = 0 := by
      simpa [betaOneCorePolynomial410, sub_eq_add_neg, neg_smul] using hwall
    have htie := threeTerm_degree_tie_beta410
      ((5 : k) • A ^ 3) ((-(24 : k)) • (A * C0))
      ((-(4 : k)) • B ^ 2)
      (smul_ne_zero (by norm_num) (pow_ne_zero 3 hA))
      (smul_ne_zero (by norm_num) (mul_ne_zero hA hC))
      (smul_ne_zero (by norm_num) (pow_ne_zero 2 hB)) hsum
    have hPdeg : ((5 : k) • A ^ 3).natDegree = 3 * A.natDegree := by
      rw [natDegree_smul _ (by norm_num : (5 : k) ≠ 0), natDegree_pow]
    have hQdeg : ((-(24 : k)) • (A * C0)).natDegree =
        A.natDegree + C0.natDegree := by
      rw [natDegree_smul _ (by norm_num : (-(24 : k)) ≠ 0),
        natDegree_mul hA hC]
    have hRdeg : ((-(4 : k)) • B ^ 2).natDegree =
        2 * B.natDegree := by
      rw [natDegree_smul _ (by norm_num : (-(4 : k)) ≠ 0),
        natDegree_pow]
    rw [hPdeg, hQdeg, hRdeg] at htie
    exact htie

/-- Exact surviving packet on the cubic wall. -/
def BetaCubicWallNewtonResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (betaCubicReducedTwoCore410 A C0 = 0 ∨
      (betaCubicReducedTwoCore410 A C0).natDegree = 0 ∨
      (betaCubicReducedTwoCore410 A C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree) ∧
    (betaPureTerminalPolynomial410 beta A B C0 = 0 ∨
      (betaPureTerminalPolynomial410 beta A B C0).natDegree = 0 ∨
      (betaPureTerminalPolynomial410 beta A B C0).natDegree ≤
        max
          (lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
            (zeroLoadZPolynomial410 A B C0) B C0).natDegree
          (betaLaterTerminalPolynomial410 gamma delta zeta eta theta
            A B C0).natDegree)

/-- The other invariant and terminal row exclude their respective unique
beta faces on the cubic wall.  Later loads remain in the displayed degree
competitors. -/
theorem constantIntegral410_betaCubicWall_newton_residual
    (alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hbeta : beta ≠ 0) (hB : B ≠ 0)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hTwo : firstIntegralTwoPolynomial410 0 beta gamma delta zeta eta theta
      A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410 0 beta gamma delta zeta eta theta
      A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
          betaLoadOneRest410 gamma delta zeta eta theta A B C0 = C k1 ∧
      BetaCubicWallNewtonResidual410 beta gamma delta zeta eta theta
        A B C0 := by
  constructor
  · rw [← firstIntegralOne410_eq_zero_add_later_of_betaCubicWall
      beta gamma delta zeta eta theta A B C0 hwall]
    exact hOne
  · constructor
    · have hcoreEq := betaTwoCorePolynomial410_eq_reduced_of_cubicWall
          A B C0 hwall
      by_cases hcore : betaCubicReducedTwoCore410 A C0 = 0
      · exact Or.inl hcore
      · right
        by_cases hdegree : (betaCubicReducedTwoCore410 A C0).natDegree = 0
        · exact Or.inl hdegree
        · right
          by_contra hle
          have hrest :
              (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
                betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree <
                (betaCubicReducedTwoCore410 A C0).natDegree := by
            exact (natDegree_add_le _ _).trans_lt (by omega)
          have heq :
              (7 / 512 * beta : k) • betaCubicReducedTwoCore410 A C0 +
                  (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
                    betaLoadTwoRest410 gamma delta zeta eta theta A B C0) =
                C k2 := by
            rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
              loadCorrectionTwoPolynomial410_eq_beta_add_rest,
              betaLoadTwoPolynomial410_eq_core, hcoreEq] at hTwo
            simpa only [add_assoc, add_left_comm, add_comm] using hTwo
          exact (smul_add_lower_ne_C410
            (7 / 512 * beta) k2 (betaCubicReducedTwoCore410 A C0)
            (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
              betaLoadTwoRest410 gamma delta zeta eta theta A B C0)
            (betaCubicReducedTwoCore410 A C0).natDegree
            (mul_ne_zero (by norm_num) hbeta) hcore (by omega) rfl hrest) heq
    · by_cases hface : betaPureTerminalPolynomial410 beta A B C0 = 0
      · exact Or.inl hface
      · right
        by_cases hdegree :
            (betaPureTerminalPolynomial410 beta A B C0).natDegree = 0
        · exact Or.inl hdegree
        · right
          by_contra hle
          have hrest :
              (lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
                    (zeroLoadZPolynomial410 A B C0) B C0 +
                betaLaterTerminalPolynomial410 gamma delta zeta eta theta
                  A B C0).natDegree <
                (betaPureTerminalPolynomial410 beta A B C0).natDegree := by
            exact (natDegree_add_le _ _).trans_lt (by omega)
          have heq :
              (1 : k) • betaPureTerminalPolynomial410 beta A B C0 +
                  (lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
                      (zeroLoadZPolynomial410 A B C0) B C0 +
                    betaLaterTerminalPolynomial410 gamma delta zeta eta theta
                      A B C0) = C terminal := by
            rw [lowerRow410_eq_zeroLoad_add_beta_add_later] at hLower
            simpa only [one_smul, add_assoc, add_left_comm, add_comm] using hLower
          exact (smul_add_lower_ne_C410 (1 : k) terminal
            (betaPureTerminalPolynomial410 beta A B C0)
            (lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
                (zeroLoadZPolynomial410 A B C0) B C0 +
              betaLaterTerminalPolynomial410 gamma delta zeta eta theta
                A B C0)
            (betaPureTerminalPolynomial410 beta A B C0).natDegree
            one_ne_zero hface (by omega) rfl hrest) heq

end BetaCubicWall410

end Max11DegreeRoutes
