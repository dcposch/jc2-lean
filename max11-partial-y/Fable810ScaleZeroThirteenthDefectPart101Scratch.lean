import Grok810ScaleTwoFourteenthFaceScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 1 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000


/-! ## Literal next Keller coefficient -/

/-- The fourteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the twelfth-defect
packet start at degree `3`. -/
theorem fableScaleZero_fourteenthCoefficientJacobianRow_raw_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  exact fourteenthCoefficientJacobianRow_810 hp hq hjac


end Max11DegreeRoutes
end
/-! Part 20 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section DepressedRow810Fourteenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]


/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`3` Jacobian coefficient is
exactly `4 T G' + 3 U F' + 2 V E' + W D'
- F U' - 2 E V' - 3 D W' - 4 C X'`. -/
theorem differentialJacobian_coeff_3_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 3 =
      (4 : F) * g.coeff 4 * d (f.coeff 0) +
        (3 : F) * g.coeff 3 * d (f.coeff 1) +
        (2 : F) * g.coeff 2 * d (f.coeff 2) +
        g.coeff 1 * d (f.coeff 3) -
          f.coeff 1 * d (g.coeff 3) -
          (2 : F) * f.coeff 2 * d (g.coeff 2) -
          (3 : F) * f.coeff 3 * d (g.coeff 1) -
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (3 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1),
        (3, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne03_12 : ((0, 3) : ℕ × ℕ) ≠ (1, 2) := by decide
  have hne03_21 : ((0, 3) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne03_30 : ((0, 3) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne12_21 : ((1, 2) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne12_30 : ((1, 2) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne21_30 : ((2, 1) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 3 =
        (4 : F) * g.coeff 4 * d (f.coeff 0) +
          (3 : F) * g.coeff 3 * d (f.coeff 1) +
          (2 : F) * g.coeff 2 * d (f.coeff 2) +
          g.coeff 1 * d (f.coeff 3) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]),
        Finset.sum_singleton]
      ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder3, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 3 =
        f.coeff 1 * d (g.coeff 3) +
          (2 : F) * f.coeff 2 * d (g.coeff 2) +
          (3 : F) * f.coeff 3 * d (g.coeff 1) +
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]),
        Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder0, hder1, hder2, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring


end DepressedRow810Fourteenth
end Max11DegreeRoutes
end
/-! Part 2 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FourteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 16000000 in
/-- First residual of the degree-`3` row.  Its exactness certificate
uses the degree-`5` and degree-`6` rows again, with the multipliers
`-(1/16) A` and `-(1/16) B`. -/
def xiResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 8 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * D0
    - (1 / 16 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * A * B
    + (1 / 4 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * E0
    - (1 / 8 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A * C0
    - (1 / 16 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * B ^ 2
    + (1 / 32 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A ^ 3
    + (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * F0
    - (9 / 64 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A * D0
    - (3 / 16 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * B * C0
    + (15 / 128 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A ^ 2 * B
    + (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * G0
    - (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * E0
    - (3 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B * D0
    - (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * C0 ^ 2
    + (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 2 * C0
    + (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * B ^ 2
    - (3 / 128 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 4
    - (5 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * F0
    - (5 / 32 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B * E0
    - (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * C0 * D0
    + (105 / 1024 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 2 * D0
    + (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * B * C0
    + (5 / 128 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B ^ 3
    - (165 / 2048 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 3 * B
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * B * F0
    - (3 / 16 : F) * gammaResidual810 L A B C0 P R * C0 * E0
    + (9 / 128 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * E0
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * D0 ^ 2
    + (21 / 128 : F) * gammaResidual810 L A B C0 P R * A * B * D0
    + (3 / 32 : F) * gammaResidual810 L A B C0 P R * A * C0 ^ 2
    + (3 / 32 : F) * gammaResidual810 L A B C0 P R * B ^ 2 * C0
    - (15 / 256 : F) * gammaResidual810 L A B C0 P R * A ^ 3 * C0
    - (45 / 512 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * B ^ 2
    + (9 / 1024 : F) * gammaResidual810 L A B C0 P R * A ^ 5
    - (7 / 64 : F) * betaResidual810 L A B Q * C0 * F0
    + (35 / 1024 : F) * betaResidual810 L A B Q * A ^ 2 * F0
    - (7 / 64 : F) * betaResidual810 L A B Q * D0 * E0
    + (21 / 256 : F) * betaResidual810 L A B Q * A * B * E0
    + (49 / 512 : F) * betaResidual810 L A B Q * A * C0 * D0
    + (49 / 1024 : F) * betaResidual810 L A B Q * B ^ 2 * D0
    - (231 / 8192 : F) * betaResidual810 L A B Q * A ^ 3 * D0
    + (7 / 128 : F) * betaResidual810 L A B Q * B * C0 ^ 2
    - (189 / 2048 : F) * betaResidual810 L A B Q * A ^ 2 * B * C0
    - (63 / 2048 : F) * betaResidual810 L A B Q * A * B ^ 3
    + (357 / 16384 : F) * betaResidual810 L A B Q * A ^ 4 * B
    + (7245 / 524288 : F) * L * A ^ 5 * B
    - (4725 / 262144 : F) * L * A ^ 4 * D0
    - (315 / 4096 : F) * L * A ^ 3 * B * C0
    + (189 / 8192 : F) * L * A ^ 3 * F0
    - (315 / 8192 : F) * L * A ^ 2 * B ^ 3
    + (315 / 4096 : F) * L * A ^ 2 * B * E0
    + (693 / 8192 : F) * L * A ^ 2 * C0 * D0
    + (693 / 8192 : F) * L * A * B ^ 2 * D0
    + (189 / 2048 : F) * L * A * B * C0 ^ 2
    - (9 / 128 : F) * L * A * B * G0
    - (45 / 512 : F) * L * A * C0 * F0
    - (45 / 512 : F) * L * A * D0 * E0
    + (63 / 2048 : F) * L * B ^ 3 * C0
    - (45 / 1024 : F) * L * B ^ 2 * F0
    - (27 / 256 : F) * L * B * C0 * E0
    - (27 / 512 : F) * L * B * D0 ^ 2
    - (63 / 1024 : F) * L * C0 ^ 2 * D0
    + (9 / 64 : F) * L * D0 * G0
    + (9 / 64 : F) * L * E0 * F0
    - (165 / 65536 : F) * A ^ 7
    + (385 / 16384 : F) * A ^ 5 * C0
    + (1925 / 32768 : F) * A ^ 4 * B ^ 2
    - (245 / 8192 : F) * A ^ 4 * E0
    - (525 / 4096 : F) * A ^ 3 * B * D0
    - (35 / 512 : F) * A ^ 3 * C0 ^ 2
    + (5 / 128 : F) * A ^ 3 * G0
    - (105 / 512 : F) * A ^ 2 * B ^ 2 * C0
    + (135 / 1024 : F) * A ^ 2 * B * F0
    + (75 / 512 : F) * A ^ 2 * C0 * E0
    + (75 / 1024 : F) * A ^ 2 * D0 ^ 2
    - (35 / 1024 : F) * A * B ^ 4
    + (75 / 512 : F) * A * B ^ 2 * E0
    + (165 / 512 : F) * A * B * C0 * D0
    + (15 / 256 : F) * A * C0 ^ 3
    - (5 / 32 : F) * A * C0 * G0
    - (5 / 32 : F) * A * D0 * F0
    - (5 / 64 : F) * A * E0 ^ 2
    + (55 / 1024 : F) * B ^ 3 * D0
    + (45 / 512 : F) * B ^ 2 * C0 ^ 2
    - (5 / 64 : F) * B ^ 2 * G0
    - (25 / 128 : F) * B * C0 * F0
    - (25 / 128 : F) * B * D0 * E0
    - (15 / 128 : F) * C0 ^ 2 * E0
    - (15 / 128 : F) * C0 * D0 ^ 2
    + (5 / 16 : F) * E0 * G0
    + (5 / 32 : F) * F0 ^ 2


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
