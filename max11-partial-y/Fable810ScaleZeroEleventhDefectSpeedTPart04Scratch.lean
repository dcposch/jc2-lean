import Fable810ScaleZeroEleventhDefectSpeedTPart03Scratch

/-! # Scale-zero eleventh defect for the normalized `(8,10)`, `H = 0` leaf

The tenth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first ten octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, and `h⁷⁷`.  This file
consumes the next unused Keller coefficient of the same monic
octic-decic depression: the degree-`5` Jacobian row is
`6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X' = 0`.  The
corresponding twelfth cleared polynomial defect of weight eighty-four
is likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`84` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`4` residual of
the same monic depression.
-/

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

section DepressedRow810Twelfth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 64000000 in
/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`5` Jacobian coefficient is
exactly `6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X'`. -/
theorem differentialJacobian_coeff_5_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 5 =
      (6 : F) * g.coeff 6 * d (f.coeff 0) +
        (5 : F) * g.coeff 5 * d (f.coeff 1) +
        (4 : F) * g.coeff 4 * d (f.coeff 2) +
        (3 : F) * g.coeff 3 * d (f.coeff 3) +
        (2 : F) * g.coeff 2 * d (f.coeff 4) +
        g.coeff 1 * d (f.coeff 5) -
          f.coeff 1 * d (g.coeff 5) -
          (2 : F) * f.coeff 2 * d (g.coeff 4) -
          (3 : F) * f.coeff 3 * d (g.coeff 3) -
          (4 : F) * f.coeff 4 * d (g.coeff 2) -
          (5 : F) * f.coeff 5 * d (g.coeff 1) -
          (6 : F) * f.coeff 6 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne05_14 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
  have hne05_23 : ((0, 5) : ℕ × ℕ) ≠ (2, 3) := by decide
  have hne05_32 : ((0, 5) : ℕ × ℕ) ≠ (3, 2) := by decide
  have hne05_41 : ((0, 5) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne05_50 : ((0, 5) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne14_23 : ((1, 4) : ℕ × ℕ) ≠ (2, 3) := by decide
  have hne14_32 : ((1, 4) : ℕ × ℕ) ≠ (3, 2) := by decide
  have hne14_41 : ((1, 4) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne14_50 : ((1, 4) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne23_32 : ((2, 3) : ℕ × ℕ) ≠ (3, 2) := by decide
  have hne23_41 : ((2, 3) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne23_50 : ((2, 3) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne32_41 : ((3, 2) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne32_50 : ((3, 2) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne41_50 : ((4, 1) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 5 =
        (6 : F) * g.coeff 6 * d (f.coeff 0) +
          (5 : F) * g.coeff 5 * d (f.coeff 1) +
          (4 : F) * g.coeff 4 * d (f.coeff 2) +
          (3 : F) * g.coeff 3 * d (f.coeff 3) +
          (2 : F) * g.coeff 2 * d (f.coeff 4) +
          g.coeff 1 * d (f.coeff 5) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne05_14, hne05_23, hne05_32, hne05_41, hne05_50]),
        Finset.sum_insert (by simp [hne14_23, hne14_32, hne14_41, hne14_50]),
        Finset.sum_insert (by simp [hne23_32, hne23_41, hne23_50]),
        Finset.sum_insert (by simp [hne32_41, hne32_50]),
        Finset.sum_insert (by simp [hne41_50]),
        Finset.sum_singleton]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder5, hder4, hder3, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 5 =
        f.coeff 1 * d (g.coeff 5) +
          (2 : F) * f.coeff 2 * d (g.coeff 4) +
          (3 : F) * f.coeff 3 * d (g.coeff 3) +
          (4 : F) * f.coeff 4 * d (g.coeff 2) +
          (5 : F) * f.coeff 5 * d (g.coeff 1) +
          (6 : F) * f.coeff 6 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne05_14, hne05_23, hne05_32, hne05_41, hne05_50]),
        Finset.sum_insert (by simp [hne14_23, hne14_32, hne14_41, hne14_50]),
        Finset.sum_insert (by simp [hne23_32, hne23_41, hne23_50]),
        Finset.sum_insert (by simp [hne32_41, hne32_50]),
        Finset.sum_insert (by simp [hne41_50]),
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
    have hder4 : f.derivative.coeff 4 = (5 : F) * f.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder5 : f.derivative.coeff 5 = (6 : F) * f.coeff 6 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2, hder3, hder4, hder5]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 64000000 in
theorem muResidual810_deriv_zero
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0)
    (hrow8 : (9 : F) * L * d G0 + (8 : F) * P * d F0 +
        (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A -
        F0 * d P - (2 : F) * E0 * d Q -
        (3 : F) * D0 * d R - (4 : F) * C0 * d S0 -
        (5 : F) * B * d T0 - (6 : F) * A * d U0 -
        (8 : F) * d W0 = 0)
    (hrow7 : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0)
    (hrow : (6 : F) * R * d G0 + (5 : F) * S0 * d F0 +
        (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + W0 * d B -
        F0 * d S0 - (2 : F) * E0 * d T0 -
        (3 : F) * D0 * d U0 - (4 : F) * C0 * d V0 -
        (5 : F) * B * d W0 - (6 : F) * A * d X0 = 0) :
    d (muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h21 : d (21 : F) = 0 := d.map_natCast 21
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h315 : d (315 : F) = 0 := d.map_natCast 315
  have h512 : d (512 : F) = 0 := d.map_natCast 512
  have h1024 : d (1024 : F) = 0 := d.map_natCast 1024
  have h2048 : d (2048 : F) = 0 := d.map_natCast 2048
  have h32768 : d (32768 : F) = 0 := d.map_natCast 32768
  have h77 : d (77 : F) = 0 := d.map_natCast 77
  have h105 : d (105 : F) = 0 := d.map_natCast 105
  have h8192 : d (8192 : F) = 0 := d.map_natCast 8192
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_inv, h4]
  have h18 : d (1 / 8 : F) = 0 := by
    simp [Derivation.leibniz_inv, h8]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h58 : d (5 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h5]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h15128 : d (15 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h15]
  have h5128 : d (5 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h5]
  have h7128 : d (7 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h7]
  have h9128 : d (9 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h9]
  have h1564 : d (15 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h15]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h9]
  have h764 : d (7 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h7]
  have h35512 : d (35 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h35]
  have h211024 : d (21 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h21]
  have h631024 : d (63 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h63]
  have h31532768 : d (315 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h315]
  have h778192 : d (77 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h77]
  have h3158192 : d (315 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h315]
  have h1051024 : d (105 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h105]
  have h63512 : d (63 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h63]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h3]
  have h352048 : d (35 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h35]

  have h13 : d (13 : F) = 0 := d.map_natCast 13
  have h17 : d (17 : F) = 0 := d.map_natCast 17
  have h75 : d (75 : F) = 0 := d.map_natCast 75
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h85 : d (85 : F) = 0 := d.map_natCast 85
  have h189 : d (189 : F) = 0 := d.map_natCast 189
  have h441 : d (441 : F) = 0 := d.map_natCast 441
  have h455 : d (455 : F) = 0 := d.map_natCast 455
  have h1071 : d (1071 : F) = 0 := d.map_natCast 1071
  have h4096 : d (4096 : F) = 0 := d.map_natCast 4096
  have h16384 : d (16384 : F) = 0 := d.map_natCast 16384
  have h65536n : d (65536 : F) = 0 := d.map_natCast 65536
  have h44132768 : d (441 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h441]
  have h44165536 : d (441 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, h441]
  have h4558192 : d (455 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h455]
  have h107116384 : d (1071 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, h1071]
  have h1894096 : d (189 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h189]
  have h851024 : d (85 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h85]
  have h751024 : d (75 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h75]
  have h811024 : d (81 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h81]
  have h932 : d (9 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h9]
  have h732 : d (7 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h7]
  have h21128 : d (21 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h21]
  have h35128 : d (35 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h35]
  have h771024 : d (77 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h77]

  have h256 : d (256 : F) = 0 := d.map_natCast 256
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h225 : d (225 : F) = 0 := d.map_natCast 225
  have h385 : d (385 : F) = 0 := d.map_natCast 385
  have h945 : d (945 : F) = 0 := d.map_natCast 945
  have h45256 : d (45 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h45]
  have h452048 : d (45 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h45]
  have h1894096' : d (189 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h189]
  have h94532768 : d (945 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h945]
  have h38565536 : d (385 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, h385]
  have h2251024 : d (225 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h225]
  have h7256 : d (7 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h7]
  have h3858192 : d (385 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h385]
  have h1532 : d (15 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h15]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have h35256 : d (35 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h35]
  have _hiota := hiota
  have hPderiv : d P = (5 / 4 : F) * d A := by
    have halpha' : d P - (5 / 4 : F) * d A = 0 := by
      simpa [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 4 : F) * d B + (9 / 8 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
      simpa [betaResidual810, map_sub, Derivation.leibniz, h54, h98, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz]
    ring
  have hsqE : d (E0 * E0) = (2 : F) * E0 * d E0 := by
    simp [Derivation.leibniz]
    ring
  have hcubC : d (C0 ^ 3) = (3 : F) * C0 ^ 2 * d C0 := by
    have h2C : d (C0 ^ 2) = (2 : F) * C0 * d C0 := by
      simpa [pow_two] using hsqC
    simp [pow_three, Derivation.leibniz, h2C]
    ring
  have hquarB : d (B ^ 4) = (4 : F) * B ^ 3 * d B := by
    have : B ^ 4 = B ^ 3 * B := by ring
    rw [this]
    simp [Derivation.leibniz, hcubB]
    ring
  have hsextA : d (A ^ 6) = (6 : F) * A ^ 5 * d A := by
    have : A ^ 6 = A ^ 5 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquint]
    ring
  have hgamma_id :
      d (gammaResidual810 L A B C0 P R) =
        d R - ((5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
          (9 / 8 : F) * L * d B + alphaResidual810 A P * d A) := by
    simp only [gammaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h532, hL, halpha, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hRderiv' :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + alphaResidual810 A P * d A := by
    linear_combination hgamma_id.symm + hgamma
  have hRderiv :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + (P - (5 / 4 : F) * A) * d A := by
    rw [hRderiv']
    simp only [alphaResidual810]
  have hdelta_id :
      d (deltaResidual810 L A B C0 D0 P Q S0) =
        d S0 - ((5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
          alphaResidual810 A P * d B +
          (7 / 8 : F) * betaResidual810 L A B Q * d A +
          (5 / 16 : F) * (A * d B + B * d A) +
          (9 / 64 : F) * L * A * d A) := by
    unfold deltaResidual810
    simp [map_sub, map_add, Derivation.leibniz, h54, h98, h78, h516, h964,
      h9128, hL, halpha, hbeta, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hSderiv' :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        alphaResidual810 A P * d B +
        (7 / 8 : F) * betaResidual810 L A B Q * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    linear_combination hdelta_id.symm + hdelta
  have hSderiv :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        (P - (5 / 4 : F) * A) * d B +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    rw [hSderiv']
    simp [alphaResidual810, betaResidual810]
  have hepsilon_id :
      d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) =
        d T0 - ((5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
          (5 / 16 : F) * (A * d C0 + C0 * d A) -
          (15 / 128 : F) * A ^ 2 * d A +
          L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
          alphaResidual810 A P * d C0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d B +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A) := by
    simp only [epsilonResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h532, h516, h5128, h15128, h964, hL, halpha, hbeta,
      hgamma, zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hcub]
    ring
  have hTderiv' :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        alphaResidual810 A P * d C0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d B +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A := by
    linear_combination hepsilon_id.symm + hepsilon
  have hTderiv :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        (P - (5 / 4 : F) * A) * d C0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d B +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d A := by
    rw [hTderiv']
    simp [gammaResidual810, alphaResidual810, betaResidual810]
  have hzeta_id :
      d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) =
        d U0 - ((5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
          alphaResidual810 A P * d D0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
          (5 / 16 : F) * (A * d D0 + D0 * d A) +
          (5 / 16 : F) * (B * d C0 + C0 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
          (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
          (63 / 1024 : F) * L * A ^ 2 * d A +
          (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
          (9 / 64 : F) * L * B * d B) := by
    simp only [zetaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h58, h516, h7128, h15128, h211024, h964, h9128, hL,
      halpha, hbeta, hgamma, hdelta, zero_mul, add_zero, mul_zero, pow_two,
      hsq, hsqB, hcub]
    ring
  have hUderiv' :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        alphaResidual810 A P * d D0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    linear_combination hzeta_id.symm + hzeta
  have hUderiv :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        (P - (5 / 4 : F) * A) * d D0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d C0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d B +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A *
          d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    rw [hUderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810]
  have heta_id :
      d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) =
        d V0 - ((5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
          alphaResidual810 A P * d E0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
          (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
          (5 / 16 : F) * (A * d E0 + E0 * d A) +
          (5 / 16 : F) * (B * d D0 + D0 * d B) +
          (5 / 16 : F) * C0 * d C0 -
          (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
          (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
          (35 / 512 : F) * A ^ 3 * d A +
          (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
          (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
          (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
          (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A) := by
    simp only [etaResidual810, map_sub, map_add, Derivation.leibniz, h12,
      h14, h18, h54, h98, h78, h34, h58, h516, h532, h15128, h352048, h964,
      h631024, h764, h332, hL, halpha, hbeta, hgamma, hdelta, hepsilon,
      zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hsqC, hcub, hquar]
    ring
  have hVderiv' :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        alphaResidual810 A P * d E0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
        (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
        (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A := by
    linear_combination heta_id.symm + heta
  have hVderiv :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        (P - (5 / 4 : F) * A) * d E0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d D0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d C0 +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d B +
        (1 / 2 : F) * (T0 - ((5 / 4 : F) * E0 + (5 / 32 : F) * B ^ 2 +
          (5 / 16 : F) * A * C0 - (5 / 128 : F) * A ^ 3 +
          L * ((9 / 8 : F) * D0 + (9 / 64 : F) * A * B) +
          (P - (5 / 4 : F) * A) * C0 +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * B +
          (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
            (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A)) * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) *
          (A * d B + B * d A) -
        (3 / 16 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A * d A := by
    rw [hVderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810]
  have _htheta := htheta
  have hWderiv :
      d W0 = (9 / 8 : F) * L * d G0 + P * d F0 +
        (7 / 8 : F) * Q * d E0 + (3 / 4 : F) * R * d D0 +
        (5 / 8 : F) * S0 * d C0 + (1 / 2 : F) * T0 * d B +
        (3 / 8 : F) * U0 * d A -
        (1 / 8 : F) * F0 * d P - (1 / 4 : F) * E0 * d Q -
        (3 / 8 : F) * D0 * d R - (1 / 2 : F) * C0 * d S0 -
        (5 / 8 : F) * B * d T0 - (3 / 4 : F) * A * d U0 := by
    linear_combination (-1 / 8 : F) * hrow8
  have hXderiv :
      d X0 = P * d G0 + (7 / 8 : F) * Q * d F0 +
        (3 / 4 : F) * R * d E0 + (5 / 8 : F) * S0 * d D0 +
        (1 / 2 : F) * T0 * d C0 + (3 / 8 : F) * U0 * d B +
        (1 / 4 : F) * V0 * d A -
        (1 / 8 : F) * F0 * d Q - (1 / 4 : F) * E0 * d R -
        (3 / 8 : F) * D0 * d S0 - (1 / 2 : F) * C0 * d T0 -
        (5 / 8 : F) * B * d U0 - (3 / 4 : F) * A * d V0 := by
    linear_combination (-1 / 8 : F) * hrow7
  have hrow_red := hrow
  rw [hWderiv, hXderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow_red
  simp only [muResidual810, halpha, hbeta, hgamma, hdelta, hepsilon,
    hzeta, heta, map_sub, map_add, Derivation.leibniz,
    h12, h14, h18, h38, h54, h98, h78, h34, h58, h516, h316, h532, h15128,
    h5128, h7128, h9128, h1564, h964, h764, h35512, h211024, h631024,
    h31532768, h778192, h3158192, h1051024, h63512, h332, h352048, hL,
    h44132768, h44165536, h4558192, h107116384, h1894096, h851024, h751024,
    h811024, h932, h732, h21128, h35128, h771024, h45256, h452048,
    h1894096', h94532768, h38565536, h2251024, h7256, h3858192, h1532,
    h116, h35256, zero_mul, add_zero, mul_zero, pow_two, hsq,
    hsqB, hsqC, hsqD, hsqE, hcub, hcubB, hcubC, hquar, hquarB, hquint,
    hsextA]
  simp only [alphaResidual810, betaResidual810, gammaResidual810,
    deltaResidual810, epsilonResidual810, zetaResidual810, etaResidual810]
  simp only [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv, hVderiv]
  linear_combination (1 / 8 : F) * hrow_red

end DepressedRow810Twelfth


end Max11DegreeRoutes
end
