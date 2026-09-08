import Sol610ScaleTwoAlignedFourteenthSquareSourceScratch

/-! # The weight-seventy tail recurrence for aligned `(6,10)`

The degree-one Keller row is the fourth negative Laurent-tail row of the
depressed sextic/decic Faber expansion.  Its raw coefficient is corrected by
the already-consumed weight-55 and weight-60 tails.  This file records the
exact coefficient and proves the small differential recurrence independently
of the later source clearing.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RawFourthTail610

variable {F : Type*} [Field F] [CharZero F]

def rawFourthTailPure610 (A B C0 D0 E0 : F) : F :=
  -(65 / 19683 : F) * A ^ 7 + (70 / 2187 : F) * A ^ 5 * C0 +
  (175 / 2187 : F) * A ^ 4 * B ^ 2 - (35 / 729 : F) * A ^ 4 * E0 -
  (140 / 729 : F) * A ^ 3 * B * D0 -
  (70 / 729 : F) * A ^ 3 * C0 ^ 2 -
  (70 / 243 : F) * A ^ 2 * B ^ 2 * C0 +
  (20 / 81 : F) * A ^ 2 * C0 * E0 +
  (10 / 81 : F) * A ^ 2 * D0 ^ 2 -
  (35 / 729 : F) * A * B ^ 4 +
  (20 / 81 : F) * A * B ^ 2 * E0 +
  (40 / 81 : F) * A * B * C0 * D0 +
  (20 / 243 : F) * A * C0 ^ 3 - (5 / 27 : F) * A * E0 ^ 2 +
  (20 / 243 : F) * B ^ 3 * D0 +
  (10 / 81 : F) * B ^ 2 * C0 ^ 2 -
  (10 / 27 : F) * B * D0 * E0 - (5 / 27 : F) * C0 ^ 2 * E0 -
  (5 / 27 : F) * C0 * D0 ^ 2

def rawFourthTailLBlock610 (A B C0 D0 E0 : F) : F :=
  (21 / 512 : F) * A ^ 5 * B - (15 / 256 : F) * A ^ 4 * D0 -
  (15 / 64 : F) * A ^ 3 * B * C0 -
  (15 / 128 : F) * A ^ 2 * B ^ 3 +
  (9 / 32 : F) * A ^ 2 * B * E0 +
  (9 / 32 : F) * A ^ 2 * C0 * D0 +
  (9 / 32 : F) * A * B ^ 2 * D0 +
  (9 / 32 : F) * A * B * C0 ^ 2 - (3 / 8 : F) * A * D0 * E0 +
  (3 / 32 : F) * B ^ 3 * C0 - (3 / 8 : F) * B * C0 * E0 -
  (3 / 16 : F) * B * D0 ^ 2 - (3 / 16 : F) * C0 ^ 2 * D0

def rawFourthTailAlphaBlock610 (A B C0 D0 E0 : F) : F :=
  (44 / 6561 : F) * A ^ 6 - (40 / 729 : F) * A ^ 4 * C0 -
  (80 / 729 : F) * A ^ 3 * B ^ 2 + (20 / 243 : F) * A ^ 3 * E0 +
  (20 / 81 : F) * A ^ 2 * B * D0 +
  (10 / 81 : F) * A ^ 2 * C0 ^ 2 +
  (20 / 81 : F) * A * B ^ 2 * C0 - (8 / 27 : F) * A * C0 * E0 -
  (4 / 27 : F) * A * D0 ^ 2 + (5 / 243 : F) * B ^ 4 -
  (4 / 27 : F) * B ^ 2 * E0 - (8 / 27 : F) * B * C0 * D0 -
  (4 / 81 : F) * C0 ^ 3 + (2 / 9 : F) * E0 ^ 2

def rawFourthTailBetaBlock610 (A B C0 D0 E0 : F) : F :=
  -(6545 / 186624 : F) * A ^ 4 * B +
  (385 / 7776 : F) * A ^ 3 * D0 +
  (385 / 2592 : F) * A ^ 2 * B * C0 +
  (385 / 7776 : F) * A * B ^ 3 - (35 / 216 : F) * A * B * E0 -
  (35 / 216 : F) * A * C0 * D0 - (35 / 432 : F) * B ^ 2 * D0 -
  (35 / 432 : F) * B * C0 ^ 2 + (7 / 36 : F) * D0 * E0

def rawFourthTailDeltaBlock610 (A B C0 D0 E0 : F) : F :=
  -(455 / 7776 : F) * A ^ 3 * B + (35 / 432 : F) * A ^ 2 * D0 +
  (35 / 216 : F) * A * B * C0 + (35 / 1296 : F) * B ^ 3 -
  (5 / 36 : F) * B * E0 - (5 / 36 : F) * C0 * D0

def rawFourthTailEpsilonBlock610 (A B C0 D0 E0 : F) : F :=
  -(7 / 243 : F) * A ^ 4 + (4 / 27 : F) * A ^ 2 * C0 +
  (4 / 27 : F) * A * B ^ 2 - (2 / 9 : F) * A * E0 -
  (2 / 9 : F) * B * D0 - (1 / 9 : F) * C0 ^ 2

def rawFourthTailEtaBlock610 (A B C0 E0 : F) : F :=
  (5 / 81 : F) * A ^ 3 - (2 / 9 : F) * A * C0 -
  (1 / 9 : F) * B ^ 2 + (1 / 3 : F) * E0

def rawFourthTailThetaBlock610 (A B D0 : F) : F :=
  -(5 / 36 : F) * A * B + (1 / 6 : F) * D0

def rawFourthTailZetaBlock610 (A B C0 D0 : F) : F :=
  (3 / 16 : F) * A ^ 2 * B - (1 / 4 : F) * A * D0 -
  (1 / 4 : F) * B * C0

/-- Coefficient of `Y⁻⁴` in the formal sum
`f^(5/3) + L f^(3/2) + α f^(4/3) + β f^(7/6) + γ f +
δ f^(5/6) + ε f^(2/3) + ζ f^(1/2) + η f^(1/3) + θ f^(1/6)` for
`f = Y⁶ + A Y⁴ + B Y³ + C Y² + D Y + E`. -/
def rawFourthTailCoefficient610
    (L A B C0 D0 E0 alpha beta delta epsilon zeta eta theta : F) : F :=
  rawFourthTailPure610 A B C0 D0 E0 +
  L * rawFourthTailLBlock610 A B C0 D0 E0 +
  alpha * rawFourthTailAlphaBlock610 A B C0 D0 E0 +
  beta * rawFourthTailBetaBlock610 A B C0 D0 E0 +
  delta * rawFourthTailDeltaBlock610 A B C0 D0 E0 +
  epsilon * rawFourthTailEpsilonBlock610 A B C0 D0 E0 +
  eta * rawFourthTailEtaBlock610 A B C0 E0 +
  theta * rawFourthTailThetaBlock610 A B D0 +
  zeta * rawFourthTailZetaBlock610 A B C0 D0

/-- The canonical weight-fourteen residual: the raw fourth tail plus
`B/6` times the first tail and `A/3` times the second tail. -/
def fourteenthResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  rawFourthTailCoefficient610 L A B C0 D0 E0
      (alphaResidual610 A P) (betaResidual610 L A B Q)
      (deltaResidual610 L A B C0 D0 P Q S0)
      (epsilonResidual610 L A B C0 D0 E0 P Q R T0)
      (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0)
      (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0)
      (thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) +
    (1 / 6 : F) * B *
      kappaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 +
    (1 / 3 : F) * A *
      lambdaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0

end RawFourthTail610

section FourthTailDifferential610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- Abstract fourth-tail recurrence.  The hypotheses `hfirst` and `hsecond`
are precisely the already-consumed degree-four and degree-three rows; `hnext`
is the new degree-one row after the polynomial part has been removed. -/
theorem fourthTailCorrected_deriv_zero610
    (d : Derivation k F F) (A B c1 c2 c4 : F)
    (hfirst : (6 : F) * d c1 = 0)
    (hsecond : (6 : F) * d c2 = 0)
    (hnext :
      (6 : F) * d c4 + d B * c1 + (3 : F) * B * d c1 +
        (2 : F) * d A * c2 + (4 : F) * A * d c2 = 0) :
    d (c4 + (1 / 6 : F) * B * c1 + (1 / 3 : F) * A * c2) = 0 := by
  have h6ne : (6 : F) ≠ 0 := by norm_num
  have hdc1 : d c1 = 0 := by
    exact (mul_eq_zero.mp hfirst).resolve_left h6ne
  have hdc2 : d c2 = 0 := by
    exact (mul_eq_zero.mp hsecond).resolve_left h6ne
  have h6d : d (6 : F) = 0 := d.map_natCast 6
  have h3d : d (3 : F) = 0 := d.map_natCast 3
  have h16 : d (1 / 6 : F) = 0 := by
    simp [Derivation.leibniz_inv, h6d]
  have h13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_inv, h3d]
  have hnext' :
      (6 : F) * d c4 + d B * c1 + (2 : F) * d A * c2 = 0 := by
    rw [hdc1, hdc2] at hnext
    simpa only [mul_zero, add_zero] using hnext
  simp only [map_add, Derivation.leibniz, h16, h13, zero_mul, zero_add,
    hdc1, hdc2, mul_zero, add_zero]
  linear_combination (1 / 6 : F) * hnext'

end FourthTailDifferential610

#print axioms fourthTailCorrected_deriv_zero610

end Max11DegreeRoutes
