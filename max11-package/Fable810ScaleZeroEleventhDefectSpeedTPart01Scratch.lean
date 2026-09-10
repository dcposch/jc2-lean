import Grok810ScaleZeroTenthDefectScratch

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

set_option maxHeartbeats 64000000 in
/-- The twelfth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the tenth-defect
packet start at degree `5`. -/
theorem fableScaleZero_twelfthCoefficientJacobianRow_raw_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

section Depression810TwelfthClearing

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 64000000 in
/-- First residual of the degree-`5` row. -/
def muResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 8 : F) * W0 * B
    - (1 / 8 : F) * alphaResidual810 A P * B * F0
    + (1 / 4 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * C0
    - (3 / 32 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A ^ 2
    + (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * D0
    - (9 / 32 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A * B
    + (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * E0
    + (1 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 3
    - (1 / 4 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * C0
    - (3 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B ^ 2
    + (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * F0
    + (45 / 256 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 2 * B
    - (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * D0
    - (5 / 16 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B * C0
    + (3 / 4 : F) * gammaResidual810 L A B C0 P R * G0
    - (45 / 2048 : F) * gammaResidual810 L A B C0 P R * A ^ 4
    + (15 / 128 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * C0
    + (9 / 64 : F) * gammaResidual810 L A B C0 P R * A * B ^ 2
    - (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * E0
    - (9 / 32 : F) * gammaResidual810 L A B C0 P R * B * D0
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * C0 ^ 2
    - (189 / 4096 : F) * betaResidual810 L A B Q * A ^ 3 * B
    + (63 / 1024 : F) * betaResidual810 L A B Q * A ^ 2 * D0
    + (35 / 256 : F) * betaResidual810 L A B Q * A * B * C0
    - (7 / 64 : F) * betaResidual810 L A B Q * A * F0
    + (7 / 256 : F) * betaResidual810 L A B Q * B ^ 3
    - (7 / 32 : F) * betaResidual810 L A B Q * B * E0
    - (7 / 64 : F) * betaResidual810 L A B Q * C0 * D0
    - (945 / 32768 : F) * L * A ^ 4 * B
    + (315 / 8192 : F) * L * A ^ 3 * D0
    + (63 / 512 : F) * L * A ^ 2 * B * C0
    - (63 / 1024 : F) * L * A ^ 2 * F0
    + (189 / 4096 : F) * L * A * B ^ 3
    - (9 / 64 : F) * L * A * B * E0
    - (63 / 512 : F) * L * A * C0 * D0
    - (81 / 1024 : F) * L * B ^ 2 * D0
    - (9 / 128 : F) * L * B * C0 ^ 2
    + (9 / 64 : F) * L * C0 * F0
    + (9 / 64 : F) * L * D0 * E0
    + (385 / 65536 : F) * A ^ 6
    - (385 / 8192 : F) * A ^ 4 * C0
    - (105 / 1024 : F) * A ^ 3 * B ^ 2
    + (35 / 512 : F) * A ^ 3 * E0
    + (225 / 1024 : F) * A ^ 2 * B * D0
    + (105 / 1024 : F) * A ^ 2 * C0 ^ 2
    - (15 / 128 : F) * A ^ 2 * G0
    + (15 / 64 : F) * A * B ^ 2 * C0
    - (35 / 128 : F) * A * B * F0
    - (15 / 64 : F) * A * C0 * E0
    - (15 / 128 : F) * A * D0 ^ 2
    + (45 / 2048 : F) * B ^ 4
    - (5 / 32 : F) * B ^ 2 * E0
    - (35 / 128 : F) * B * C0 * D0
    - (5 / 128 : F) * C0 ^ 3
    + (5 / 16 : F) * C0 * G0
    + (5 / 16 : F) * D0 * F0
    + (5 / 32 : F) * E0 ^ 2

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk01
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    (203408205 : F[X]) * a7 ^ 12
    - (801115392 : F[X]) * h ^ 6 * a7 ^ 10 * b8
    - (199709874 : F[X]) * h ^ 7 * a7 ^ 11 * Polynomial.C lambda
    - (1502091360 : F[X]) * h ^ 8 * a7 ^ 10 * a6
    + (801115392 : F[X]) * h ^ 14 * a7 ^ 9 * b7
    + (8240044032 : F[X]) * h ^ 14 * a7 ^ 8 * a6 * b8
    + (2253137040 : F[X]) * h ^ 15 * a7 ^ 9 * a6 * Polynomial.C lambda
    + (1573619520 : F[X]) * h ^ 16 * a7 ^ 9 * a5
    + (1287506880 : F[X]) * h ^ 16 * a7 ^ 8 * a6 ^ 2
    - (797423616 : F[X]) * h ^ 22 * a7 ^ 8 * b6

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk02 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (7442620416 : F[X]) * h ^ 22 * a7 ^ 7 * a6 * b7
    - (8505851904 : F[X]) * h ^ 22 * a7 ^ 7 * a5 * b8
    - (29770481664 : F[X]) * h ^ 22 * a7 ^ 6 * a6 ^ 2 * b8
    - (2317512384 : F[X]) * h ^ 23 * a7 ^ 8 * a5 * Polynomial.C lambda
    - (9270049536 : F[X]) * h ^ 23 * a7 ^ 7 * a6 ^ 2 * Polynomial.C lambda
    - (1661299200 : F[X]) * h ^ 24 * a7 ^ 8 * a4
    - (1329039360 : F[X]) * h ^ 24 * a7 ^ 7 * a6 * a5
    + (12404367360 : F[X]) * h ^ 24 * a7 ^ 6 * a6 ^ 3
    + (787578880 : F[X]) * h ^ 30 * a7 ^ 7 * b5
    + (6615662592 : F[X]) * h ^ 30 * a7 ^ 6 * a6 * b6

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk03 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (7718273024 : F[X]) * h ^ 30 * a7 ^ 6 * a5 * b7
    + (8820883456 : F[X]) * h ^ 30 * a7 ^ 6 * a4 * b8
    + (23154819072 : F[X]) * h ^ 30 * a7 ^ 5 * a6 ^ 2 * b7
    + (52925300736 : F[X]) * h ^ 30 * a7 ^ 5 * a6 * a5 * b8
    + (44104417280 : F[X]) * h ^ 30 * a7 ^ 4 * a6 ^ 3 * b8
    + (2392270848 : F[X]) * h ^ 31 * a7 ^ 7 * a4 * Polynomial.C lambda
    + (16745895936 : F[X]) * h ^ 31 * a7 ^ 6 * a6 * a5 * Polynomial.C lambda
    + (16745895936 : F[X]) * h ^ 31 * a7 ^ 5 * a6 ^ 3 * Polynomial.C lambda
    + (1772052480 : F[X]) * h ^ 32 * a7 ^ 7 * a3
    - (37213102080 : F[X]) * h ^ 32 * a7 ^ 5 * a6 ^ 2 * a5

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk04 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (31010918400 : F[X]) * h ^ 32 * a7 ^ 4 * a6 ^ 4
    - (767033344 : F[X]) * h ^ 38 * a7 ^ 6 * b4
    - (5752750080 : F[X]) * h ^ 38 * a7 ^ 5 * a6 * b5
    - (6903300096 : F[X]) * h ^ 38 * a7 ^ 5 * a5 * b6
    - (8053850112 : F[X]) * h ^ 38 * a7 ^ 5 * a4 * b7
    - (9204400128 : F[X]) * h ^ 38 * a7 ^ 5 * a3 * b8
    - (17258250240 : F[X]) * h ^ 38 * a7 ^ 4 * a6 ^ 2 * b6
    - (40269250560 : F[X]) * h ^ 38 * a7 ^ 4 * a6 * a5 * b7
    - (46022000640 : F[X]) * h ^ 38 * a7 ^ 4 * a6 * a4 * b8
    - (23011000320 : F[X]) * h ^ 38 * a7 ^ 4 * a5 ^ 2 * b8

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk05 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (26846167040 : F[X]) * h ^ 38 * a7 ^ 3 * a6 ^ 3 * b7
    - (92044001280 : F[X]) * h ^ 38 * a7 ^ 3 * a6 ^ 2 * a5 * b8
    - (23011000320 : F[X]) * h ^ 38 * a7 ^ 2 * a6 ^ 4 * b8
    - (2480873472 : F[X]) * h ^ 39 * a7 ^ 6 * a3 * Polynomial.C lambda
    - (14885240832 : F[X]) * h ^ 39 * a7 ^ 5 * a6 * a4 * Polynomial.C lambda
    - (7442620416 : F[X]) * h ^ 39 * a7 ^ 5 * a5 ^ 2 * Polynomial.C lambda
    - (37213102080 : F[X]) * h ^ 39 * a7 ^ 4 * a6 ^ 2 * a5 * Polynomial.C lambda
    - (12404367360 : F[X]) * h ^ 39 * a7 ^ 3 * a6 ^ 4 * Polynomial.C lambda
    - (1917583360 : F[X]) * h ^ 40 * a7 ^ 6 * a2
    + (1438187520 : F[X]) * h ^ 40 * a7 ^ 5 * a6 * a3

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk06 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (1438187520 : F[X]) * h ^ 40 * a7 ^ 5 * a5 * a4
    + (35954688000 : F[X]) * h ^ 40 * a7 ^ 4 * a6 ^ 2 * a4
    + (35954688000 : F[X]) * h ^ 40 * a7 ^ 4 * a6 * a5 ^ 2
    + (91085209600 : F[X]) * h ^ 40 * a7 ^ 3 * a6 ^ 3 * a5
    + (20134625280 : F[X]) * h ^ 40 * a7 ^ 2 * a6 ^ 5
    + (726663168 : F[X]) * h ^ 46 * a7 ^ 5 * b3
    + (4844421120 : F[X]) * h ^ 46 * a7 ^ 4 * a6 * b4
    + (6055526400 : F[X]) * h ^ 46 * a7 ^ 4 * a5 * b5
    + (7266631680 : F[X]) * h ^ 46 * a7 ^ 4 * a4 * b6
    + (8477736960 : F[X]) * h ^ 46 * a7 ^ 4 * a3 * b7

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk07 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (9688842240 : F[X]) * h ^ 46 * a7 ^ 4 * a2 * b8
    + (12111052800 : F[X]) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * b5
    + (29066526720 : F[X]) * h ^ 46 * a7 ^ 3 * a6 * a5 * b6
    + (33910947840 : F[X]) * h ^ 46 * a7 ^ 3 * a6 * a4 * b7
    + (38755368960 : F[X]) * h ^ 46 * a7 ^ 3 * a6 * a3 * b8
    + (16955473920 : F[X]) * h ^ 46 * a7 ^ 3 * a5 ^ 2 * b7
    + (38755368960 : F[X]) * h ^ 46 * a7 ^ 3 * a5 * a4 * b8
    + (14533263360 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 3 * b6
    + (50866421760 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a5 * b7
    + (58133053440 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a4 * b8

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk08 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (58133053440 : F[X]) * h ^ 46 * a7 ^ 2 * a6 * a5 ^ 2 * b8
    + (8477736960 : F[X]) * h ^ 46 * a7 * a6 ^ 4 * b7
    + (38755368960 : F[X]) * h ^ 46 * a7 * a6 ^ 3 * a5 * b8
    + (1937768448 : F[X]) * h ^ 46 * a6 ^ 5 * b8
    + (2588737536 : F[X]) * h ^ 47 * a7 ^ 5 * a2 * Polynomial.C lambda
    + (12943687680 : F[X]) * h ^ 47 * a7 ^ 4 * a6 * a3 * Polynomial.C lambda
    + (12943687680 : F[X]) * h ^ 47 * a7 ^ 4 * a5 * a4 * Polynomial.C lambda
    + (25887375360 : F[X]) * h ^ 47 * a7 ^ 3 * a6 ^ 2 * a4 * Polynomial.C lambda
    + (25887375360 : F[X]) * h ^ 47 * a7 ^ 3 * a6 * a5 ^ 2 * Polynomial.C lambda
    + (25887375360 : F[X]) * h ^ 47 * a7 ^ 2 * a6 ^ 3 * a5 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk09 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (2588737536 : F[X]) * h ^ 47 * a7 * a6 ^ 5 * Polynomial.C lambda
    + (2119434240 : F[X]) * h ^ 48 * a7 ^ 5 * a1
    - (3027763200 : F[X]) * h ^ 48 * a7 ^ 4 * a6 * a2
    - (3027763200 : F[X]) * h ^ 48 * a7 ^ 4 * a5 * a3
    - (1513881600 : F[X]) * h ^ 48 * a7 ^ 4 * a4 ^ 2
    - (33305395200 : F[X]) * h ^ 48 * a7 ^ 3 * a6 ^ 2 * a3
    - (66610790400 : F[X]) * h ^ 48 * a7 ^ 3 * a6 * a5 * a4
    - (11101798400 : F[X]) * h ^ 48 * a7 ^ 3 * a5 ^ 3
    - (60555264000 : F[X]) * h ^ 48 * a7 ^ 2 * a6 ^ 3 * a4
    - (90832896000 : F[X]) * h ^ 48 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk10 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (43902566400 : F[X]) * h ^ 48 * a7 * a6 ^ 4 * a5
    - (1917583360 : F[X]) * h ^ 48 * a6 ^ 6
    - (645922816 : F[X]) * h ^ 54 * a7 ^ 4 * b2
    - (3875536896 : F[X]) * h ^ 54 * a7 ^ 3 * a6 * b3
    - (5167382528 : F[X]) * h ^ 54 * a7 ^ 3 * a5 * b4
    - (6459228160 : F[X]) * h ^ 54 * a7 ^ 3 * a4 * b5
    - (7751073792 : F[X]) * h ^ 54 * a7 ^ 3 * a3 * b6
    - (9042919424 : F[X]) * h ^ 54 * a7 ^ 3 * a2 * b7
    - (10334765056 : F[X]) * h ^ 54 * a7 ^ 3 * a1 * b8
    - (7751073792 : F[X]) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * b4

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk11 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (19377684480 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a5 * b5
    - (23253221376 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a4 * b6
    - (27128758272 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a3 * b7
    - (31004295168 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a2 * b8
    - (11626610688 : F[X]) * h ^ 54 * a7 ^ 2 * a5 ^ 2 * b6
    - (27128758272 : F[X]) * h ^ 54 * a7 ^ 2 * a5 * a4 * b7
    - (31004295168 : F[X]) * h ^ 54 * a7 ^ 2 * a5 * a3 * b8
    - (15502147584 : F[X]) * h ^ 54 * a7 ^ 2 * a4 ^ 2 * b8
    - (6459228160 : F[X]) * h ^ 54 * a7 * a6 ^ 3 * b5
    - (23253221376 : F[X]) * h ^ 54 * a7 * a6 ^ 2 * a5 * b6

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk12 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (27128758272 : F[X]) * h ^ 54 * a7 * a6 ^ 2 * a4 * b7
    - (31004295168 : F[X]) * h ^ 54 * a7 * a6 ^ 2 * a3 * b8
    - (27128758272 : F[X]) * h ^ 54 * a7 * a6 * a5 ^ 2 * b7
    - (62008590336 : F[X]) * h ^ 54 * a7 * a6 * a5 * a4 * b8
    - (10334765056 : F[X]) * h ^ 54 * a7 * a5 ^ 3 * b8
    - (1937768448 : F[X]) * h ^ 54 * a6 ^ 4 * b6
    - (9042919424 : F[X]) * h ^ 54 * a6 ^ 3 * a5 * b7
    - (10334765056 : F[X]) * h ^ 54 * a6 ^ 3 * a4 * b8
    - (15502147584 : F[X]) * h ^ 54 * a6 ^ 2 * a5 ^ 2 * b8
    - (2724986880 : F[X]) * h ^ 55 * a7 ^ 4 * a1 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk13 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (10899947520 : F[X]) * h ^ 55 * a7 ^ 3 * a6 * a2 * Polynomial.C lambda
    - (10899947520 : F[X]) * h ^ 55 * a7 ^ 3 * a5 * a3 * Polynomial.C lambda
    - (5449973760 : F[X]) * h ^ 55 * a7 ^ 3 * a4 ^ 2 * Polynomial.C lambda
    - (16349921280 : F[X]) * h ^ 55 * a7 ^ 2 * a6 ^ 2 * a3 * Polynomial.C lambda
    - (32699842560 : F[X]) * h ^ 55 * a7 ^ 2 * a6 * a5 * a4 * Polynomial.C lambda
    - (5449973760 : F[X]) * h ^ 55 * a7 ^ 2 * a5 ^ 3 * Polynomial.C lambda
    - (10899947520 : F[X]) * h ^ 55 * a7 * a6 ^ 3 * a4 * Polynomial.C lambda
    - (16349921280 : F[X]) * h ^ 55 * a7 * a6 ^ 2 * a5 ^ 2 * Polynomial.C lambda
    - (2724986880 : F[X]) * h ^ 55 * a6 ^ 4 * a5 * Polynomial.C lambda
    - (2422210560 : F[X]) * h ^ 56 * a7 ^ 4 * a0

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk14 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (4844421120 : F[X]) * h ^ 56 * a7 ^ 3 * a6 * a1
    + (4844421120 : F[X]) * h ^ 56 * a7 ^ 3 * a5 * a2
    + (4844421120 : F[X]) * h ^ 56 * a7 ^ 3 * a4 * a3
    + (29066526720 : F[X]) * h ^ 56 * a7 ^ 2 * a6 ^ 2 * a2
    + (58133053440 : F[X]) * h ^ 56 * a7 ^ 2 * a6 * a5 * a3
    + (29066526720 : F[X]) * h ^ 56 * a7 ^ 2 * a6 * a4 ^ 2
    + (29066526720 : F[X]) * h ^ 56 * a7 ^ 2 * a5 ^ 2 * a4
    + (33910947840 : F[X]) * h ^ 56 * a7 * a6 ^ 3 * a3
    + (101732843520 : F[X]) * h ^ 56 * a7 * a6 ^ 2 * a5 * a4
    + (33910947840 : F[X]) * h ^ 56 * a7 * a6 * a5 ^ 3

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk15 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (12111052800 : F[X]) * h ^ 56 * a6 ^ 4 * a4
    + (24222105600 : F[X]) * h ^ 56 * a6 ^ 3 * a5 ^ 2
    + (469762048 : F[X]) * h ^ 62 * a7 ^ 3 * b1
    + (2818572288 : F[X]) * h ^ 62 * a7 ^ 2 * a6 * b2
    + (4227858432 : F[X]) * h ^ 62 * a7 ^ 2 * a5 * b3
    + (5637144576 : F[X]) * h ^ 62 * a7 ^ 2 * a4 * b4
    + (7046430720 : F[X]) * h ^ 62 * a7 ^ 2 * a3 * b5
    + (8455716864 : F[X]) * h ^ 62 * a7 ^ 2 * a2 * b6
    + (9865003008 : F[X]) * h ^ 62 * a7 ^ 2 * a1 * b7
    + (11274289152 : F[X]) * h ^ 62 * a7 ^ 2 * a0 * b8

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk16 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (4227858432 : F[X]) * h ^ 62 * a7 * a6 ^ 2 * b3
    + (11274289152 : F[X]) * h ^ 62 * a7 * a6 * a5 * b4
    + (14092861440 : F[X]) * h ^ 62 * a7 * a6 * a4 * b5
    + (16911433728 : F[X]) * h ^ 62 * a7 * a6 * a3 * b6
    + (19730006016 : F[X]) * h ^ 62 * a7 * a6 * a2 * b7
    + (22548578304 : F[X]) * h ^ 62 * a7 * a6 * a1 * b8
    + (7046430720 : F[X]) * h ^ 62 * a7 * a5 ^ 2 * b5
    + (16911433728 : F[X]) * h ^ 62 * a7 * a5 * a4 * b6
    + (19730006016 : F[X]) * h ^ 62 * a7 * a5 * a3 * b7
    + (22548578304 : F[X]) * h ^ 62 * a7 * a5 * a2 * b8

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk17 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (9865003008 : F[X]) * h ^ 62 * a7 * a4 ^ 2 * b7
    + (22548578304 : F[X]) * h ^ 62 * a7 * a4 * a3 * b8
    + (1879048192 : F[X]) * h ^ 62 * a6 ^ 3 * b4
    + (7046430720 : F[X]) * h ^ 62 * a6 ^ 2 * a5 * b5
    + (8455716864 : F[X]) * h ^ 62 * a6 ^ 2 * a4 * b6
    + (9865003008 : F[X]) * h ^ 62 * a6 ^ 2 * a3 * b7
    + (11274289152 : F[X]) * h ^ 62 * a6 ^ 2 * a2 * b8
    + (8455716864 : F[X]) * h ^ 62 * a6 * a5 ^ 2 * b6
    + (19730006016 : F[X]) * h ^ 62 * a6 * a5 * a4 * b7
    + (22548578304 : F[X]) * h ^ 62 * a6 * a5 * a3 * b8

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk18 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (11274289152 : F[X]) * h ^ 62 * a6 * a4 ^ 2 * b8
    + (3288334336 : F[X]) * h ^ 62 * a5 ^ 3 * b7
    + (11274289152 : F[X]) * h ^ 62 * a5 ^ 2 * a4 * b8
    + (2906652672 : F[X]) * h ^ 63 * a7 ^ 3 * a0 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 ^ 2 * a6 * a1 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 ^ 2 * a5 * a2 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 ^ 2 * a4 * a3 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 * a6 ^ 2 * a2 * Polynomial.C lambda
    + (17439916032 : F[X]) * h ^ 63 * a7 * a6 * a5 * a3 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 * a6 * a4 ^ 2 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk19 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (8719958016 : F[X]) * h ^ 63 * a7 * a5 ^ 2 * a4 * Polynomial.C lambda
    + (2906652672 : F[X]) * h ^ 63 * a6 ^ 3 * a3 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a6 ^ 2 * a5 * a4 * Polynomial.C lambda
    + (2906652672 : F[X]) * h ^ 63 * a6 * a5 ^ 3 * Polynomial.C lambda
    - (7046430720 : F[X]) * h ^ 64 * a7 ^ 2 * a6 * a0
    - (7046430720 : F[X]) * h ^ 64 * a7 ^ 2 * a5 * a1
    - (7046430720 : F[X]) * h ^ 64 * a7 ^ 2 * a4 * a2
    - (3523215360 : F[X]) * h ^ 64 * a7 ^ 2 * a3 ^ 2
    - (22900899840 : F[X]) * h ^ 64 * a7 * a6 ^ 2 * a1
    - (45801799680 : F[X]) * h ^ 64 * a7 * a6 * a5 * a2

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk20 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (45801799680 : F[X]) * h ^ 64 * a7 * a6 * a4 * a3
    - (22900899840 : F[X]) * h ^ 64 * a7 * a5 ^ 2 * a3
    - (22900899840 : F[X]) * h ^ 64 * a7 * a5 * a4 ^ 2
    - (12918456320 : F[X]) * h ^ 64 * a6 ^ 3 * a2
    - (38755368960 : F[X]) * h ^ 64 * a6 ^ 2 * a5 * a3
    - (19377684480 : F[X]) * h ^ 64 * a6 ^ 2 * a4 ^ 2
    - (38755368960 : F[X]) * h ^ 64 * a6 * a5 ^ 2 * a4
    - (3229614080 : F[X]) * h ^ 64 * a5 ^ 4
    - (1610612736 : F[X]) * h ^ 70 * a7 * a6 * b1
    - (3221225472 : F[X]) * h ^ 70 * a7 * a5 * b2

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk21 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (4831838208 : F[X]) * h ^ 70 * a7 * a4 * b3
    - (6442450944 : F[X]) * h ^ 70 * a7 * a3 * b4
    - (8053063680 : F[X]) * h ^ 70 * a7 * a2 * b5
    - (9663676416 : F[X]) * h ^ 70 * a7 * a1 * b6
    - (11274289152 : F[X]) * h ^ 70 * a7 * a0 * b7
    - (1610612736 : F[X]) * h ^ 70 * a6 ^ 2 * b2
    - (4831838208 : F[X]) * h ^ 70 * a6 * a5 * b3
    - (6442450944 : F[X]) * h ^ 70 * a6 * a4 * b4
    - (8053063680 : F[X]) * h ^ 70 * a6 * a3 * b5
    - (9663676416 : F[X]) * h ^ 70 * a6 * a2 * b6

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk22 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (11274289152 : F[X]) * h ^ 70 * a6 * a1 * b7
    - (12884901888 : F[X]) * h ^ 70 * a6 * a0 * b8
    - (3221225472 : F[X]) * h ^ 70 * a5 ^ 2 * b4
    - (8053063680 : F[X]) * h ^ 70 * a5 * a4 * b5
    - (9663676416 : F[X]) * h ^ 70 * a5 * a3 * b6
    - (11274289152 : F[X]) * h ^ 70 * a5 * a2 * b7
    - (12884901888 : F[X]) * h ^ 70 * a5 * a1 * b8
    - (4831838208 : F[X]) * h ^ 70 * a4 ^ 2 * b6
    - (11274289152 : F[X]) * h ^ 70 * a4 * a3 * b7
    - (12884901888 : F[X]) * h ^ 70 * a4 * a2 * b8

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk23 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (6442450944 : F[X]) * h ^ 70 * a3 ^ 2 * b8
    - (6341787648 : F[X]) * h ^ 71 * a7 * a6 * a0 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a7 * a5 * a1 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a7 * a4 * a2 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a7 * a3 ^ 2 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a6 ^ 2 * a1 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a6 * a5 * a2 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a6 * a4 * a3 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a5 ^ 2 * a3 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a5 * a4 ^ 2 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk24 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (10066329600 : F[X]) * h ^ 72 * a7 * a5 * a0
    + (10066329600 : F[X]) * h ^ 72 * a7 * a4 * a1
    + (10066329600 : F[X]) * h ^ 72 * a7 * a3 * a2
    + (14092861440 : F[X]) * h ^ 72 * a6 ^ 2 * a0
    + (28185722880 : F[X]) * h ^ 72 * a6 * a5 * a1
    + (28185722880 : F[X]) * h ^ 72 * a6 * a4 * a2
    + (14092861440 : F[X]) * h ^ 72 * a6 * a3 ^ 2
    + (14092861440 : F[X]) * h ^ 72 * a5 ^ 2 * a2
    + (28185722880 : F[X]) * h ^ 72 * a5 * a4 * a3
    + (4697620480 : F[X]) * h ^ 72 * a4 ^ 3

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk25 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    + (2147483648 : F[X]) * h ^ 78 * a5 * b1
    + (4294967296 : F[X]) * h ^ 78 * a4 * b2
    + (6442450944 : F[X]) * h ^ 78 * a3 * b3
    + (8589934592 : F[X]) * h ^ 78 * a2 * b4
    + (10737418240 : F[X]) * h ^ 78 * a1 * b5
    + (12884901888 : F[X]) * h ^ 78 * a0 * b6
    + (3623878656 : F[X]) * h ^ 79 * a5 * a0 * Polynomial.C lambda
    + (3623878656 : F[X]) * h ^ 79 * a4 * a1 * Polynomial.C lambda
    + (3623878656 : F[X]) * h ^ 79 * a3 * a2 * Polynomial.C lambda
    - (16106127360 : F[X]) * h ^ 80 * a4 * a0

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
abbrev fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk26 (acc : F[X])
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    acc
    - (16106127360 : F[X]) * h ^ 80 * a3 * a1
    - (8053063680 : F[X]) * h ^ 80 * a2 ^ 2

set_option maxHeartbeats 64000000 in
/-- Polynomial numerator of `17179869184 h⁸⁴ μ` on the ninth-power face. -/
def localClearedTwelfthDefect810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk26
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk25
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk24
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk23
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk22
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk21
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk20
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk19
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk18
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk17
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk16
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk15
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk14
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk13
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk12
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk11
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk10
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk09
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk08
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk07
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk06
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk05
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk04
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk03
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk02
      (fable810eleventhSpeedT_localClearedTwelfthDefect810_chunk01 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda


end Depression810TwelfthClearing

end Max11DegreeRoutes
end
