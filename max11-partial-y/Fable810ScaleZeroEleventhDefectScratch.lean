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

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

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

set_option maxHeartbeats 4000000 in
/-- Polynomial numerator of `17179869184 h⁸⁴ μ` on the ninth-power face. -/
def localClearedTwelfthDefect810
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
    - (16106127360 : F[X]) * h ^ 80 * a3 * a1
    - (8053063680 : F[X]) * h ^ 80 * a2 ^ 2

set_option maxHeartbeats 40000000 in
/-- Clearing the first integral `μ` of the degree-`5` row against `h⁸⁴`
on the ninth-power face. -/
theorem twelfthDefect_eq_clearedMu810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (17179869184 : F) * h ^ 84 *
        muResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
          (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1)
          (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1 a0)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
          (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
          (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
          (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3)
          (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2)
          (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2 b1) =
    (203408205 : F) * a7 ^ 12
    - (801115392 : F) * h ^ 6 * a7 ^ 10 * b8
    - (199709874 : F) * h ^ 7 * a7 ^ 11 * lambda
    - (1502091360 : F) * h ^ 8 * a7 ^ 10 * a6
    + (801115392 : F) * h ^ 14 * a7 ^ 9 * b7
    + (8240044032 : F) * h ^ 14 * a7 ^ 8 * a6 * b8
    + (2253137040 : F) * h ^ 15 * a7 ^ 9 * a6 * lambda
    + (1573619520 : F) * h ^ 16 * a7 ^ 9 * a5
    + (1287506880 : F) * h ^ 16 * a7 ^ 8 * a6 ^ 2
    - (797423616 : F) * h ^ 22 * a7 ^ 8 * b6
    - (7442620416 : F) * h ^ 22 * a7 ^ 7 * a6 * b7
    - (8505851904 : F) * h ^ 22 * a7 ^ 7 * a5 * b8
    - (29770481664 : F) * h ^ 22 * a7 ^ 6 * a6 ^ 2 * b8
    - (2317512384 : F) * h ^ 23 * a7 ^ 8 * a5 * lambda
    - (9270049536 : F) * h ^ 23 * a7 ^ 7 * a6 ^ 2 * lambda
    - (1661299200 : F) * h ^ 24 * a7 ^ 8 * a4
    - (1329039360 : F) * h ^ 24 * a7 ^ 7 * a6 * a5
    + (12404367360 : F) * h ^ 24 * a7 ^ 6 * a6 ^ 3
    + (787578880 : F) * h ^ 30 * a7 ^ 7 * b5
    + (6615662592 : F) * h ^ 30 * a7 ^ 6 * a6 * b6
    + (7718273024 : F) * h ^ 30 * a7 ^ 6 * a5 * b7
    + (8820883456 : F) * h ^ 30 * a7 ^ 6 * a4 * b8
    + (23154819072 : F) * h ^ 30 * a7 ^ 5 * a6 ^ 2 * b7
    + (52925300736 : F) * h ^ 30 * a7 ^ 5 * a6 * a5 * b8
    + (44104417280 : F) * h ^ 30 * a7 ^ 4 * a6 ^ 3 * b8
    + (2392270848 : F) * h ^ 31 * a7 ^ 7 * a4 * lambda
    + (16745895936 : F) * h ^ 31 * a7 ^ 6 * a6 * a5 * lambda
    + (16745895936 : F) * h ^ 31 * a7 ^ 5 * a6 ^ 3 * lambda
    + (1772052480 : F) * h ^ 32 * a7 ^ 7 * a3
    - (37213102080 : F) * h ^ 32 * a7 ^ 5 * a6 ^ 2 * a5
    - (31010918400 : F) * h ^ 32 * a7 ^ 4 * a6 ^ 4
    - (767033344 : F) * h ^ 38 * a7 ^ 6 * b4
    - (5752750080 : F) * h ^ 38 * a7 ^ 5 * a6 * b5
    - (6903300096 : F) * h ^ 38 * a7 ^ 5 * a5 * b6
    - (8053850112 : F) * h ^ 38 * a7 ^ 5 * a4 * b7
    - (9204400128 : F) * h ^ 38 * a7 ^ 5 * a3 * b8
    - (17258250240 : F) * h ^ 38 * a7 ^ 4 * a6 ^ 2 * b6
    - (40269250560 : F) * h ^ 38 * a7 ^ 4 * a6 * a5 * b7
    - (46022000640 : F) * h ^ 38 * a7 ^ 4 * a6 * a4 * b8
    - (23011000320 : F) * h ^ 38 * a7 ^ 4 * a5 ^ 2 * b8
    - (26846167040 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 3 * b7
    - (92044001280 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 2 * a5 * b8
    - (23011000320 : F) * h ^ 38 * a7 ^ 2 * a6 ^ 4 * b8
    - (2480873472 : F) * h ^ 39 * a7 ^ 6 * a3 * lambda
    - (14885240832 : F) * h ^ 39 * a7 ^ 5 * a6 * a4 * lambda
    - (7442620416 : F) * h ^ 39 * a7 ^ 5 * a5 ^ 2 * lambda
    - (37213102080 : F) * h ^ 39 * a7 ^ 4 * a6 ^ 2 * a5 * lambda
    - (12404367360 : F) * h ^ 39 * a7 ^ 3 * a6 ^ 4 * lambda
    - (1917583360 : F) * h ^ 40 * a7 ^ 6 * a2
    + (1438187520 : F) * h ^ 40 * a7 ^ 5 * a6 * a3
    + (1438187520 : F) * h ^ 40 * a7 ^ 5 * a5 * a4
    + (35954688000 : F) * h ^ 40 * a7 ^ 4 * a6 ^ 2 * a4
    + (35954688000 : F) * h ^ 40 * a7 ^ 4 * a6 * a5 ^ 2
    + (91085209600 : F) * h ^ 40 * a7 ^ 3 * a6 ^ 3 * a5
    + (20134625280 : F) * h ^ 40 * a7 ^ 2 * a6 ^ 5
    + (726663168 : F) * h ^ 46 * a7 ^ 5 * b3
    + (4844421120 : F) * h ^ 46 * a7 ^ 4 * a6 * b4
    + (6055526400 : F) * h ^ 46 * a7 ^ 4 * a5 * b5
    + (7266631680 : F) * h ^ 46 * a7 ^ 4 * a4 * b6
    + (8477736960 : F) * h ^ 46 * a7 ^ 4 * a3 * b7
    + (9688842240 : F) * h ^ 46 * a7 ^ 4 * a2 * b8
    + (12111052800 : F) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * b5
    + (29066526720 : F) * h ^ 46 * a7 ^ 3 * a6 * a5 * b6
    + (33910947840 : F) * h ^ 46 * a7 ^ 3 * a6 * a4 * b7
    + (38755368960 : F) * h ^ 46 * a7 ^ 3 * a6 * a3 * b8
    + (16955473920 : F) * h ^ 46 * a7 ^ 3 * a5 ^ 2 * b7
    + (38755368960 : F) * h ^ 46 * a7 ^ 3 * a5 * a4 * b8
    + (14533263360 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 3 * b6
    + (50866421760 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a5 * b7
    + (58133053440 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a4 * b8
    + (58133053440 : F) * h ^ 46 * a7 ^ 2 * a6 * a5 ^ 2 * b8
    + (8477736960 : F) * h ^ 46 * a7 * a6 ^ 4 * b7
    + (38755368960 : F) * h ^ 46 * a7 * a6 ^ 3 * a5 * b8
    + (1937768448 : F) * h ^ 46 * a6 ^ 5 * b8
    + (2588737536 : F) * h ^ 47 * a7 ^ 5 * a2 * lambda
    + (12943687680 : F) * h ^ 47 * a7 ^ 4 * a6 * a3 * lambda
    + (12943687680 : F) * h ^ 47 * a7 ^ 4 * a5 * a4 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 3 * a6 ^ 2 * a4 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 3 * a6 * a5 ^ 2 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 2 * a6 ^ 3 * a5 * lambda
    + (2588737536 : F) * h ^ 47 * a7 * a6 ^ 5 * lambda
    + (2119434240 : F) * h ^ 48 * a7 ^ 5 * a1
    - (3027763200 : F) * h ^ 48 * a7 ^ 4 * a6 * a2
    - (3027763200 : F) * h ^ 48 * a7 ^ 4 * a5 * a3
    - (1513881600 : F) * h ^ 48 * a7 ^ 4 * a4 ^ 2
    - (33305395200 : F) * h ^ 48 * a7 ^ 3 * a6 ^ 2 * a3
    - (66610790400 : F) * h ^ 48 * a7 ^ 3 * a6 * a5 * a4
    - (11101798400 : F) * h ^ 48 * a7 ^ 3 * a5 ^ 3
    - (60555264000 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 3 * a4
    - (90832896000 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2
    - (43902566400 : F) * h ^ 48 * a7 * a6 ^ 4 * a5
    - (1917583360 : F) * h ^ 48 * a6 ^ 6
    - (645922816 : F) * h ^ 54 * a7 ^ 4 * b2
    - (3875536896 : F) * h ^ 54 * a7 ^ 3 * a6 * b3
    - (5167382528 : F) * h ^ 54 * a7 ^ 3 * a5 * b4
    - (6459228160 : F) * h ^ 54 * a7 ^ 3 * a4 * b5
    - (7751073792 : F) * h ^ 54 * a7 ^ 3 * a3 * b6
    - (9042919424 : F) * h ^ 54 * a7 ^ 3 * a2 * b7
    - (10334765056 : F) * h ^ 54 * a7 ^ 3 * a1 * b8
    - (7751073792 : F) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * b4
    - (19377684480 : F) * h ^ 54 * a7 ^ 2 * a6 * a5 * b5
    - (23253221376 : F) * h ^ 54 * a7 ^ 2 * a6 * a4 * b6
    - (27128758272 : F) * h ^ 54 * a7 ^ 2 * a6 * a3 * b7
    - (31004295168 : F) * h ^ 54 * a7 ^ 2 * a6 * a2 * b8
    - (11626610688 : F) * h ^ 54 * a7 ^ 2 * a5 ^ 2 * b6
    - (27128758272 : F) * h ^ 54 * a7 ^ 2 * a5 * a4 * b7
    - (31004295168 : F) * h ^ 54 * a7 ^ 2 * a5 * a3 * b8
    - (15502147584 : F) * h ^ 54 * a7 ^ 2 * a4 ^ 2 * b8
    - (6459228160 : F) * h ^ 54 * a7 * a6 ^ 3 * b5
    - (23253221376 : F) * h ^ 54 * a7 * a6 ^ 2 * a5 * b6
    - (27128758272 : F) * h ^ 54 * a7 * a6 ^ 2 * a4 * b7
    - (31004295168 : F) * h ^ 54 * a7 * a6 ^ 2 * a3 * b8
    - (27128758272 : F) * h ^ 54 * a7 * a6 * a5 ^ 2 * b7
    - (62008590336 : F) * h ^ 54 * a7 * a6 * a5 * a4 * b8
    - (10334765056 : F) * h ^ 54 * a7 * a5 ^ 3 * b8
    - (1937768448 : F) * h ^ 54 * a6 ^ 4 * b6
    - (9042919424 : F) * h ^ 54 * a6 ^ 3 * a5 * b7
    - (10334765056 : F) * h ^ 54 * a6 ^ 3 * a4 * b8
    - (15502147584 : F) * h ^ 54 * a6 ^ 2 * a5 ^ 2 * b8
    - (2724986880 : F) * h ^ 55 * a7 ^ 4 * a1 * lambda
    - (10899947520 : F) * h ^ 55 * a7 ^ 3 * a6 * a2 * lambda
    - (10899947520 : F) * h ^ 55 * a7 ^ 3 * a5 * a3 * lambda
    - (5449973760 : F) * h ^ 55 * a7 ^ 3 * a4 ^ 2 * lambda
    - (16349921280 : F) * h ^ 55 * a7 ^ 2 * a6 ^ 2 * a3 * lambda
    - (32699842560 : F) * h ^ 55 * a7 ^ 2 * a6 * a5 * a4 * lambda
    - (5449973760 : F) * h ^ 55 * a7 ^ 2 * a5 ^ 3 * lambda
    - (10899947520 : F) * h ^ 55 * a7 * a6 ^ 3 * a4 * lambda
    - (16349921280 : F) * h ^ 55 * a7 * a6 ^ 2 * a5 ^ 2 * lambda
    - (2724986880 : F) * h ^ 55 * a6 ^ 4 * a5 * lambda
    - (2422210560 : F) * h ^ 56 * a7 ^ 4 * a0
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a6 * a1
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a5 * a2
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a4 * a3
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a6 ^ 2 * a2
    + (58133053440 : F) * h ^ 56 * a7 ^ 2 * a6 * a5 * a3
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a6 * a4 ^ 2
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a5 ^ 2 * a4
    + (33910947840 : F) * h ^ 56 * a7 * a6 ^ 3 * a3
    + (101732843520 : F) * h ^ 56 * a7 * a6 ^ 2 * a5 * a4
    + (33910947840 : F) * h ^ 56 * a7 * a6 * a5 ^ 3
    + (12111052800 : F) * h ^ 56 * a6 ^ 4 * a4
    + (24222105600 : F) * h ^ 56 * a6 ^ 3 * a5 ^ 2
    + (469762048 : F) * h ^ 62 * a7 ^ 3 * b1
    + (2818572288 : F) * h ^ 62 * a7 ^ 2 * a6 * b2
    + (4227858432 : F) * h ^ 62 * a7 ^ 2 * a5 * b3
    + (5637144576 : F) * h ^ 62 * a7 ^ 2 * a4 * b4
    + (7046430720 : F) * h ^ 62 * a7 ^ 2 * a3 * b5
    + (8455716864 : F) * h ^ 62 * a7 ^ 2 * a2 * b6
    + (9865003008 : F) * h ^ 62 * a7 ^ 2 * a1 * b7
    + (11274289152 : F) * h ^ 62 * a7 ^ 2 * a0 * b8
    + (4227858432 : F) * h ^ 62 * a7 * a6 ^ 2 * b3
    + (11274289152 : F) * h ^ 62 * a7 * a6 * a5 * b4
    + (14092861440 : F) * h ^ 62 * a7 * a6 * a4 * b5
    + (16911433728 : F) * h ^ 62 * a7 * a6 * a3 * b6
    + (19730006016 : F) * h ^ 62 * a7 * a6 * a2 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a6 * a1 * b8
    + (7046430720 : F) * h ^ 62 * a7 * a5 ^ 2 * b5
    + (16911433728 : F) * h ^ 62 * a7 * a5 * a4 * b6
    + (19730006016 : F) * h ^ 62 * a7 * a5 * a3 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a5 * a2 * b8
    + (9865003008 : F) * h ^ 62 * a7 * a4 ^ 2 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a4 * a3 * b8
    + (1879048192 : F) * h ^ 62 * a6 ^ 3 * b4
    + (7046430720 : F) * h ^ 62 * a6 ^ 2 * a5 * b5
    + (8455716864 : F) * h ^ 62 * a6 ^ 2 * a4 * b6
    + (9865003008 : F) * h ^ 62 * a6 ^ 2 * a3 * b7
    + (11274289152 : F) * h ^ 62 * a6 ^ 2 * a2 * b8
    + (8455716864 : F) * h ^ 62 * a6 * a5 ^ 2 * b6
    + (19730006016 : F) * h ^ 62 * a6 * a5 * a4 * b7
    + (22548578304 : F) * h ^ 62 * a6 * a5 * a3 * b8
    + (11274289152 : F) * h ^ 62 * a6 * a4 ^ 2 * b8
    + (3288334336 : F) * h ^ 62 * a5 ^ 3 * b7
    + (11274289152 : F) * h ^ 62 * a5 ^ 2 * a4 * b8
    + (2906652672 : F) * h ^ 63 * a7 ^ 3 * a0 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a6 * a1 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a5 * a2 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a4 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a6 ^ 2 * a2 * lambda
    + (17439916032 : F) * h ^ 63 * a7 * a6 * a5 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a6 * a4 ^ 2 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a5 ^ 2 * a4 * lambda
    + (2906652672 : F) * h ^ 63 * a6 ^ 3 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a6 ^ 2 * a5 * a4 * lambda
    + (2906652672 : F) * h ^ 63 * a6 * a5 ^ 3 * lambda
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a6 * a0
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a5 * a1
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a4 * a2
    - (3523215360 : F) * h ^ 64 * a7 ^ 2 * a3 ^ 2
    - (22900899840 : F) * h ^ 64 * a7 * a6 ^ 2 * a1
    - (45801799680 : F) * h ^ 64 * a7 * a6 * a5 * a2
    - (45801799680 : F) * h ^ 64 * a7 * a6 * a4 * a3
    - (22900899840 : F) * h ^ 64 * a7 * a5 ^ 2 * a3
    - (22900899840 : F) * h ^ 64 * a7 * a5 * a4 ^ 2
    - (12918456320 : F) * h ^ 64 * a6 ^ 3 * a2
    - (38755368960 : F) * h ^ 64 * a6 ^ 2 * a5 * a3
    - (19377684480 : F) * h ^ 64 * a6 ^ 2 * a4 ^ 2
    - (38755368960 : F) * h ^ 64 * a6 * a5 ^ 2 * a4
    - (3229614080 : F) * h ^ 64 * a5 ^ 4
    - (1610612736 : F) * h ^ 70 * a7 * a6 * b1
    - (3221225472 : F) * h ^ 70 * a7 * a5 * b2
    - (4831838208 : F) * h ^ 70 * a7 * a4 * b3
    - (6442450944 : F) * h ^ 70 * a7 * a3 * b4
    - (8053063680 : F) * h ^ 70 * a7 * a2 * b5
    - (9663676416 : F) * h ^ 70 * a7 * a1 * b6
    - (11274289152 : F) * h ^ 70 * a7 * a0 * b7
    - (1610612736 : F) * h ^ 70 * a6 ^ 2 * b2
    - (4831838208 : F) * h ^ 70 * a6 * a5 * b3
    - (6442450944 : F) * h ^ 70 * a6 * a4 * b4
    - (8053063680 : F) * h ^ 70 * a6 * a3 * b5
    - (9663676416 : F) * h ^ 70 * a6 * a2 * b6
    - (11274289152 : F) * h ^ 70 * a6 * a1 * b7
    - (12884901888 : F) * h ^ 70 * a6 * a0 * b8
    - (3221225472 : F) * h ^ 70 * a5 ^ 2 * b4
    - (8053063680 : F) * h ^ 70 * a5 * a4 * b5
    - (9663676416 : F) * h ^ 70 * a5 * a3 * b6
    - (11274289152 : F) * h ^ 70 * a5 * a2 * b7
    - (12884901888 : F) * h ^ 70 * a5 * a1 * b8
    - (4831838208 : F) * h ^ 70 * a4 ^ 2 * b6
    - (11274289152 : F) * h ^ 70 * a4 * a3 * b7
    - (12884901888 : F) * h ^ 70 * a4 * a2 * b8
    - (6442450944 : F) * h ^ 70 * a3 ^ 2 * b8
    - (6341787648 : F) * h ^ 71 * a7 * a6 * a0 * lambda
    - (6341787648 : F) * h ^ 71 * a7 * a5 * a1 * lambda
    - (6341787648 : F) * h ^ 71 * a7 * a4 * a2 * lambda
    - (3170893824 : F) * h ^ 71 * a7 * a3 ^ 2 * lambda
    - (3170893824 : F) * h ^ 71 * a6 ^ 2 * a1 * lambda
    - (6341787648 : F) * h ^ 71 * a6 * a5 * a2 * lambda
    - (6341787648 : F) * h ^ 71 * a6 * a4 * a3 * lambda
    - (3170893824 : F) * h ^ 71 * a5 ^ 2 * a3 * lambda
    - (3170893824 : F) * h ^ 71 * a5 * a4 ^ 2 * lambda
    + (10066329600 : F) * h ^ 72 * a7 * a5 * a0
    + (10066329600 : F) * h ^ 72 * a7 * a4 * a1
    + (10066329600 : F) * h ^ 72 * a7 * a3 * a2
    + (14092861440 : F) * h ^ 72 * a6 ^ 2 * a0
    + (28185722880 : F) * h ^ 72 * a6 * a5 * a1
    + (28185722880 : F) * h ^ 72 * a6 * a4 * a2
    + (14092861440 : F) * h ^ 72 * a6 * a3 ^ 2
    + (14092861440 : F) * h ^ 72 * a5 ^ 2 * a2
    + (28185722880 : F) * h ^ 72 * a5 * a4 * a3
    + (4697620480 : F) * h ^ 72 * a4 ^ 3
    + (2147483648 : F) * h ^ 78 * a5 * b1
    + (4294967296 : F) * h ^ 78 * a4 * b2
    + (6442450944 : F) * h ^ 78 * a3 * b3
    + (8589934592 : F) * h ^ 78 * a2 * b4
    + (10737418240 : F) * h ^ 78 * a1 * b5
    + (12884901888 : F) * h ^ 78 * a0 * b6
    + (3623878656 : F) * h ^ 79 * a5 * a0 * lambda
    + (3623878656 : F) * h ^ 79 * a4 * a1 * lambda
    + (3623878656 : F) * h ^ 79 * a3 * a2 * lambda
    - (16106127360 : F) * h ^ 80 * a4 * a0
    - (16106127360 : F) * h ^ 80 * a3 * a1
    - (8053063680 : F) * h ^ 80 * a2 ^ 2 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  have h16384 : (16384 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h32768 : (32768 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  have hh84 : h ^ 84 ≠ 0 := pow_ne_zero 84 hh
  have hL :
      depressedL810 h (octicDepressionR810 h a7) b9 = -lambda / 4 :=
    depressedL810_eq_of_ninthPower h a7 b9 lambda hh hN
  have hA :
      depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / (16 * h ^ 14) :=
    depressedA810_eq_cleared h a7 a6 hh
  have hB :
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) /
          (32 * h ^ 21) :=
    depressedB810_eq_cleared h a7 a6 a5 hh
  have hC :
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
            480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) /
          (2048 * h ^ 28) :=
    depressedC810_eq_cleared h a7 a6 a5 a4 hh
  have hD0 :
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
        (1024 * a3 * h ^ 32 - 512 * a4 * a7 * h ^ 24 +
            160 * a5 * a7 ^ 2 * h ^ 16 - 40 * a6 * a7 ^ 3 * h ^ 8 +
            7 * a7 ^ 5) /
          (1024 * h ^ 35) :=
    depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh
  have hE0 :
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
        (65536 * a2 * h ^ 40 - 24576 * a3 * a7 * h ^ 32 +
            6144 * a4 * a7 ^ 2 * h ^ 24 - 1280 * a5 * a7 ^ 3 * h ^ 16 +
            240 * a6 * a7 ^ 4 * h ^ 8 - 35 * a7 ^ 6) /
          (65536 * h ^ 42) :=
    depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh
  have hF0 :
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 =
        (131072 * a1 * h ^ 48 - 32768 * a2 * a7 * h ^ 40 +
            6144 * a3 * a7 ^ 2 * h ^ 32 - 1024 * a4 * a7 ^ 3 * h ^ 24 +
            160 * a5 * a7 ^ 4 * h ^ 16 - 24 * a6 * a7 ^ 5 * h ^ 8 +
            3 * a7 ^ 7) /
          (131072 * h ^ 49) :=
    depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh
  have hG0 :
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
          a0 =
        (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
            262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
            4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
            64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) /
          (16777216 * h ^ 56) :=
    depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh
  have hP :
      depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
          (64 * h ^ 14) :=
    depressedP810_eq_cleared_ninthPower h a7 b9 b8 lambda hh hN
  have hQ :
      depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
        (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
            9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
          (64 * h ^ 21) :=
    depressedQ810_eq_cleared h a7 b9 b8 b7 lambda hh hN
  have hR :
      depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
        (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
            896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
            2048 * b6 * h ^ 22) /
          (2048 * h ^ 28) :=
    depressedR810_eq_cleared h a7 b9 b8 b7 b6 lambda hh hN
  have hS :
      depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
            896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
            6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
          (8192 * h ^ 35) :=
    depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 lambda hh hN
  have hT0 :
      depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
        (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
            2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
            30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
            131072 * b4 * h ^ 38) /
          (131072 * h ^ 42) :=
    depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU0 :
      depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 =
        (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
            448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
            10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
            131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
          (262144 * h ^ 49) :=
    depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV0 :
      depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 =
        (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
            1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
            61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
            1572864 * a7 ^ 2 * b4 * h ^ 38 -
            6291456 * a7 * b3 * h ^ 46 + 16777216 * b2 * h ^ 54) /
          (16777216 * h ^ 56) :=
    depressedV810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW0 :
      depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 =
        (40 * a7 ^ 9 - 9 * lambda * a7 ^ 8 * h ^ 7 -
            256 * a7 ^ 7 * b8 * h ^ 6 + 1792 * a7 ^ 6 * b7 * h ^ 14 -
            12288 * a7 ^ 5 * b6 * h ^ 22 + 81920 * a7 ^ 4 * b5 * h ^ 30 -
            524288 * a7 ^ 3 * b4 * h ^ 38 +
            3145728 * a7 ^ 2 * b3 * h ^ 46 -
            16777216 * a7 * b2 * h ^ 54 + 67108864 * b1 * h ^ 62) /
          (67108864 * h ^ 63) :=
    depressedW810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
  simp only [muResidual810, hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ,
    hR, hS, hT0, hU0, hV0, hW0, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h256, h512, h1024, h2048,
    h4096, h8192, h16384, h32768, h65536, h131072, h262144, h16777216,
    h67108864, h17179869184, hh14, hh21, hh28, hh35, hh42, hh49, hh56,
    hh63, hh84]
  ring

end Depression810TwelfthClearing

/-! ## Degree-`5` depressed Jacobian coefficient -/

section DepressedRow810Twelfth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

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

set_option maxHeartbeats 80000000 in
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
  simp only [muResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810, map_sub, map_add, Derivation.leibniz,
    h12, h14, h18, h38, h54, h98, h78, h34, h58, h516, h316, h532, h15128,
    h5128, h7128, h9128, h1564, h964, h764, h35512, h211024, h631024,
    h31532768, h778192, h3158192, h1051024, h63512, h332, h352048, hL,
    h44132768, h44165536, h4558192, h107116384, h1894096, h851024, h751024,
    h811024, h932, h732, h21128, h35128, h771024, h45256, h452048,
    h1894096', h94532768, h38565536, h2251024, h7256, h3858192, h1532,
    h116, h35256, zero_mul, add_zero, mul_zero, pow_two, hsq,
    hsqB, hsqC, hsqD, hsqE, hcub, hcubB, hcubC, hquar, hquarB, hquint,
    hsextA]
  rw [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv]
  linear_combination (1 / 8 : F) * hrow_red

end DepressedRow810Twelfth

section NonzeroTwelfthFaceClearing810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The eleventh octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁸⁴`. -/
theorem nonzeroFace810_twelfthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      localClearedTwelfthDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * h0 ^ 84 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = h ^ 8 := by
    simp only [hp8, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = h ^ 10 := by
    simp only [hq10, hH, h, map_pow]
    ring
  have hpDep := affineDepress_sourceOctic68 p h
    (octicDepressionR810 h a7) hp hh hpTop
  have hL0 : depressedL68 h (octicDepressionR810 h a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter h a7 hh
  have hNrat : 5 * a7 * h ^ 2 - 4 * b9 = RatFunc.C lambda * h ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    simpa only [hH, h, a7, b9, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hLval :
      depressedL810 h (octicDepressionR810 h a7) b9 =
        RatFunc.C (-lambda / 4) := by
    have hL := depressedL810_eq_of_ninthPower h a7 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j h (octicDepressionR810 h a7) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 q)
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = h ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedQ810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedR810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedS810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedT810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedV810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg3 :
      g.coeff 3 =
        depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedU810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedW810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg0 :
      g.coeff 0 =
        depressedX810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 b0 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff0_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedX810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0]
  have hg8' :
      g.coeff 8 =
        depressedP810 h (octicDepressionR810 h a7) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * octicDepressionR810 h a7 +
        (sourceToRatFunc68 q).coeff 9 / h ^ 9 =
          depressedL810 h (octicDepressionR810 h a7) b9 := by
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (Polynomial.C (-lambda / 4) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow15 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_15_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 15) hbracket
    simpa [f, g, Polynomial.coeff_C, show (15 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow14 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 5) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_14_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 14) hbracket
    simpa [f, g, Polynomial.coeff_C, show (14 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 5) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 8) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 5) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 7) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 5) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 6) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 5) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 4) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 5) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 5) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 5) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 3) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 5) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 2) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 3) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 4) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 5) +
        g.coeff 1 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 3) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 2) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 3) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 4) +
        g.coeff 1 * ratFuncDerivation68 (f.coeff 5) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 3) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 2) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 1) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr

  have hf6 : f.coeff 6 = depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hf5 : f.coeff 5 =
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 := by
    dsimp only [f, depressedB810, a7, a6, a5]
    rw [hpDep, coeff_depressedOctic68_five]
  have hf4 : f.coeff 4 =
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 := by
    dsimp only [f, depressedC810, a7, a6, a5, a4]
    rw [hpDep, coeff_depressedOctic68_four]
  have hf3 : f.coeff 3 =
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 := by
    dsimp only [f, depressedD810, a7, a6, a5, a4, a3]
    rw [hpDep, coeff_depressedOctic68_three]
  have hf2 : f.coeff 2 =
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 := by
    dsimp only [f, depressedE810, a7, a6, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedOctic68_two]
  have hf1 : f.coeff 1 =
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedF810, a7, a6, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedOctic68_one]
  have hf0 : f.coeff 0 =
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedG810, a7, a6, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedOctic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual810 (f.coeff 6) (g.coeff 8)) = 0 :=
    alphaResidual810_deriv_zero ratFuncDerivation68 (f.coeff 6)
      (g.coeff 8) hrow15
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (g.coeff 7)) = 0 :=
    betaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (g.coeff 7) hLconst (by simpa using hrow14)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow13)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow12)
  have hepsilon0 :
      ratFuncDerivation68
        (epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow11)
  have hzeta0 :
      ratFuncDerivation68
        (zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 3) hLconst halpha0 hbeta0 hgamma0 hdelta0
      (by simpa using hrow10)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 2)) = 0 :=
    etaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 2) hLconst halpha0 hbeta0
      hgamma0 hdelta0 hepsilon0 (by simpa using hrow9)
  have htheta0deriv :
      ratFuncDerivation68
        (thetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 1)) = 0 :=
    thetaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 1) hLconst halpha0
      hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 (by simpa using hrow8)
  have hiota0deriv :
      ratFuncDerivation68
        (iotaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 0)) = 0 :=
    iotaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0deriv
      (by simpa using hrow7)
  have hmu0deriv :
      ratFuncDerivation68
        (muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    muResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (g.coeff 0) hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0
      heta0deriv htheta0deriv hiota0deriv (by simpa using hrow8)
      (by simpa using hrow7) (by simpa using hrow5)
  obtain ⟨mu0, hmu0⟩ :
      ∃ a : k,
        muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hmu0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedTwelfthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        (17179869184 : RatFunc k) * h ^ 84 *
          muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) := by
    have hF := twelfthDefect_eq_clearedMu810 h a7 a6 a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh (by convert hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedTwelfthDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, map_add, RatFunc.algebraMap_C, h, a7, a6, a5,
      a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, muResidual810,
      alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810, zetaResidual810, etaResidual810, hf6, hf5, hf4, hf3, hf2, hf1,
      hf0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedTwelfthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (17179869184 * mu0) * h0 ^ 84) := by
    rw [hclear, hmu0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨17179869184 * mu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end NonzeroTwelfthFaceClearing810

section ScaleZeroEleventhDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-! ## Degree-`5` source Jacobian row -/

/-- Source-facing degree-`5` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_twelfthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp8, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using fableScaleZero_twelfthCoefficientJacobianRow_raw_810 hp hq hjac

/-- At scale zero the common core is constant, so the leading octic
coefficient of the degree-`5` row is a differential constant. -/
theorem scaleZero_twelfthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  have hrow := fableScaleZero_twelfthCoefficientJacobianRow_raw_810 hp hq hjac
  simpa using hrow

/-- Source-facing scale-zero collapse of the degree-`5` row. -/
theorem normalized810ScaleZero_twelfthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    scaleZero_twelfthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)

/-! ## Degree-`5` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`5` Jacobian coefficient
is exactly
`6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `G = f.coeff 0`, `L = g.coeff 9`,
`P = g.coeff 8`, `Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`,
`T = g.coeff 4`, `U = g.coeff 3`, `V = g.coeff 2`, `W = g.coeff 1`,
and `X = g.coeff 0`. -/
theorem scaleZero_monicOcticDecic_degree5Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
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
          (6 : F) * f.coeff 6 * d (g.coeff 0) :=
  differentialJacobian_coeff_5_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if the degree-`8` and degree-`5` Jacobian
rows vanish, `L` is constant, and the residuals `α, β, γ, δ, ε, ζ, η, θ`
are constant, then the first residual `κ` is a differential constant. -/
theorem scaleZero_muResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
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
    d (muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 :=
  muResidual810_deriv_zero d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hrow8
    hrow7 hrow

/-! ## Cleared weight-`84` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_eleventhClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda eta : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_twelfthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, eta, hN, heta⟩

/-- Aligned constant face `N = 0`: the same degree-`5` clearing applies
with `λ = 0`, and the weight-`84` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedEleventhClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ eta : k,
      localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_twelfthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨eta, heta⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`84` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroEleventhClearedDefect_exists_C_810
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (_hlambda : lambda ≠ 0)
    (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9) :
    ∃ eta : k,
      localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_twelfthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨eta, heta⟩

variable [IsAlgClosed k]

/-- Source-facing tenth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`84`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_eleventhClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambda, eta, hN, hX⟩ :=
    scaleZero_eleventhClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, eta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hX⟩

/-- The weight-`84` defect is a literal ground-field constant. -/
theorem normalized810ScaleZero_eleventhClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta := by
  obtain ⟨t, lambda, eta, ht, hHsq, _hN, hX⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  refine ⟨t, lambda, eta * t ^ 84, ht, hHsq, ?_⟩
  have hconst :
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C (eta * t ^ 84) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 84)).symm
  exact hconst

/-- Newton degree of the tenth cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_eleventhClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized810ScaleZero_eleventhClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hX]
  exact (natDegree_C eta).le

/-- Aligned/nonzero split of the scale-zero tenth defect: both constant
faces of `N` make the weight-`84` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_eleventhClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ eta : k,
            localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
                (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
                (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
              Polynomial.C eta * (Polynomial.C t) ^ 84) ∨
        ∃ lambda eta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
            Polynomial.C eta * (Polynomial.C t) ^ 84) := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, eta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hX
  · exact Or.inr ⟨lambda, eta, hlambda, hN, hX⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-`84` defect.  Neither vanishing face is claimed closed. -/
theorem normalized810ScaleZero_eleventhClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
      let X :=
        localClearedTwelfthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1)
          lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      X = Polynomial.C eta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (eta = 0 ∧ X = 0 ∨
        eta ≠ 0 ∧ X = Polynomial.C eta) := by
  dsimp only
  obtain ⟨t, lambda, eta0, ht, hHsq, hN, hXpow⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  let eta : k := eta0 * t ^ 84
  have hX :
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta := by
    rw [hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 84)).symm
  refine ⟨t, lambda, eta, ht, hHsq, hN, hX, ?_, ?_⟩
  · by_cases hlambda : lambda = 0
    · left
      refine ⟨hlambda, ?_⟩
      simpa only [hlambda, Polynomial.C_0, zero_mul] using hN
    · right
      refine ⟨hlambda, ?_⟩
      have hNconst :
          (5 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
                  H -
              (4 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
            Polynomial.C (lambda * t ^ 9) := by
        rw [hN, ← Polynomial.C_pow]
        exact (map_mul (Polynomial.C : k →+* k[X]) lambda (t ^ 9)).symm
      exact hNconst
  · by_cases heta : eta = 0
    · left
      refine ⟨heta, ?_⟩
      simpa only [heta, Polynomial.C_0] using hX
    · exact Or.inr ⟨heta, hX⟩

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`84` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_eleventhClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          0 =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨eta, hX⟩ :=
    scaleZero_alignedEleventhClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, eta, ht, hHsq, by simpa only [p, q] using hX⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`84` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_eleventhClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, eta, ht, hlambda, hHsq, hN, hX⟩

end ScaleZeroEleventhDefect810


#print axioms fableScaleZero_twelfthCoefficientJacobianRow_raw_810
#print axioms scaleZero_twelfthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_twelfthCoefficientJacobianRow
#print axioms normalized810ScaleZero_twelfthCoefficientJacobianRow_collapsed
#print axioms differentialJacobian_coeff_5_monicOcticDecic
#print axioms scaleZero_monicOcticDecic_degree5Row_810
#print axioms muResidual810_deriv_zero
#print axioms scaleZero_muResidual_deriv_zero_810
#print axioms affineDepress_degreeTen_coeff1_810
#print axioms twelfthDefect_eq_clearedMu810
#print axioms nonzeroFace810_twelfthDefectPowerRelation
#print axioms scaleZero_eleventhClearedDefect_exists_C_810
#print axioms scaleZero_alignedEleventhClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroEleventhClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_eleventhClearedDefect
#print axioms normalized810ScaleZero_eleventhClearedDefect_exists_C
#print axioms normalized810ScaleZero_eleventhClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_eleventhClearedDefectFirstFace
#print axioms normalized810ScaleZero_eleventhClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_eleventhClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_eleventhClearedDefect

end Max11DegreeRoutes
