import Fable810ScaleZeroEleventhDefectScratch

/-! # Scale-zero twelfth defect for the normalized `(8,10)`, `H = 0` leaf

The eleventh-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first eleven octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, `h⁷⁷`, and `h⁸⁴`.
This file consumes the next unused Keller coefficient of the same monic
octic-decic depression: the degree-`4` Jacobian row is
`5 S G' + 4 T F' + 3 U E' + 2 V D' + W C'
- F T' - 2 E U' - 3 D V' - 4 C W' - 5 B X' = 0`.  Its first integral
needs the degree-`6` row a second time, with multiplier `-(5/64) A`,
and the corresponding thirteenth cleared polynomial defect of weight
ninety-one is likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`91` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`3` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

/-- The thirteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the eleventh-defect
packet start at degree `4`. -/
theorem fableScaleZero_thirteenthCoefficientJacobianRow_raw_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : K)) -
      ((p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 4) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (4 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 4 :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1),
        (4, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC5, hC4, hC3, hC2]
  linear_combination hcoeff

section Depression810ThirteenthClearing

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`4` row.  Unlike the previous first
integrals, its exactness certificate uses the degree-`6` row again with
the multiplier `-(5/64) A`. -/
def nuResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 8 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * C0
    - (5 / 128 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * A ^ 2
    + (1 / 4 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * D0
    - (5 / 32 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A * B
    + (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * E0
    - (3 / 16 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A * C0
    - (15 / 128 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * B ^ 2
    + (25 / 512 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A ^ 3
    + (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * F0
    - (3 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * D0
    - (1 / 4 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B * C0
    + (5 / 32 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 2 * B
    + (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * G0
    - (5 / 32 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * E0
    - (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B * D0
    - (15 / 128 : F) * deltaResidual810 L A B C0 D0 P Q S0 * C0 ^ 2
    + (135 / 1024 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 2 * C0
    + (75 / 512 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * B ^ 2
    - (825 / 32768 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 4
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * A * F0
    - (3 / 16 : F) * gammaResidual810 L A B C0 P R * B * E0
    - (3 / 16 : F) * gammaResidual810 L A B C0 P R * C0 * D0
    + (3 / 32 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * D0
    + (27 / 128 : F) * gammaResidual810 L A B C0 P R * A * B * C0
    + (5 / 128 : F) * gammaResidual810 L A B C0 P R * B ^ 3
    - (75 / 1024 : F) * gammaResidual810 L A B C0 P R * A ^ 3 * B
    - (7 / 64 : F) * betaResidual810 L A B Q * B * F0
    - (7 / 64 : F) * betaResidual810 L A B Q * C0 * E0
    + (49 / 1024 : F) * betaResidual810 L A B Q * A ^ 2 * E0
    - (7 / 128 : F) * betaResidual810 L A B Q * D0 ^ 2
    + (7 / 64 : F) * betaResidual810 L A B Q * A * B * D0
    + (7 / 128 : F) * betaResidual810 L A B Q * A * C0 ^ 2
    + (63 / 1024 : F) * betaResidual810 L A B Q * B ^ 2 * C0
    - (147 / 4096 : F) * betaResidual810 L A B Q * A ^ 3 * C0
    - (945 / 16384 : F) * betaResidual810 L A B Q * A ^ 2 * B ^ 2
    + (357 / 65536 : F) * betaResidual810 L A B Q * A ^ 5
    + (12075 / 4194304 : F) * L * A ^ 6
    - (5985 / 262144 : F) * L * A ^ 4 * C0
    - (1575 / 32768 : F) * L * A ^ 3 * B ^ 2
    + (63 / 2048 : F) * L * A ^ 3 * E0
    + (819 / 8192 : F) * L * A ^ 2 * B * D0
    + (819 / 16384 : F) * L * A ^ 2 * C0 ^ 2
    - (45 / 1024 : F) * L * A ^ 2 * G0
    + (441 / 4096 : F) * L * A * B ^ 2 * C0
    - (27 / 256 : F) * L * A * B * F0
    - (27 / 256 : F) * L * A * C0 * E0
    - (27 / 512 : F) * L * A * D0 ^ 2
    + (315 / 32768 : F) * L * B ^ 4
    - (63 / 1024 : F) * L * B ^ 2 * E0
    - (63 / 512 : F) * L * B * C0 * D0
    - (21 / 1024 : F) * L * C0 ^ 3
    + (9 / 64 : F) * L * C0 * G0
    + (9 / 64 : F) * L * D0 * F0
    + (9 / 128 : F) * L * E0 ^ 2
    + (1925 / 65536 : F) * A ^ 5 * B
    - (315 / 8192 : F) * A ^ 4 * D0
    - (665 / 4096 : F) * A ^ 3 * B * C0
    + (55 / 1024 : F) * A ^ 3 * F0
    - (175 / 2048 : F) * A ^ 2 * B ^ 3
    + (45 / 256 : F) * A ^ 2 * B * E0
    + (45 / 256 : F) * A ^ 2 * C0 * D0
    + (195 / 1024 : F) * A * B ^ 2 * D0
    + (195 / 1024 : F) * A * B * C0 ^ 2
    - (25 / 128 : F) * A * B * G0
    - (25 / 128 : F) * A * C0 * F0
    - (25 / 128 : F) * A * D0 * E0
    + (35 / 512 : F) * B ^ 3 * C0
    - (15 / 128 : F) * B ^ 2 * F0
    - (15 / 64 : F) * B * C0 * E0
    - (15 / 128 : F) * B * D0 ^ 2
    - (15 / 128 : F) * C0 ^ 2 * D0
    + (5 / 16 : F) * D0 * G0
    + (5 / 16 : F) * E0 * F0

set_option maxHeartbeats 16000000 in
/-- Polynomial numerator of `281474976710656 h⁹¹ ν` on the ninth-power
face. -/
def localClearedThirteenthDefect810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    - (1898935526600 : F[X]) * a7 ^ 13
    + (7434891097088 : F[X]) * h ^ 6 * a7 ^ 11 * b8
    + (1851462138435 : F[X]) * h ^ 7 * a7 ^ 12 * Polynomial.C lambda
    + (16263824274880 : F[X]) * h ^ 8 * a7 ^ 11 * a6
    - (7434891097088 : F[X]) * h ^ 14 * a7 ^ 10 * b7
    - (84970183966720 : F[X]) * h ^ 14 * a7 ^ 9 * a6 * b8
    - (23001694331616 : F[X]) * h ^ 15 * a7 ^ 10 * a6 * Polynomial.C lambda
    - (17259568618240 : F[X]) * h ^ 16 * a7 ^ 10 * a5
    - (26553182489600 : F[X]) * h ^ 16 * a7 ^ 9 * a6 ^ 2
    + (7388711649280 : F[X]) * h ^ 22 * a7 ^ 9 * b6
    + (77581472317440 : F[X]) * h ^ 22 * a7 ^ 8 * a6 * b7
    + (88664539791360 : F[X]) * h ^ 22 * a7 ^ 8 * a5 * b8
    + (354658159165440 : F[X]) * h ^ 22 * a7 ^ 7 * a6 ^ 2 * b8
    + (23897864240640 : F[X]) * h ^ 23 * a7 ^ 9 * a5 * Polynomial.C lambda
    + (107540389082880 : F[X]) * h ^ 23 * a7 ^ 8 * a6 ^ 2 * Polynomial.C lambda
    + (18471779123200 : F[X]) * h ^ 24 * a7 ^ 9 * a4
    + (41561503027200 : F[X]) * h ^ 24 * a7 ^ 8 * a6 * a5
    - (110830674739200 : F[X]) * h ^ 24 * a7 ^ 7 * a6 ^ 3
    - (7267585228800 : F[X]) * h ^ 30 * a7 ^ 8 * b5
    - (69768818196480 : F[X]) * h ^ 30 * a7 ^ 7 * a6 * b6
    - (81396954562560 : F[X]) * h ^ 30 * a7 ^ 7 * a5 * b7
    - (93025090928640 : F[X]) * h ^ 30 * a7 ^ 7 * a4 * b8
    - (284889340968960 : F[X]) * h ^ 30 * a7 ^ 6 * a6 ^ 2 * b7
    - (651175636500480 : F[X]) * h ^ 30 * a7 ^ 6 * a6 * a5 * b8
    - (651175636500480 : F[X]) * h ^ 30 * a7 ^ 5 * a6 ^ 3 * b8
    - (24936901816320 : F[X]) * h ^ 31 * a7 ^ 8 * a4 * Polynomial.C lambda
    - (199495214530560 : F[X]) * h ^ 31 * a7 ^ 7 * a6 * a5 * Polynomial.C lambda
    - (232744416952320 : F[X]) * h ^ 31 * a7 ^ 6 * a6 ^ 3 * Polynomial.C lambda
    - (19985859379200 : F[X]) * h ^ 32 * a7 ^ 8 * a3
    - (29070340915200 : F[X]) * h ^ 32 * a7 ^ 7 * a6 * a4
    - (14535170457600 : F[X]) * h ^ 32 * a7 ^ 7 * a5 ^ 2
    + (356111676211200 : F[X]) * h ^ 32 * a7 ^ 6 * a6 ^ 2 * a5
    + (406984772812800 : F[X]) * h ^ 32 * a7 ^ 5 * a6 ^ 4
    + (7020761579520 : F[X]) * h ^ 38 * a7 ^ 7 * b4
    + (61431663820800 : F[X]) * h ^ 38 * a7 ^ 6 * a6 * b5
    + (73717996584960 : F[X]) * h ^ 38 * a7 ^ 6 * a5 * b6
    + (86004329349120 : F[X]) * h ^ 38 * a7 ^ 6 * a4 * b7
    + (98290662113280 : F[X]) * h ^ 38 * a7 ^ 6 * a3 * b8
    + (221153989754880 : F[X]) * h ^ 38 * a7 ^ 5 * a6 ^ 2 * b6
    + (516025976094720 : F[X]) * h ^ 38 * a7 ^ 5 * a6 * a5 * b7
    + (589743972679680 : F[X]) * h ^ 38 * a7 ^ 5 * a6 * a4 * b8
    + (294871986339840 : F[X]) * h ^ 38 * a7 ^ 5 * a5 ^ 2 * b8
    + (430021646745600 : F[X]) * h ^ 38 * a7 ^ 4 * a6 ^ 3 * b7
    + (1474359931699200 : F[X]) * h ^ 38 * a7 ^ 4 * a6 ^ 2 * a5 * b8
    + (491453310566400 : F[X]) * h ^ 38 * a7 ^ 3 * a6 ^ 4 * b8
    + (26163306823680 : F[X]) * h ^ 39 * a7 ^ 7 * a3 * Polynomial.C lambda
    + (183143147765760 : F[X]) * h ^ 39 * a7 ^ 6 * a6 * a4 * Polynomial.C lambda
    + (91571573882880 : F[X]) * h ^ 39 * a7 ^ 6 * a5 ^ 2 * Polynomial.C lambda
    + (549429443297280 : F[X]) * h ^ 39 * a7 ^ 5 * a6 ^ 2 * a5 * Polynomial.C lambda
    + (228928934707200 : F[X]) * h ^ 39 * a7 ^ 4 * a6 ^ 4 * Polynomial.C lambda
    + (21939879936000 : F[X]) * h ^ 40 * a7 ^ 7 * a2
    + (15357915955200 : F[X]) * h ^ 40 * a7 ^ 6 * a6 * a3
    + (15357915955200 : F[X]) * h ^ 40 * a7 ^ 6 * a5 * a4
    - (368589982924800 : F[X]) * h ^ 40 * a7 ^ 5 * a6 ^ 2 * a4
    - (368589982924800 : F[X]) * h ^ 40 * a7 ^ 5 * a6 * a5 ^ 2
    - (1305422856192000 : F[X]) * h ^ 40 * a7 ^ 4 * a6 ^ 3 * a5
    - (399305814835200 : F[X]) * h ^ 40 * a7 ^ 3 * a6 ^ 5
    - (6552710807552 : F[X]) * h ^ 46 * a7 ^ 6 * b3
    - (52421686460416 : F[X]) * h ^ 46 * a7 ^ 5 * a6 * b4
    - (65527108075520 : F[X]) * h ^ 46 * a7 ^ 5 * a5 * b5
    - (78632529690624 : F[X]) * h ^ 46 * a7 ^ 5 * a4 * b6
    - (91737951305728 : F[X]) * h ^ 46 * a7 ^ 5 * a3 * b7
    - (104843372920832 : F[X]) * h ^ 46 * a7 ^ 5 * a2 * b8
    - (163817770188800 : F[X]) * h ^ 46 * a7 ^ 4 * a6 ^ 2 * b5
    - (393162648453120 : F[X]) * h ^ 46 * a7 ^ 4 * a6 * a5 * b6
    - (458689756528640 : F[X]) * h ^ 46 * a7 ^ 4 * a6 * a4 * b7
    - (524216864604160 : F[X]) * h ^ 46 * a7 ^ 4 * a6 * a3 * b8
    - (229344878264320 : F[X]) * h ^ 46 * a7 ^ 4 * a5 ^ 2 * b7
    - (524216864604160 : F[X]) * h ^ 46 * a7 ^ 4 * a5 * a4 * b8
    - (262108432302080 : F[X]) * h ^ 46 * a7 ^ 3 * a6 ^ 3 * b6
    - (917379513057280 : F[X]) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * a5 * b7
    - (1048433729208320 : F[X]) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * a4 * b8
    - (1048433729208320 : F[X]) * h ^ 46 * a7 ^ 3 * a6 * a5 ^ 2 * b8
    - (229344878264320 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 4 * b7
    - (1048433729208320 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 3 * a5 * b8
    - (104843372920832 : F[X]) * h ^ 46 * a7 * a6 ^ 5 * b8
    - (27644248719360 : F[X]) * h ^ 47 * a7 ^ 6 * a2 * Polynomial.C lambda
    - (165865492316160 : F[X]) * h ^ 47 * a7 ^ 5 * a6 * a3 * Polynomial.C lambda
    - (165865492316160 : F[X]) * h ^ 47 * a7 ^ 5 * a5 * a4 * Polynomial.C lambda
    - (414663730790400 : F[X]) * h ^ 47 * a7 ^ 4 * a6 ^ 2 * a4 * Polynomial.C lambda
    - (414663730790400 : F[X]) * h ^ 47 * a7 ^ 4 * a6 * a5 ^ 2 * Polynomial.C lambda
    - (552884974387200 : F[X]) * h ^ 47 * a7 ^ 3 * a6 ^ 3 * a5 * Polynomial.C lambda
    - (82932746158080 : F[X]) * h ^ 47 * a7 ^ 2 * a6 ^ 5 * Polynomial.C lambda
    - (24572665528320 : F[X]) * h ^ 48 * a7 ^ 6 * a1
    + (368589982924800 : F[X]) * h ^ 48 * a7 ^ 4 * a6 ^ 2 * a3
    + (737179965849600 : F[X]) * h ^ 48 * a7 ^ 4 * a6 * a5 * a4
    + (122863327641600 : F[X]) * h ^ 48 * a7 ^ 4 * a5 ^ 3
    + (982906621132800 : F[X]) * h ^ 48 * a7 ^ 3 * a6 ^ 3 * a4
    + (1474359931699200 : F[X]) * h ^ 48 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2
    + (1105769948774400 : F[X]) * h ^ 48 * a7 ^ 2 * a6 ^ 4 * a5
    + (98290662113280 : F[X]) * h ^ 48 * a7 * a6 ^ 6
    + (5667209347072 : F[X]) * h ^ 54 * a7 ^ 5 * b2
    + (42504070103040 : F[X]) * h ^ 54 * a7 ^ 4 * a6 * b3
    + (56672093470720 : F[X]) * h ^ 54 * a7 ^ 4 * a5 * b4
    + (70840116838400 : F[X]) * h ^ 54 * a7 ^ 4 * a4 * b5
    + (85008140206080 : F[X]) * h ^ 54 * a7 ^ 4 * a3 * b6
    + (99176163573760 : F[X]) * h ^ 54 * a7 ^ 4 * a2 * b7
    + (113344186941440 : F[X]) * h ^ 54 * a7 ^ 4 * a1 * b8
    + (113344186941440 : F[X]) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * b4
    + (283360467353600 : F[X]) * h ^ 54 * a7 ^ 3 * a6 * a5 * b5
    + (340032560824320 : F[X]) * h ^ 54 * a7 ^ 3 * a6 * a4 * b6
    + (396704654295040 : F[X]) * h ^ 54 * a7 ^ 3 * a6 * a3 * b7
    + (453376747765760 : F[X]) * h ^ 54 * a7 ^ 3 * a6 * a2 * b8
    + (170016280412160 : F[X]) * h ^ 54 * a7 ^ 3 * a5 ^ 2 * b6
    + (396704654295040 : F[X]) * h ^ 54 * a7 ^ 3 * a5 * a4 * b7
    + (453376747765760 : F[X]) * h ^ 54 * a7 ^ 3 * a5 * a3 * b8
    + (226688373882880 : F[X]) * h ^ 54 * a7 ^ 3 * a4 ^ 2 * b8
    + (141680233676800 : F[X]) * h ^ 54 * a7 ^ 2 * a6 ^ 3 * b5
    + (510048841236480 : F[X]) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a5 * b6
    + (595056981442560 : F[X]) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a4 * b7
    + (680065121648640 : F[X]) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a3 * b8
    + (595056981442560 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a5 ^ 2 * b7
    + (1360130243297280 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a5 * a4 * b8
    + (226688373882880 : F[X]) * h ^ 54 * a7 ^ 2 * a5 ^ 3 * b8
    + (85008140206080 : F[X]) * h ^ 54 * a7 * a6 ^ 4 * b6
    + (396704654295040 : F[X]) * h ^ 54 * a7 * a6 ^ 3 * a5 * b7
    + (453376747765760 : F[X]) * h ^ 54 * a7 * a6 ^ 3 * a4 * b8
    + (680065121648640 : F[X]) * h ^ 54 * a7 * a6 ^ 2 * a5 ^ 2 * b8
    + (19835232714752 : F[X]) * h ^ 54 * a6 ^ 5 * b7
    + (113344186941440 : F[X]) * h ^ 54 * a6 ^ 4 * a5 * b8
    + (29487198633984 : F[X]) * h ^ 55 * a7 ^ 5 * a1 * Polynomial.C lambda
    + (147435993169920 : F[X]) * h ^ 55 * a7 ^ 4 * a6 * a2 * Polynomial.C lambda
    + (147435993169920 : F[X]) * h ^ 55 * a7 ^ 4 * a5 * a3 * Polynomial.C lambda
    + (73717996584960 : F[X]) * h ^ 55 * a7 ^ 4 * a4 ^ 2 * Polynomial.C lambda
    + (294871986339840 : F[X]) * h ^ 55 * a7 ^ 3 * a6 ^ 2 * a3 * Polynomial.C lambda
    + (589743972679680 : F[X]) * h ^ 55 * a7 ^ 3 * a6 * a5 * a4 * Polynomial.C lambda
    + (98290662113280 : F[X]) * h ^ 55 * a7 ^ 3 * a5 ^ 3 * Polynomial.C lambda
    + (294871986339840 : F[X]) * h ^ 55 * a7 ^ 2 * a6 ^ 3 * a4 * Polynomial.C lambda
    + (442307979509760 : F[X]) * h ^ 55 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * Polynomial.C lambda
    + (147435993169920 : F[X]) * h ^ 55 * a7 * a6 ^ 4 * a5 * Polynomial.C lambda
    + (4914533105664 : F[X]) * h ^ 55 * a6 ^ 6 * Polynomial.C lambda
    + (28336046735360 : F[X]) * h ^ 56 * a7 ^ 5 * a0
    - (17710029209600 : F[X]) * h ^ 56 * a7 ^ 4 * a6 * a1
    - (17710029209600 : F[X]) * h ^ 56 * a7 ^ 4 * a5 * a2
    - (17710029209600 : F[X]) * h ^ 56 * a7 ^ 4 * a4 * a3
    - (354200584192000 : F[X]) * h ^ 56 * a7 ^ 3 * a6 ^ 2 * a2
    - (708401168384000 : F[X]) * h ^ 56 * a7 ^ 3 * a6 * a5 * a3
    - (354200584192000 : F[X]) * h ^ 56 * a7 ^ 3 * a6 * a4 ^ 2
    - (354200584192000 : F[X]) * h ^ 56 * a7 ^ 3 * a5 ^ 2 * a4
    - (672981109964800 : F[X]) * h ^ 56 * a7 ^ 2 * a6 ^ 3 * a3
    - (2018943329894400 : F[X]) * h ^ 56 * a7 ^ 2 * a6 ^ 2 * a5 * a4
    - (672981109964800 : F[X]) * h ^ 56 * a7 ^ 2 * a6 * a5 ^ 3
    - (495880817868800 : F[X]) * h ^ 56 * a7 * a6 ^ 4 * a4
    - (991761635737600 : F[X]) * h ^ 56 * a7 * a6 ^ 3 * a5 ^ 2
    - (131054216151040 : F[X]) * h ^ 56 * a6 ^ 5 * a5
    - (3908420239360 : F[X]) * h ^ 62 * a7 ^ 4 * b1
    - (31267361914880 : F[X]) * h ^ 62 * a7 ^ 3 * a6 * b2
    - (46901042872320 : F[X]) * h ^ 62 * a7 ^ 3 * a5 * b3
    - (62534723829760 : F[X]) * h ^ 62 * a7 ^ 3 * a4 * b4
    - (78168404787200 : F[X]) * h ^ 62 * a7 ^ 3 * a3 * b5
    - (93802085744640 : F[X]) * h ^ 62 * a7 ^ 3 * a2 * b6
    - (109435766702080 : F[X]) * h ^ 62 * a7 ^ 3 * a1 * b7
    - (125069447659520 : F[X]) * h ^ 62 * a7 ^ 3 * a0 * b8
    - (70351564308480 : F[X]) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * b3
    - (187604171489280 : F[X]) * h ^ 62 * a7 ^ 2 * a6 * a5 * b4
    - (234505214361600 : F[X]) * h ^ 62 * a7 ^ 2 * a6 * a4 * b5
    - (281406257233920 : F[X]) * h ^ 62 * a7 ^ 2 * a6 * a3 * b6
    - (328307300106240 : F[X]) * h ^ 62 * a7 ^ 2 * a6 * a2 * b7
    - (375208342978560 : F[X]) * h ^ 62 * a7 ^ 2 * a6 * a1 * b8
    - (117252607180800 : F[X]) * h ^ 62 * a7 ^ 2 * a5 ^ 2 * b5
    - (281406257233920 : F[X]) * h ^ 62 * a7 ^ 2 * a5 * a4 * b6
    - (328307300106240 : F[X]) * h ^ 62 * a7 ^ 2 * a5 * a3 * b7
    - (375208342978560 : F[X]) * h ^ 62 * a7 ^ 2 * a5 * a2 * b8
    - (164153650053120 : F[X]) * h ^ 62 * a7 ^ 2 * a4 ^ 2 * b7
    - (375208342978560 : F[X]) * h ^ 62 * a7 ^ 2 * a4 * a3 * b8
    - (62534723829760 : F[X]) * h ^ 62 * a7 * a6 ^ 3 * b4
    - (234505214361600 : F[X]) * h ^ 62 * a7 * a6 ^ 2 * a5 * b5
    - (281406257233920 : F[X]) * h ^ 62 * a7 * a6 ^ 2 * a4 * b6
    - (328307300106240 : F[X]) * h ^ 62 * a7 * a6 ^ 2 * a3 * b7
    - (375208342978560 : F[X]) * h ^ 62 * a7 * a6 ^ 2 * a2 * b8
    - (281406257233920 : F[X]) * h ^ 62 * a7 * a6 * a5 ^ 2 * b6
    - (656614600212480 : F[X]) * h ^ 62 * a7 * a6 * a5 * a4 * b7
    - (750416685957120 : F[X]) * h ^ 62 * a7 * a6 * a5 * a3 * b8
    - (375208342978560 : F[X]) * h ^ 62 * a7 * a6 * a4 ^ 2 * b8
    - (109435766702080 : F[X]) * h ^ 62 * a7 * a5 ^ 3 * b7
    - (375208342978560 : F[X]) * h ^ 62 * a7 * a5 ^ 2 * a4 * b8
    - (19542101196800 : F[X]) * h ^ 62 * a6 ^ 4 * b5
    - (93802085744640 : F[X]) * h ^ 62 * a6 ^ 3 * a5 * b6
    - (109435766702080 : F[X]) * h ^ 62 * a6 ^ 3 * a4 * b7
    - (125069447659520 : F[X]) * h ^ 62 * a6 ^ 3 * a3 * b8
    - (164153650053120 : F[X]) * h ^ 62 * a6 ^ 2 * a5 ^ 2 * b7
    - (375208342978560 : F[X]) * h ^ 62 * a6 ^ 2 * a5 * a4 * b8
    - (125069447659520 : F[X]) * h ^ 62 * a6 * a5 ^ 3 * b8
    - (31878052577280 : F[X]) * h ^ 63 * a7 ^ 4 * a0 * Polynomial.C lambda
    - (127512210309120 : F[X]) * h ^ 63 * a7 ^ 3 * a6 * a1 * Polynomial.C lambda
    - (127512210309120 : F[X]) * h ^ 63 * a7 ^ 3 * a5 * a2 * Polynomial.C lambda
    - (127512210309120 : F[X]) * h ^ 63 * a7 ^ 3 * a4 * a3 * Polynomial.C lambda
    - (191268315463680 : F[X]) * h ^ 63 * a7 ^ 2 * a6 ^ 2 * a2 * Polynomial.C lambda
    - (382536630927360 : F[X]) * h ^ 63 * a7 ^ 2 * a6 * a5 * a3 * Polynomial.C lambda
    - (191268315463680 : F[X]) * h ^ 63 * a7 ^ 2 * a6 * a4 ^ 2 * Polynomial.C lambda
    - (191268315463680 : F[X]) * h ^ 63 * a7 ^ 2 * a5 ^ 2 * a4 * Polynomial.C lambda
    - (127512210309120 : F[X]) * h ^ 63 * a7 * a6 ^ 3 * a3 * Polynomial.C lambda
    - (382536630927360 : F[X]) * h ^ 63 * a7 * a6 ^ 2 * a5 * a4 * Polynomial.C lambda
    - (127512210309120 : F[X]) * h ^ 63 * a7 * a6 * a5 ^ 3 * Polynomial.C lambda
    - (31878052577280 : F[X]) * h ^ 63 * a6 ^ 4 * a4 * Polynomial.C lambda
    - (63756105154560 : F[X]) * h ^ 63 * a6 ^ 3 * a5 ^ 2 * Polynomial.C lambda
    + (39084202393600 : F[X]) * h ^ 64 * a7 ^ 3 * a6 * a0
    + (39084202393600 : F[X]) * h ^ 64 * a7 ^ 3 * a5 * a1
    + (39084202393600 : F[X]) * h ^ 64 * a7 ^ 3 * a4 * a2
    + (19542101196800 : F[X]) * h ^ 64 * a7 ^ 3 * a3 ^ 2
    + (322444669747200 : F[X]) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a1
    + (644889339494400 : F[X]) * h ^ 64 * a7 ^ 2 * a6 * a5 * a2
    + (644889339494400 : F[X]) * h ^ 64 * a7 ^ 2 * a6 * a4 * a3
    + (322444669747200 : F[X]) * h ^ 64 * a7 ^ 2 * a5 ^ 2 * a3
    + (322444669747200 : F[X]) * h ^ 64 * a7 ^ 2 * a5 * a4 ^ 2
    + (390842023936000 : F[X]) * h ^ 64 * a7 * a6 ^ 3 * a2
    + (1172526071808000 : F[X]) * h ^ 64 * a7 * a6 ^ 2 * a5 * a3
    + (586263035904000 : F[X]) * h ^ 64 * a7 * a6 ^ 2 * a4 ^ 2
    + (1172526071808000 : F[X]) * h ^ 64 * a7 * a6 * a5 ^ 2 * a4
    + (97710505984000 : F[X]) * h ^ 64 * a7 * a5 ^ 4
    + (141680233676800 : F[X]) * h ^ 64 * a6 ^ 4 * a3
    + (566720934707200 : F[X]) * h ^ 64 * a6 ^ 3 * a5 * a4
    + (283360467353600 : F[X]) * h ^ 64 * a6 ^ 2 * a5 ^ 3
    + (17867063951360 : F[X]) * h ^ 70 * a7 ^ 2 * a6 * b1
    + (35734127902720 : F[X]) * h ^ 70 * a7 ^ 2 * a5 * b2
    + (53601191854080 : F[X]) * h ^ 70 * a7 ^ 2 * a4 * b3
    + (71468255805440 : F[X]) * h ^ 70 * a7 ^ 2 * a3 * b4
    + (89335319756800 : F[X]) * h ^ 70 * a7 ^ 2 * a2 * b5
    + (107202383708160 : F[X]) * h ^ 70 * a7 ^ 2 * a1 * b6
    + (125069447659520 : F[X]) * h ^ 70 * a7 ^ 2 * a0 * b7
    + (35734127902720 : F[X]) * h ^ 70 * a7 * a6 ^ 2 * b2
    + (107202383708160 : F[X]) * h ^ 70 * a7 * a6 * a5 * b3
    + (142936511610880 : F[X]) * h ^ 70 * a7 * a6 * a4 * b4
    + (178670639513600 : F[X]) * h ^ 70 * a7 * a6 * a3 * b5
    + (214404767416320 : F[X]) * h ^ 70 * a7 * a6 * a2 * b6
    + (250138895319040 : F[X]) * h ^ 70 * a7 * a6 * a1 * b7
    + (285873023221760 : F[X]) * h ^ 70 * a7 * a6 * a0 * b8
    + (71468255805440 : F[X]) * h ^ 70 * a7 * a5 ^ 2 * b4
    + (178670639513600 : F[X]) * h ^ 70 * a7 * a5 * a4 * b5
    + (214404767416320 : F[X]) * h ^ 70 * a7 * a5 * a3 * b6
    + (250138895319040 : F[X]) * h ^ 70 * a7 * a5 * a2 * b7
    + (285873023221760 : F[X]) * h ^ 70 * a7 * a5 * a1 * b8
    + (107202383708160 : F[X]) * h ^ 70 * a7 * a4 ^ 2 * b6
    + (250138895319040 : F[X]) * h ^ 70 * a7 * a4 * a3 * b7
    + (285873023221760 : F[X]) * h ^ 70 * a7 * a4 * a2 * b8
    + (142936511610880 : F[X]) * h ^ 70 * a7 * a3 ^ 2 * b8
    + (17867063951360 : F[X]) * h ^ 70 * a6 ^ 3 * b3
    + (71468255805440 : F[X]) * h ^ 70 * a6 ^ 2 * a5 * b4
    + (89335319756800 : F[X]) * h ^ 70 * a6 ^ 2 * a4 * b5
    + (107202383708160 : F[X]) * h ^ 70 * a6 ^ 2 * a3 * b6
    + (125069447659520 : F[X]) * h ^ 70 * a6 ^ 2 * a2 * b7
    + (142936511610880 : F[X]) * h ^ 70 * a6 ^ 2 * a1 * b8
    + (89335319756800 : F[X]) * h ^ 70 * a6 * a5 ^ 2 * b5
    + (214404767416320 : F[X]) * h ^ 70 * a6 * a5 * a4 * b6
    + (250138895319040 : F[X]) * h ^ 70 * a6 * a5 * a3 * b7
    + (285873023221760 : F[X]) * h ^ 70 * a6 * a5 * a2 * b8
    + (125069447659520 : F[X]) * h ^ 70 * a6 * a4 ^ 2 * b7
    + (285873023221760 : F[X]) * h ^ 70 * a6 * a4 * a3 * b8
    + (35734127902720 : F[X]) * h ^ 70 * a5 ^ 3 * b6
    + (125069447659520 : F[X]) * h ^ 70 * a5 ^ 2 * a4 * b7
    + (142936511610880 : F[X]) * h ^ 70 * a5 ^ 2 * a3 * b8
    + (142936511610880 : F[X]) * h ^ 70 * a5 * a4 ^ 2 * b8
    + (105527346462720 : F[X]) * h ^ 71 * a7 ^ 2 * a6 * a0 * Polynomial.C lambda
    + (105527346462720 : F[X]) * h ^ 71 * a7 ^ 2 * a5 * a1 * Polynomial.C lambda
    + (105527346462720 : F[X]) * h ^ 71 * a7 ^ 2 * a4 * a2 * Polynomial.C lambda
    + (52763673231360 : F[X]) * h ^ 71 * a7 ^ 2 * a3 ^ 2 * Polynomial.C lambda
    + (105527346462720 : F[X]) * h ^ 71 * a7 * a6 ^ 2 * a1 * Polynomial.C lambda
    + (211054692925440 : F[X]) * h ^ 71 * a7 * a6 * a5 * a2 * Polynomial.C lambda
    + (211054692925440 : F[X]) * h ^ 71 * a7 * a6 * a4 * a3 * Polynomial.C lambda
    + (105527346462720 : F[X]) * h ^ 71 * a7 * a5 ^ 2 * a3 * Polynomial.C lambda
    + (105527346462720 : F[X]) * h ^ 71 * a7 * a5 * a4 ^ 2 * Polynomial.C lambda
    + (35175782154240 : F[X]) * h ^ 71 * a6 ^ 3 * a2 * Polynomial.C lambda
    + (105527346462720 : F[X]) * h ^ 71 * a6 ^ 2 * a5 * a3 * Polynomial.C lambda
    + (52763673231360 : F[X]) * h ^ 71 * a6 ^ 2 * a4 ^ 2 * Polynomial.C lambda
    + (105527346462720 : F[X]) * h ^ 71 * a6 * a5 ^ 2 * a4 * Polynomial.C lambda
    + (8793945538560 : F[X]) * h ^ 71 * a5 ^ 4 * Polynomial.C lambda
    - (67001489817600 : F[X]) * h ^ 72 * a7 ^ 2 * a5 * a0
    - (67001489817600 : F[X]) * h ^ 72 * a7 ^ 2 * a4 * a1
    - (67001489817600 : F[X]) * h ^ 72 * a7 ^ 2 * a3 * a2
    - (268005959270400 : F[X]) * h ^ 72 * a7 * a6 ^ 2 * a0
    - (536011918540800 : F[X]) * h ^ 72 * a7 * a6 * a5 * a1
    - (536011918540800 : F[X]) * h ^ 72 * a7 * a6 * a4 * a2
    - (268005959270400 : F[X]) * h ^ 72 * a7 * a6 * a3 ^ 2
    - (268005959270400 : F[X]) * h ^ 72 * a7 * a5 ^ 2 * a2
    - (536011918540800 : F[X]) * h ^ 72 * a7 * a5 * a4 * a3
    - (89335319756800 : F[X]) * h ^ 72 * a7 * a4 ^ 3
    - (156336809574400 : F[X]) * h ^ 72 * a6 ^ 3 * a1
    - (469010428723200 : F[X]) * h ^ 72 * a6 ^ 2 * a5 * a2
    - (469010428723200 : F[X]) * h ^ 72 * a6 ^ 2 * a4 * a3
    - (469010428723200 : F[X]) * h ^ 72 * a6 * a5 ^ 2 * a3
    - (469010428723200 : F[X]) * h ^ 72 * a6 * a5 * a4 ^ 2
    - (156336809574400 : F[X]) * h ^ 72 * a5 ^ 3 * a4
    - (21990232555520 : F[X]) * h ^ 78 * a7 * a5 * b1
    - (43980465111040 : F[X]) * h ^ 78 * a7 * a4 * b2
    - (65970697666560 : F[X]) * h ^ 78 * a7 * a3 * b3
    - (87960930222080 : F[X]) * h ^ 78 * a7 * a2 * b4
    - (109951162777600 : F[X]) * h ^ 78 * a7 * a1 * b5
    - (131941395333120 : F[X]) * h ^ 78 * a7 * a0 * b6
    - (10995116277760 : F[X]) * h ^ 78 * a6 ^ 2 * b1
    - (43980465111040 : F[X]) * h ^ 78 * a6 * a5 * b2
    - (65970697666560 : F[X]) * h ^ 78 * a6 * a4 * b3
    - (87960930222080 : F[X]) * h ^ 78 * a6 * a3 * b4
    - (109951162777600 : F[X]) * h ^ 78 * a6 * a2 * b5
    - (131941395333120 : F[X]) * h ^ 78 * a6 * a1 * b6
    - (153931627888640 : F[X]) * h ^ 78 * a6 * a0 * b7
    - (32985348833280 : F[X]) * h ^ 78 * a5 ^ 2 * b3
    - (87960930222080 : F[X]) * h ^ 78 * a5 * a4 * b4
    - (109951162777600 : F[X]) * h ^ 78 * a5 * a3 * b5
    - (131941395333120 : F[X]) * h ^ 78 * a5 * a2 * b6
    - (153931627888640 : F[X]) * h ^ 78 * a5 * a1 * b7
    - (175921860444160 : F[X]) * h ^ 78 * a5 * a0 * b8
    - (54975581388800 : F[X]) * h ^ 78 * a4 ^ 2 * b5
    - (131941395333120 : F[X]) * h ^ 78 * a4 * a3 * b6
    - (153931627888640 : F[X]) * h ^ 78 * a4 * a2 * b7
    - (175921860444160 : F[X]) * h ^ 78 * a4 * a1 * b8
    - (76965813944320 : F[X]) * h ^ 78 * a3 ^ 2 * b7
    - (175921860444160 : F[X]) * h ^ 78 * a3 * a2 * b8
    - (80401787781120 : F[X]) * h ^ 79 * a7 * a5 * a0 * Polynomial.C lambda
    - (80401787781120 : F[X]) * h ^ 79 * a7 * a4 * a1 * Polynomial.C lambda
    - (80401787781120 : F[X]) * h ^ 79 * a7 * a3 * a2 * Polynomial.C lambda
    - (40200893890560 : F[X]) * h ^ 79 * a6 ^ 2 * a0 * Polynomial.C lambda
    - (80401787781120 : F[X]) * h ^ 79 * a6 * a5 * a1 * Polynomial.C lambda
    - (80401787781120 : F[X]) * h ^ 79 * a6 * a4 * a2 * Polynomial.C lambda
    - (40200893890560 : F[X]) * h ^ 79 * a6 * a3 ^ 2 * Polynomial.C lambda
    - (40200893890560 : F[X]) * h ^ 79 * a5 ^ 2 * a2 * Polynomial.C lambda
    - (80401787781120 : F[X]) * h ^ 79 * a5 * a4 * a3 * Polynomial.C lambda
    - (13400297963520 : F[X]) * h ^ 79 * a4 ^ 3 * Polynomial.C lambda
    + (109951162777600 : F[X]) * h ^ 80 * a7 * a4 * a0
    + (109951162777600 : F[X]) * h ^ 80 * a7 * a3 * a1
    + (54975581388800 : F[X]) * h ^ 80 * a7 * a2 ^ 2
    + (357341279027200 : F[X]) * h ^ 80 * a6 * a5 * a0
    + (357341279027200 : F[X]) * h ^ 80 * a6 * a4 * a1
    + (357341279027200 : F[X]) * h ^ 80 * a6 * a3 * a2
    + (178670639513600 : F[X]) * h ^ 80 * a5 ^ 2 * a1
    + (357341279027200 : F[X]) * h ^ 80 * a5 * a4 * a2
    + (178670639513600 : F[X]) * h ^ 80 * a5 * a3 ^ 2
    + (178670639513600 : F[X]) * h ^ 80 * a4 ^ 2 * a3
    + (35184372088832 : F[X]) * h ^ 86 * a4 * b1
    + (70368744177664 : F[X]) * h ^ 86 * a3 * b2
    + (105553116266496 : F[X]) * h ^ 86 * a2 * b3
    + (140737488355328 : F[X]) * h ^ 86 * a1 * b4
    + (175921860444160 : F[X]) * h ^ 86 * a0 * b5
    + (49478023249920 : F[X]) * h ^ 87 * a4 * a0 * Polynomial.C lambda
    + (49478023249920 : F[X]) * h ^ 87 * a3 * a1 * Polynomial.C lambda
    + (24739011624960 : F[X]) * h ^ 87 * a2 ^ 2 * Polynomial.C lambda
    - (219902325555200 : F[X]) * h ^ 88 * a3 * a0
    - (219902325555200 : F[X]) * h ^ 88 * a2 * a1

set_option maxHeartbeats 400000000 in
/-- Clearing the first integral `ν` of the degree-`4` row against `h⁹¹`
on the ninth-power face. -/
theorem thirteenthDefect_eq_clearedNu810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (281474976710656 : F) * h ^ 91 *
        nuResidual810
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
    - (1898935526600 : F) * a7 ^ 13
    + (7434891097088 : F) * h ^ 6 * a7 ^ 11 * b8
    + (1851462138435 : F) * h ^ 7 * a7 ^ 12 * lambda
    + (16263824274880 : F) * h ^ 8 * a7 ^ 11 * a6
    - (7434891097088 : F) * h ^ 14 * a7 ^ 10 * b7
    - (84970183966720 : F) * h ^ 14 * a7 ^ 9 * a6 * b8
    - (23001694331616 : F) * h ^ 15 * a7 ^ 10 * a6 * lambda
    - (17259568618240 : F) * h ^ 16 * a7 ^ 10 * a5
    - (26553182489600 : F) * h ^ 16 * a7 ^ 9 * a6 ^ 2
    + (7388711649280 : F) * h ^ 22 * a7 ^ 9 * b6
    + (77581472317440 : F) * h ^ 22 * a7 ^ 8 * a6 * b7
    + (88664539791360 : F) * h ^ 22 * a7 ^ 8 * a5 * b8
    + (354658159165440 : F) * h ^ 22 * a7 ^ 7 * a6 ^ 2 * b8
    + (23897864240640 : F) * h ^ 23 * a7 ^ 9 * a5 * lambda
    + (107540389082880 : F) * h ^ 23 * a7 ^ 8 * a6 ^ 2 * lambda
    + (18471779123200 : F) * h ^ 24 * a7 ^ 9 * a4
    + (41561503027200 : F) * h ^ 24 * a7 ^ 8 * a6 * a5
    - (110830674739200 : F) * h ^ 24 * a7 ^ 7 * a6 ^ 3
    - (7267585228800 : F) * h ^ 30 * a7 ^ 8 * b5
    - (69768818196480 : F) * h ^ 30 * a7 ^ 7 * a6 * b6
    - (81396954562560 : F) * h ^ 30 * a7 ^ 7 * a5 * b7
    - (93025090928640 : F) * h ^ 30 * a7 ^ 7 * a4 * b8
    - (284889340968960 : F) * h ^ 30 * a7 ^ 6 * a6 ^ 2 * b7
    - (651175636500480 : F) * h ^ 30 * a7 ^ 6 * a6 * a5 * b8
    - (651175636500480 : F) * h ^ 30 * a7 ^ 5 * a6 ^ 3 * b8
    - (24936901816320 : F) * h ^ 31 * a7 ^ 8 * a4 * lambda
    - (199495214530560 : F) * h ^ 31 * a7 ^ 7 * a6 * a5 * lambda
    - (232744416952320 : F) * h ^ 31 * a7 ^ 6 * a6 ^ 3 * lambda
    - (19985859379200 : F) * h ^ 32 * a7 ^ 8 * a3
    - (29070340915200 : F) * h ^ 32 * a7 ^ 7 * a6 * a4
    - (14535170457600 : F) * h ^ 32 * a7 ^ 7 * a5 ^ 2
    + (356111676211200 : F) * h ^ 32 * a7 ^ 6 * a6 ^ 2 * a5
    + (406984772812800 : F) * h ^ 32 * a7 ^ 5 * a6 ^ 4
    + (7020761579520 : F) * h ^ 38 * a7 ^ 7 * b4
    + (61431663820800 : F) * h ^ 38 * a7 ^ 6 * a6 * b5
    + (73717996584960 : F) * h ^ 38 * a7 ^ 6 * a5 * b6
    + (86004329349120 : F) * h ^ 38 * a7 ^ 6 * a4 * b7
    + (98290662113280 : F) * h ^ 38 * a7 ^ 6 * a3 * b8
    + (221153989754880 : F) * h ^ 38 * a7 ^ 5 * a6 ^ 2 * b6
    + (516025976094720 : F) * h ^ 38 * a7 ^ 5 * a6 * a5 * b7
    + (589743972679680 : F) * h ^ 38 * a7 ^ 5 * a6 * a4 * b8
    + (294871986339840 : F) * h ^ 38 * a7 ^ 5 * a5 ^ 2 * b8
    + (430021646745600 : F) * h ^ 38 * a7 ^ 4 * a6 ^ 3 * b7
    + (1474359931699200 : F) * h ^ 38 * a7 ^ 4 * a6 ^ 2 * a5 * b8
    + (491453310566400 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 4 * b8
    + (26163306823680 : F) * h ^ 39 * a7 ^ 7 * a3 * lambda
    + (183143147765760 : F) * h ^ 39 * a7 ^ 6 * a6 * a4 * lambda
    + (91571573882880 : F) * h ^ 39 * a7 ^ 6 * a5 ^ 2 * lambda
    + (549429443297280 : F) * h ^ 39 * a7 ^ 5 * a6 ^ 2 * a5 * lambda
    + (228928934707200 : F) * h ^ 39 * a7 ^ 4 * a6 ^ 4 * lambda
    + (21939879936000 : F) * h ^ 40 * a7 ^ 7 * a2
    + (15357915955200 : F) * h ^ 40 * a7 ^ 6 * a6 * a3
    + (15357915955200 : F) * h ^ 40 * a7 ^ 6 * a5 * a4
    - (368589982924800 : F) * h ^ 40 * a7 ^ 5 * a6 ^ 2 * a4
    - (368589982924800 : F) * h ^ 40 * a7 ^ 5 * a6 * a5 ^ 2
    - (1305422856192000 : F) * h ^ 40 * a7 ^ 4 * a6 ^ 3 * a5
    - (399305814835200 : F) * h ^ 40 * a7 ^ 3 * a6 ^ 5
    - (6552710807552 : F) * h ^ 46 * a7 ^ 6 * b3
    - (52421686460416 : F) * h ^ 46 * a7 ^ 5 * a6 * b4
    - (65527108075520 : F) * h ^ 46 * a7 ^ 5 * a5 * b5
    - (78632529690624 : F) * h ^ 46 * a7 ^ 5 * a4 * b6
    - (91737951305728 : F) * h ^ 46 * a7 ^ 5 * a3 * b7
    - (104843372920832 : F) * h ^ 46 * a7 ^ 5 * a2 * b8
    - (163817770188800 : F) * h ^ 46 * a7 ^ 4 * a6 ^ 2 * b5
    - (393162648453120 : F) * h ^ 46 * a7 ^ 4 * a6 * a5 * b6
    - (458689756528640 : F) * h ^ 46 * a7 ^ 4 * a6 * a4 * b7
    - (524216864604160 : F) * h ^ 46 * a7 ^ 4 * a6 * a3 * b8
    - (229344878264320 : F) * h ^ 46 * a7 ^ 4 * a5 ^ 2 * b7
    - (524216864604160 : F) * h ^ 46 * a7 ^ 4 * a5 * a4 * b8
    - (262108432302080 : F) * h ^ 46 * a7 ^ 3 * a6 ^ 3 * b6
    - (917379513057280 : F) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * a5 * b7
    - (1048433729208320 : F) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * a4 * b8
    - (1048433729208320 : F) * h ^ 46 * a7 ^ 3 * a6 * a5 ^ 2 * b8
    - (229344878264320 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 4 * b7
    - (1048433729208320 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 3 * a5 * b8
    - (104843372920832 : F) * h ^ 46 * a7 * a6 ^ 5 * b8
    - (27644248719360 : F) * h ^ 47 * a7 ^ 6 * a2 * lambda
    - (165865492316160 : F) * h ^ 47 * a7 ^ 5 * a6 * a3 * lambda
    - (165865492316160 : F) * h ^ 47 * a7 ^ 5 * a5 * a4 * lambda
    - (414663730790400 : F) * h ^ 47 * a7 ^ 4 * a6 ^ 2 * a4 * lambda
    - (414663730790400 : F) * h ^ 47 * a7 ^ 4 * a6 * a5 ^ 2 * lambda
    - (552884974387200 : F) * h ^ 47 * a7 ^ 3 * a6 ^ 3 * a5 * lambda
    - (82932746158080 : F) * h ^ 47 * a7 ^ 2 * a6 ^ 5 * lambda
    - (24572665528320 : F) * h ^ 48 * a7 ^ 6 * a1
    + (368589982924800 : F) * h ^ 48 * a7 ^ 4 * a6 ^ 2 * a3
    + (737179965849600 : F) * h ^ 48 * a7 ^ 4 * a6 * a5 * a4
    + (122863327641600 : F) * h ^ 48 * a7 ^ 4 * a5 ^ 3
    + (982906621132800 : F) * h ^ 48 * a7 ^ 3 * a6 ^ 3 * a4
    + (1474359931699200 : F) * h ^ 48 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2
    + (1105769948774400 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 4 * a5
    + (98290662113280 : F) * h ^ 48 * a7 * a6 ^ 6
    + (5667209347072 : F) * h ^ 54 * a7 ^ 5 * b2
    + (42504070103040 : F) * h ^ 54 * a7 ^ 4 * a6 * b3
    + (56672093470720 : F) * h ^ 54 * a7 ^ 4 * a5 * b4
    + (70840116838400 : F) * h ^ 54 * a7 ^ 4 * a4 * b5
    + (85008140206080 : F) * h ^ 54 * a7 ^ 4 * a3 * b6
    + (99176163573760 : F) * h ^ 54 * a7 ^ 4 * a2 * b7
    + (113344186941440 : F) * h ^ 54 * a7 ^ 4 * a1 * b8
    + (113344186941440 : F) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * b4
    + (283360467353600 : F) * h ^ 54 * a7 ^ 3 * a6 * a5 * b5
    + (340032560824320 : F) * h ^ 54 * a7 ^ 3 * a6 * a4 * b6
    + (396704654295040 : F) * h ^ 54 * a7 ^ 3 * a6 * a3 * b7
    + (453376747765760 : F) * h ^ 54 * a7 ^ 3 * a6 * a2 * b8
    + (170016280412160 : F) * h ^ 54 * a7 ^ 3 * a5 ^ 2 * b6
    + (396704654295040 : F) * h ^ 54 * a7 ^ 3 * a5 * a4 * b7
    + (453376747765760 : F) * h ^ 54 * a7 ^ 3 * a5 * a3 * b8
    + (226688373882880 : F) * h ^ 54 * a7 ^ 3 * a4 ^ 2 * b8
    + (141680233676800 : F) * h ^ 54 * a7 ^ 2 * a6 ^ 3 * b5
    + (510048841236480 : F) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a5 * b6
    + (595056981442560 : F) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a4 * b7
    + (680065121648640 : F) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a3 * b8
    + (595056981442560 : F) * h ^ 54 * a7 ^ 2 * a6 * a5 ^ 2 * b7
    + (1360130243297280 : F) * h ^ 54 * a7 ^ 2 * a6 * a5 * a4 * b8
    + (226688373882880 : F) * h ^ 54 * a7 ^ 2 * a5 ^ 3 * b8
    + (85008140206080 : F) * h ^ 54 * a7 * a6 ^ 4 * b6
    + (396704654295040 : F) * h ^ 54 * a7 * a6 ^ 3 * a5 * b7
    + (453376747765760 : F) * h ^ 54 * a7 * a6 ^ 3 * a4 * b8
    + (680065121648640 : F) * h ^ 54 * a7 * a6 ^ 2 * a5 ^ 2 * b8
    + (19835232714752 : F) * h ^ 54 * a6 ^ 5 * b7
    + (113344186941440 : F) * h ^ 54 * a6 ^ 4 * a5 * b8
    + (29487198633984 : F) * h ^ 55 * a7 ^ 5 * a1 * lambda
    + (147435993169920 : F) * h ^ 55 * a7 ^ 4 * a6 * a2 * lambda
    + (147435993169920 : F) * h ^ 55 * a7 ^ 4 * a5 * a3 * lambda
    + (73717996584960 : F) * h ^ 55 * a7 ^ 4 * a4 ^ 2 * lambda
    + (294871986339840 : F) * h ^ 55 * a7 ^ 3 * a6 ^ 2 * a3 * lambda
    + (589743972679680 : F) * h ^ 55 * a7 ^ 3 * a6 * a5 * a4 * lambda
    + (98290662113280 : F) * h ^ 55 * a7 ^ 3 * a5 ^ 3 * lambda
    + (294871986339840 : F) * h ^ 55 * a7 ^ 2 * a6 ^ 3 * a4 * lambda
    + (442307979509760 : F) * h ^ 55 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * lambda
    + (147435993169920 : F) * h ^ 55 * a7 * a6 ^ 4 * a5 * lambda
    + (4914533105664 : F) * h ^ 55 * a6 ^ 6 * lambda
    + (28336046735360 : F) * h ^ 56 * a7 ^ 5 * a0
    - (17710029209600 : F) * h ^ 56 * a7 ^ 4 * a6 * a1
    - (17710029209600 : F) * h ^ 56 * a7 ^ 4 * a5 * a2
    - (17710029209600 : F) * h ^ 56 * a7 ^ 4 * a4 * a3
    - (354200584192000 : F) * h ^ 56 * a7 ^ 3 * a6 ^ 2 * a2
    - (708401168384000 : F) * h ^ 56 * a7 ^ 3 * a6 * a5 * a3
    - (354200584192000 : F) * h ^ 56 * a7 ^ 3 * a6 * a4 ^ 2
    - (354200584192000 : F) * h ^ 56 * a7 ^ 3 * a5 ^ 2 * a4
    - (672981109964800 : F) * h ^ 56 * a7 ^ 2 * a6 ^ 3 * a3
    - (2018943329894400 : F) * h ^ 56 * a7 ^ 2 * a6 ^ 2 * a5 * a4
    - (672981109964800 : F) * h ^ 56 * a7 ^ 2 * a6 * a5 ^ 3
    - (495880817868800 : F) * h ^ 56 * a7 * a6 ^ 4 * a4
    - (991761635737600 : F) * h ^ 56 * a7 * a6 ^ 3 * a5 ^ 2
    - (131054216151040 : F) * h ^ 56 * a6 ^ 5 * a5
    - (3908420239360 : F) * h ^ 62 * a7 ^ 4 * b1
    - (31267361914880 : F) * h ^ 62 * a7 ^ 3 * a6 * b2
    - (46901042872320 : F) * h ^ 62 * a7 ^ 3 * a5 * b3
    - (62534723829760 : F) * h ^ 62 * a7 ^ 3 * a4 * b4
    - (78168404787200 : F) * h ^ 62 * a7 ^ 3 * a3 * b5
    - (93802085744640 : F) * h ^ 62 * a7 ^ 3 * a2 * b6
    - (109435766702080 : F) * h ^ 62 * a7 ^ 3 * a1 * b7
    - (125069447659520 : F) * h ^ 62 * a7 ^ 3 * a0 * b8
    - (70351564308480 : F) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * b3
    - (187604171489280 : F) * h ^ 62 * a7 ^ 2 * a6 * a5 * b4
    - (234505214361600 : F) * h ^ 62 * a7 ^ 2 * a6 * a4 * b5
    - (281406257233920 : F) * h ^ 62 * a7 ^ 2 * a6 * a3 * b6
    - (328307300106240 : F) * h ^ 62 * a7 ^ 2 * a6 * a2 * b7
    - (375208342978560 : F) * h ^ 62 * a7 ^ 2 * a6 * a1 * b8
    - (117252607180800 : F) * h ^ 62 * a7 ^ 2 * a5 ^ 2 * b5
    - (281406257233920 : F) * h ^ 62 * a7 ^ 2 * a5 * a4 * b6
    - (328307300106240 : F) * h ^ 62 * a7 ^ 2 * a5 * a3 * b7
    - (375208342978560 : F) * h ^ 62 * a7 ^ 2 * a5 * a2 * b8
    - (164153650053120 : F) * h ^ 62 * a7 ^ 2 * a4 ^ 2 * b7
    - (375208342978560 : F) * h ^ 62 * a7 ^ 2 * a4 * a3 * b8
    - (62534723829760 : F) * h ^ 62 * a7 * a6 ^ 3 * b4
    - (234505214361600 : F) * h ^ 62 * a7 * a6 ^ 2 * a5 * b5
    - (281406257233920 : F) * h ^ 62 * a7 * a6 ^ 2 * a4 * b6
    - (328307300106240 : F) * h ^ 62 * a7 * a6 ^ 2 * a3 * b7
    - (375208342978560 : F) * h ^ 62 * a7 * a6 ^ 2 * a2 * b8
    - (281406257233920 : F) * h ^ 62 * a7 * a6 * a5 ^ 2 * b6
    - (656614600212480 : F) * h ^ 62 * a7 * a6 * a5 * a4 * b7
    - (750416685957120 : F) * h ^ 62 * a7 * a6 * a5 * a3 * b8
    - (375208342978560 : F) * h ^ 62 * a7 * a6 * a4 ^ 2 * b8
    - (109435766702080 : F) * h ^ 62 * a7 * a5 ^ 3 * b7
    - (375208342978560 : F) * h ^ 62 * a7 * a5 ^ 2 * a4 * b8
    - (19542101196800 : F) * h ^ 62 * a6 ^ 4 * b5
    - (93802085744640 : F) * h ^ 62 * a6 ^ 3 * a5 * b6
    - (109435766702080 : F) * h ^ 62 * a6 ^ 3 * a4 * b7
    - (125069447659520 : F) * h ^ 62 * a6 ^ 3 * a3 * b8
    - (164153650053120 : F) * h ^ 62 * a6 ^ 2 * a5 ^ 2 * b7
    - (375208342978560 : F) * h ^ 62 * a6 ^ 2 * a5 * a4 * b8
    - (125069447659520 : F) * h ^ 62 * a6 * a5 ^ 3 * b8
    - (31878052577280 : F) * h ^ 63 * a7 ^ 4 * a0 * lambda
    - (127512210309120 : F) * h ^ 63 * a7 ^ 3 * a6 * a1 * lambda
    - (127512210309120 : F) * h ^ 63 * a7 ^ 3 * a5 * a2 * lambda
    - (127512210309120 : F) * h ^ 63 * a7 ^ 3 * a4 * a3 * lambda
    - (191268315463680 : F) * h ^ 63 * a7 ^ 2 * a6 ^ 2 * a2 * lambda
    - (382536630927360 : F) * h ^ 63 * a7 ^ 2 * a6 * a5 * a3 * lambda
    - (191268315463680 : F) * h ^ 63 * a7 ^ 2 * a6 * a4 ^ 2 * lambda
    - (191268315463680 : F) * h ^ 63 * a7 ^ 2 * a5 ^ 2 * a4 * lambda
    - (127512210309120 : F) * h ^ 63 * a7 * a6 ^ 3 * a3 * lambda
    - (382536630927360 : F) * h ^ 63 * a7 * a6 ^ 2 * a5 * a4 * lambda
    - (127512210309120 : F) * h ^ 63 * a7 * a6 * a5 ^ 3 * lambda
    - (31878052577280 : F) * h ^ 63 * a6 ^ 4 * a4 * lambda
    - (63756105154560 : F) * h ^ 63 * a6 ^ 3 * a5 ^ 2 * lambda
    + (39084202393600 : F) * h ^ 64 * a7 ^ 3 * a6 * a0
    + (39084202393600 : F) * h ^ 64 * a7 ^ 3 * a5 * a1
    + (39084202393600 : F) * h ^ 64 * a7 ^ 3 * a4 * a2
    + (19542101196800 : F) * h ^ 64 * a7 ^ 3 * a3 ^ 2
    + (322444669747200 : F) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a1
    + (644889339494400 : F) * h ^ 64 * a7 ^ 2 * a6 * a5 * a2
    + (644889339494400 : F) * h ^ 64 * a7 ^ 2 * a6 * a4 * a3
    + (322444669747200 : F) * h ^ 64 * a7 ^ 2 * a5 ^ 2 * a3
    + (322444669747200 : F) * h ^ 64 * a7 ^ 2 * a5 * a4 ^ 2
    + (390842023936000 : F) * h ^ 64 * a7 * a6 ^ 3 * a2
    + (1172526071808000 : F) * h ^ 64 * a7 * a6 ^ 2 * a5 * a3
    + (586263035904000 : F) * h ^ 64 * a7 * a6 ^ 2 * a4 ^ 2
    + (1172526071808000 : F) * h ^ 64 * a7 * a6 * a5 ^ 2 * a4
    + (97710505984000 : F) * h ^ 64 * a7 * a5 ^ 4
    + (141680233676800 : F) * h ^ 64 * a6 ^ 4 * a3
    + (566720934707200 : F) * h ^ 64 * a6 ^ 3 * a5 * a4
    + (283360467353600 : F) * h ^ 64 * a6 ^ 2 * a5 ^ 3
    + (17867063951360 : F) * h ^ 70 * a7 ^ 2 * a6 * b1
    + (35734127902720 : F) * h ^ 70 * a7 ^ 2 * a5 * b2
    + (53601191854080 : F) * h ^ 70 * a7 ^ 2 * a4 * b3
    + (71468255805440 : F) * h ^ 70 * a7 ^ 2 * a3 * b4
    + (89335319756800 : F) * h ^ 70 * a7 ^ 2 * a2 * b5
    + (107202383708160 : F) * h ^ 70 * a7 ^ 2 * a1 * b6
    + (125069447659520 : F) * h ^ 70 * a7 ^ 2 * a0 * b7
    + (35734127902720 : F) * h ^ 70 * a7 * a6 ^ 2 * b2
    + (107202383708160 : F) * h ^ 70 * a7 * a6 * a5 * b3
    + (142936511610880 : F) * h ^ 70 * a7 * a6 * a4 * b4
    + (178670639513600 : F) * h ^ 70 * a7 * a6 * a3 * b5
    + (214404767416320 : F) * h ^ 70 * a7 * a6 * a2 * b6
    + (250138895319040 : F) * h ^ 70 * a7 * a6 * a1 * b7
    + (285873023221760 : F) * h ^ 70 * a7 * a6 * a0 * b8
    + (71468255805440 : F) * h ^ 70 * a7 * a5 ^ 2 * b4
    + (178670639513600 : F) * h ^ 70 * a7 * a5 * a4 * b5
    + (214404767416320 : F) * h ^ 70 * a7 * a5 * a3 * b6
    + (250138895319040 : F) * h ^ 70 * a7 * a5 * a2 * b7
    + (285873023221760 : F) * h ^ 70 * a7 * a5 * a1 * b8
    + (107202383708160 : F) * h ^ 70 * a7 * a4 ^ 2 * b6
    + (250138895319040 : F) * h ^ 70 * a7 * a4 * a3 * b7
    + (285873023221760 : F) * h ^ 70 * a7 * a4 * a2 * b8
    + (142936511610880 : F) * h ^ 70 * a7 * a3 ^ 2 * b8
    + (17867063951360 : F) * h ^ 70 * a6 ^ 3 * b3
    + (71468255805440 : F) * h ^ 70 * a6 ^ 2 * a5 * b4
    + (89335319756800 : F) * h ^ 70 * a6 ^ 2 * a4 * b5
    + (107202383708160 : F) * h ^ 70 * a6 ^ 2 * a3 * b6
    + (125069447659520 : F) * h ^ 70 * a6 ^ 2 * a2 * b7
    + (142936511610880 : F) * h ^ 70 * a6 ^ 2 * a1 * b8
    + (89335319756800 : F) * h ^ 70 * a6 * a5 ^ 2 * b5
    + (214404767416320 : F) * h ^ 70 * a6 * a5 * a4 * b6
    + (250138895319040 : F) * h ^ 70 * a6 * a5 * a3 * b7
    + (285873023221760 : F) * h ^ 70 * a6 * a5 * a2 * b8
    + (125069447659520 : F) * h ^ 70 * a6 * a4 ^ 2 * b7
    + (285873023221760 : F) * h ^ 70 * a6 * a4 * a3 * b8
    + (35734127902720 : F) * h ^ 70 * a5 ^ 3 * b6
    + (125069447659520 : F) * h ^ 70 * a5 ^ 2 * a4 * b7
    + (142936511610880 : F) * h ^ 70 * a5 ^ 2 * a3 * b8
    + (142936511610880 : F) * h ^ 70 * a5 * a4 ^ 2 * b8
    + (105527346462720 : F) * h ^ 71 * a7 ^ 2 * a6 * a0 * lambda
    + (105527346462720 : F) * h ^ 71 * a7 ^ 2 * a5 * a1 * lambda
    + (105527346462720 : F) * h ^ 71 * a7 ^ 2 * a4 * a2 * lambda
    + (52763673231360 : F) * h ^ 71 * a7 ^ 2 * a3 ^ 2 * lambda
    + (105527346462720 : F) * h ^ 71 * a7 * a6 ^ 2 * a1 * lambda
    + (211054692925440 : F) * h ^ 71 * a7 * a6 * a5 * a2 * lambda
    + (211054692925440 : F) * h ^ 71 * a7 * a6 * a4 * a3 * lambda
    + (105527346462720 : F) * h ^ 71 * a7 * a5 ^ 2 * a3 * lambda
    + (105527346462720 : F) * h ^ 71 * a7 * a5 * a4 ^ 2 * lambda
    + (35175782154240 : F) * h ^ 71 * a6 ^ 3 * a2 * lambda
    + (105527346462720 : F) * h ^ 71 * a6 ^ 2 * a5 * a3 * lambda
    + (52763673231360 : F) * h ^ 71 * a6 ^ 2 * a4 ^ 2 * lambda
    + (105527346462720 : F) * h ^ 71 * a6 * a5 ^ 2 * a4 * lambda
    + (8793945538560 : F) * h ^ 71 * a5 ^ 4 * lambda
    - (67001489817600 : F) * h ^ 72 * a7 ^ 2 * a5 * a0
    - (67001489817600 : F) * h ^ 72 * a7 ^ 2 * a4 * a1
    - (67001489817600 : F) * h ^ 72 * a7 ^ 2 * a3 * a2
    - (268005959270400 : F) * h ^ 72 * a7 * a6 ^ 2 * a0
    - (536011918540800 : F) * h ^ 72 * a7 * a6 * a5 * a1
    - (536011918540800 : F) * h ^ 72 * a7 * a6 * a4 * a2
    - (268005959270400 : F) * h ^ 72 * a7 * a6 * a3 ^ 2
    - (268005959270400 : F) * h ^ 72 * a7 * a5 ^ 2 * a2
    - (536011918540800 : F) * h ^ 72 * a7 * a5 * a4 * a3
    - (89335319756800 : F) * h ^ 72 * a7 * a4 ^ 3
    - (156336809574400 : F) * h ^ 72 * a6 ^ 3 * a1
    - (469010428723200 : F) * h ^ 72 * a6 ^ 2 * a5 * a2
    - (469010428723200 : F) * h ^ 72 * a6 ^ 2 * a4 * a3
    - (469010428723200 : F) * h ^ 72 * a6 * a5 ^ 2 * a3
    - (469010428723200 : F) * h ^ 72 * a6 * a5 * a4 ^ 2
    - (156336809574400 : F) * h ^ 72 * a5 ^ 3 * a4
    - (21990232555520 : F) * h ^ 78 * a7 * a5 * b1
    - (43980465111040 : F) * h ^ 78 * a7 * a4 * b2
    - (65970697666560 : F) * h ^ 78 * a7 * a3 * b3
    - (87960930222080 : F) * h ^ 78 * a7 * a2 * b4
    - (109951162777600 : F) * h ^ 78 * a7 * a1 * b5
    - (131941395333120 : F) * h ^ 78 * a7 * a0 * b6
    - (10995116277760 : F) * h ^ 78 * a6 ^ 2 * b1
    - (43980465111040 : F) * h ^ 78 * a6 * a5 * b2
    - (65970697666560 : F) * h ^ 78 * a6 * a4 * b3
    - (87960930222080 : F) * h ^ 78 * a6 * a3 * b4
    - (109951162777600 : F) * h ^ 78 * a6 * a2 * b5
    - (131941395333120 : F) * h ^ 78 * a6 * a1 * b6
    - (153931627888640 : F) * h ^ 78 * a6 * a0 * b7
    - (32985348833280 : F) * h ^ 78 * a5 ^ 2 * b3
    - (87960930222080 : F) * h ^ 78 * a5 * a4 * b4
    - (109951162777600 : F) * h ^ 78 * a5 * a3 * b5
    - (131941395333120 : F) * h ^ 78 * a5 * a2 * b6
    - (153931627888640 : F) * h ^ 78 * a5 * a1 * b7
    - (175921860444160 : F) * h ^ 78 * a5 * a0 * b8
    - (54975581388800 : F) * h ^ 78 * a4 ^ 2 * b5
    - (131941395333120 : F) * h ^ 78 * a4 * a3 * b6
    - (153931627888640 : F) * h ^ 78 * a4 * a2 * b7
    - (175921860444160 : F) * h ^ 78 * a4 * a1 * b8
    - (76965813944320 : F) * h ^ 78 * a3 ^ 2 * b7
    - (175921860444160 : F) * h ^ 78 * a3 * a2 * b8
    - (80401787781120 : F) * h ^ 79 * a7 * a5 * a0 * lambda
    - (80401787781120 : F) * h ^ 79 * a7 * a4 * a1 * lambda
    - (80401787781120 : F) * h ^ 79 * a7 * a3 * a2 * lambda
    - (40200893890560 : F) * h ^ 79 * a6 ^ 2 * a0 * lambda
    - (80401787781120 : F) * h ^ 79 * a6 * a5 * a1 * lambda
    - (80401787781120 : F) * h ^ 79 * a6 * a4 * a2 * lambda
    - (40200893890560 : F) * h ^ 79 * a6 * a3 ^ 2 * lambda
    - (40200893890560 : F) * h ^ 79 * a5 ^ 2 * a2 * lambda
    - (80401787781120 : F) * h ^ 79 * a5 * a4 * a3 * lambda
    - (13400297963520 : F) * h ^ 79 * a4 ^ 3 * lambda
    + (109951162777600 : F) * h ^ 80 * a7 * a4 * a0
    + (109951162777600 : F) * h ^ 80 * a7 * a3 * a1
    + (54975581388800 : F) * h ^ 80 * a7 * a2 ^ 2
    + (357341279027200 : F) * h ^ 80 * a6 * a5 * a0
    + (357341279027200 : F) * h ^ 80 * a6 * a4 * a1
    + (357341279027200 : F) * h ^ 80 * a6 * a3 * a2
    + (178670639513600 : F) * h ^ 80 * a5 ^ 2 * a1
    + (357341279027200 : F) * h ^ 80 * a5 * a4 * a2
    + (178670639513600 : F) * h ^ 80 * a5 * a3 ^ 2
    + (178670639513600 : F) * h ^ 80 * a4 ^ 2 * a3
    + (35184372088832 : F) * h ^ 86 * a4 * b1
    + (70368744177664 : F) * h ^ 86 * a3 * b2
    + (105553116266496 : F) * h ^ 86 * a2 * b3
    + (140737488355328 : F) * h ^ 86 * a1 * b4
    + (175921860444160 : F) * h ^ 86 * a0 * b5
    + (49478023249920 : F) * h ^ 87 * a4 * a0 * lambda
    + (49478023249920 : F) * h ^ 87 * a3 * a1 * lambda
    + (24739011624960 : F) * h ^ 87 * a2 ^ 2 * lambda
    - (219902325555200 : F) * h ^ 88 * a3 * a0
    - (219902325555200 : F) * h ^ 88 * a2 * a1 := by
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
  have h4194304 : (4194304 : F) ≠ 0 := by norm_num
  have h281474976710656 : (281474976710656 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  have hh91 : h ^ 91 ≠ 0 := pow_ne_zero 91 hh
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
  simp only [nuResidual810, hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ,
    hR, hS, hT0, hU0, hV0, hW0, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810, thetaResidual810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h256, h512, h1024, h2048,
    h4096, h8192, h16384, h32768, h65536, h131072, h262144, h4194304,
    h16777216, h67108864, h281474976710656, hh14, hh21, hh28, hh35, hh42,
    hh49, hh56, hh63, hh91]
  ring

end Depression810ThirteenthClearing

/-! ## Degree-`4` depressed Jacobian coefficient -/

section DepressedRow810Thirteenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`4` Jacobian coefficient is
exactly `5 S G' + 4 T F' + 3 U E' + 2 V D' + W C'
- F T' - 2 E U' - 3 D V' - 4 C W' - 5 B X'`. -/
theorem differentialJacobian_coeff_4_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 4 =
      (5 : F) * g.coeff 5 * d (f.coeff 0) +
        (4 : F) * g.coeff 4 * d (f.coeff 1) +
        (3 : F) * g.coeff 3 * d (f.coeff 2) +
        (2 : F) * g.coeff 2 * d (f.coeff 3) +
        g.coeff 1 * d (f.coeff 4) -
          f.coeff 1 * d (g.coeff 4) -
          (2 : F) * f.coeff 2 * d (g.coeff 3) -
          (3 : F) * f.coeff 3 * d (g.coeff 2) -
          (4 : F) * f.coeff 4 * d (g.coeff 1) -
          (5 : F) * f.coeff 5 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1),
        (4, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne04_13 : ((0, 4) : ℕ × ℕ) ≠ (1, 3) := by decide
  have hne04_22 : ((0, 4) : ℕ × ℕ) ≠ (2, 2) := by decide
  have hne04_31 : ((0, 4) : ℕ × ℕ) ≠ (3, 1) := by decide
  have hne04_40 : ((0, 4) : ℕ × ℕ) ≠ (4, 0) := by decide
  have hne13_22 : ((1, 3) : ℕ × ℕ) ≠ (2, 2) := by decide
  have hne13_31 : ((1, 3) : ℕ × ℕ) ≠ (3, 1) := by decide
  have hne13_40 : ((1, 3) : ℕ × ℕ) ≠ (4, 0) := by decide
  have hne22_31 : ((2, 2) : ℕ × ℕ) ≠ (3, 1) := by decide
  have hne22_40 : ((2, 2) : ℕ × ℕ) ≠ (4, 0) := by decide
  have hne31_40 : ((3, 1) : ℕ × ℕ) ≠ (4, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 4 =
        (5 : F) * g.coeff 5 * d (f.coeff 0) +
          (4 : F) * g.coeff 4 * d (f.coeff 1) +
          (3 : F) * g.coeff 3 * d (f.coeff 2) +
          (2 : F) * g.coeff 2 * d (f.coeff 3) +
          g.coeff 1 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne04_13, hne04_22, hne04_31, hne04_40]),
        Finset.sum_insert (by simp [hne13_22, hne13_31, hne13_40]),
        Finset.sum_insert (by simp [hne22_31, hne22_40]),
        Finset.sum_insert (by simp [hne31_40]),
        Finset.sum_singleton]
      ring
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
      hder4, hder3, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 4 =
        f.coeff 1 * d (g.coeff 4) +
          (2 : F) * f.coeff 2 * d (g.coeff 3) +
          (3 : F) * f.coeff 3 * d (g.coeff 2) +
          (4 : F) * f.coeff 4 * d (g.coeff 1) +
          (5 : F) * f.coeff 5 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne04_13, hne04_22, hne04_31, hne04_40]),
        Finset.sum_insert (by simp [hne13_22, hne13_31, hne13_40]),
        Finset.sum_insert (by simp [hne22_31, hne22_40]),
        Finset.sum_insert (by simp [hne31_40]),
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
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder0, hder1, hder2, hder3, hder4]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 400000000 in
theorem nuResidual810_deriv_zero
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
    (hrow6 : (7 : F) * Q * d G0 + (6 : F) * R * d F0 +
        (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        W0 * d A -
        F0 * d R - (2 : F) * E0 * d S0 -
        (3 : F) * D0 * d T0 - (4 : F) * C0 * d U0 -
        (5 : F) * B * d V0 - (6 : F) * A * d W0 = 0)
    (hrow : (5 : F) * S0 * d G0 + (4 : F) * T0 * d F0 +
        (3 : F) * U0 * d E0 + (2 : F) * V0 * d D0 +
        W0 * d C0 -
        F0 * d T0 - (2 : F) * E0 * d U0 -
        (3 : F) * D0 * d V0 - (4 : F) * C0 * d W0 -
        (5 : F) * B * d X0 = 0) :
    d (nuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 := by
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
  have hn25 : d (25 : F) = 0 := d.map_natCast 25
  have hn27 : d (27 : F) = 0 := d.map_natCast 27
  have hn49 : d (49 : F) = 0 := d.map_natCast 49
  have hn55 : d (55 : F) = 0 := d.map_natCast 55
  have hn135 : d (135 : F) = 0 := d.map_natCast 135
  have hn147 : d (147 : F) = 0 := d.map_natCast 147
  have hn175 : d (175 : F) = 0 := d.map_natCast 175
  have hn195 : d (195 : F) = 0 := d.map_natCast 195
  have hn357 : d (357 : F) = 0 := d.map_natCast 357
  have hn665 : d (665 : F) = 0 := d.map_natCast 665
  have hn819 : d (819 : F) = 0 := d.map_natCast 819
  have hn825 : d (825 : F) = 0 := d.map_natCast 825
  have hn1575 : d (1575 : F) = 0 := d.map_natCast 1575
  have hn1925 : d (1925 : F) = 0 := d.map_natCast 1925
  have hn5985 : d (5985 : F) = 0 := d.map_natCast 5985
  have hn12075 : d (12075 : F) = 0 := d.map_natCast 12075
  have hn262144 : d (262144 : F) = 0 := d.map_natCast 262144
  have hn4194304 : d (4194304 : F) = 0 := d.map_natCast 4194304
  have hf25_128 : d (25 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, hn25]
  have hf27_128 : d (27 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, hn27]
  have hf27_256 : d (27 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, hn27]
  have hf25_512 : d (25 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, hn25]
  have hf27_512 : d (27 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, hn27]
  have hf75_512 : d (75 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h75]
  have hf45_1024 : d (45 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h45]
  have hf49_1024 : d (49 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn49]
  have hf55_1024 : d (55 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn55]
  have hf135_1024 : d (135 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn135]
  have hf195_1024 : d (195 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn195]
  have hf63_2048 : d (63 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h63]
  have hf175_2048 : d (175 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, hn175]
  have hf147_4096 : d (147 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, hn147]
  have hf441_4096 : d (441 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h441]
  have hf665_4096 : d (665 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, hn665]
  have hf819_8192 : d (819 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, hn819]
  have hf819_16384 : d (819 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, hn819]
  have hf945_16384 : d (945 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, h945]
  have hf825_32768 : d (825 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, hn825]
  have hf1575_32768 : d (1575 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, hn1575]
  have hf357_65536 : d (357 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, hn357]
  have hf1925_65536 : d (1925 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, hn1925]
  have hf5985_262144 : d (5985 / 262144 : F) = 0 := by
    simp [Derivation.leibniz_div, hn262144, hn5985]
  have hf12075_4194304 : d (12075 / 4194304 : F) = 0 := by
    simp [Derivation.leibniz_div, hn4194304, hn12075]
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
  have hrow6_red := hrow6
  rw [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow6_red
  simp only [nuResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810, thetaResidual810, map_sub, map_add,
    Derivation.leibniz, h12, h14, h18, h38, h54, h98, h78, h34, h58, h516,
    h316, h532, h15128, h5128, h7128, h9128, h1564, h964, h764, h35512,
    h211024, h631024, h31532768, h778192, h3158192, h1051024, h63512, h332,
    h352048, hL, h44132768, h44165536, h4558192, h107116384, h1894096,
    h851024, h751024, h811024, h932, h732, h21128, h35128, h771024, h45256,
    h452048, h1894096', h94532768, h38565536, h2251024, h7256, h3858192,
    h1532, h116, h35256, hf25_128, hf27_128, hf27_256, hf25_512, hf27_512,
    hf75_512, hf45_1024, hf49_1024, hf55_1024, hf135_1024, hf195_1024,
    hf63_2048, hf175_2048, hf147_4096, hf441_4096, hf665_4096, hf819_8192,
    hf819_16384, hf945_16384, hf825_32768, hf1575_32768, hf357_65536,
    hf1925_65536, hf5985_262144, hf12075_4194304, zero_mul, add_zero,
    mul_zero, pow_two, hsq, hsqB, hsqC, hsqD, hsqE, hcub, hcubB, hcubC,
    hquar, hquarB, hquint, hsextA]
  rw [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv]
  linear_combination (1 / 8 : F) * hrow_red - (5 / 64 : F) * A * hrow6_red

end DepressedRow810Thirteenth

section NonzeroThirteenthFaceClearing810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- The twelfth octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁹¹`. -/
theorem nonzeroFace810_thirteenthDefectPowerRelation
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
      localClearedThirteenthDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * h0 ^ 91 := by
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
  have hrow4 :
      (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 0) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 1) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 2) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 3) +
        g.coeff 1 * ratFuncDerivation68 (f.coeff 4) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 3) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 2) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 1) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_4_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 4) hbracket
    simpa [f, g, Polynomial.coeff_C, show (4 : ℕ) ≠ 0 by norm_num] using
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
  have hnu0deriv :
      ratFuncDerivation68
        (nuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    nuResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (g.coeff 0) hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0
      heta0deriv htheta0deriv hiota0deriv (by simpa using hrow8)
      (by simpa using hrow7) (by simpa using hrow6) (by simpa using hrow4)
  obtain ⟨nu0, hnu0⟩ :
      ∃ a : k,
        nuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hnu0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedThirteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        (281474976710656 : RatFunc k) * h ^ 91 *
          nuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) := by
    have hF := thirteenthDefect_eq_clearedNu810 h a7 a6 a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh (by convert hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedThirteenthDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, map_add, RatFunc.algebraMap_C, h, a7, a6, a5,
      a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, nuResidual810,
      alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810, zetaResidual810,
      etaResidual810, thetaResidual810, hf6, hf5, hf4, hf3, hf2, hf1,
      hf0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedThirteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (281474976710656 * nu0) * h0 ^ 91) := by
    rw [hclear, hnu0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨281474976710656 * nu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end NonzeroThirteenthFaceClearing810

section ScaleZeroTwelfthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-! ## Degree-`4` source Jacobian row -/

/-- Source-facing degree-`4` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_thirteenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : k)) -
      ((p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
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
  simpa only [p, q] using fableScaleZero_thirteenthCoefficientJacobianRow_raw_810 hp hq hjac

/-- At scale zero the common core is constant, so the leading octic
coefficient of the degree-`4` row is a differential constant. -/
theorem scaleZero_thirteenthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : k)) -
      ((p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
      0 := by
  have hrow := fableScaleZero_thirteenthCoefficientJacobianRow_raw_810 hp hq hjac
  simpa using hrow

/-- Source-facing scale-zero collapse of the degree-`4` row. -/
theorem normalized810ScaleZero_thirteenthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : k)) -
      ((p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
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
    scaleZero_thirteenthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)


/-! ## Degree-`4` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`4` Jacobian coefficient
is exactly
`5 S G' + 4 T F' + 3 U E' + 2 V D' + W C'
- F T' - 2 E U' - 3 D V' - 4 C W' - 5 B X'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `G = f.coeff 0`, `L = g.coeff 9`,
`P = g.coeff 8`, `Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`,
`T = g.coeff 4`, `U = g.coeff 3`, `V = g.coeff 2`, `W = g.coeff 1`,
and `X = g.coeff 0`. -/
theorem scaleZero_monicOcticDecic_degree4Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 4 =
      (5 : F) * g.coeff 5 * d (f.coeff 0) +
        (4 : F) * g.coeff 4 * d (f.coeff 1) +
        (3 : F) * g.coeff 3 * d (f.coeff 2) +
        (2 : F) * g.coeff 2 * d (f.coeff 3) +
        g.coeff 1 * d (f.coeff 4) -
          f.coeff 1 * d (g.coeff 4) -
          (2 : F) * f.coeff 2 * d (g.coeff 3) -
          (3 : F) * f.coeff 3 * d (g.coeff 2) -
          (4 : F) * f.coeff 4 * d (g.coeff 1) -
          (5 : F) * f.coeff 5 * d (g.coeff 0) :=
  differentialJacobian_coeff_4_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if the degree-`8`, degree-`7`, degree-`6`,
and degree-`4` Jacobian rows vanish, `L` is constant, and the residuals
`α, β, γ, δ, ε, ζ, η, θ, ι` are constant, then the next residual `ν` is
a differential constant. -/
theorem scaleZero_nuResidual_deriv_zero_810
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
    (hrow6 : (7 : F) * Q * d G0 + (6 : F) * R * d F0 +
        (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        W0 * d A -
        F0 * d R - (2 : F) * E0 * d S0 -
        (3 : F) * D0 * d T0 - (4 : F) * C0 * d U0 -
        (5 : F) * B * d V0 - (6 : F) * A * d W0 = 0)
    (hrow : (5 : F) * S0 * d G0 + (4 : F) * T0 * d F0 +
        (3 : F) * U0 * d E0 + (2 : F) * V0 * d D0 +
        W0 * d C0 -
        F0 * d T0 - (2 : F) * E0 * d U0 -
        (3 : F) * D0 * d V0 - (4 : F) * C0 * d W0 -
        (5 : F) * B * d X0 = 0) :
    d (nuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 :=
  nuResidual810_deriv_zero d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hrow8
    hrow7 hrow6 hrow

/-! ## Cleared weight-`91` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_twelfthClearedDefect_exists_C_810
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
      localClearedThirteenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 91 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_thirteenthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, eta, hN, heta⟩

/-- Aligned constant face `N = 0`: the same degree-`4` clearing applies
with `λ = 0`, and the weight-`91` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedTwelfthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ eta : k,
      localClearedThirteenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
        Polynomial.C eta * (Polynomial.C t) ^ 91 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_thirteenthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨eta, heta⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`91` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroTwelfthClearedDefect_exists_C_810
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
      localClearedThirteenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 91 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_thirteenthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨eta, heta⟩

variable [IsAlgClosed k]

/-- Source-facing twelfth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`91`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_twelfthClearedDefect
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
      localClearedThirteenthDefect810 (Polynomial.C t)
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
        Polynomial.C eta * (Polynomial.C t) ^ 91 := by
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
    scaleZero_twelfthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, eta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hX⟩

/-- The weight-`91` defect is a literal ground-field constant. -/
theorem normalized810ScaleZero_twelfthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirteenthDefect810 (Polynomial.C t)
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
    normalized810ScaleZero_exists_twelfthClearedDefect hsource
  refine ⟨t, lambda, eta * t ^ 91, ht, hHsq, ?_⟩
  have hconst :
      localClearedThirteenthDefect810 (Polynomial.C t)
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
        Polynomial.C (eta * t ^ 91) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 91)).symm
  exact hconst

/-- Newton degree of the twelfth cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_twelfthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedThirteenthDefect810 (Polynomial.C t)
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
    normalized810ScaleZero_twelfthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hX]
  exact (natDegree_C eta).le

/-- Aligned/nonzero split of the scale-zero twelfth defect: both constant
faces of `N` make the weight-`91` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_twelfthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ eta : k,
            localClearedThirteenthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
                (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
                (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
              Polynomial.C eta * (Polynomial.C t) ^ 91) ∨
        ∃ lambda eta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedThirteenthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
            Polynomial.C eta * (Polynomial.C t) ^ 91) := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_twelfthClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, eta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hX
  · exact Or.inr ⟨lambda, eta, hlambda, hN, hX⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-`91` defect.  Neither vanishing face is claimed closed. -/
theorem normalized810ScaleZero_twelfthClearedDefectBranches
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
        localClearedThirteenthDefect810 (Polynomial.C t)
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
    normalized810ScaleZero_exists_twelfthClearedDefect hsource
  let eta : k := eta0 * t ^ 91
  have hX :
      localClearedThirteenthDefect810 (Polynomial.C t)
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
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 91)).symm
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
weight-`91` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_twelfthClearedDefect
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
      localClearedThirteenthDefect810 (Polynomial.C t)
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
        Polynomial.C eta * (Polynomial.C t) ^ 91 := by
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
    scaleZero_alignedTwelfthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, eta, ht, hHsq, by simpa only [p, q] using hX⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`91` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_twelfthClearedDefect
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
      localClearedThirteenthDefect810 (Polynomial.C t)
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
        Polynomial.C eta * (Polynomial.C t) ^ 91 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_twelfthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, eta, ht, hlambda, hHsq, hN, hX⟩

end ScaleZeroTwelfthDefect810


#print axioms fableScaleZero_thirteenthCoefficientJacobianRow_raw_810
#print axioms scaleZero_thirteenthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_thirteenthCoefficientJacobianRow
#print axioms normalized810ScaleZero_thirteenthCoefficientJacobianRow_collapsed
#print axioms differentialJacobian_coeff_4_monicOcticDecic
#print axioms scaleZero_monicOcticDecic_degree4Row_810
#print axioms nuResidual810_deriv_zero
#print axioms scaleZero_nuResidual_deriv_zero_810
#print axioms thirteenthDefect_eq_clearedNu810
#print axioms nonzeroFace810_thirteenthDefectPowerRelation
#print axioms scaleZero_twelfthClearedDefect_exists_C_810
#print axioms scaleZero_alignedTwelfthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroTwelfthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_twelfthClearedDefect
#print axioms normalized810ScaleZero_twelfthClearedDefect_exists_C
#print axioms normalized810ScaleZero_twelfthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_twelfthClearedDefectFirstFace
#print axioms normalized810ScaleZero_twelfthClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_twelfthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_twelfthClearedDefect

end Max11DegreeRoutes
