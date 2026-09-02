import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroRowZeroFiveScratch

/-! # Offset-240 nonzero terminal I3 scalar

The first unused I3 coefficient after the two cusp jets is contracted
coefficient `2` (expanded `120`).  It reduces the surviving nonzero face
to one exact scalar wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyTerminalI368

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem cubicFirstIntegralThreePolynomial68_coeff_two_terminalTwoForty68
    (gamma epsilon : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 2 =
      (8 / 9 : k) *
        (-A.coeff 2 * B.coeff 0 * d.coeff 0 -
          B.coeff 0 ^ 2 * c.coeff 2 +
          3 * (c.coeff 0 * e.coeff 2 +
            c.coeff 1 * e.coeff 1 + c.coeff 2 * e.coeff 0)) +
        2 * epsilon * c.coeff 2 + 4 * gamma * e.coeff 2 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add]
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hDC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hd
  have hABdPoly : A * B * d =
      (B.coeff 0 * d.coeff 0) • A := by
    calc
      A * B * d = A * C (B.coeff 0) * C (d.coeff 0) := by
        exact congrArg₂ (fun p q : k[X] => A * p * q) hBC hDC
      _ = (B.coeff 0 * d.coeff 0) • A := by
        rw [Polynomial.smul_eq_C_mul, map_mul]
        ring
  have hABd : (A * B * d).coeff 2 =
      A.coeff 2 * B.coeff 0 * d.coeff 0 := by
    rw [hABdPoly, coeff_smul, smul_eq_mul]
    ring
  have hB2cPoly : B ^ 2 * c = B.coeff 0 ^ 2 • c := by
    calc
      B ^ 2 * c = C (B.coeff 0) ^ 2 * c := by
        exact congrArg (fun p : k[X] => p ^ 2 * c) hBC
      _ = B.coeff 0 ^ 2 • c := by
        rw [Polynomial.smul_eq_C_mul, map_pow]
  have hB2c : (B ^ 2 * c).coeff 2 =
      B.coeff 0 ^ 2 * c.coeff 2 := by
    rw [hB2cPoly, coeff_smul, smul_eq_mul]
  have hce : (c * e).coeff 2 =
      c.coeff 0 * e.coeff 2 + c.coeff 1 * e.coeff 1 +
        c.coeff 2 * e.coeff 0 := by
    rw [mul_coeff_two68]
  have hd2deg : (d ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hd2 : (d ^ 2).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd2deg.trans_lt (by norm_num))
  have hB2deg : (B ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hB2 : (B ^ 2).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2deg.trans_lt (by norm_num))
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce, hd2, hB2,
    zero_mul, add_zero]
  ring

theorem fiveToSix_ordinaryTwoForty_terminal_i3_scalar68
    (a a2 b c c1 c0 d y e1 e0 gamma epsilon : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hface : b * y + c * d = 0)
    (hfirst : b * e1 + c1 * d = 0)
    (hwall : 4 * a * (b * e0 + c0 * d) +
      3 * a * epsilon * b + 6 * a * gamma * d -
        4 * b * c ^ 2 = 0)
    (hsecond : 2 * a2 * b * c ^ 2 - 4 * a * b * c0 * c -
      2 * a * b * c1 ^ 2 - 3 * a * b * c * gamma +
        6 * a * d * y = 0)
    (hi3 : (8 / 9 : k) *
        (-a2 * b * d - b ^ 2 * c +
          3 * (c0 * y + c1 * e1 + c * e0)) +
        2 * epsilon * c + 4 * gamma * y = 0) :
    4 * b ^ 5 + 9 * b ^ 2 * d * gamma - 18 * d ^ 3 = 0 := by
  have ha' : a = (-3 * c ^ 2) / b ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hb)).2
    linear_combination hdisc
  have hy' : y = (-c * d) / b := by
    apply (eq_div_iff hb).2
    linear_combination hface
  have he1' : e1 = (-c1 * d) / b := by
    apply (eq_div_iff hb).2
    linear_combination hfirst
  have hepsilon : epsilon =
      (4 * b * c ^ 2 - 4 * a * (b * e0 + c0 * d) -
        6 * a * gamma * d) / (3 * a * b) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb)).2
    linear_combination hwall
  have ha2 : a2 =
      (4 * a * b * c0 * c + 2 * a * b * c1 ^ 2 +
        3 * a * b * c * gamma - 6 * a * d * y) /
          (2 * b * c ^ 2) := by
    apply (eq_div_iff
      (mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero 2 hc))).2
    linear_combination hsecond
  rw [hepsilon, ha2, hy', he1', ha'] at hi3
  field_simp [hb, hc] at hi3
  have hprod : c *
      (4 * b ^ 5 + 9 * b ^ 2 * d * gamma - 18 * d ^ 3) = 0 := by
    linear_combination (-1 / 72 : k) * hi3
  exact (mul_eq_zero.mp hprod).resolve_left hc

set_option maxHeartbeats 12000000 in
theorem fiveToSix_offsetTwoForty_nonzero_terminal_i3_source_packet68
    (gamma epsilon i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 0 ≠ 0) (hy : e.coeff 2 ≠ 0)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hfirst : B.coeff 0 * e.coeff 1 +
      c.coeff 1 * d.coeff 0 = 0)
    (hwall : 4 * A.coeff 4 *
        (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
      3 * A.coeff 4 * epsilon * B.coeff 0 +
      6 * A.coeff 4 * gamma * d.coeff 0 -
        4 * B.coeff 0 * c.coeff 2 ^ 2 = 0)
    (hsecond : 2 * A.coeff 2 * B.coeff 0 * c.coeff 2 ^ 2 -
      4 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 2 -
      2 * A.coeff 4 * B.coeff 0 * c.coeff 1 ^ 2 -
      3 * A.coeff 4 * B.coeff 0 * c.coeff 2 * gamma +
        6 * A.coeff 4 * d.coeff 0 * e.coeff 2 = 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    4 * B.coeff 0 ^ 5 +
      9 * B.coeff 0 ^ 2 * d.coeff 0 * gamma -
        18 * d.coeff 0 ^ 3 = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff 2) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_two_terminalTwoForty68
    gamma epsilon A B c d e hA hB hc hd he] at hcoeff
  norm_num [coeff_C] at hcoeff
  exact fiveToSix_ordinaryTwoForty_terminal_i3_scalar68
    (A.coeff 4) (A.coeff 2) (B.coeff 0) (c.coeff 2)
    (c.coeff 1) (c.coeff 0) (d.coeff 0) (e.coeff 2)
    (e.coeff 1) (e.coeff 0) gamma epsilon ha hb hcTop hdisc
    hface hfirst hwall hsecond (by linear_combination hcoeff)

#print axioms cubicFirstIntegralThreePolynomial68_coeff_two_terminalTwoForty68
#print axioms fiveToSix_ordinaryTwoForty_terminal_i3_scalar68
#print axioms fiveToSix_offsetTwoForty_nonzero_terminal_i3_source_packet68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyTerminalI368

end Max11DegreeRoutes
