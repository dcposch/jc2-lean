import LowScale68ScaleTwoRhoOneNoncubicNext

/-! # Elimination of the last rho-one noncubic component

The three affine rows first give two quadratic equations in `T`.  Their
closed quadratic resultant factors as `R₁₀(V) * (3V-1)^5`.  The earlier
two-row component split gives either the cubic point or `P₁₀(V)=0`, and a
short univariate Bezout certificate proves `P₁₀` and `R₁₀` coprime.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RhoOneNoncubicElimination68

variable {k : Type*} [Field k] [CharZero k]

/-! ## Two quadratic consequences of the three affine rows -/

def rhoOneQuadraticOneA68 (V : k) : k :=
  -45 * V ^ 2 - 30 * V + 30

def rhoOneQuadraticOneB68 (V : k) : k :=
  30 * V ^ 3 + (160 / 3) * V ^ 2 - (484 / 9) * V + 88 / 9

def rhoOneQuadraticOneC68 (V : k) : k :=
  4 * V ^ 5 - (10 / 3) * V ^ 4 - (220 / 9) * V ^ 3 +
    (2002 / 81) * V ^ 2 - (1870 / 243) * V + 187 / 243

def rhoOneQuadraticTwoA68 (V : k) : k :=
  -(165 / 2) * V ^ 2 + (605 / 3) * V - 737 / 9

def rhoOneQuadraticTwoB68 (V : k) : k :=
  -55 * V ^ 4 + (715 / 3) * V ^ 3 - (1100 / 3) * V ^ 2 +
    (14762 / 81) * V - 6413 / 243

def rhoOneQuadraticTwoC68 (V : k) : k :=
  (110 / 3) * V ^ 5 - (385 / 3) * V ^ 4 + (4598 / 27) * V ^ 3 -
    (23353 / 243) * V ^ 2 + (51425 / 2187) * V - 27115 / 13122

theorem rhoOne_affine_quadratic_one68 (T V : k) :
    rhoOneAffineThree68 T V - 9 * rhoOneAffineFour68 T V =
      rhoOneQuadraticOneA68 V * T ^ 2 +
        rhoOneQuadraticOneB68 V * T + rhoOneQuadraticOneC68 V := by
  simp only [rhoOneAffineThree68, rhoOneAffineFour68,
    rhoOneResidualThree68, rhoOneResidualFour68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68,
    rhoOneInitialE68, topRowThree68, topRowFour68,
    rhoOneQuadraticOneA68, rhoOneQuadraticOneB68,
    rhoOneQuadraticOneC68]
  ring

theorem rhoOne_affine_quadratic_two68 (T V : k) :
    rhoOneAffineTwo68 T V - (12 * V - 16) * rhoOneAffineFour68 T V =
      rhoOneQuadraticTwoA68 V * T ^ 2 +
        rhoOneQuadraticTwoB68 V * T + rhoOneQuadraticTwoC68 V := by
  simp only [rhoOneAffineTwo68, rhoOneResidualTwo68,
    rhoOneAffineFour68, rhoOneResidualFour68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68,
    rhoOneInitialE68, topRowTwo68, topRowFour68,
    rhoOneQuadraticTwoA68, rhoOneQuadraticTwoB68,
    rhoOneQuadraticTwoC68]
  ring

/-- Closed determinant formula for two quadratics with a common root. -/
theorem quadratic_common_root_resultant_zero68
    (a b c d e f T : k)
    (hp : a * T ^ 2 + b * T + c = 0)
    (hq : d * T ^ 2 + e * T + f = 0) :
    (a * f - c * d) ^ 2 -
        (a * e - b * d) * (b * f - c * e) = 0 := by
  let X := a * e - b * d
  let Y := a * f - c * d
  linear_combination
    (X * e + d * (X * T - Y)) * hp +
      (-X * b - a * (X * T - Y)) * hq

def rhoOneQuadraticResultant68 (V : k) : k :=
  let a := rhoOneQuadraticOneA68 V
  let b := rhoOneQuadraticOneB68 V
  let c := rhoOneQuadraticOneC68 V
  let d := rhoOneQuadraticTwoA68 V
  let e := rhoOneQuadraticTwoB68 V
  let f := rhoOneQuadraticTwoC68 V
  (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e)

def rhoOneThirdRowResultantFactor68 (V : k) : k :=
  3280500 * V ^ 10 - 14324850 * V ^ 9 + 24530850 * V ^ 8 -
    22492080 * V ^ 7 + 12829590 * V ^ 6 - 4949451 * V ^ 5 +
    1354905 * V ^ 4 - 267195 * V ^ 3 + 37145 * V ^ 2 - 3400 * V + 170

set_option maxHeartbeats 2000000 in
theorem rhoOne_quadratic_resultant_factor68 (V : k) :
    rhoOneQuadraticResultant68 V =
      -(121 / 177147 : k) * rhoOneThirdRowResultantFactor68 V *
        (3 * V - 1) ^ 5 := by
  simp only [rhoOneQuadraticResultant68, rhoOneQuadraticOneA68,
    rhoOneQuadraticOneB68, rhoOneQuadraticOneC68,
    rhoOneQuadraticTwoA68, rhoOneQuadraticTwoB68,
    rhoOneQuadraticTwoC68, rhoOneThirdRowResultantFactor68]
  ring

/-! ## A compact univariate Bezout certificate -/

private def rhoOneP10BezoutLeft68 (V : k) : k :=
  (2186699631606249921625111011432314625 /
      307601687518487562016284118310114 : k) * V ^ 9 -
  (16806776874362624671314691700826981475 /
      615203375036975124032568236620228 : k) * V ^ 8 +
  (35524606789605553453887770414452569025 /
      922805062555462686048852354930342 : k) * V ^ 7 -
  (75511405256763405578531022992197867385 /
      2768415187666388058146557064791026 : k) * V ^ 6 +
  (196300624818591458877524022929447517455 /
      16610491125998328348879342388746156 : k) * V ^ 5 -
  (345547016387068957787506552213487426597 /
      99662946755989970093276054332476936 : k) * V ^ 4 +
  (53552078598342450407480943727989635155 /
      74747210066992477569957040749357702 : k) * V ^ 3 -
  (91204692821429186286356195196435946187 /
      896966520803909730839484488992292424 : k) * V ^ 2 +
  (12724563979873064269069871621455828685 /
      1345449781205864596259226733488438636 : k) * V -
  (606031110997177676648551425017002523 /
      1345449781205864596259226733488438636 : k)

private def rhoOneR10BezoutRight68 (V : k) : k :=
  -(29395074247805615613099158956347461399 /
      307601687518487562016284118310114 : k) * V ^ 9 +
  (151697587379134373267231645943979096615 /
      1845610125110925372097704709860684 : k) * V ^ 8 +
  (11234028301618958984284749297943923659 /
      307601687518487562016284118310114 : k) * V ^ 7 -
  (292901162094628135414242788525734392541 /
      4152622781499582087219835597186539 : k) * V ^ 6 +
  (2095926959155033561420218399538526191483 /
      49831473377994985046638027166238468 : k) * V ^ 5 -
  (223857756456746016529028323637613111593 /
      14237563822284281441896579190353848 : k) * V ^ 4 +
  (130563795267965264903131033458937485769 /
      32034518600139633244267303178296158 : k) * V ^ 3 -
  (1922177682154223128282836458270958721357 /
      2690899562411729192518453466976877272 : k) * V ^ 2 +
  (9035433088514496872883058395341419651 /
      103496137015835738173786671806802972 : k) * V -
  (14650124065176336661997777112076302955 /
      2690899562411729192518453466976877272 : k)

set_option maxHeartbeats 4000000 in
/-- Exact extended-Euclidean certificate for the two degree-ten factors. -/
theorem rhoOne_degreeTen_bezout68 (V : k) :
    rhoOneP10BezoutLeft68 V * rhoOneNoncubicVPolynomial68 V +
      rhoOneR10BezoutRight68 V * rhoOneThirdRowResultantFactor68 V = 1 := by
  simp only [rhoOneP10BezoutLeft68, rhoOneR10BezoutRight68,
    rhoOneNoncubicVPolynomial68, rhoOneThirdRowResultantFactor68]
  ring

/-! ## Elimination and source descent -/

theorem rhoOne_affine_three_rows_force_cubic68 (T V : k)
    (h4 : rhoOneAffineFour68 T V = 0)
    (h3 : rhoOneAffineThree68 T V = 0)
    (h2 : rhoOneAffineTwo68 T V = 0) :
    3 * V - 1 = 0 := by
  have hq1 : rhoOneQuadraticOneA68 V * T ^ 2 +
      rhoOneQuadraticOneB68 V * T + rhoOneQuadraticOneC68 V = 0 := by
    rw [← rhoOne_affine_quadratic_one68 T V, h3, h4]
    ring
  have hq2 : rhoOneQuadraticTwoA68 V * T ^ 2 +
      rhoOneQuadraticTwoB68 V * T + rhoOneQuadraticTwoC68 V = 0 := by
    rw [← rhoOne_affine_quadratic_two68 T V, h2, h4]
    ring
  have hres : rhoOneQuadraticResultant68 V = 0 := by
    exact quadratic_common_root_resultant_zero68
      (rhoOneQuadraticOneA68 V) (rhoOneQuadraticOneB68 V)
      (rhoOneQuadraticOneC68 V) (rhoOneQuadraticTwoA68 V)
      (rhoOneQuadraticTwoB68 V) (rhoOneQuadraticTwoC68 V) T hq1 hq2
  rw [rhoOne_quadratic_resultant_factor68] at hres
  have hres' : -(121 / 177147 : k) *
      (rhoOneThirdRowResultantFactor68 V * (3 * V - 1) ^ 5) = 0 := by
    simpa only [mul_assoc] using hres
  have hprod : rhoOneThirdRowResultantFactor68 V * (3 * V - 1) ^ 5 = 0 :=
    (mul_eq_zero.mp hres').resolve_left (by norm_num)
  rcases rhoOne_affine_component_split68 T V h4 h3 with hcore | hP
  · rw [hcore.1]
    ring
  · rcases mul_eq_zero.mp hprod with hR | hlin
    · have hbez := rhoOne_degreeTen_bezout68 V
      rw [hP, hR] at hbez
      norm_num at hbez
    · exact eq_zero_of_pow_eq_zero hlin

theorem rhoOneNoncubicThreeRowPacket68_impossible
    {p q : k[X][X]} {j l : k} {h0 : k[X]}
    {T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l}
    {g u : k[X]} (hpacket : RhoOneNoncubicThreeRowPacket68 T0 g u) : False := by
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hP, h4, h3, h2⟩ :=
    hpacket
  have hlin := rhoOne_affine_three_rows_force_cubic68
    (t / z ^ 3) (v / z ^ 2) h4 h3 h2
  have hV : v / z ^ 2 = (1 / 3 : k) := by
    linear_combination (1 / 3 : k) * hlin
  rw [hV, rhoOneNoncubicVPolynomial68_ne_at_cubic] at hP
  norm_num at hP

/-- All rho-one components now force the transverse triple divisibility. -/
theorem SquareConstantLIntegratedLocalRootData68.rhoOne_allComponents_descend
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3 := by
  rcases T0.rhoOne_component_split_or_descend hp hH hp6 hp5 hp4 with
    hdesc | hnon
  · exact hdesc
  · have hthree := T0.rhoOneNoncubic_nextRow hp hH hp6 hp5 hp4 hnon
    exact (rhoOneNoncubicThreeRowPacket68_impossible hthree).elim

end RhoOneNoncubicElimination68

#print axioms quadratic_common_root_resultant_zero68
#print axioms rhoOne_quadratic_resultant_factor68
#print axioms rhoOne_degreeTen_bezout68
#print axioms rhoOne_affine_three_rows_force_cubic68
#print axioms rhoOneNoncubicThreeRowPacket68_impossible
#print axioms SquareConstantLIntegratedLocalRootData68.rhoOne_allComponents_descend

end Max11DegreeRoutes
