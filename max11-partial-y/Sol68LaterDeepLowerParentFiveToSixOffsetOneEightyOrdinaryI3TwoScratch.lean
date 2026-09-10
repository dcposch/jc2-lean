import Fable68LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryJoinScratch
import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryReductionAssemblyScratch

/-! # Complementary offset-180 I3 coefficient two

This leaf is disjoint from the row-zero coefficient-`4` continuation.
It consumes the next lower literal I3 coefficient, contracted coefficient
`2` (expanded coefficient `120`), and reduces it against the already frozen
offset-`180` face and join jets.  The result is an exact lower-jet scalar;
no source row is duplicated.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryI3Two68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 20000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal I3 coefficient `2` in the contracted offset-`180` chart. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_two_ordinaryOneEighty68
    (gamma epsilon : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 2 =
      (8 / 9 : k) *
        (-(B.coeff 0 *
            (A.coeff 2 * d.coeff 0 + A.coeff 1 * d.coeff 1)) -
          B.coeff 0 ^ 2 * c.coeff 2 +
          3 * (c.coeff 0 * e.coeff 2 + c.coeff 1 * e.coeff 1 +
            c.coeff 2 * e.coeff 0) +
          (3 / 2 : k) * d.coeff 1 ^ 2) +
        2 * epsilon * c.coeff 2 + 4 * gamma * e.coeff 2 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add]
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hAd : (A * d).coeff 2 =
      A.coeff 2 * d.coeff 0 + A.coeff 1 * d.coeff 1 := by
    rw [mul_coeff_two68, hd2]
    ring
  have hABdPoly : A * B * d = B.coeff 0 • (A * d) := by
    calc
      A * B * d = A * C (B.coeff 0) * d := by
        exact congrArg (fun q : k[X] => A * q * d) hBC
      _ = B.coeff 0 • (A * d) := by
        rw [Polynomial.smul_eq_C_mul]
        ring
  have hABd : (A * B * d).coeff 2 = B.coeff 0 *
      (A.coeff 2 * d.coeff 0 + A.coeff 1 * d.coeff 1) := by
    rw [hABdPoly, coeff_smul, smul_eq_mul, hAd]
  have hB2cPoly : B ^ 2 * c = B.coeff 0 ^ 2 • c := by
    calc
      B ^ 2 * c = C (B.coeff 0) ^ 2 * c := by
        exact congrArg (fun q : k[X] => q ^ 2 * c) hBC
      _ = B.coeff 0 ^ 2 • c := by
        rw [Polynomial.smul_eq_C_mul, map_pow]
  have hB2c : (B ^ 2 * c).coeff 2 =
      B.coeff 0 ^ 2 * c.coeff 2 := by
    rw [hB2cPoly, coeff_smul, smul_eq_mul]
  have hce : (c * e).coeff 2 =
      c.coeff 0 * e.coeff 2 + c.coeff 1 * e.coeff 1 +
        c.coeff 2 * e.coeff 0 := by
    rw [mul_coeff_two68]
  have hdsq : (d ^ 2).coeff 2 = d.coeff 1 ^ 2 := by
    rw [pow_two, mul_coeff_two68, hd2]
    ring
  have hB2deg : (B ^ 2).natDegree ≤ 0 := by
    compute_degree
    omega
  have hB2zero : (B ^ 2).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2deg.trans_lt (by norm_num))
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce, hdsq,
    hB2zero]
  ring

/-- Algebraic reduction of I3 coefficient `2` by the frozen face, edge
cubic and three join jets.  It is kept denominator-free for later
resultants. -/
theorem fiveToSix_ordinaryOneEighty_i3Two_reduced68
    (a₁ a₂ b c c₀ c₁ d₀ x e₀ e₁ e₂ y gamma epsilon : k)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hface : b * y + c * x = 0)
    (hedge : 9 * y ^ 2 - 4 * c ^ 3 = 0)
    (hjetEdge : 2 * c * d₀ - c₁ * x = 0)
    (hjetLoad : 2 * b * e₂ + 3 * c₁ * x = 0)
    (hgain : 2 * c₁ ^ 2 - c * (8 * c₀ + 21 * gamma) = 0)
    (hi3two : (8 / 9 : k) *
        (-(b * (a₂ * d₀ + a₁ * x)) - b ^ 2 * c +
          3 * (c₀ * e₂ + c₁ * e₁ + c * e₀) +
          (3 / 2 : k) * x ^ 2) +
        2 * epsilon * c + 4 * gamma * e₂ = 0) :
    84 * a₁ * b ^ 2 * c * x + 42 * a₂ * b ^ 2 * c₁ * x +
      28 * b ^ 3 * c ^ 2 - 252 * b * c ^ 2 * e₀ -
      189 * b * c ^ 2 * epsilon - 252 * b * c * c₁ * e₁ +
      162 * c * c₀ * c₁ * x + 54 * c₁ ^ 3 * x = 0 := by
  have hpins : c ^ 2 * (4 * b ^ 2 * c - 9 * x ^ 2) = 0 := by
    linear_combination (-(b ^ 2)) * hedge +
      (9 * (b * y - c * x)) * hface
  have hpin : 4 * b ^ 2 * c - 9 * x ^ 2 = 0 :=
    (mul_eq_zero.mp hpins).resolve_left (pow_ne_zero 2 hc)
  have hd₀val : d₀ = c₁ * x / (2 * c) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hc)).2
    linear_combination hjetEdge
  have he₂val : e₂ = (-3 * c₁ * x) / (2 * b) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hb)).2
    linear_combination hjetLoad
  have hgamma : gamma = (2 * c₁ ^ 2 - 8 * c * c₀) / (21 * c) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hc)).2
    linear_combination (-1 : k) * hgain
  have hx2 : x ^ 2 = (4 / 9 : k) * b ^ 2 * c := by
    linear_combination (-1 / 9 : k) * hpin
  rw [hd₀val, he₂val, hgamma, hx2] at hi3two
  field_simp [hb, hc] at hi3two
  linear_combination (-1 / 36 : k) * hi3two

set_option maxHeartbeats 15000000 in
/-- Source packet for the disjoint I3 lane.  Besides the literal
coefficient it returns its denominator-free reduction against the verified
join frontier. -/
theorem fiveToSix_offsetOneEighty_ordinary_i3Two_source_packet68
    (gamma epsilon i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (hb : B.coeff 0 ≠ 0) (hcTop : c.coeff 2 ≠ 0)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hedge : 9 * e.coeff 3 ^ 2 - 4 * c.coeff 2 ^ 3 = 0)
    (hjetEdge : 2 * c.coeff 2 * d.coeff 0 -
      c.coeff 1 * d.coeff 1 = 0)
    (hjetLoad : 2 * B.coeff 0 * e.coeff 2 +
      3 * c.coeff 1 * d.coeff 1 = 0)
    (hgain : 2 * c.coeff 1 ^ 2 -
      c.coeff 2 * (8 * c.coeff 0 + 21 * gamma) = 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    ((8 / 9 : k) *
        (-(B.coeff 0 *
            (A.coeff 2 * d.coeff 0 + A.coeff 1 * d.coeff 1)) -
          B.coeff 0 ^ 2 * c.coeff 2 +
          3 * (c.coeff 0 * e.coeff 2 + c.coeff 1 * e.coeff 1 +
            c.coeff 2 * e.coeff 0) +
          (3 / 2 : k) * d.coeff 1 ^ 2) +
        2 * epsilon * c.coeff 2 + 4 * gamma * e.coeff 2 = 0) ∧
      (84 * A.coeff 1 * B.coeff 0 ^ 2 * c.coeff 2 * d.coeff 1 +
        42 * A.coeff 2 * B.coeff 0 ^ 2 * c.coeff 1 * d.coeff 1 +
        28 * B.coeff 0 ^ 3 * c.coeff 2 ^ 2 -
        252 * B.coeff 0 * c.coeff 2 ^ 2 * e.coeff 0 -
        189 * B.coeff 0 * c.coeff 2 ^ 2 * epsilon -
        252 * B.coeff 0 * c.coeff 2 * c.coeff 1 * e.coeff 1 +
        162 * c.coeff 2 * c.coeff 0 * c.coeff 1 * d.coeff 1 +
        54 * c.coeff 1 ^ 3 * d.coeff 1 = 0) := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff 2) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_two_ordinaryOneEighty68
    gamma epsilon A B c d e hA hB hc hd he] at hcoeff
  norm_num [coeff_C] at hcoeff
  have hraw : (8 / 9 : k) *
        (-(B.coeff 0 *
            (A.coeff 2 * d.coeff 0 + A.coeff 1 * d.coeff 1)) -
          B.coeff 0 ^ 2 * c.coeff 2 +
          3 * (c.coeff 0 * e.coeff 2 + c.coeff 1 * e.coeff 1 +
            c.coeff 2 * e.coeff 0) +
          (3 / 2 : k) * d.coeff 1 ^ 2) +
        2 * epsilon * c.coeff 2 + 4 * gamma * e.coeff 2 = 0 := by
    linear_combination hcoeff
  refine ⟨hraw, ?_⟩
  exact fiveToSix_ordinaryOneEighty_i3Two_reduced68
    (A.coeff 1) (A.coeff 2) (B.coeff 0) (c.coeff 2)
    (c.coeff 0) (c.coeff 1) (d.coeff 0) (d.coeff 1)
    (e.coeff 0) (e.coeff 1) (e.coeff 2) (e.coeff 3) gamma epsilon
    hb hcTop hface hedge hjetEdge hjetLoad hgain hraw

#print axioms cubicFirstIntegralThreePolynomial68_coeff_two_ordinaryOneEighty68
#print axioms fiveToSix_ordinaryOneEighty_i3Two_reduced68
#print axioms fiveToSix_offsetOneEighty_ordinary_i3Two_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryI3Two68

end Max11DegreeRoutes
