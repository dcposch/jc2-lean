import Grok810ScaleZeroConeDefectFacesScratch

/-! # Scale-zero unique-`G₀` and ratio-tie closure for normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroConeDefectFacesScratch` on the constant
core `H = (C t)²`.  That file showed that `ξ` (weight `98`), `μ` (weight
`84`) and `ο` (weight `105`) are ground constants on the free octic core
and closed every unique load-free face among
`{7 deg A, 5 deg B, 3 deg C₀, 3 deg D₀, 2 deg E₀, 2 deg F₀}`, reducing
`normalized810ScaleZero_impossible` to
`normalized810ScaleZero_coneDefectFacesResidual`.

CAS job `derive_810_scale_zero_cone_ratio_ties.py` (outer degrees
`(8,10)`, leading `h⁴`, `h⁵` with `h` a nonzero constant) computes
Groebner bases of leading forms on leftover cones.

* Unique-`G₀` of Newton degree one, other letters vanishing: `G₀`-linear
  coefficients of `κ, ν, ξ, μ, ο` are `(7/8) β`, `(5/8) δ`, `(1/2) ε`,
  `(3/4) γ`, `(3/8) ζ`.  Vanishing those loads, the primitive is `θ G₀`.
  `d ρ = C (j / t) ≠ 0` forces `θ ≠ 0`.  Unique-`G₀` with `l ≠ 0` is
  empty by the parent.  The remaining chamber `l = 0`, `θ ≠ 0` is the
  Groebner leftover (ideal `(β, γ, δ, ε, ζ)`, not `(1)`).  The unused
  degree-one Jacobian row `2 V G' + W F' - F V' - 2 E X'` of
  `differentialJacobian_coeff_1_monicOcticDecic` (already on the parent
  import chain) is the next comparison on that chamber.

* Pair ratio-ties in which `7 deg A` is a maximum of the six named
  weights, with the other five letters of degree zero except possibly
  `B`: the face `A⁷` of `ξ` strictly leads, so the generated ideal
  contains a power of the leading coefficient of `A`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.  The theorems
`normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `A`–ratio cones with the other five letters of degree zero -/

section ABRAtio810

variable {k : Type*} [Field k] [CharZero k]

/-- `7 deg A` is a maximum of `{7 deg A, 5 deg B}` and the other five
letters are constants.  CAS: the `A⁷` face of `ξ` strictly leads, even
on the ratio-tie `7 deg A = 5 deg B`. -/
def ARatioLeadsXiCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    5 * B.natDegree ≤ 7 * A.natDegree ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

private theorem zero_pow_two_rt {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_rt {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_rt {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_rt {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

private theorem zero_pow_six_rt {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

private theorem zero_pow_seven_rt {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G1_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G1, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G2_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G2, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G3_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G3, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G4_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G4, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G5_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G5, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G6_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G6, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G7_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G7, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G8_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G8, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  omega

theorem degreeZeroXiNoA7Polynomial810_natDegree_lt_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rw [degreeZeroXiNoA7Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroXiNoA7G1_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G2_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G3_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G4_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G5_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G6_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G7_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G8_natDegree_lt_of_A_ratio l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

theorem xi_A7_impossible_of_A_ratio
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (-(165 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(165 / 65536 : k)) • A ^ 7).natDegree = 7 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroXiNoA7Polynomial810_natDegree_lt_of_A_ratio l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_A7_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end ABRAtio810

/-! ## Unique-`G₀` with `l ≠ 0` -/

section UniqueG0LNe810

variable {k : Type*} [Field k] [CharZero k]

theorem uniqueHighG0DegOne_impossible_of_l_ne
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hcone : UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  rcases hcone with ⟨hGdeg, hA0, hB0, hC0, hD0, hE0, hF0⟩
  have hGpos : 0 < G0.natDegree := by simp [hGdeg]
  exact uniqueNonconstantG0_impossible_of_l_ne l beta gamma delta epsilon
    zeta eta theta j A B C0 D0 E0 F0 G0 hl hj hA0 hB0 hC0 hD0 hE0 hF0
    hGpos hder

end UniqueG0LNe810

/-! ## Residual after the `A`-ratio faces and unique-`G₀` with `l ≠ 0` -/

section RatioTiesClosed810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Remaining cones after `A⁷` of `ξ` closes every `A`-ratio chamber
with the other five letters constant, and after unique-`G₀` with
`l ≠ 0`.  The Groebner leftover named by CAS is unique-`G₀` of degree
one with `l = 0`: loads `β, γ, δ, ε, ζ` vanish and `θ ≠ 0`.  The next
unused row is the degree-one Jacobian coefficient
`2 V G' + W F' - F V' - 2 E X'`
(`differentialJacobian_coeff_1_monicOcticDecic`). -/
theorem normalized810ScaleZero_coneRatioTiesResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hxi, hmu, hom, _hAmax, _hBleads, _hCleads, _hDleads, _hEleads,
      _hFleads⟩ :=
    normalized810ScaleZero_coneDefectFacesResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hxi, hmu, hom, ?_, ?_⟩
  · intro hA
    exact xi_A7_impossible_of_A_ratio l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hA hxi
  · intro hG0
    by_contra hlne
    exact uniqueHighG0DegOne_impossible_of_l_ne l beta gamma delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv hG0 hder

theorem normalized810ScaleZero_impossible_of_ratioTiesResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
          cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta
                epsilon zeta eta theta A B C0 D0 E0 F0 G0) =
            Polynomial.C (j / t) ∧
          (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
          (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0)) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneRatioTiesResidual hsource)

end RatioTiesClosed810

#print axioms ARatioLeadsXiCone810
#print axioms xi_A7_impossible_of_A_ratio
#print axioms uniqueHighG0DegOne_impossible_of_l_ne
#print axioms normalized810ScaleZero_coneRatioTiesResidual
#print axioms normalized810ScaleZero_impossible_of_ratioTiesResidual

end Max11DegreeRoutes
