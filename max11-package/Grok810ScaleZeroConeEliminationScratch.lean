import Grok810ScaleZeroConeEliminationSpeedTPart02Scratch
import Grok810ScaleZeroConeEliminationSpeedTPart03Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Honest residual -/

section Residual810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Exact residual after the first unique-face layer of the `(8,10)`
scale-zero cone tree.

The free core has polynomial representatives and the grouped primitive
has Newton degree one.  A constant core is empty; the unique-`A` cone is
empty except the leftover chamber `L = 0`, `deg B = 0`, and vanishing
combined `A⁷` coefficient `51 (385 B + 51 β)`; a unique nonconstant
`C₀` with `L ≠ 0` is empty; a unique nonconstant `G₀` with `L ≠ 0` is
empty.

Remaining named cones: unique-`A` after `A⁷` cancellation
(`L = 0`, `deg B = 0`, `385 B + 51 β = 0`), whose next unused datum is
the combined `A⁶` coefficient `15 (-434 D₀ - 187 δ)`; unique-`B` with
`A = 0`; unique-`C₀` with `L = 0` (or with `L ≠ 0` and `A` high enough
that `A⁸ L` competes with `C₀⁴ L`); unique-`D₀` with `A = 0`; unique
`E₀`/`F₀` chambers whose quadratic leading coefficient vanishes;
unique-`G₀` with `L = 0` and `deg G₀ = 1` with nonzero linear
coefficient (Newton degree one, allowed by `d ρ = C (j / t)`); and every
cone in which two or more letters share the maximal degree.  The
weight-`105` defect remains a ground constant and is not consumed. -/
theorem normalized810ScaleZero_coneEliminationResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta : k)
      (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0) ∧
      (UniqueHighACone810 A B C0 D0 E0 F0 G0 →
        l = 0 ∧ B.natDegree = 0 ∧
          highA_l0_A7Coefficient810 beta B = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ 0 < C0.natDegree ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0 ∧ l ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          0 < G0.natDegree ∧ l ≠ 0) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq, _hrow, _hX,
      hcore⟩ :=
    normalized810ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hl, hder, hdeg⟩ := hcore
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq, hder, hdeg, ?_,
    ?_, ?_, ?_⟩
  · intro hconst
    exact degreeZeroPrimitivePolynomial810_false_of_constant_core
      l beta gamma delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0
      G0 hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2.1 hconst.2.2.2.2.2.1 hconst.2.2.2.2.2.2 hder
  · intro hcone
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlne
      exact uniqueHighA_impossible_of_l_ne l beta gamma delta epsilon
        zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv hcone hder
    · by_contra hBpos
      have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBpos
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne l beta gamma delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv hcone hder
      subst hl0
      exact uniqueHighA_impossible_of_l_zero_B_pos beta gamma delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv hcone
        hpos hder
    · have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne l beta gamma delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv hcone hder
      have hB0 : B.natDegree = 0 := by
        by_contra hBpos
        have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBpos
        subst hl0
        exact uniqueHighA_impossible_of_l_zero_B_pos beta gamma delta
          epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv hcone
          hpos hder
      subst hl0
      by_contra hKne
      exact uniqueHighA_impossible_of_l_zero_B_const_A7_ne beta gamma
        delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv
        hcone hB0 hKne hder
  · intro hC
    exact uniqueNonconstantC0_impossible_of_l_ne l beta gamma delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hC.2.2.2.2.2.2.2
      hjdiv hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1 hC.2.2.2.2.1 hC.2.2.2.2.2.1
      hC.2.2.2.2.2.2.1 hder
  · intro hG
    exact uniqueNonconstantG0_impossible_of_l_ne l beta gamma delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hG.2.2.2.2.2.2.2
      hjdiv hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2.1
      hG.2.2.2.2.2.2.1 hder

set_option maxHeartbeats 64000000 in
/-- Glue of the two constant faces through the cone residual: the
scale-zero source is empty once the named leftover cones are excluded.
Neither leftover cone is claimed empty here. -/
theorem normalized810ScaleZero_impossible_of_coneResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta : k)
        (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
                zeta eta theta A B C0 D0 E0 F0 G0) =
            C (j / t) ∧
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            1 ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              G0.natDegree = 0) ∧
          (UniqueHighACone810 A B C0 D0 E0 F0 G0 →
            l = 0 ∧ B.natDegree = 0 ∧
              highA_l0_A7Coefficient810 beta B = 0) ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ 0 < C0.natDegree ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              G0.natDegree = 0 ∧ l ≠ 0) ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              0 < G0.natDegree ∧ l ≠ 0)) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneEliminationResidual hsource)

set_option maxHeartbeats 64000000 in
/-- Identity glue: a source-facing `False` theorem is exactly the
tracked scale-zero exclusion.  No face is closed here. -/
theorem planeKeller810ScaleZeroExclusion_of_impossible
    {K : Type*} [Field K]
    (himpossible :
      ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
        Normalized810LeadingCoreSource P Q H 0 → False) :
    PlaneKeller810ScaleZeroExclusion (K := K) :=
  himpossible

end Residual810

#print axioms natDegree_eq_one_of_derivative_eq_nonzero_C810
#print axioms UniqueHighACone810
#print axioms highA_l0_A7Coefficient810
#print axioms degreeZeroPrimitivePolynomial810
#print axioms octicDepressionR810_constantScale_eq_algebraMap
#print axioms constantScale_monicOctic_polynomialCore810
#print axioms monicOcticDecic_rhoLoads_exist_ground810
#print axioms algebraMap_degreeZeroPrimitivePolynomial810
#print axioms normalized810ScaleZero_exists_primitivePolynomial
#print axioms degreeZeroPrimitivePolynomial810_false_of_constant_core
#print axioms uniqueHighA_impossible_of_l_ne
#print axioms uniqueHighA_impossible_of_l_zero_B_pos
#print axioms uniqueHighA_impossible_of_l_zero_B_const_A7_ne
#print axioms uniqueNonconstantC0_impossible_of_l_ne
#print axioms uniqueNonconstantG0_impossible_of_l_ne
#print axioms normalized810ScaleZero_coneEliminationResidual
#print axioms normalized810ScaleZero_impossible_of_coneResidual
#print axioms planeKeller810ScaleZeroExclusion_of_impossible

end Max11DegreeRoutes
