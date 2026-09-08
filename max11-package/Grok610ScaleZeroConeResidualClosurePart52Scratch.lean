import Grok610ScaleZeroConeResidualClosurePart40Scratch
import Grok610ScaleZeroConeResidualClosurePart41Scratch
import Grok610ScaleZeroConeResidualClosurePart42Scratch
import Grok610ScaleZeroConeResidualClosurePart46Scratch
import Grok610ScaleZeroConeResidualClosurePart48Scratch
import Grok610ScaleZeroConeResidualClosurePart49Scratch
import Grok610ScaleZeroConeResidualClosurePart50Scratch
import Grok610ScaleZeroConeResidualClosurePart51Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualClosure610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact residual after the leftover unique-face cones of the scale-zero
cascade are closed.

The free core has polynomial representatives and the integrated primitive
has Newton degree one.  In addition to the parent cascade, the unique-`A`
chamber `L = 0` with `B` constant is empty unless the combined `A⁶`
coefficient vanishes, the unique-`A` chamber `L = 0`, `B = 0`, `β = 0`
is empty unless `D₀` is a nonzero constant whose combined `A⁵`
coefficient vanishes (and then `δ` is constrained), a unique nonconstant
`C₀` with nonzero cubic coefficient is empty, a unique nonconstant `E₀`
with `β = 0` and `deg E₀ ≥ 2` is empty, the unique-`B` chamber
`2 deg B < 3 deg A` is empty, and the mixed constant-`(A,B,C₀)` high-`D₀`
chamber with `β = 0` and `deg E₀ < 2 deg D₀` is empty.

Remaining named cones: the unique-`A` `A⁶`-cancelled chamber
`L = 0`, `deg B = 0`, `B ≠ 0`, `β = (64/11) B`; the unique-`A`
`A⁵`-cancelled chamber `L = 0`, `B = 0`, `β = 0`, `D₀` a nonzero
constant, `δ = -(640/147) D₀`; unique nonconstant `C₀` of degree one
with vanishing cubic (and, if present, quadratic) faces; unique
nonconstant `E₀` of degree one with `β = 0` and nonzero linear
coefficient; the unique-`B` tie `3 deg A = 2 deg B`; unique-high `C₀`
with at least one other letter nonconstant; unique-high `D₀` with `A`
nonconstant, or with `E₀` of degree at least `2 deg D₀`; unique-high
`E₀` with another letter nonconstant; and every cone in which two or
more letters share the maximal degree.  The already-constant first
integrals `κ, λ, μ` and the weight-seventy residual `ο` are not
consumed. -/
theorem normalized610ScaleZero_coneResidualClosureResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      (UniqueHighACone610 A B C0 D0 E0 →
        l = 0 ∧ B.natDegree = 0 ∧ (B = 0 → beta = 0) ∧
          (B ≠ 0 → highA_l0_constB_A6Coefficient610 beta B = 0) ∧
          (B = 0 →
            D0.natDegree = 0 ∧ D0 ≠ 0 ∧
              highA_l0_B0_beta0_A5Coefficient610 delta D0 = 0)) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ A6BLeadsHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 0 < E0.natDegree ∧ beta ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ 0 < C0.natDegree ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧
          uniqueC0_cubicCoefficient610 l beta A B ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 1 < E0.natDegree ∧ beta = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree < 2 * D0.natDegree ∧
          beta = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hnonconst, hHighA, hExtB, hBonly, hDonly, hEonly⟩ :=
    normalized610ScaleZero_coneCascadeResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, hder,
    hdeg, hnonconst, ?_, hExtB, ?_, hBonly, hDonly, hEonly, ?_, ?_, ?_⟩
  · intro hcone
    have hparent := hHighA hcone
    refine ⟨hparent.1, hparent.2.1, hparent.2.2, ?_, ?_⟩
    · intro hBne
      by_contra hKne
      have hl0 : l = 0 := hparent.1
      have hBdeg : B.natDegree = 0 := hparent.2.1
      subst hl0
      exact uniqueHighA_impossible_of_l_zero_B_const_A6_ne alpha beta delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hcone hBdeg
        hKne hder
    · intro hB0
      have hl0 : l = 0 := hparent.1
      have hbeta0 : beta = 0 := hparent.2.2 hB0
      subst hl0
      subst hB0
      subst hbeta0
      have hD0 : D0.natDegree = 0 := by
        by_contra hDpos
        exact uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_D0_pos
          alpha delta epsilon zeta eta theta (j / t) A C0 D0 E0 hjdiv
          hcone (Nat.pos_of_ne_zero hDpos) hder
      refine ⟨hD0, ?_, ?_⟩
      · intro hDzero
        subst hDzero
        have hdelta0 : delta = 0 := by
          by_contra hdeltane
          have hK :
              highA_l0_B0_beta0_A5Coefficient610 delta (0 : k[X]) ≠ 0 := by
            simp only [highA_l0_B0_beta0_A5Coefficient610, smul_zero,
              zero_add]
            exact C_ne_zero.mpr
              (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num))
                hdeltane)
          exact uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
            alpha delta epsilon zeta eta theta (j / t) A C0 0 E0 hjdiv
            hcone (by simp [natDegree_zero]) hK hder
        subst hdelta0
        exact uniqueHighA_impossible_of_l_zero_B_zero_D0_zero_delta_zero
          alpha epsilon zeta eta theta (j / t) A C0 E0 hjdiv hcone hder
      · by_contra hKne
        exact uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
          alpha delta epsilon zeta eta theta (j / t) A C0 D0 E0 hjdiv
          hcone hD0 hKne hder
  · intro hcone
    exact uniqueHighB_impossible_of_A6B_leads l alpha beta delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 hjdiv hcone hder
  · intro hC
    exact uniqueNonconstantC0_impossible_of_cubic_ne l alpha beta delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hC.1 hC.2.1
      hC.2.2.1 hC.2.2.2.1 hC.2.2.2.2.1 hC.2.2.2.2.2 hder
  · intro hE
    have hbeta0 : beta = 0 := hE.2.2.2.2.2
    subst hbeta0
    exact uniqueNonconstantE0_impossible_of_beta_zero_deg_ge_two l alpha
      delta epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hE.1 hE.2.1
      hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hder
  · intro hM
    have hbeta0 : beta = 0 := hM.2.2.2.2.2
    subst hbeta0
    exact mixedConstABC_beta0_D0_leads_impossible l alpha delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 hjdiv hM.1 hM.2.1 hM.2.2.1
      hM.2.2.2.1 hM.2.2.2.2.1 hder

end ResidualClosure610

end Max11DegreeRoutes
