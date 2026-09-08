import Grok610ScaleZeroConeCascadePart51Scratch
import Grok610ScaleZeroConeCascadePart52Scratch
import Grok610ScaleZeroConeCascadePart54Scratch
import Grok610ScaleZeroConeCascadePart55Scratch
import Grok610ScaleZeroConeCascadePart56Scratch
import Grok610ScaleZeroConeCascadePart60Scratch
import Grok610ScaleZeroConeCascadePart61Scratch
import Grok610ScaleZeroConeCascadePart62Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Residual610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact residual of the scale-zero cone cascade.

The free core has polynomial representatives, the integrated primitive
has Newton degree one, a constant core is impossible, the unique-`A`
cone is empty except the two leftover chambers `L = 0` with `B`
constant (and `β = 0` if `B = 0`), the extreme unique-`B` cone
`3 deg A < 2 deg B` with `7 deg A < 5 deg B` is empty, a unique
nonconstant `B` or `D₀` is empty, and a unique nonconstant `E₀` with
`β ≠ 0` is empty.

The leaf is not closed.  A nonconstant polynomial core remains in which
either two or more letters share the maximal degree, or else `A`
uniquely leads with `L = 0` and `B` a constant, and in the `B = 0`
chamber also `β = 0`, or else `E₀` is the unique nonconstant letter
with `β = 0`.  The already-constant first integrals `κ, λ, μ` and the
weight-seventy residual `ο` are not consumed. -/
theorem normalized610ScaleZero_coneCascadeResidual
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
        l = 0 ∧ B.natDegree = 0 ∧ (B = 0 → beta = 0)) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 0 < E0.natDegree ∧ beta ≠ 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      _hrow, _homicron, hcore⟩ :=
    normalized610ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD, hE, hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX,
      hder, hdeg⟩ := hcore
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, hder,
    hdeg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hconst
    exact degreeZeroPrimitivePolynomial610_false_of_constant_core
      l alpha beta delta epsilon zeta eta theta (j / t) A B C0 D0 E0
      hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2 hder
  · intro hcone
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlne
      exact uniqueHighA_impossible_of_l_ne610 l alpha beta delta epsilon
        zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
    · by_contra hBpos
      have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBpos
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne610 l alpha beta delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
      subst hl0
      exact uniqueHighA_impossible_of_l_zero_B_pos610 alpha beta delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hcone hpos hder
    · intro hB0
      by_contra hbetane
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne610 l alpha beta delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
      subst hl0
      subst hB0
      exact uniqueHighA_impossible_of_l_zero_B_zero_beta_ne alpha beta
        delta epsilon zeta eta theta (j / t) A C0 D0 E0 hjdiv hbetane
        hcone hder
  · intro hcone
    exact extremeHighB_impossible l alpha beta delta epsilon zeta eta
      theta (j / t) A B C0 D0 E0 hjdiv hcone hder
  · intro hBonly
    exact uniqueNonconstantB_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hBonly.1 hBonly.2.1
      hBonly.2.2.1 hBonly.2.2.2.1 hBonly.2.2.2.2 hder
  · intro hDonly
    exact uniqueNonconstantD0_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hDonly.1 hDonly.2.1
      hDonly.2.2.1 hDonly.2.2.2.1 hDonly.2.2.2.2 hder
  · intro hEonly
    exact uniqueNonconstantE0_impossible_of_beta_ne l alpha beta delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hEonly.2.2.2.2.2
      hEonly.1 hEonly.2.1 hEonly.2.2.1 hEonly.2.2.2.1 hEonly.2.2.2.2.1
      hder

end Residual610

end Max11DegreeRoutes
