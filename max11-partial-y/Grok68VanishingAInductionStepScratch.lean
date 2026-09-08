import Grok68VanishingAInductionStepPart18Scratch

/-! # Uniform producing induction on the `q=0` vanishing-A chamber

Committed green through `k=4` produces vanishing `A_(2N-j)=0` for
`j≤4`, and matching from a granted vanishing depth is already uniform
(`Grok68VanishingAUniformCompanionScratch.lean`).

The order-`k` producing companion, under vanishing through `k-1`, does
not take per-`k` input:

* only the `A_p` slot of `A'` reaches the companion remainder index
  (the `A_(p-k)` slot overshoots `deg(Bc)`);
* remainder cancel reduces to the pair `W0_(2p-k-1)` and `A_p W2_(p-k-1)`,
  which cancel by the companion weights against `(B c)_(p-k)`;
* load cancel is the two-generator combination of the order-`k` disc
  and I4 jets with cofactors `(25P-14k)` and `(15P-14k)` (CAS leftover
  `0` on `k=2..7`, and the same closed form for general `k`).

This file lands remainder cancel, the load identity, and the producing
step uniformly on `1≤k≤D`.  Induction from the committed `k≤4` base
gives vanishing of `A` through `k=D` for every `m`.  Matching through
`k=D` is then a theorem of granted vanishing, so the comparison
polynomials drop to degree at most `N-1` and `E-D-1`.  Those degree
bounds are not the identities `r_c=r_e=0`, so the committed
`vanishingA_zero_remainder_impossible68` does not fire.

This is not a closure.  Named gap: the comparison remainders after
matching through `D`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Two-endpoint Cauchy products -/

/-! ## Remainder transport at an arbitrary positive index -/

/-! ## `A'` against a shorter right factor, after vanishing through `r-1` -/

/-! ## Remainder cancel under vanishing through `r-1` -/

/-! ## Row-two load as a derivative -/

/-! ## Derivative Cauchy products and the row-zero load splitting -/

/-! ## Source: order-`r` disc with vanishing through `r-1` -/

/-! ## Companion reduction under vanishing through `r-1` -/

/-! ## Matching algebra at the unmatched last slot -/

/-! ## Row-two load coefficient, uniformly -/

/-! ## Row-zero load under vanishing through `r-1` -/

/-! ## Load identity under vanishing through `r-1` -/

/-! ## Producing step and induction through `D` -/

#print axioms coeff_mul_sub_bounds_vanishing_left68
#print axioms fiveToSix_qZero_derivA_mul_of_vanishing68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport_at68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_step68
#print axioms fiveToSix_qZero_rowTwo_load_derivative68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet_vanishing_pred68
#print axioms fiveToSix_qZero_disc_reduced_of_ih68
#print axioms fiveToSix_qZero_i4_reduced_of_ih68
#print axioms fiveToSix_qZero_matched_weights_cancel68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_load_of_vanishing68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_of_vanishing68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_D68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_step68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_induction_step68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68

end Max11DegreeRoutes
