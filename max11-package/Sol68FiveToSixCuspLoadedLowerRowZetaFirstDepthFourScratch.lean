import Sol68FiveToSixCuspLoadedLowerRowZetaFirstDepthThreeScratch

/-! # The fourth zeta-first successor coefficient

The complete depth-three residual is retained as a conjunct.  Conditional
only on its load-free tail, the same source-backed I3/I4 coefficient is
consumed at reflected depth `mu+4` and split at the four literal loads.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstDepthFour68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The verified first three layers, plus the exact fourth-layer split on
their common load-free tail. -/
def FiveToSixCuspZetaFirstDepthFourResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t1 := mu+1
  let t2 := mu+2
  let t3 := mu+3
  let t4 := mu+4
  FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ((Delta.reflect U).coeff t1 = 0 →
      (Delta.reflect U).coeff t2 = 0 →
      (Delta.reflect U).coeff t3 = 0 →
      (S ≤ t4 ∨ G-S ≤ t4 ∨ 4*N-G ≤ t4 ∨ 4*N-S ≤ t4 ∨
        ((Delta.reflect U).coeff t4 = 0 ∧
          Delta.natDegree ≤ N+S-5)))

theorem fiveToSix_zetaFirst_depthFour_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hthree : FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t1 := mu+1
  let t2 := mu+2
  let t3 := mu+3
  let t4 := mu+4
  refine ⟨hthree,?_⟩
  intro hz1 hz2 hz3
  have hcopy := hthree
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hcopy
  have hs := hcopy.1
  by_cases hS4 : t4 < S
  · by_cases hBc4 : t4 < G-S
    · by_cases hGamma4 : t4 < 4*N-G
      · by_cases hB34 : t4 < 4*N-S
        · right;right;right;right
          have h0 := hs
          change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ mu = R-S ∧ _ ∧
            (∀ q, q ≤ mu → (Delta.reflect U).coeff q = 0) ∧ _ at h0
          have hzero := h0.2.2.2.2.2.2.2.2.1
          have hprior : ∀ j, j < t4 → (Delta.reflect U).coeff j = 0 := by
            intro j hj
            by_cases hj1 : j = t1
            · simpa only [hj1] using hz1
            · by_cases hj2 : j = t2
              · simpa only [hj2] using hz2
              · by_cases hj3 : j = t3
                · simpa only [hj3] using hz3
                · exact hzero j (by
                    dsimp only [t4,t3,t2,t1] at hj hj1 hj2 hj3
                    omega)
          have hnext := fiveToSix_zetaFirst_discriminant_zero_of_prior68
            alpha gamma epsilon zeta eta terminal A B c d e N G S t4 hs
            hS4 hBc4 hGamma4 hB34 hprior
          rcases h0 with ⟨hSp,hSR,hd,he,hp,hless,hmu,hz,_hzero,hsupp⟩
          rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
          have hDelta : Delta.natDegree ≤ U := by
            dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
            compute_degree
            omega
          have hall : ∀ j, j ≤ t4 → (Delta.reflect U).coeff j = 0 := by
            intro j hj
            by_cases heq : j = t4
            · simpa only [heq,Delta,U] using hnext
            · exact hprior j (by omega)
          have hdrop := natDegree_le_of_reflect_initial_zero68 Delta U t4
            hDelta (by dsimp only [U,t4,mu,R] at *; omega) hall
          refine ⟨?_,?_⟩
          · simpa only [Delta,U] using hnext
          · simpa only [show U-t4-1 = N+S-5 by
                dsimp only [U,t4,mu,R] at *; omega] using hdrop
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

#print axioms fiveToSix_zetaFirst_depthFour_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstDepthFour68

end Max11DegreeRoutes
