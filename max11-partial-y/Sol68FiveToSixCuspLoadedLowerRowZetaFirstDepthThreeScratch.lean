import Sol68FiveToSixCuspLoadedLowerRowZetaFirstDepthTwoScratch

/-! # The third zeta-first successor coefficient

Every load retained at `mu+1` or `mu+2` is preserved literally.  Only the
twice load-free tail consumes the same source-backed I3/I4 coefficient at
reflected depth `mu+3`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstDepthThree68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact third-depth packet, retaining the first two load layers verbatim. -/
def FiveToSixCuspZetaFirstDepthThreeResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t1 := mu+1
  let t2 := mu+2
  let t3 := mu+3
  FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S ∧
    (S ≤ t1 ∨ G-S ≤ t1 ∨ 4*N-G ≤ t1 ∨ 4*N-S ≤ t1 ∨
      ((Delta.reflect U).coeff t1 = 0 ∧ Delta.natDegree ≤ N+S-2 ∧
        (S ≤ t2 ∨ G-S ≤ t2 ∨ 4*N-G ≤ t2 ∨ 4*N-S ≤ t2 ∨
          ((Delta.reflect U).coeff t2 = 0 ∧ Delta.natDegree ≤ N+S-3 ∧
            (S ≤ t3 ∨ G-S ≤ t3 ∨ 4*N-G ≤ t3 ∨ 4*N-S ≤ t3 ∨
              ((Delta.reflect U).coeff t3 = 0 ∧
                Delta.natDegree ≤ N+S-4))))))

theorem fiveToSix_zetaFirst_depthThree_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (htwo : FiveToSixCuspZetaFirstDepthTwoResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t1 := mu+1
  let t2 := mu+2
  let t3 := mu+3
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    (S ≤ t1 ∨ G-S ≤ t1 ∨ 4*N-G ≤ t1 ∨ 4*N-S ≤ t1 ∨
      ((Delta.reflect U).coeff t1 = 0 ∧ Delta.natDegree ≤ N+S-2 ∧
        (S ≤ t2 ∨ G-S ≤ t2 ∨ 4*N-G ≤ t2 ∨ 4*N-S ≤ t2 ∨
          ((Delta.reflect U).coeff t2 = 0 ∧
            Delta.natDegree ≤ N+S-3)))) at htwo
  rcases htwo with ⟨hs,hS1 | hBc1 | hGamma1 | hB31 | hfree1⟩
  · exact ⟨hs,Or.inl hS1⟩
  · exact ⟨hs,Or.inr (Or.inl hBc1)⟩
  · exact ⟨hs,Or.inr (Or.inr (Or.inl hGamma1))⟩
  · exact ⟨hs,Or.inr (Or.inr (Or.inr (Or.inl hB31)))⟩
  · rcases hfree1.2.2 with hS2 | hBc2 | hGamma2 | hB32 | hfree2
    · exact ⟨hs,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hfree1.1,hfree1.2.1,Or.inl hS2⟩)))⟩
    · exact ⟨hs,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hfree1.1,hfree1.2.1,Or.inr (Or.inl hBc2)⟩)))⟩
    · exact ⟨hs,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hfree1.1,hfree1.2.1,Or.inr (Or.inr (Or.inl hGamma2))⟩)))⟩
    · exact ⟨hs,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hfree1.1,hfree1.2.1,
          Or.inr (Or.inr (Or.inr (Or.inl hB32)))⟩)))⟩
    · refine ⟨hs,?_⟩
      right;right;right;right
      refine ⟨hfree1.1,hfree1.2.1,?_⟩
      right;right;right;right
      refine ⟨hfree2.1,hfree2.2,?_⟩
      by_cases hS3 : t3 < S
      · by_cases hBc3 : t3 < G-S
        · by_cases hGamma3 : t3 < 4*N-G
          · by_cases hB33 : t3 < 4*N-S
            · right;right;right;right
              have h0 := hs
              change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ mu = R-S ∧ _ ∧
                (∀ q, q ≤ mu → (Delta.reflect U).coeff q = 0) ∧ _ at h0
              have hzero := h0.2.2.2.2.2.2.2.2.1
              have hprior : ∀ j, j < t3 → (Delta.reflect U).coeff j = 0 := by
                intro j hj
                by_cases hj1 : j = t1
                · simpa only [hj1] using hfree1.1
                · by_cases hj2 : j = t2
                  · simpa only [hj2] using hfree2.1
                  · exact hzero j (by
                      dsimp only [t3,t2,t1] at hj hj1 hj2
                      omega)
              have hnext := fiveToSix_zetaFirst_discriminant_zero_of_prior68
                alpha gamma epsilon zeta eta terminal A B c d e N G S t3 hs
                hS3 hBc3 hGamma3 hB33 hprior
              rcases h0 with ⟨hSp,hSR,hd,he,hp,hless,hmu,hz,_hzero,hsupp⟩
              rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
              have hDelta : Delta.natDegree ≤ U := by
                dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
                compute_degree
                omega
              have hall : ∀ j, j ≤ t3 → (Delta.reflect U).coeff j = 0 := by
                intro j hj
                by_cases heq : j = t3
                · simpa only [heq,Delta,U] using hnext
                · exact hprior j (by omega)
              have hdrop := natDegree_le_of_reflect_initial_zero68 Delta U t3
                hDelta (by dsimp only [U,t3,mu,R] at *; omega) hall
              refine ⟨?_,?_⟩
              · simpa only [Delta,U] using hnext
              · simpa only [show U-t3-1 = N+S-4 by
                    dsimp only [U,t3,mu,R] at *; omega] using hdrop
            · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
          · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inl (by omega)

#print axioms fiveToSix_zetaFirst_depthThree_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstDepthThree68

end Max11DegreeRoutes
