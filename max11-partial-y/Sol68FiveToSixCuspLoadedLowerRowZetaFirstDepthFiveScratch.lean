import Sol68FiveToSixCuspLoadedLowerRowZetaFirstDepthFourScratch

/-! # The fifth zeta-first successor and its finite load threshold

The complete depth-four residual remains a conjunct.  Its four-times-zero
tail is refined at `mu+5`.  Independently, the packet arithmetic identifies
the exact finite stopping bound: the literal `S` load occurs at successor
number `S-mu`, unless another one of the four loads occurs sooner.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstDepthFive68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact arithmetic finite-stopping certificate.  Since `mu<S`, the
`S`-load is first met at `mu+(S-mu)=S`; every smaller successor misses it. -/
theorem fiveToSix_zetaFirst_S_load_finite68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    let mu := min S (7*N-2*G-S)
    0 < S-mu ∧ mu+(S-mu) = S ∧
      ∀ j, j < S-mu → mu+j < S := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ R-S < S ∧ mu = R-S ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  change 0 < S-mu ∧ mu+(S-mu) = S ∧ _
  constructor
  · omega
  constructor
  · omega
  · intro j hj
    omega

/-- The verified first four layers, plus the exact fifth-layer split on
their common load-free tail. -/
def FiveToSixCuspZetaFirstDepthFiveResidual68
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
  let t5 := mu+5
  FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ((Delta.reflect U).coeff t1 = 0 →
      (Delta.reflect U).coeff t2 = 0 →
      (Delta.reflect U).coeff t3 = 0 →
      (Delta.reflect U).coeff t4 = 0 →
      (S ≤ t5 ∨ G-S ≤ t5 ∨ 4*N-G ≤ t5 ∨ 4*N-S ≤ t5 ∨
        ((Delta.reflect U).coeff t5 = 0 ∧
          Delta.natDegree ≤ N+S-6)))

theorem fiveToSix_zetaFirst_depthFive_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hfour : FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t1 := mu+1
  let t2 := mu+2
  let t3 := mu+3
  let t4 := mu+4
  let t5 := mu+5
  refine ⟨hfour,?_⟩
  intro hz1 hz2 hz3 hz4
  have hcopy := hfour
  change FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hcopy
  have hthree := hcopy.1
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hthree
  have hs := hthree.1
  by_cases hS5 : t5 < S
  · by_cases hBc5 : t5 < G-S
    · by_cases hGamma5 : t5 < 4*N-G
      · by_cases hB35 : t5 < 4*N-S
        · right;right;right;right
          have h0 := hs
          change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ mu = R-S ∧ _ ∧
            (∀ q, q ≤ mu → (Delta.reflect U).coeff q = 0) ∧ _ at h0
          have hzero := h0.2.2.2.2.2.2.2.2.1
          have hprior : ∀ j, j < t5 → (Delta.reflect U).coeff j = 0 := by
            intro j hj
            by_cases hj1 : j = t1
            · simpa only [hj1] using hz1
            · by_cases hj2 : j = t2
              · simpa only [hj2] using hz2
              · by_cases hj3 : j = t3
                · simpa only [hj3] using hz3
                · by_cases hj4 : j = t4
                  · simpa only [hj4] using hz4
                  · exact hzero j (by
                      dsimp only [t5,t4,t3,t2,t1] at hj hj1 hj2 hj3 hj4
                      omega)
          have hnext := fiveToSix_zetaFirst_discriminant_zero_of_prior68
            alpha gamma epsilon zeta eta terminal A B c d e N G S t5 hs
            hS5 hBc5 hGamma5 hB35 hprior
          rcases h0 with ⟨hSp,hSR,hd,he,hp,hless,hmu,hz,_hzero,hsupp⟩
          rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
          have hDelta : Delta.natDegree ≤ U := by
            dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
            compute_degree
            omega
          have hall : ∀ j, j ≤ t5 → (Delta.reflect U).coeff j = 0 := by
            intro j hj
            by_cases heq : j = t5
            · simpa only [heq,Delta,U] using hnext
            · exact hprior j (by omega)
          have hdrop := natDegree_le_of_reflect_initial_zero68 Delta U t5
            hDelta (by dsimp only [U,t5,mu,R] at *; omega) hall
          refine ⟨?_,?_⟩
          · simpa only [Delta,U] using hnext
          · simpa only [show U-t5-1 = N+S-6 by
                dsimp only [U,t5,mu,R] at *; omega] using hdrop
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

#print axioms fiveToSix_zetaFirst_S_load_finite68
#print axioms fiveToSix_zetaFirst_depthFive_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstDepthFive68

end Max11DegreeRoutes
