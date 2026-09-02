import Sol68FiveToSixCuspLoadedLowerRowZetaFirstClosureScratch

/-! # The second zeta-first successor coefficient

The first successor retained the four exact source loads at reflected depth
`mu+1`.  On its load-free branch this file consumes the same literal
I3/I4 first-integral coefficient at `mu+2`, retaining the same four loads
at their new exact depth.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstDepthTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Generic load-free successor coefficient.  Its four strict hypotheses
are exactly the four places where a literal source term can first enter. -/
theorem fiveToSix_zetaFirst_discriminant_zero_of_prior68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q < S) (hqBc : q < G-S)
    (hqGamma : q < 4*N-G) (hqB3 : q < 4*N-S)
    (hprior : ∀ j, j < q →
      ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
        (8*N-2*G)).coeff j = 0) :
    ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
      (8*N-2*G)).coeff q = 0 := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  change 0 < S ∧ S < R ∧ d.natDegree ≤ V ∧ e.natDegree ≤ 6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  change (∀ j, j < q → (Delta.reflect U).coeff j = 0) at hprior
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases hcusp with ⟨hb,hcn,hds,hes,hcusp0⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hDelta : Delta.natDegree ≤ U := by
    dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
    compute_degree
    omega
  have hBzero : B.coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hczero : c.coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hB3c : (B^3*c).coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hB2 : (B^2).coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hcd : (c*d).coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hBe : (B*e).coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hB3 : (B^3).coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hBd2 : (B*d^2).coeff (U+V-q) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hid := fiveToSix_firstIntegrals_cuspCombination68 gamma epsilon zeta
    A B c d e
  have hcoef := congrArg (fun p : k[X] => p.coeff (U+V-q)) hid
  rw [hi3,hi4,hz] at hcoef
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,coeff_mul_C,
    hBzero,hczero,hB3c,hB2,hcd,hBe,hB3,hBd2,zero_mul,mul_zero,
    zero_smul,add_zero,sub_zero] at hcoef
  have hprod : (Delta*d).coeff (U+V-q) = 0 := by
    change 0 = (Delta*d).coeff (U+V-q) at hcoef
    exact hcoef.symm
  have href := coeff_mul_at_reflect_of_left_lower_zero68 Delta d U V q hDelta
    hd (by dsimp only [U,V] at *; omega) hprior
  rw [href] at hprod
  have hdsR : (d.reflect V).coeff 0 ≠ 0 := by
    simpa only [coeff_reflect,revAt_zero,V] using hds
  have hqzero : (Delta.reflect U).coeff q = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hdsR
  simpa only [Delta,U] using hqzero

/-- Exact depth-two packet.  A load reached at `mu+1` is untouched.  Only
the first load-free branch is refined by the coefficient at `mu+2`. -/
def FiveToSixCuspZetaFirstDepthTwoResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t1 := mu+1
  let t2 := mu+2
  FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S ∧
    (S ≤ t1 ∨ G-S ≤ t1 ∨ 4*N-G ≤ t1 ∨ 4*N-S ≤ t1 ∨
      ((Delta.reflect U).coeff t1 = 0 ∧ Delta.natDegree ≤ N+S-2 ∧
        (S ≤ t2 ∨ G-S ≤ t2 ∨ 4*N-G ≤ t2 ∨ 4*N-S ≤ t2 ∨
          ((Delta.reflect U).coeff t2 = 0 ∧
            Delta.natDegree ≤ N+S-3))))

theorem fiveToSix_zetaFirst_depthTwo_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hfirst : FiveToSixCuspZetaFirstNextResidual68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstDepthTwoResidual68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t1 := mu+1
  let t2 := mu+2
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    (S ≤ t1 ∨ G-S ≤ t1 ∨ 4*N-G ≤ t1 ∨ 4*N-S ≤ t1 ∨
      ((Delta.reflect U).coeff t1 = 0 ∧ Delta.natDegree ≤ N+S-2)) at hfirst
  rcases hfirst with ⟨hs,hS1 | hBc1 | hGamma1 | hB31 | hfree1⟩
  · exact ⟨hs,Or.inl hS1⟩
  · exact ⟨hs,Or.inr (Or.inl hBc1)⟩
  · exact ⟨hs,Or.inr (Or.inr (Or.inl hGamma1))⟩
  · exact ⟨hs,Or.inr (Or.inr (Or.inr (Or.inl hB31)))⟩
  · refine ⟨hs,Or.inr (Or.inr (Or.inr (Or.inr ⟨hfree1.1,hfree1.2,?_⟩)))⟩
    by_cases hS2 : t2 < S
    · by_cases hBc2 : t2 < G-S
      · by_cases hGamma2 : t2 < 4*N-G
        · by_cases hB32 : t2 < 4*N-S
          · right;right;right;right
            have hprior : ∀ j, j < t2 → (Delta.reflect U).coeff j = 0 := by
              intro j hj
              by_cases hj1 : j = t1
              · simpa only [hj1] using hfree1.1
              · have h0 := hs
                change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ mu = R-S ∧ _ ∧
                  (∀ q, q ≤ mu → (Delta.reflect U).coeff q = 0) ∧ _ at h0
                exact h0.2.2.2.2.2.2.2.2.1 j (by
                  dsimp only [t2,t1] at hj hj1
                  omega)
            have hnext := fiveToSix_zetaFirst_discriminant_zero_of_prior68
              alpha gamma epsilon zeta eta terminal A B c d e N G S t2 hs
              hS2 hBc2 hGamma2 hB32 hprior
            have h0 := hs
            change _ ∧ _ ∧ _ ∧ _ ∧
              FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta
                terminal A B c d e N G S ∧ _ ∧ mu = R-S ∧ _ ∧ _ at h0
            rcases h0 with ⟨hSp,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
            rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
            have hDelta : Delta.natDegree ≤ U := by
              dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
              compute_degree
              omega
            have hall : ∀ j, j ≤ t2 → (Delta.reflect U).coeff j = 0 := by
              intro j hj
              by_cases heq : j = t2
              · simpa only [heq,Delta,U] using hnext
              · exact hprior j (by omega)
            have hdrop := natDegree_le_of_reflect_initial_zero68 Delta U t2
              hDelta (by dsimp only [U,t2,mu,R] at *; omega) hall
            refine ⟨?_,?_⟩
            · simpa only [Delta,U] using hnext
            · simpa only [show U-t2-1 = N+S-3 by
                  dsimp only [U,t2,mu,R] at *; omega] using hdrop
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)

#print axioms fiveToSix_zetaFirst_discriminant_zero_of_prior68
#print axioms fiveToSix_zetaFirst_depthTwo_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstDepthTwo68

end Max11DegreeRoutes
