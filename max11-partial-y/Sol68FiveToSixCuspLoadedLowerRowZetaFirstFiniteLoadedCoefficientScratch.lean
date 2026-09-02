import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteStoppingScratch

/-! # The exact coefficient at the least zeta-first load

At the least load witness the first-integral combination is no longer
homogeneous.  This file retains all four literal source terms at once:
`B*d^2`, `B^3*c`, `gamma*(c*d-B*e)`, and `gamma*B^3`.  No exclusivity of
their load thresholds is assumed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedCoefficient68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal scalar left by the exact I3/I4 coefficient at an arbitrary
least-load witness. -/
def FiveToSixCuspZetaFirstLoadedScalar68
    (gamma : k) (A B c d e : k[X]) (N G S q : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let idx := U+V-q
  (Delta.reflect U).coeff q * d.coeff V +
      (2/3 : k) * (B^3*c).coeff idx -
      (3/2 : k) * (B*d^2).coeff idx +
      (9/2*gamma : k) *
        ((c*d).coeff idx - (B*e).coeff idx) +
      (3/4*gamma : k) * (B^3).coeff idx = 0

/-- Exact source coefficient with every potentially coincident load term
retained.  Only the vanished `zeta` block and the two source-side multiplier
coefficients are removed. -/
theorem fiveToSix_zetaFirst_loaded_coefficient68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S)
    (hprior : ∀ j, j < q →
      ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
        (8*N-2*G)).coeff j = 0) :
    FiveToSixCuspZetaFirstLoadedScalar68 gamma A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let idx := U+V-q
  change 0 < S ∧ S < R ∧ d.natDegree ≤ V ∧ e.natDegree ≤ 6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  change ∀ j, j < q → (Delta.reflect U).coeff j = 0 at hprior
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases hcusp with ⟨hb,hcn,hds,hes,hcusp0⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hDelta : Delta.natDegree ≤ U := by
    dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
    compute_degree
    omega
  have hBzero : B.coeff idx = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp only [idx,U,V]
    omega
  have hczero : c.coeff idx = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp only [idx,U,V]
    omega
  have hid := fiveToSix_firstIntegrals_cuspCombination68 gamma epsilon zeta
    A B c d e
  have hcoef := congrArg (fun p : k[X] => p.coeff idx) hid
  rw [hi3,hi4,hz] at hcoef
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,coeff_mul_C,
    hBzero,hczero,zero_mul,mul_zero,zero_smul,add_zero,sub_zero] at hcoef
  have href := coeff_mul_at_reflect_of_left_lower_zero68 Delta d U V q hDelta
    hd (by dsimp only [U,V] at *; omega) hprior
  have hds0 : (d.reflect V).coeff 0 = d.coeff V := by
    simp only [coeff_reflect,revAt_zero]
  change 0 = (Delta*d).coeff idx +
      (2/3 : k) * (B^3*c).coeff idx -
      (3/2 : k) * (B*d^2).coeff idx +
      (9/2*gamma : k) * ((c*d).coeff idx - (B*e).coeff idx) +
      (3/4*gamma : k) * (B^3).coeff idx at hcoef
  rw [show idx = U+V-q from rfl,href,hds0] at hcoef
  change FiveToSixCuspZetaFirstLoadedScalar68 gamma A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedScalar68,Delta,U,V,idx]
  exact hcoef.symm

/-- Minimality places each threshold either at/before the old depth, exactly
at the new witness, or strictly after it.  Thus no hidden intermediate load
is discarded when several source terms coincide. -/
theorem fiveToSix_zetaFirst_least_load_positions68
    (N G S mu q : ℕ) (hmuS : mu < S) (hqS : q ≤ S)
    (hminimal : ∀ j, mu < j → j < q →
      ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) :
    (q = S ∨ q < S) ∧
      (G-S ≤ mu ∨ G-S = q ∨ q < G-S) ∧
      (4*N-G ≤ mu ∨ 4*N-G = q ∨ q < 4*N-G) ∧
      (4*N-S ≤ mu ∨ 4*N-S = q ∨ q < 4*N-S) := by
  have hplaceBc : G-S ≤ mu ∨ G-S = q ∨ q < G-S := by
    by_cases hlo : G-S ≤ mu
    · exact Or.inl hlo
    by_cases hhi : q < G-S
    · exact Or.inr (Or.inr hhi)
    right;left
    by_contra hne
    have hbetween : mu < G-S ∧ G-S < q := by omega
    exact hminimal (G-S) hbetween.1 hbetween.2 (Or.inr (Or.inl le_rfl))
  have hplaceGamma : 4*N-G ≤ mu ∨ 4*N-G = q ∨ q < 4*N-G := by
    by_cases hlo : 4*N-G ≤ mu
    · exact Or.inl hlo
    by_cases hhi : q < 4*N-G
    · exact Or.inr (Or.inr hhi)
    right;left
    by_contra hne
    have hbetween : mu < 4*N-G ∧ 4*N-G < q := by omega
    exact hminimal (4*N-G) hbetween.1 hbetween.2
      (Or.inr (Or.inr (Or.inl le_rfl)))
  have hplaceB3 : 4*N-S ≤ mu ∨ 4*N-S = q ∨ q < 4*N-S := by
    by_cases hlo : 4*N-S ≤ mu
    · exact Or.inl hlo
    by_cases hhi : q < 4*N-S
    · exact Or.inr (Or.inr hhi)
    right;left
    by_contra hne
    have hbetween : mu < 4*N-S ∧ 4*N-S < q := by omega
    exact hminimal (4*N-S) hbetween.1 hbetween.2
      (Or.inr (Or.inr (Or.inr le_rfl)))
  exact ⟨by omega,hplaceBc,hplaceGamma,hplaceB3⟩

/-- Complete least-load handoff with the literal loaded scalar attached. -/
def FiveToSixCuspZetaFirstFiniteLoadedResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteStoppingResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ∃ q, mu < q ∧ q ≤ S ∧
      (∀ j, j < q → (Delta.reflect U).coeff j = 0) ∧
      (∀ j, mu < j → j < q →
        ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q ∧
      FiveToSixCuspZetaFirstLoadedScalar68 gamma A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hfinite : FiveToSixCuspZetaFirstFiniteStoppingResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hfinite,?_⟩
  have hf := hfinite
  change FiveToSixCuspZetaFirstDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hf
  rcases hf.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload⟩
  have hfour := hf.1
  change FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hfour
  have hthree := hfour.1
  change FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hthree
  have hthree' := hthree.1
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hthree'
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,
    fiveToSix_zetaFirst_loaded_coefficient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q
      hthree'.1 hqS hprior⟩

#print axioms fiveToSix_zetaFirst_loaded_coefficient68
#print axioms fiveToSix_zetaFirst_least_load_positions68
#print axioms fiveToSix_zetaFirst_finiteLoaded_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedCoefficient68

end Max11DegreeRoutes
