import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowTwoScratch

/-! # The one-lower I3/I4 coefficient after the least zeta-first load

The source witness is unchanged.  Reflection at `q+1` leaves exactly the
two discriminant convolution terms `Delta_q*d_1` and `Delta_(q+1)*d_0`.
All one-lower load convolutions are retained literally.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextCoefficient68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- If the left factor vanishes strictly below `t`, its coefficient at
`t+1` has exactly two surviving convolution terms. -/
theorem mul_coeff_succ_of_left_lower_zero68
    (p d : k[X]) (t : ℕ)
    (hzero : ∀ j, j < t → p.coeff j = 0) :
    (p*d).coeff (t+1) =
      p.coeff t * d.coeff 1 + p.coeff (t+1) * d.coeff 0 := by
  let f : ℕ → k := fun j => p.coeff j * d.coeff (t+1-j)
  let s := Finset.range (t+2)
  have ht : t ∈ s := Finset.mem_range.mpr (by omega)
  have hts : t+1 ∈ s.erase t :=
    Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩
  have hz : ∀ j ∈ (s.erase t).erase (t+1), f j = 0 := by
    intro j hj
    have hj1 := Finset.mem_erase.mp hj
    have hj2 := Finset.mem_erase.mp hj1.2
    have hjr := Finset.mem_range.mp hj2.2
    have hjlt : j < t := by omega
    dsimp only [f]
    rw [hzero j hjlt,zero_mul]
  have hsum : (p*d).coeff (t+1) = ∑ j ∈ s, f j := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h1 := Finset.add_sum_erase s f ht
  have h2 := Finset.add_sum_erase (s.erase t) f hts
  have h3 : ∑ j ∈ (s.erase t).erase (t+1), f j = 0 :=
    Finset.sum_eq_zero hz
  rw [hsum,← h1,← h2,h3,add_zero]
  dsimp only [f]
  have ht1 : t + 1 - t = 1 := by omega
  have ht0 : t + 1 - (t + 1) = 0 := by omega
  rw [ht1,ht0]

/-- Fixed-bound reflected form of the shifted two-term convolution. -/
theorem coeff_mul_at_reflect_succ_of_left_lower_zero68
    (p d : k[X]) (u v t : ℕ)
    (hp : p.natDegree ≤ u) (hd : d.natDegree ≤ v)
    (ht : t+1 ≤ u+v)
    (hzero : ∀ j, j < t → (p.reflect u).coeff j = 0) :
    (p*d).coeff (u+v-(t+1)) =
      (p.reflect u).coeff t * (d.reflect v).coeff 1 +
        (p.reflect u).coeff (t+1) * (d.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff (t+1))
    (reflect_mul p d hp hd)
  rw [coeff_reflect,revAt_le ht,
    mul_coeff_succ_of_left_lower_zero68 _ _ _ hzero] at h
  exact h

/-- Exact one-lower loaded scalar. -/
def FiveToSixCuspZetaFirstLoadedNextScalar68
    (gamma : k) (A B c d e : k[X]) (N G S q : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let t := q+1
  let idx := U+V-t
  (Delta.reflect U).coeff q * (d.reflect V).coeff 1 +
      (Delta.reflect U).coeff t * d.coeff V +
      (2/3 : k) * (B^3*c).coeff idx -
      (3/2 : k) * (B*d^2).coeff idx +
      (9/2*gamma : k) * ((c*d).coeff idx - (B*e).coeff idx) +
      (3/4*gamma : k) * (B^3).coeff idx = 0

/-- Exact source-backed I3/I4 coefficient at `q+1`. -/
theorem fiveToSix_zetaFirst_loaded_next_coefficient68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S)
    (hprior : ∀ j, j < q →
      ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
        (8*N-2*G)).coeff j = 0) :
    FiveToSixCuspZetaFirstLoadedNextScalar68 gamma A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let t := q+1
  let idx := U+V-t
  change 0 < S ∧ S < R ∧ d.natDegree ≤ V ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  change ∀ j, j < q → (Delta.reflect U).coeff j = 0 at hprior
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hDelta : Delta.natDegree ≤ U := by
    dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
    compute_degree
    omega
  have hBzero : B.coeff idx = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp only [idx,t,U,V]
    omega
  have hczero : c.coeff idx = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp only [idx,t,U,V]
    omega
  have hid := fiveToSix_firstIntegrals_cuspCombination68 gamma epsilon zeta
    A B c d e
  have hcoef := congrArg (fun p : k[X] => p.coeff idx) hid
  rw [hi3,hi4,hz] at hcoef
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,coeff_mul_C,
    hBzero,hczero,zero_mul,mul_zero,zero_smul,add_zero,sub_zero] at hcoef
  have href := coeff_mul_at_reflect_succ_of_left_lower_zero68
    Delta d U V q hDelta hd (by dsimp only [U,V]; omega) hprior
  have hds0 : (d.reflect V).coeff 0 = d.coeff V := by
    simp only [coeff_reflect,revAt_zero]
  change 0 = (Delta*d).coeff idx +
      (2/3 : k) * (B^3*c).coeff idx -
      (3/2 : k) * (B*d^2).coeff idx +
      (9/2*gamma : k) * ((c*d).coeff idx - (B*e).coeff idx) +
      (3/4*gamma : k) * (B^3).coeff idx at hcoef
  rw [show idx = U+V-(q+1) by rfl,href,hds0] at hcoef
  change FiveToSixCuspZetaFirstLoadedNextScalar68 gamma A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedNextScalar68,Delta,U,V,t,idx]
  exact hcoef.symm

/-- Same frozen witness, now with its one-lower I3/I4 equation attached. -/
def FiveToSixCuspZetaFirstFiniteLoadedNextResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedRowTwoResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ∃ q, mu < q ∧ q ≤ S ∧
      (∀ j, j < q → (Delta.reflect U).coeff j = 0) ∧
      (∀ j, mu < j → j < q →
        ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q ∧
      FiveToSixCuspZetaFirstLoadedScalar68 gamma A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedRowZeroScalar68
        gamma epsilon A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedRowOneScalar68
        gamma epsilon A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedRowTwoScalar68
        gamma epsilon A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedNextScalar68 gamma A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_next_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hrows : FiveToSixCuspZetaFirstFiniteLoadedRowTwoResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedNextResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hrows,?_⟩
  have hr2 := hrows
  change FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr2
  rcases hr2.2 with
    ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0,hrow1,hrow2⟩
  have hr1 := hr2.1
  change FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr1
  have hr0 := hr1.1
  change FiveToSixCuspZetaFirstFiniteLoadedResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr0
  have hl := hr0.1
  change FiveToSixCuspZetaFirstFiniteStoppingResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hl
  have hf := hl.1
  change FiveToSixCuspZetaFirstDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hf
  have hfour := hf.1
  change FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hfour
  have hthree := hfour.1
  change FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hthree
  have hthree' := hthree.1
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hthree'
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0,hrow1,hrow2,
    fiveToSix_zetaFirst_loaded_next_coefficient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q
      hthree'.1 hqS hprior⟩

#print axioms mul_coeff_succ_of_left_lower_zero68
#print axioms coeff_mul_at_reflect_succ_of_left_lower_zero68
#print axioms fiveToSix_zetaFirst_loaded_next_coefficient68
#print axioms fiveToSix_zetaFirst_finiteLoaded_next_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextCoefficient68

end Max11DegreeRoutes
