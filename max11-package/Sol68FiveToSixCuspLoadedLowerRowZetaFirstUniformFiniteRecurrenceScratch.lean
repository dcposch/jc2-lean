import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextTwoCoefficientScratch

/-! # Uniform finite recurrence after the least zeta-first load

This replaces fixed-depth unrolling by a source-backed family for every
`m ≤ S-q`.  The reflected discriminant--`d` coefficient is an exact finite
convolution, and I3/I4 together with all three lower rows is retained at the
same depth.  All five I3/I4 load products remain literal.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformFiniteRecurrence68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact finite convolution after a left-hand coefficient gap.  The `Ico`
form is directly suited to induction on the finite depth `m`. -/
theorem mul_coeff_add_Ico_of_left_lower_zero68
    (p d : k[X]) (q m : ℕ)
    (hzero : ∀ j, j < q → p.coeff j = 0) :
    (p*d).coeff (q+m) =
      ∑ j ∈ Finset.Ico q (q+m+1),
        p.coeff j * d.coeff (q+m-j) := by
  let f : ℕ → k := fun j => p.coeff j * d.coeff (q+m-j)
  have hsum : (p*d).coeff (q+m) =
      ∑ j ∈ Finset.range (q+m+1), f j := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have hz : ∑ j ∈ Finset.range q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjq := Finset.mem_range.mp hj
    dsimp only [f]
    rw [hzero j hjq,zero_mul]
  have hle : q ≤ q+m+1 := by omega
  have hsplit := Finset.sum_range_add_sum_Ico f hle
  rw [hsum,← hsplit,hz,zero_add]

/-- Fixed-bound reflected finite convolution at arbitrary depth `q+m`. -/
theorem coeff_mul_at_reflect_add_Ico_of_left_lower_zero68
    (p d : k[X]) (u v q m : ℕ)
    (hp : p.natDegree ≤ u) (hd : d.natDegree ≤ v)
    (ht : q+m ≤ u+v)
    (hzero : ∀ j, j < q → (p.reflect u).coeff j = 0) :
    (p*d).coeff (u+v-(q+m)) =
      ∑ j ∈ Finset.Ico q (q+m+1),
        (p.reflect u).coeff j *
          (d.reflect v).coeff (q+m-j) := by
  have h := congrArg (fun r : k[X] => r.coeff (q+m))
    (reflect_mul p d hp hd)
  rw [coeff_reflect,revAt_le ht,
    mul_coeff_add_Ico_of_left_lower_zero68 _ _ _ _ hzero] at h
  exact h

/-- Uniform I3/I4 scalar at finite depth `q+m`.  The five load groups are
`B^3*c`, `B*d^2`, `c*d`, `B*e`, and `B^3`. -/
def FiveToSixCuspZetaFirstLoadedUniformScalar68
    (gamma : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let t := q+m
  let idx := U+V-t
  (∑ j ∈ Finset.Ico q (t+1),
      (Delta.reflect U).coeff j * (d.reflect V).coeff (t-j)) +
      (2/3 : k) * (B^3*c).coeff idx -
      (3/2 : k) * (B*d^2).coeff idx +
      (9/2*gamma : k) * ((c*d).coeff idx - (B*e).coeff idx) +
      (3/4*gamma : k) * (B^3).coeff idx = 0

/-- Uniform row-zero scalar at the same finite depth. -/
def FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let ridx := 13*N-2*G-S-(q+m)-1
  (secondaryResidualRowZeroPolynomial68 A B c d e).coeff ridx +
      (2/9*gamma : k) * (B*derivative A*c).coeff ridx +
      (2/3*gamma : k) * (B*derivative e).coeff ridx -
      (1/9*epsilon : k) * (A*B*derivative A).coeff ridx -
      (2/9*gamma : k) * (A*derivative A*d).coeff ridx -
      (2/3*gamma : k) * (d*derivative c).coeff ridx -
      (1/3*epsilon : k) * (d*derivative A).coeff ridx = 0

/-- Uniform row-one scalar at the same finite depth. -/
def FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let ridx := 12*N-2*G-S-(q+m)-1
  (secondaryResidualRowOnePolynomial68 A B c d e).coeff ridx +
      (4/3*gamma : k) * (A*derivative e).coeff ridx -
      (4/3*gamma : k) * (c*derivative c).coeff ridx +
      (2/9*gamma : k) * (derivative A*B^2).coeff ridx +
      (2/3*gamma : k) * (B*derivative d).coeff ridx -
      (2/3*gamma : k) * (d*derivative B).coeff ridx +
      (2/3*epsilon : k) * (A*derivative c).coeff ridx +
      (2*epsilon : k) * (derivative e).coeff ridx = 0

/-- Uniform row-two scalar at the same finite depth. -/
def FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let ridx := 11*N-2*G-S-(q+m)-1
  (secondaryResidualRowTwoPolynomial68 A B c d e).coeff ridx +
      (4/3*gamma : k) * (A*derivative d).coeff ridx -
      (4/3*gamma : k) * (B*derivative c).coeff ridx -
      (4/3*gamma : k) * (c*derivative B).coeff ridx -
      (2/3*gamma : k) * (d*derivative A).coeff ridx -
      (1/3*epsilon : k) * (derivative A*B).coeff ridx +
      (2/3*epsilon : k) * (A*derivative B).coeff ridx +
      (2*epsilon : k) * (derivative d).coeff ridx = 0

/-- Exact source-backed I3/I4 coefficient for arbitrary bounded depth. -/
theorem fiveToSix_zetaFirst_loaded_uniform_coefficient68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q m : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S) (hm : m ≤ S-q)
    (hprior : ∀ j, j < q →
      ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
        (8*N-2*G)).coeff j = 0) :
    FiveToSixCuspZetaFirstLoadedUniformScalar68
      gamma A B c d e N G S q m := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let t := q+m
  let idx := U+V-t
  change 0 < S ∧ S < R ∧ d.natDegree ≤ V ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  change ∀ j, j < q → (Delta.reflect U).coeff j = 0 at hprior
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hqm : q+m ≤ S := by omega
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
  have href := coeff_mul_at_reflect_add_Ico_of_left_lower_zero68
    Delta d U V q m hDelta hd (by dsimp only [U,V]; omega) hprior
  change 0 = (Delta*d).coeff idx +
      (2/3 : k) * (B^3*c).coeff idx -
      (3/2 : k) * (B*d^2).coeff idx +
      (9/2*gamma : k) * ((c*d).coeff idx - (B*e).coeff idx) +
      (3/4*gamma : k) * (B^3).coeff idx at hcoef
  rw [show idx = U+V-(q+m) by rfl,href] at hcoef
  change FiveToSixCuspZetaFirstLoadedUniformScalar68
    gamma A B c d e N G S q m
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformScalar68,Delta,U,V,t,idx]
  exact hcoef.symm

/-- Exact source-backed row-zero coefficient for arbitrary bounded depth. -/
theorem fiveToSix_zetaFirst_loaded_uniform_rowZero68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q m : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S) (hm : m ≤ S-q) :
    FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S q m := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 13*N-2*G-S-(q+m)-1
  change 0 < S ∧ S < R ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hqm : q+m ≤ S := by omega
  have hrpos : 0 < ridx := by
    dsimp only [ridx]
    omega
  have hrow := hpos ridx hrpos
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hrow
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,zero_mul,
    mul_zero,zero_smul,add_zero] at hrow
  change FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
    gamma epsilon A B c d e N G S q m
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68,ridx]
  dsimp only [ridx] at hrow
  linear_combination hrow

/-- Exact source-backed row-one coefficient for arbitrary bounded depth. -/
theorem fiveToSix_zetaFirst_loaded_uniform_rowOne68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q m : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68
      gamma epsilon A B c d e N G S q m := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 12*N-2*G-S-(q+m)-1
  change 0 < S ∧ S < R ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff ridx) hrow1
  rw [coeff_add,cubicLoadRowOnePolynomial68_uniform_pinned_eq68,hz] at hcoeff
  simp only [coeff_zero,coeff_add,coeff_sub,coeff_smul,smul_eq_mul,
    zero_mul,mul_zero,zero_smul,add_zero] at hcoeff
  change FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68
    gamma epsilon A B c d e N G S q m
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68,ridx]
  dsimp only [ridx] at hcoeff
  linear_combination hcoeff

/-- Exact source-backed row-two coefficient for arbitrary bounded depth. -/
theorem fiveToSix_zetaFirst_loaded_uniform_rowTwo68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q m : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S q m := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 11*N-2*G-S-(q+m)-1
  change 0 < S ∧ S < R ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff ridx) hrow2
  rw [coeff_add,cubicLoadRowTwoPolynomial68_uniform_pinned_eq68,hz] at hcoeff
  simp only [coeff_zero,coeff_add,coeff_sub,coeff_smul,smul_eq_mul,
    zero_mul,mul_zero,zero_smul,add_zero] at hcoeff
  change FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
    gamma epsilon A B c d e N G S q m
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68,ridx]
  dsimp only [ridx] at hcoeff
  linear_combination hcoeff

/-- Induction-ready bounded family: every depth through the support wall has
the exact I3/I4 equation and all three exact lower rows. -/
def FiveToSixCuspZetaFirstLoadedUniformFiniteFamily68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  ∀ m, m ≤ S-q →
    FiveToSixCuspZetaFirstLoadedUniformScalar68
        gamma A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
        gamma epsilon A B c d e N G S q m

theorem fiveToSix_zetaFirst_loaded_uniform_finite_family68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S)
    (hprior : ∀ j, j < q →
      ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
        (8*N-2*G)).coeff j = 0) :
    FiveToSixCuspZetaFirstLoadedUniformFiniteFamily68
      gamma epsilon A B c d e N G S q := by
  intro m hm
  exact ⟨
    fiveToSix_zetaFirst_loaded_uniform_coefficient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q m
      hs hqS hm hprior,
    fiveToSix_zetaFirst_loaded_uniform_rowZero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q m
      hs hqS hm,
    fiveToSix_zetaFirst_loaded_uniform_rowOne68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q m hs,
    fiveToSix_zetaFirst_loaded_uniform_rowTwo68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q m hs⟩

/-- The verified fixed q/q+1/q+2 packet, strengthened by the entire bounded
finite source family on its exact least-load witness. -/
def FiveToSixCuspZetaFirstUniformFiniteRecurrenceResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedNextTwoResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ∃ q, mu < q ∧ q ≤ S ∧
      (∀ j, j < q → (Delta.reflect U).coeff j = 0) ∧
      (∀ j, mu < j → j < q →
        ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q ∧
      FiveToSixCuspZetaFirstLoadedScalar68 gamma A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedUniformFiniteFamily68
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_uniform_finite_recurrence_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hnext2 : FiveToSixCuspZetaFirstFiniteLoadedNextTwoResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstUniformFiniteRecurrenceResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hnext2,?_⟩
  rcases hnext2.2 with
    ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrowZero,hrowOne,hrowTwo,
      hnext,hnextRowZero,hnextRowOne,hnextRowTwo,hnextTwo⟩
  have hn2 := hnext2.1
  have hn1 := hn2.1
  have hn0 := hn1.1
  have hn := hn0.1
  have hr2 := hn.1
  change FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr2
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
  have hsupport := hthree.1
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hsupport
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,
    fiveToSix_zetaFirst_loaded_uniform_finite_family68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q
      hsupport.1 hqS hprior⟩

#print axioms mul_coeff_add_Ico_of_left_lower_zero68
#print axioms coeff_mul_at_reflect_add_Ico_of_left_lower_zero68
#print axioms fiveToSix_zetaFirst_loaded_uniform_coefficient68
#print axioms fiveToSix_zetaFirst_loaded_uniform_finite_family68
#print axioms fiveToSix_zetaFirst_uniform_finite_recurrence_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformFiniteRecurrence68

end Max11DegreeRoutes
