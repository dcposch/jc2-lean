import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextCoefficientScratch

/-! # The one-lower row-zero equation after the least zeta-first load

The source witness and the least loaded index `q` are unchanged.  This file
attaches the exact row-zero coefficient at `13*N-2*G-S-q-2`; all gamma and
epsilon load convolutions at that index remain literal.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowZero68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal row-zero scalar one coefficient below the same-q equation. -/
def FiveToSixCuspZetaFirstLoadedNextRowZeroScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  let ridx := 13*N-2*G-S-q-2
  (secondaryResidualRowZeroPolynomial68 A B c d e).coeff ridx +
      (2/9*gamma : k) * (B*derivative A*c).coeff ridx +
      (2/3*gamma : k) * (B*derivative e).coeff ridx -
      (1/9*epsilon : k) * (A*B*derivative A).coeff ridx -
      (2/9*gamma : k) * (A*derivative A*d).coeff ridx -
      (2/3*gamma : k) * (d*derivative c).coeff ridx -
      (1/3*epsilon : k) * (d*derivative A).coeff ridx = 0

/-- Exact source-backed one-lower row-zero coefficient.  No q-wall load is
removed: each possible contribution is present in the displayed scalar. -/
theorem fiveToSix_zetaFirst_loaded_next_rowZero68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S) :
    FiveToSixCuspZetaFirstLoadedNextRowZeroScalar68
      gamma epsilon A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 13*N-2*G-S-q-2
  change 0 < S ∧ S < R ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hrpos : 0 < ridx := by
    dsimp only [ridx]
    omega
  have hrow := hpos ridx hrpos
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hrow
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,zero_mul,
    mul_zero,zero_smul,add_zero] at hrow
  change FiveToSixCuspZetaFirstLoadedNextRowZeroScalar68
    gamma epsilon A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedNextRowZeroScalar68,ridx]
  dsimp only [ridx] at hrow
  linear_combination hrow

/-- The frozen source packet with both q+1 equations now attached. -/
def FiveToSixCuspZetaFirstFiniteLoadedNextRowZeroResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedNextResidual68
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
      FiveToSixCuspZetaFirstLoadedNextScalar68 gamma A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedNextRowZeroScalar68
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_next_rowZero_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hnext : FiveToSixCuspZetaFirstFiniteLoadedNextResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedNextRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hnext,?_⟩
  rcases hnext.2 with
    ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0,hrow1,hrow2,hnextscalar⟩
  have hr2 := hnext.1
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
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0,hrow1,hrow2,
    hnextscalar,
    fiveToSix_zetaFirst_loaded_next_rowZero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q
      hsupport.1 hqS⟩

#print axioms fiveToSix_zetaFirst_loaded_next_rowZero68
#print axioms fiveToSix_zetaFirst_finiteLoaded_next_rowZero_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowZero68

end Max11DegreeRoutes
