import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowOneScratch

/-! # The row-two equation at the frozen least zeta-first load

This is the final lower-row family at the same least witness.  The exact
coefficient at `11*N-2*G-S-q-1` is added without changing the source or
discarding any live gamma/epsilon term.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal row-two scalar at the retained least load. -/
def FiveToSixCuspZetaFirstLoadedRowTwoScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  let ridx := 11*N-2*G-S-q-1
  (secondaryResidualRowTwoPolynomial68 A B c d e).coeff ridx +
      (4/3*gamma : k) * (A*derivative d).coeff ridx -
      (4/3*gamma : k) * (B*derivative c).coeff ridx -
      (4/3*gamma : k) * (c*derivative B).coeff ridx -
      (2/3*gamma : k) * (d*derivative A).coeff ridx -
      (1/3*epsilon : k) * (derivative A*B).coeff ridx +
      (2/3*epsilon : k) * (A*derivative B).coeff ridx +
      (2*epsilon : k) * (derivative d).coeff ridx = 0

/-- Exact source-backed row-two coefficient at the frozen least witness. -/
theorem fiveToSix_zetaFirst_loaded_rowTwo68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstLoadedRowTwoScalar68
      gamma epsilon A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 11*N-2*G-S-q-1
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
  change FiveToSixCuspZetaFirstLoadedRowTwoScalar68
    gamma epsilon A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedRowTwoScalar68,ridx]
  dsimp only [ridx] at hcoeff
  linear_combination hcoeff

/-- Complete same-witness packet containing I3/I4 and all three lower rows. -/
def FiveToSixCuspZetaFirstFiniteLoadedRowTwoResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
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
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_rowTwo_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hrowOne : FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedRowTwoResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hrowOne,?_⟩
  have hr1 := hrowOne
  change FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr1
  rcases hr1.2 with
    ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0scalar,hrow1scalar⟩
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
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0scalar,hrow1scalar,
    fiveToSix_zetaFirst_loaded_rowTwo68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q hthree'.1⟩

#print axioms fiveToSix_zetaFirst_loaded_rowTwo68
#print axioms fiveToSix_zetaFirst_finiteLoaded_rowTwo_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowTwo68

end Max11DegreeRoutes
