import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowZeroScratch

/-! # The one-lower row-one equation after the least zeta-first load

This attaches the literal row-one coefficient at
`12*N-2*G-S-q-2` to the frozen q/q+1 source packet.  No coincident gamma or
epsilon convolution is discarded.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal row-one scalar one coefficient below its same-q equation. -/
def FiveToSixCuspZetaFirstLoadedNextRowOneScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  let ridx := 12*N-2*G-S-q-2
  (secondaryResidualRowOnePolynomial68 A B c d e).coeff ridx +
      (4/3*gamma : k) * (A*derivative e).coeff ridx -
      (4/3*gamma : k) * (c*derivative c).coeff ridx +
      (2/9*gamma : k) * (derivative A*B^2).coeff ridx +
      (2/3*gamma : k) * (B*derivative d).coeff ridx -
      (2/3*gamma : k) * (d*derivative B).coeff ridx +
      (2/3*epsilon : k) * (A*derivative c).coeff ridx +
      (2*epsilon : k) * (derivative e).coeff ridx = 0

/-- Exact source-backed one-lower row-one coefficient, with every pinned load
term still displayed. -/
theorem fiveToSix_zetaFirst_loaded_next_rowOne68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstLoadedNextRowOneScalar68
      gamma epsilon A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 12*N-2*G-S-q-2
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
  change FiveToSixCuspZetaFirstLoadedNextRowOneScalar68
    gamma epsilon A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedNextRowOneScalar68,ridx]
  dsimp only [ridx] at hcoeff
  linear_combination hcoeff

/-- The exact q/q+1 packet after adjoining its one-lower row-one equation. -/
def FiveToSixCuspZetaFirstFiniteLoadedNextRowOneResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedNextRowZeroResidual68
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
        gamma epsilon A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedNextRowOneScalar68
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_next_rowOne_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hrow0 : FiveToSixCuspZetaFirstFiniteLoadedNextRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedNextRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hrow0,?_⟩
  rcases hrow0.2 with
    ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrowZero,hrowOne,hrowTwo,
      hnext,hnextRowZero⟩
  have hn := hrow0.1
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
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrowZero,hrowOne,hrowTwo,
    hnext,hnextRowZero,
    fiveToSix_zetaFirst_loaded_next_rowOne68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q hsupport.1⟩

#print axioms fiveToSix_zetaFirst_loaded_next_rowOne68
#print axioms fiveToSix_zetaFirst_finiteLoaded_next_rowOne_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowOne68

end Max11DegreeRoutes
