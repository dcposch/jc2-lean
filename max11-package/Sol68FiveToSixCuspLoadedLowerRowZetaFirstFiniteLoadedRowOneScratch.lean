import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowZeroScratch

/-! # The independent row-one equation at the least zeta-first load

The exact row-one coefficient at `12*N-2*G-S-q-1` is attached to the
least-witness I3/I4 and row-zero equations.  Every gamma/epsilon load term
surviving the source pin `zeta=0` remains literal.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal row-one scalar at the retained least load. -/
def FiveToSixCuspZetaFirstLoadedRowOneScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  let ridx := 12*N-2*G-S-q-1
  (secondaryResidualRowOnePolynomial68 A B c d e).coeff ridx +
      (4/3*gamma : k) * (A*derivative e).coeff ridx -
      (4/3*gamma : k) * (c*derivative c).coeff ridx +
      (2/9*gamma : k) * (derivative A*B^2).coeff ridx +
      (2/3*gamma : k) * (B*derivative d).coeff ridx -
      (2/3*gamma : k) * (d*derivative B).coeff ridx +
      (2/3*epsilon : k) * (A*derivative c).coeff ridx +
      (2*epsilon : k) * (derivative e).coeff ridx = 0

/-- Exact source-backed row-one coefficient.  Unlike row zero, no positive-
coefficient adapter is needed because the full row-one polynomial is zero. -/
theorem fiveToSix_zetaFirst_loaded_rowOne68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstLoadedRowOneScalar68
      gamma epsilon A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 12*N-2*G-S-q-1
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
  change FiveToSixCuspZetaFirstLoadedRowOneScalar68
    gamma epsilon A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedRowOneScalar68,ridx]
  dsimp only [ridx] at hcoeff
  linear_combination hcoeff

/-- Full exact three-equation system at the same least source witness. -/
def FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
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
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_rowOne_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hrowZero : FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hrowZero,?_⟩
  have hr := hrowZero
  change FiveToSixCuspZetaFirstFiniteLoadedResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr
  rcases hr.2 with
    ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0scalar⟩
  have hl := hr.1
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
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrow0scalar,
    fiveToSix_zetaFirst_loaded_rowOne68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q hthree'.1⟩

#print axioms fiveToSix_zetaFirst_loaded_rowOne68
#print axioms fiveToSix_zetaFirst_finiteLoaded_rowOne_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowOne68

end Max11DegreeRoutes
