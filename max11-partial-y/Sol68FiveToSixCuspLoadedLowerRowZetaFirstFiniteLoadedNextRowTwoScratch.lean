import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowOneScratch

/-! # The one-lower row-two equation after the least zeta-first load

This is the final lower-row equation at depth `q+1`, extracted at
`11*N-2*G-S-q-2` from the same frozen source and with all pinned loads kept.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal row-two scalar one coefficient below its same-q equation. -/
def FiveToSixCuspZetaFirstLoadedNextRowTwoScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  let ridx := 11*N-2*G-S-q-2
  (secondaryResidualRowTwoPolynomial68 A B c d e).coeff ridx +
      (4/3*gamma : k) * (A*derivative d).coeff ridx -
      (4/3*gamma : k) * (B*derivative c).coeff ridx -
      (4/3*gamma : k) * (c*derivative B).coeff ridx -
      (2/3*gamma : k) * (d*derivative A).coeff ridx -
      (1/3*epsilon : k) * (derivative A*B).coeff ridx +
      (2/3*epsilon : k) * (A*derivative B).coeff ridx +
      (2*epsilon : k) * (derivative d).coeff ridx = 0

/-- Exact source-backed one-lower row-two coefficient. -/
theorem fiveToSix_zetaFirst_loaded_next_rowTwo68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstLoadedNextRowTwoScalar68
      gamma epsilon A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 11*N-2*G-S-q-2
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
  change FiveToSixCuspZetaFirstLoadedNextRowTwoScalar68
    gamma epsilon A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedNextRowTwoScalar68,ridx]
  dsimp only [ridx] at hcoeff
  linear_combination hcoeff

/-- Complete exact q/q+1 packet with all three lower rows at both depths. -/
def FiveToSixCuspZetaFirstFiniteLoadedNextRowTwoResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedNextRowOneResidual68
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
        gamma epsilon A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedNextRowTwoScalar68
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_next_rowTwo_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hrow1 : FiveToSixCuspZetaFirstFiniteLoadedNextRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedNextRowTwoResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hrow1,?_⟩
  rcases hrow1.2 with
    ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrowZero,hrowOne,hrowTwo,
      hnext,hnextRowZero,hnextRowOne⟩
  have hn0 := hrow1.1
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
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hrowZero,hrowOne,hrowTwo,
    hnext,hnextRowZero,hnextRowOne,
    fiveToSix_zetaFirst_loaded_next_rowTwo68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q hsupport.1⟩

#print axioms fiveToSix_zetaFirst_loaded_next_rowTwo68
#print axioms fiveToSix_zetaFirst_finiteLoaded_next_rowTwo_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedNextRowTwo68

end Max11DegreeRoutes
