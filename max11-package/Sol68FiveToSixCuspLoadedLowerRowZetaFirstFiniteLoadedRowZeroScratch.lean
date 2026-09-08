import Sol68FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedCoefficientScratch

/-! # The independent row-zero equation at the least zeta-first load

The exact positive row-zero coefficient is attached at
`13*N-2*G-S-q-1`.  Since the least witness can lie beyond the original
first wall, every surviving gamma/epsilon load term is retained literally.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowZero68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal positive row-zero scalar after the verified pin `zeta=0`.
No term is removed using an exclusive load assumption. -/
def FiveToSixCuspZetaFirstLoadedRowZeroScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  let ridx := 13*N-2*G-S-q-1
  (secondaryResidualRowZeroPolynomial68 A B c d e).coeff ridx +
      (2/9*gamma : k) * (B*derivative A*c).coeff ridx +
      (2/3*gamma : k) * (B*derivative e).coeff ridx -
      (1/9*epsilon : k) * (A*B*derivative A).coeff ridx -
      (2/9*gamma : k) * (A*derivative A*d).coeff ridx -
      (2/3*gamma : k) * (d*derivative c).coeff ridx -
      (1/3*epsilon : k) * (d*derivative A).coeff ridx = 0

/-- Exact source-backed row-zero coefficient at the least-load index. -/
theorem fiveToSix_zetaFirst_loaded_rowZero68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S) :
    FiveToSixCuspZetaFirstLoadedRowZeroScalar68
      gamma epsilon A B c d e N G S q := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let ridx := 13*N-2*G-S-q-1
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
  change FiveToSixCuspZetaFirstLoadedRowZeroScalar68
    gamma epsilon A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstLoadedRowZeroScalar68,ridx]
  dsimp only [ridx] at hrow
  linear_combination hrow

/-- Full exact two-equation system at the retained least load. -/
def FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstFiniteLoadedResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ∃ q, mu < q ∧ q ≤ S ∧
      (∀ j, j < q → (Delta.reflect U).coeff j = 0) ∧
      (∀ j, mu < j → j < q →
        ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q ∧
      FiveToSixCuspZetaFirstLoadedScalar68 gamma A B c d e N G S q ∧
      FiveToSixCuspZetaFirstLoadedRowZeroScalar68
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_finiteLoaded_rowZero_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hloaded : FiveToSixCuspZetaFirstFiniteLoadedResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hloaded,?_⟩
  have hl := hloaded
  change FiveToSixCuspZetaFirstFiniteStoppingResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hl
  rcases hl.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar⟩
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
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,
    fiveToSix_zetaFirst_loaded_rowZero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q
      hthree'.1 hqS⟩

#print axioms fiveToSix_zetaFirst_loaded_rowZero68
#print axioms fiveToSix_zetaFirst_finiteLoaded_rowZero_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteLoadedRowZero68

end Max11DegreeRoutes
