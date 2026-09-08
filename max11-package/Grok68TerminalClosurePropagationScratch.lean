import Grok68TerminalBranchClosureScratch

/-! # Upward composition of the terminal `Fce`-zero wall closure

`Grok68TerminalBranchClosureScratch.lean` proves
`fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68`
from `(hterminal, RowOnePacket68, 9*N-7*S=0, Fce.coeff 0=0)`.

This file only cites landed reductions.  It does not re-prove any identity.

## Landed parent reductions that produce the terminal packet

* Endpoint cells to B3-equality: `fiveToSix_zetaFirst_endpoint_B3_equality_or_gamma68`
  (`Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3StrictClosureScratch.lean`).
  The strict sibling `G<2*S` is already `False` by
  `fiveToSix_zetaFirst_B3_strict_false68`.
* B3-equality finite stopping through epsilon/support:
  `fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_supportLoaded68`
  (`Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportWallScratch.lean`).
* Support-loaded to row-one packet, including the wall split `q=0 ∨ (0<q ∧ …)`:
  `fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68` /
  `fiveToSix_zetaFirst_B3_equality_support_i4_split68`
  (`Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportRowOneScratch.lean`).
* On `q=0`, Fce-zero versus vanishing-A:
  `fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68`
  (`Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThirdReductionScratch.lean`).

## Closed siblings (cited, not re-proved)

* Strict B3 cells: `fiveToSix_zetaFirst_B3_strict_false68`.
* Sparse endpoint: `fiveToSix_zetaFirst_sparse_endpoint_false68`.
* Support `q=0` and `Fce.coeff 0=0`:
  `fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68`.

## Open siblings (campaign frontier; not discharged here)

* Support `q=0` nonzero-`Fce` / vanishing-A jet:
  residual of `fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68`
  in `Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThirdReductionScratch.lean`.
* Support off-wall `0<q`:
  residual of `fiveToSix_zetaFirst_B3_equality_support_i4_split68` /
  `fiveToSix_zetaFirst_B3_equality_support_leading_packet68`
  in `Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportRowOneScratch.lean`
  and `Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeadingScratch.lean`.
* B3-equality `NextPacket` at `4*N-3*S=1`:
  `FiveToSixCuspZetaFirstB3EqualityNextPacket68`
  in `Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextScratch.lean`.
* B3-equality `NextTwoPacket` at `4*N-3*S=2 ∨ 3*N-2*S=1`:
  `FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68`
  in `Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextTwoScratch.lean`.
* Constant-`Fce` wall `D<T`:
  `FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68`
  in `Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonConstantWallScratch.lean`.
* Gamma-active `4*N-G≤S`, retained by every `*_or_residual68` in this chain.

Highest `False`: support-loaded packet on `q=0` with `Fce.coeff 0=0`.
Highest residual: endpoint cells, with that `False` branch deleted.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalClosurePropagation68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Remaining `q=0` sibling after deleting the zero-`Fce` wall. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68
    (A : k[X]) (N : ℕ) : Prop :=
  let p := 2 * N
  A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧ A.coeff (p - 3) = 0

/-- On the wall `9N=7S` the zero-`Fce` coefficient is impossible. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 ≠ 0 := by
  intro hf
  exact fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    hterminal hs hq hf

/-- The landed third-companion split, with the zero-`Fce` disjunct deleted. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68 A N := by
  have hsplit :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68] at hsplit ⊢
  rcases hsplit with hf | hA
  · exact False.elim
      (fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hs hq hf)
  · exact hA

/-- Highest `False` currently reachable: the support-loaded parent of the
row-one packet, on the wall `9N=7S` with vanishing constant `Fce`. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_qZero_Fce_zero_impossible68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    False :=
  fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal
    (fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs)
    hq hf

/-- Same wall, without the `Fce`-zero hypothesis: only vanishing-A remains. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_qZero_vanishingA68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68 A N :=
  fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal
    (fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs)
    hq

/-- Support-loaded residual: off-wall, or the `q=0` vanishing-A jet.
The off-wall leading relations themselves remain open. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall_or_qZero_vanishingA68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    0 < 9 * N - 7 * S ∨
      FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68 A N := by
  have hrow :=
    fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  have hsplit := hrow.2.2.2
  dsimp only at hsplit
  rcases hsplit with hq | hpos
  · exact Or.inr
      (fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hrow hq)
  · exact Or.inl hpos.1

/-- Highest residual currently reachable from the endpoint-cell chamber.
Closed siblings of this disjunction are already discharged by the landed
`constant_or_supportLoaded` reduction together with the terminal `Fce`-zero
`False`.  The remaining disjuncts are the open campaign frontier. -/
theorem fiveToSix_zetaFirst_endpoint_B3_equality_after_qZero_Fce_zero_closure68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hj : FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    4 * N - G ≤ S ∨
      (FiveToSixCuspZetaFirstB3EqualityNextPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S ∧ 4 * N - 3 * S = 1) ∨
      (FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S ∧
        (4 * N - 3 * S = 2 ∨ 3 * N - 2 * S = 1)) ∨
      FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S ∨
      (FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma epsilon
        zeta eta terminal A B c d e N G S ∧
        (0 < 9 * N - 7 * S ∨
          FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68 A N)) := by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_supportLoaded68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma | hwallOne | hsmall | hconstant | hsupport
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hconstant)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hsupport,
      fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall_or_qZero_vanishingA68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hsupport⟩)))

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA68
#print axioms fiveToSix_zetaFirst_B3_equality_supportLoaded_qZero_Fce_zero_impossible68
#print axioms fiveToSix_zetaFirst_B3_equality_supportLoaded_qZero_vanishingA68
#print axioms fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall_or_qZero_vanishingA68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_after_qZero_Fce_zero_closure68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalClosurePropagation68

end Max11DegreeRoutes
