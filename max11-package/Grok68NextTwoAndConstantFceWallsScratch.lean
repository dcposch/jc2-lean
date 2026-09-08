import Grok68B3EqualityNextPacketWallScratch
import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonConstantWallScratch

/-! # Endpoint chambers 4 and 5: NextTwo walls and constant-`Fce`

`Grok68TerminalClosurePropagationScratch.lean` lists the open B3-equality
side cells after the terminal `Fce`-zero `False`.  This file attacks the
two named arithmetic walls:

* Chamber 4: `FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68` at
  `4N-3S=2` or `3N-2S=1`.
* Chamber 5: `FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68`
  on `D<T`.

## Chamber 4b: `3N-2S=1` is empty

On every B3-equality cell, `G=2S` and `S<4N-G` sit inside
`FiveToSixCuspZetaFirstB3EndpointPacket68`, and the contracted cusp
supplies `5N<2G`.  These three inequalities contradict `3N-2S=1`.
The epsilon-B NextTwo wall is `False`.

## Chamber 4a: `4N-3S=2` by the `4N-3S=1` method

The ordinary NextPacket contraction has already killed
`F.coeff (9N-6S-1)` and `J.coeff (11N-6S-1)`.  On `4N-3S=2` the `S+2`
source indices coincide with the first `gamma d` load.  The compensated
I4 identity is still `Fc = F+(3/2)gamma d = -(3/4)epsilon B + (3/8) C i4`.
Wall arithmetic gives `N=3m+2`, `S=4m+2` with `m≥3`, hence
`deg d = N+2` and `deg B = (N+4)/3`, so `deg Fc ≤ deg B < deg d`.
The `Fc` block lies strictly below both `S+2` indices.  Row two collapses
to `J'`, forcing `J.coeff (11N-6S-2)=0`.  Combined with the two already
vanishing top jets this drops `J` three steps.

The same I4 identity plus a two-case comparison of `F` against `d`
records the exact `F` profile: `gamma=0` implies `deg F ≤ deg B`, while
`gamma≠0` implies `deg F = deg d`.  Neither case contradicts the cusp
leading edges.  That is the GAP to `False`.

Exact gain: consume the two `S+2` source rows on `4N-3S=2`; replace them
by `deg Fc ≤ 3N-2S` and `deg J ≤ 11N-6S-3`, with the two-case `F`
profile attached.  Next unused row: loaded uniform row one at depth
`S+2` (index `12N-6S-3`).

## Chamber 5: constant-`Fce` wall `D<T`

The landed packet already has the exact identity `Fce=0` and
`deg J ≤ 2N-1`.  Compensated I4 rewrites this as `i4=0` and
`Fc = -(3/4)epsilon B`.  The two-case dictionary is then forced:
`gamma=0` implies `deg F ≤ D`, `gamma≠0` implies `deg F = V`;
`epsilon=0` implies `Fc=0`, `epsilon≠0` implies `deg Fc = D`.
These leading-edge cases are compatible with the cusp.  The remaining
`J` coefficients mix unknown subleadings, so this is not a closure.

Exact gain: attach the I4 form and the two-case `(gamma,epsilon)`
degree dictionary to the landed `Fce=0` / `deg J ≤ 2N-1` contraction.
Next unused row: loaded uniform row one at depth `S+3D` (index `3N-1`).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextTwoAndConstantFceWalls68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber 4b: the epsilon-B wall is empty -/

/-- On a B3-equality gamma-inactive cell the bound `3N-2S=1` cannot occur. -/
theorem fiveToSix_nextTwo_epsilonWall_arith_false68
    (N G S : ℕ) (hN : 0 < N) (hgt : 5 * N < 2 * G) (hGS : G = 2 * S)
    (hGamma : S < 4 * N - G) (hwall : 3 * N - 2 * S = 1) :
    False := by
  omega

/-- The NextTwo epsilon-B disjunct is `False`. -/
theorem fiveToSix_zetaFirst_B3_equality_nextTwo_epsilonWall_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hwall : 3 * N - 2 * S = 1) :
    False := by
  rcases hp with ⟨hnext, _⟩
  rcases hnext with ⟨hGS, hcell, _⟩
  have hbase := hcell.1.1.1
  rcases hbase with ⟨hs, hBc, hGamma, q, hmuq, hqS, hprior, hminimal, hload,
    hi3, hi4, hend⟩
  have hp' := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp'
  rcases hp' with ⟨hS, hSR, hd, he, hpC, hrest⟩
  rcases hpC with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  exact fiveToSix_nextTwo_epsilonWall_arith_false68 N G S hN hgt hGS hGamma
    hwall

/-! ## Chamber 4a: wall arithmetic `4N = 3S+2` -/

/-- Degree dictionary on the gamma-d NextTwo wall: `deg B = D = (N+4)/3`,
`deg d = V = N+2`, with `D < V`, `2D < V`, and the `Fc` block strictly
below both `S+2` source indices. -/
theorem fiveToSix_nextTwo_gammaWall_degree_arith68
    (N S : ℕ) (hN : 0 < N) (hEq : 4 * N = 3 * S + 2) (hgt : 5 * N < 4 * S) :
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    0 < S ∧ 2 < N ∧ N ≤ S ∧ 0 < D ∧ D < V ∧ 2 * D < V ∧ 1 < D ∧
      V = 9 * N - 6 * S - 2 ∧ 11 * N - 6 * S - 2 = 3 * N + 2 ∧
      13 * N - 6 * S - 3 = 5 * N + 1 ∧ 11 * N - 6 * S - 3 = 3 * N + 1 ∧
      11 * N - 6 * S - 3 + 1 = 11 * N - 6 * S - 2 ∧
      2 * N + D - 1 < 11 * N - 6 * S - 3 ∧
      (2 * N - 1) + D < 11 * N - 6 * S - 3 ∧
      2 * N + (2 * N - 1) + D < 13 * N - 6 * S - 3 := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  change 0 < S ∧ 2 < N ∧ N ≤ S ∧ 0 < D ∧ D < V ∧ 2 * D < V ∧ 1 < D ∧
    V = 9 * N - 6 * S - 2 ∧ 11 * N - 6 * S - 2 = 3 * N + 2 ∧
    13 * N - 6 * S - 3 = 5 * N + 1 ∧ 11 * N - 6 * S - 3 = 3 * N + 1 ∧
    11 * N - 6 * S - 3 + 1 = 11 * N - 6 * S - 2 ∧
    2 * N + D - 1 < 11 * N - 6 * S - 3 ∧
    (2 * N - 1) + D < 11 * N - 6 * S - 3 ∧
    2 * N + (2 * N - 1) + D < 13 * N - 6 * S - 3
  have hN2 : 3 ∣ N - 2 := by
    have h : N - 2 = 3 * (S - N) := by omega
    exact ⟨S - N, h⟩
  obtain ⟨m, hm⟩ := hN2
  have hNform : N = 3 * m + 2 := by omega
  have hSform : S = 4 * m + 2 := by
    have hmul : 4 * (3 * m + 2) = 3 * S + 2 := by
      rw [← hNform]
      exact hEq
    omega
  have hmpos : 2 < m := by
    have hgt' : 5 * (3 * m + 2) < 4 * (4 * m + 2) := by
      rw [← hNform, ← hSform]
      exact hgt
    omega
  subst hNform
  subst hSform
  dsimp only [D, V]
  omega

/-! ## Literal `S+2` rows, keeping the coincident `gamma d` load -/

def FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowZeroScalar68
    (gamma : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let K := 13 * N - 6 * S - 3
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K +
    (3 / 2 * gamma : k) * (A * derivative A * d).coeff K = 0

def FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowTwoScalar68
    (gamma : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let K := 11 * N - 6 * S - 3
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K -
      (9 * gamma : k) * (A * derivative d).coeff K +
      (9 / 2 * gamma : k) * (d * derivative A).coeff K = 0

/-- On `4N-3S=2` the only extra attaining terms at the two `S+2` indices
are the first `gamma d` loads.  Every epsilon/`B` load and every other
residual product lies strictly below. -/
theorem fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_literal_rows68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2 * S) (hwall : 4 * N - 3 * S = 2)
    (hrow0 : FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S 2)
    (hrow2 : FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S 2) :
    FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowZeroScalar68
        gamma A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowTwoScalar68
        gamma A B c d e N S := by
  let K0 := 13 * N - 6 * S - 3
  let K2 := 11 * N - 6 * S - 3
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hEq : 4 * N = 3 * S + 2 := by omega
  have hgt4 : 5 * N < 4 * S := by omega
  have harith := fiveToSix_nextTwo_gammaWall_degree_arith68 N S hN hEq hgt4
  have hidx0 : 13 * N - 2 * G - S - (S + 2) - 1 = K0 := by
    rw [heq]
    dsimp only [K0]
    omega
  have hidx2 : 11 * N - 2 * G - S - (S + 2) - 1 = K2 := by
    rw [heq]
    dsimp only [K2]
    omega
  have h0ABd : (A * B ^ 2 * derivative d).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0ABBd : (A * B * derivative B * d).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0Bce : (B * c * derivative e).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0Bdd : (B * d * derivative d).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0Bd2 : (derivative B * d ^ 2).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0ccd : (c * derivative c * d).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0BAc : (B * derivative A * c).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0Be : (B * derivative e).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0ABA : (A * B * derivative A).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0dc : (d * derivative c).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h0dA : (d * derivative A).natDegree < K0 := by
    dsimp only [K0]; compute_degree; omega
  have h2B2d : (B ^ 2 * derivative d).natDegree < K2 := by
    dsimp only [K2]; compute_degree; omega
  have h2BBd : (B * derivative B * d).natDegree < K2 := by
    dsimp only [K2]; compute_degree; omega
  have h2Bc : (B * derivative c).natDegree < K2 := by
    dsimp only [K2]; compute_degree; omega
  have h2cB : (c * derivative B).natDegree < K2 := by
    dsimp only [K2]; compute_degree; omega
  have h2AB1 : (derivative A * B).natDegree < K2 := by
    dsimp only [K2]; compute_degree; omega
  have h2AB2 : (A * derivative B).natDegree < K2 := by
    dsimp only [K2]; compute_degree; omega
  have h2d : (derivative d).natDegree < K2 := by
    dsimp only [K2]; compute_degree; omega
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68] at hrow0
  rw [hidx0] at hrow0
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt h0ABd,
    coeff_eq_zero_of_natDegree_lt h0ABBd,
    coeff_eq_zero_of_natDegree_lt h0Bce,
    coeff_eq_zero_of_natDegree_lt h0Bdd,
    coeff_eq_zero_of_natDegree_lt h0Bd2,
    coeff_eq_zero_of_natDegree_lt h0ccd,
    coeff_eq_zero_of_natDegree_lt h0BAc,
    coeff_eq_zero_of_natDegree_lt h0Be,
    coeff_eq_zero_of_natDegree_lt h0ABA,
    coeff_eq_zero_of_natDegree_lt h0dc,
    coeff_eq_zero_of_natDegree_lt h0dA,
    mul_zero, add_zero, sub_zero] at hrow0
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68] at hrow2
  rw [hidx2] at hrow2
  simp only [secondaryResidualRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt h2B2d,
    coeff_eq_zero_of_natDegree_lt h2BBd,
    coeff_eq_zero_of_natDegree_lt h2Bc,
    coeff_eq_zero_of_natDegree_lt h2cB,
    coeff_eq_zero_of_natDegree_lt h2AB1,
    coeff_eq_zero_of_natDegree_lt h2AB2,
    coeff_eq_zero_of_natDegree_lt h2d,
    mul_zero, add_zero, sub_zero] at hrow2
  constructor
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68, K0]
    simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul]
    linear_combination (-27 / 4 : k) * hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68, K2]
    simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul]
    linear_combination (-27 / 4 : k) * hrow2

/-! ## Compensated I4 support drop on `4N-3S=2` -/

/-- On the NextTwo gamma wall, `deg Fc ≤ deg B < deg d`. -/
theorem fiveToSix_nextTwo_gammaWall_Fc_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2 * S) (hwall : 4 * N - 3 * S = 2) :
    let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
    Fc.natDegree ≤ 3 * N - 2 * S := by
  let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases fiveToSix_nextPacket_wall_Fc_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i4, hFc⟩
  change Fc.natDegree ≤ 3 * N - 2 * S
  dsimp only [Fc]
  rw [hFc]
  compute_degree
  omega

/-- The I4 identity at degree `V=deg d` forces
`F.coeff V + (3/2) gamma d.coeff V = 0`. -/
theorem fiveToSix_nextTwo_gammaWall_F_top_identity68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2 * S) (hwall : 4 * N - 3 * S = 2) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let V := 5 * N - 3 * S
    F.coeff V + (3 / 2 * gamma : k) * d.coeff V = 0 := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hEq : 4 * N = 3 * S + 2 := by omega
  have hgt4 : 5 * N < 4 * S := by omega
  have harith := fiveToSix_nextTwo_gammaWall_degree_arith68 N S hN hEq hgt4
  have hFcdeg := fiveToSix_nextTwo_gammaWall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hDltV : D < V := by
    dsimp only [D, V]
    omega
  have hFcV : Fc.coeff V = 0 := by
    change Fc.natDegree ≤ 3 * N - 2 * S at hFcdeg
    exact coeff_eq_zero_of_natDegree_lt (hFcdeg.trans_lt hDltV)
  dsimp only [Fc] at hFcV
  change F.coeff V + (3 / 2 * gamma : k) * d.coeff V = 0
  simpa only [coeff_add, coeff_smul, smul_eq_mul] using hFcV

/-- If `gamma=0`, then `deg F ≤ deg B`.  If `gamma≠0`, then `deg F = deg d`.
Both cases are compatible with the cusp leading edges; neither is `False`. -/
theorem fiveToSix_nextTwo_gammaWall_F_degree_cases68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2 * S) (hwall : 4 * N - 3 * S = 2)
    (hprev : FiveToSixCuspZetaFirstB3EqualityNextContracted68
      gamma A B c d e N S) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    (gamma = 0 ∧ F.natDegree ≤ D) ∨
      (gamma ≠ 0 ∧ F.natDegree = V) := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hEq : 4 * N = 3 * S + 2 := by omega
  have hgt4 : 5 * N < 4 * S := by omega
  have harith := fiveToSix_nextTwo_gammaWall_degree_arith68 N S hN hEq hgt4
  have htop := fiveToSix_nextTwo_gammaWall_F_top_identity68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hFcdeg := fiveToSix_nextTwo_gammaWall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hdV : d.natDegree ≤ V := by
    dsimp only [V]
    convert hd using 1 <;> omega
  have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hcusp.2.2.1
  have hddeg : d.natDegree = V :=
    natDegree_eq_of_le_of_coeff_ne_zero hdV hdcoeff
  change (gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V)
  by_cases hgamma : gamma = 0
  · left
    refine ⟨hgamma, ?_⟩
    have hFeq : F = Fc := by
      dsimp only [Fc]
      rw [hgamma]
      simp only [mul_zero, zero_smul, add_zero]
    rw [hFeq]
    change Fc.natDegree ≤ 3 * N - 2 * S at hFcdeg
    exact hFcdeg
  · right
    refine ⟨hgamma, ?_⟩
    have h32 : (3 / 2 : k) ≠ 0 := by norm_num
    have hFcoeff : F.coeff V ≠ 0 := by
      intro hz
      have hsum : F.coeff V + (3 / 2 * gamma : k) * d.coeff V = 0 := by
        convert htop
      rw [hz, zero_add] at hsum
      have hne : (3 / 2 * gamma : k) * d.coeff V ≠ 0 :=
        mul_ne_zero (mul_ne_zero h32 hgamma) hdcoeff
      exact hne hsum
    have hi4 := fiveToSix_zetaFirst_endpoint_B3_I4_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs
      (by omega) (by omega)
    have hFraw := hi4.1
    dsimp only [FiveToSixCuspZetaFirstB3EqualityNextContracted68] at hprev
    have hFle' : F.natDegree ≤ 9 * N - 6 * S - 1 := by
      change (B * e + c * d - (1 / 9 : k) • B ^ 3).natDegree ≤
        9 * N - 2 * G - S - S - 1 at hFraw
      convert hFraw using 1 <;> omega
    have hidx : V + 1 = 9 * N - 6 * S - 1 := by
      dsimp only [V]; omega
    have hFle'' : F.natDegree ≤ V + 1 := by
      rw [hidx]; exact hFle'
    have hcoeff : F.coeff (V + 1) = 0 := by
      rw [hidx]; exact hprev.1
    have hdrop := natDegree_le_pred hFle'' hcoeff
    have hsub : V + 1 - 1 = V := by omega
    rw [hsub] at hdrop
    exact natDegree_eq_of_le_of_coeff_ne_zero hdrop hFcoeff

/-! ## Sparse `Fc` drop and the `J` gain -/

/-- The `Fc` block of loaded row two lies strictly below `K2=11N-6S-3`. -/
theorem fiveToSix_nextTwo_gammaWall_Fc_block_below_rowTwo68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2 * S) (hwall : 4 * N - 3 * S = 2) :
    let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
    let K2 := 11 * N - 6 * S - 3
    (-(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc)).coeff K2
      = 0 := by
  let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
  let D := 3 * N - 2 * S
  let K2 := 11 * N - 6 * S - 3
  change (-(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc)).coeff
    K2 = 0
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hEq : 4 * N = 3 * S + 2 := by omega
  have hgt4 : 5 * N < 4 * S := by omega
  have harith := fiveToSix_nextTwo_gammaWall_degree_arith68 N S hN hEq hgt4
  have hFc := fiveToSix_nextTwo_gammaWall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  change Fc.natDegree ≤ D at hFc
  have hDpos : 0 < D := by
    dsimp only [D]
    omega
  have hdF0 := natDegree_derivative_le Fc
  have hdF : (derivative Fc).natDegree < D := by omega
  have hdA0 := natDegree_derivative_le A
  have hdA : (derivative A).natDegree < 2 * N := by omega
  have hAF : (A * derivative Fc).natDegree < K2 := by
    dsimp only [D, K2] at hFc hdF ⊢
    compute_degree
    omega
  have hA'F : (derivative A * Fc).natDegree < K2 := by
    dsimp only [D, K2] at hFc hdA ⊢
    compute_degree
    omega
  have hP : (-(6 : k) • (A * derivative Fc) +
      (3 : k) • (derivative A * Fc)).natDegree < K2 := by
    compute_degree
    omega
  exact coeff_eq_zero_of_natDegree_lt hP

/-- Loaded row two on the NextTwo gamma wall is a pure `J'` coefficient. -/
theorem fiveToSix_nextTwo_gammaWall_J_second_lower68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2 * S) (hwall : 4 * N - 3 * S = 2)
    (hrow2 : FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowTwoScalar68
      gamma A B c d e N S) :
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    J.coeff (11 * N - 6 * S - 2) = 0 := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let K2 := 11 * N - 6 * S - 3
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hfactor := fiveToSix_nextPacket_wall_load_factor68
    (k := k) gamma A B c d e
  have hblock := fiveToSix_nextTwo_gammaWall_Fc_block_below_rowTwo68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  dsimp only [FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowTwoScalar68]
    at hrow2
  have hpoly2 : (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e -
        (9 * gamma : k) • (A * derivative d) +
        (9 / 2 * gamma : k) • (d * derivative A)).coeff K2 = 0 := by
    simpa only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul] using hrow2
  rw [hfactor.2] at hpoly2
  change (-(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc) +
      (6 : k) • derivative J).coeff K2 = 0 at hpoly2
  simp only [coeff_add, coeff_smul, smul_eq_mul, coeff_derivative] at hpoly2
  have hblock0 : (-(6 : k) * (A * derivative Fc).coeff K2 +
      (3 : k) * (derivative A * Fc).coeff K2) = 0 := by
    have hb := hblock
    dsimp only at hb
    simpa only [coeff_add, coeff_smul, smul_eq_mul] using hb
  have hJprod : J.coeff (K2 + 1) * ((K2 : k) + 1) = 0 := by
    linear_combination (1 / 6 : k) * hpoly2 - (1 / 6 : k) * hblock0
  have hcast : (K2 : k) + 1 = ((K2 + 1 : ℕ) : k) := by
    push_cast
    rfl
  have hK2c : ((K2 : k) + 1) ≠ 0 := by
    rw [hcast]
    exact_mod_cast (show K2 + 1 ≠ 0 by dsimp only [K2]; omega)
  have hJzero : J.coeff (K2 + 1) = 0 :=
    (mul_eq_zero.mp hJprod).resolve_right hK2c
  have hidx : K2 + 1 = 11 * N - 6 * S - 2 := by dsimp only [K2]; omega
  rw [hidx] at hJzero
  exact hJzero

/-! ## Contracted NextTwo gamma-wall packet -/

def FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallContracted68
    (gamma : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  Fc.natDegree ≤ 3 * N - 2 * S ∧ J.natDegree ≤ 11 * N - 6 * S - 3

def FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallPacket68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  G = 2 * S ∧ 4 * N - 3 * S = 2 ∧
    FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallContracted68
      gamma A B c d e N S

theorem fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_contracted68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2 * S) (hwall : 4 * N - 3 * S = 2)
    (hend : FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
      A B c d e N G S)
    (hprev : FiveToSixCuspZetaFirstB3EqualityNextContracted68
      gamma A B c d e N S)
    (hrows : FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowZeroScalar68
        gamma A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallRowTwoScalar68
        gamma A B c d e N S) :
    FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallContracted68
      gamma A B c d e N S := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let Q := B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)
  let J := Q - (3 : k) • (d * e)
  let T := 11 * N - 6 * S
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hFc := fiveToSix_nextTwo_gammaWall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hJsecond := fiveToSix_nextTwo_gammaWall_J_second_lower68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
    hrows.2
  have hQ : Q.natDegree ≤ T := by dsimp only [Q, T]; compute_degree; omega
  have hde : (d * e).natDegree ≤ T := by dsimp only [T]; compute_degree; omega
  have hJ : J.natDegree ≤ T := by dsimp only [J]; compute_degree; omega
  have hJtop : J.coeff T = 0 := by
    dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68,
      FixedReflectedJet68] at hend
    have ht0 : 2 * S - G = 0 := by omega
    have hb : 11 * N - 3 * G = T := by dsimp only [T]; omega
    rw [ht0, coeff_reflect, revAt_zero, hb] at hend
    have hdetop := coeff_mul_at_bounds68 d e (5 * N - G - S) (6 * N - G - S)
      hd he
    rw [show (5 * N - G - S) + (6 * N - G - S) = T by dsimp only [T]; omega]
      at hdetop
    dsimp only [J]
    simp only [coeff_sub, coeff_smul, smul_eq_mul]
    rw [hdetop]
    linear_combination hend
  have hJone : J.natDegree ≤ T - 1 := natDegree_le_pred hJ hJtop
  dsimp only [FiveToSixCuspZetaFirstB3EqualityNextContracted68] at hprev
  have hJtwo : J.natDegree ≤ T - 2 := natDegree_le_pred hJone hprev.2
  have hJdrop : J.natDegree ≤ T - 3 := natDegree_le_pred hJtwo hJsecond
  change Fc.natDegree ≤ 3 * N - 2 * S ∧ J.natDegree ≤ 11 * N - 6 * S - 3
  refine ⟨hFc, ?_⟩
  dsimp only [T] at hJdrop
  exact hJdrop

/-- The NextTwo gamma-d wall chamber reduces to the contracted `Fc`/`J`
bounds.  The two `S+2` source rows are consumed. -/
theorem fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hwall : 4 * N - 3 * S = 2) :
    FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S := by
  rcases hp with ⟨hnext, hsplit⟩
  rcases hnext with ⟨hGS, hcell, hprev⟩
  have hbase := hcell.1.1.1
  rcases hbase with ⟨hs, hBc, hGamma, q, hmuq, hqS, hprior, hminimal, hload,
    hi3, hi4, hend⟩
  rcases hsplit with hgammaWall | hepsWall | hordinary
  · rcases hprev with hwallOne | hordinaryPrev
    · exfalso
      omega
    · have hlit :=
        fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_literal_rows68
          alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS hwall
          hgammaWall.2.1 hgammaWall.2.2
      have hcontract :=
        fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_contracted68
          alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS hwall
          hend hordinaryPrev.2 hlit
      exact ⟨hGS, hwall, hcell, hcontract⟩
  · exact False.elim
      (fiveToSix_zetaFirst_B3_equality_nextTwo_epsilonWall_false68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        ⟨⟨hGS, hcell, hprev⟩, Or.inr (Or.inl hepsWall)⟩ hepsWall.1)
  · exfalso
    omega

/-! ## Chamber 5: exact I4 form on the constant-`Fce` wall -/

/-- Recover the support packet and B3-equality arithmetic from the landed
constant-`Fce` contraction. -/
theorem fiveToSix_constantFce_support_of_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S ∧
      G = 2 * S ∧ S < 4 * N - G := by
  rcases hp with ⟨hstop, hDT, hdrop⟩
  rcases hstop with ⟨hcur, ht, hstate, hclass, hrow0, hrow2⟩
  rcases hcur with ⟨hbase, hbaseDrop⟩
  rcases hbase with ⟨hterminal, hJold, hrowOld0, hrowOld2⟩
  rcases hterminal with ⟨hgamma, hY⟩
  rcases hgamma with ⟨hgammaStop, hcontract⟩
  rcases hgammaStop with ⟨hnext, ha, hjet, hgammaRow0, hgammaRow2⟩
  rcases hnext.1 with ⟨hGS, hcell, hprev⟩
  have hbase' := hcell.1.1.1
  rcases hbase' with ⟨hs, hBc, hGamma, q, hmuq, hqS, hprior, hminimal, hload,
    hi3, hi4, hend⟩
  exact ⟨hs, hGS, hGamma⟩

/-- Landed `Fce=0` rewrites as the exact polynomial `Fc = -(3/4)epsilon B`. -/
theorem fiveToSix_constantFce_wall_Fc_eq68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
    Fc = -(3 / 4 * epsilon : k) • B := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let Fce := Fc + (3 / 4 * epsilon : k) • B
  have hFce : Fce = 0 := by
    have hdrop := hp.2.2
    dsimp only at hdrop
    exact hdrop.1
  have hsum : Fc + (3 / 4 * epsilon : k) • B = 0 := by
    dsimp only [Fce] at hFce
    exact hFce
  have hneg : Fc = -((3 / 4 * epsilon : k) • B) :=
    add_eq_zero_iff_eq_neg.mp hsum
  dsimp only [Fc, F] at hneg
  rw [← neg_smul] at hneg
  dsimp only
  exact hneg

/-- Compensated I4 on the constant-`Fce` wall is the zero constant. -/
theorem fiveToSix_constantFce_wall_i4_zero68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
      (3 / 4 * epsilon : k) • B
    ∃ i4 : k, Fce = (3 / 8 : k) • C i4 ∧ i4 = 0 := by
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
    (3 / 4 * epsilon : k) • B
  have hs := (fiveToSix_constantFce_support_of_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hp).1
  rcases fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i4, hpoly⟩
  have hFceEq : Fce = (3 / 8 : k) • C i4 := by
    dsimp only [Fce]
    linear_combination hpoly
  have hFce0 : Fce = 0 := by
    have hdrop := hp.2.2
    dsimp only at hdrop
    exact hdrop.1
  have hC : (3 / 8 : k) • C i4 = 0 := by
    rw [← hFceEq, hFce0]
  have h38 : (3 / 8 : k) ≠ 0 := by norm_num
  have hC0 : C i4 = 0 := (smul_eq_zero.mp hC).resolve_left h38
  have hi4 : i4 = 0 := by
    have hC00 : C i4 = C 0 := by rw [hC0, C_0]
    exact C_inj.mp hC00
  exact ⟨i4, hFceEq, hi4⟩

/-- Two-case `F` profile on the constant-`Fce` wall. -/
theorem fiveToSix_constantFce_wall_F_degree_cases68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    (gamma = 0 ∧ F.natDegree ≤ D) ∨
      (gamma ≠ 0 ∧ F.natDegree = V) := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  have hsupp := fiveToSix_constantFce_support_of_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hp
  have hs := hsupp.1
  have heq := hsupp.2.1
  have hp' := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp'
  rcases hp' with ⟨hS, hSR, hd, hedeg, hpC, hrest⟩
  rcases hpC with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hFc := fiveToSix_constantFce_wall_Fc_eq68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hp
  have hdV : d.natDegree ≤ V := by
    dsimp only [V]
    convert hd using 1 <;> omega
  have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hcusp.2.2.1
  have hDltV : D < V := by
    dsimp only [D, V]
    omega
  have hFcdeg : Fc.natDegree ≤ D := by
    dsimp only [Fc]
    rw [hFc]
    compute_degree
    omega
  have hFcV : Fc.coeff V = 0 :=
    coeff_eq_zero_of_natDegree_lt (hFcdeg.trans_lt hDltV)
  have htop : F.coeff V + (3 / 2 * gamma : k) * d.coeff V = 0 := by
    dsimp only [Fc] at hFcV
    simpa only [coeff_add, coeff_smul, smul_eq_mul] using hFcV
  change (gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V)
  by_cases hgamma : gamma = 0
  · left
    refine ⟨hgamma, ?_⟩
    have hFeq : F = Fc := by
      dsimp only [Fc]
      rw [hgamma]
      simp only [mul_zero, zero_smul, add_zero]
    rw [hFeq]
    exact hFcdeg
  · right
    refine ⟨hgamma, ?_⟩
    have h32 : (3 / 2 : k) ≠ 0 := by norm_num
    have hFcoeff : F.coeff V ≠ 0 := by
      intro hz
      rw [hz, zero_add] at htop
      have hne : (3 / 2 * gamma : k) * d.coeff V ≠ 0 :=
        mul_ne_zero (mul_ne_zero h32 hgamma) hdcoeff
      exact hne htop
    have hFform : F = -(3 / 4 * epsilon : k) • B - (3 / 2 * gamma : k) • d := by
      have h1 : F = Fc - (3 / 2 * gamma : k) • d := by
        dsimp only [Fc]
        exact (add_sub_cancel_right F ((3 / 2 * gamma : k) • d)).symm
      have hFc' : Fc = -(3 / 4 * epsilon : k) • B := by
        dsimp only [Fc]
        exact hFc
      rw [h1, hFc']
    have hFle : F.natDegree ≤ V := by
      rw [hFform]
      compute_degree
      omega
    exact natDegree_eq_of_le_of_coeff_ne_zero hFle hFcoeff

/-- Two-case `Fc` profile on the constant-`Fce` wall. -/
theorem fiveToSix_constantFce_wall_epsilon_degree_cases68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
    let D := 3 * N - 2 * S
    (epsilon = 0 ∧ Fc = 0) ∨
      (epsilon ≠ 0 ∧ Fc.natDegree = D) := by
  let Fc := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d
  let D := 3 * N - 2 * S
  have hsupp := fiveToSix_constantFce_support_of_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hp
  have hs := hsupp.1
  have heq := hsupp.2.1
  have hp' := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp'
  rcases hp' with ⟨hS, hSR, hd, hedeg, hpC, hrest⟩
  rcases hpC with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hFc := fiveToSix_constantFce_wall_Fc_eq68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hp
  have hDidx : D = 3 * N - G := by dsimp only [D]; omega
  have hBcoeff : B.coeff D ≠ 0 := by rw [hDidx]; exact hcusp.1
  have hBle : B.natDegree ≤ D := by
    dsimp only [D]
    convert hB using 1 <;> omega
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hBle hBcoeff
  change (epsilon = 0 ∧ Fc = 0) ∨ (epsilon ≠ 0 ∧ Fc.natDegree = D)
  by_cases heps : epsilon = 0
  · left
    refine ⟨heps, ?_⟩
    dsimp only [Fc]
    rw [hFc, heps]
    simp only [mul_zero, zero_smul, neg_zero]
  · right
    refine ⟨heps, ?_⟩
    have h34 : (3 / 4 : k) ≠ 0 := by norm_num
    have hFccoeff : Fc.coeff D ≠ 0 := by
      dsimp only [Fc]
      rw [hFc]
      simp only [coeff_smul, coeff_neg, smul_eq_mul, neg_mul]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h34 heps) hBcoeff)
    have hFcle : Fc.natDegree ≤ D := by
      dsimp only [Fc]
      rw [hFc]
      compute_degree
      omega
    exact natDegree_eq_of_le_of_coeff_ne_zero hFcle hFccoeff

def FiveToSixCuspZetaFirstB3EqualityConstantFceWallPacket68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∧
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    Fc = -(3 / 4 * epsilon : k) • B ∧
      ((gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V)) ∧
      ((epsilon = 0 ∧ Fc = 0) ∨ (epsilon ≠ 0 ∧ Fc.natDegree = D))

theorem fiveToSix_zetaFirst_B3_equality_constantFce_wall_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstB3EqualityConstantFceWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hp, ?_, ?_, ?_⟩
  · exact fiveToSix_constantFce_wall_Fc_eq68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hp
  · exact fiveToSix_constantFce_wall_F_degree_cases68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hp
  · exact fiveToSix_constantFce_wall_epsilon_degree_cases68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hp

/-! ## Source-facing assembly -/

/-- Source-facing residual after consuming chambers 4 and 5.  The
`4N-3S=1` NextPacket wall is cited from the sibling sharpening; the
`3N-2S=1` NextTwo wall is deleted as `False`. -/
theorem fiveToSix_zetaFirst_endpoint_B3_equality_nextTwo_constantFce_or_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hj : FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    4 * N - G ≤ S ∨
      FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S ∨
      FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallPacket68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S ∨
      FiveToSixCuspZetaFirstB3EqualityConstantFceWallPacket68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S ∨
      FiveToSixCuspZetaFirstB3EqualitySupportWallResidualPacket68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S := by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_support68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma | hwallOne | hsmall | hconstant | hsupport
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl
      (fiveToSix_zetaFirst_B3_equality_next_wall_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hwallOne.1
        hwallOne.2))
  · rcases hsmall with ⟨hnextTwo, hwalls⟩
    rcases hwalls with hgamma | heps
    · exact Or.inr (Or.inr (Or.inl
        (fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_packet68
          alpha gamma epsilon zeta eta terminal A B c d e N G S hnextTwo
          hgamma)))
    · exact False.elim
        (fiveToSix_zetaFirst_B3_equality_nextTwo_epsilonWall_false68
          alpha gamma epsilon zeta eta terminal A B c d e N G S hnextTwo
          heps)
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (fiveToSix_zetaFirst_B3_equality_constantFce_wall_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hconstant))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hsupport)))

#print axioms fiveToSix_nextTwo_epsilonWall_arith_false68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_epsilonWall_false68
#print axioms fiveToSix_nextTwo_gammaWall_degree_arith68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_literal_rows68
#print axioms fiveToSix_nextTwo_gammaWall_Fc_degree68
#print axioms fiveToSix_nextTwo_gammaWall_F_top_identity68
#print axioms fiveToSix_nextTwo_gammaWall_F_degree_cases68
#print axioms fiveToSix_nextTwo_gammaWall_Fc_block_below_rowTwo68
#print axioms fiveToSix_nextTwo_gammaWall_J_second_lower68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_contracted68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_packet68
#print axioms fiveToSix_constantFce_support_of_packet68
#print axioms fiveToSix_constantFce_wall_Fc_eq68
#print axioms fiveToSix_constantFce_wall_i4_zero68
#print axioms fiveToSix_constantFce_wall_F_degree_cases68
#print axioms fiveToSix_constantFce_wall_epsilon_degree_cases68
#print axioms fiveToSix_zetaFirst_B3_equality_constantFce_wall_packet68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_nextTwo_constantFce_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextTwoAndConstantFceWalls68

end Max11DegreeRoutes
