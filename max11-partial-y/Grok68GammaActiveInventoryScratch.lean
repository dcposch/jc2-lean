import Grok68ScaleZeroExclusionAssemblyScratch

/-! # Inventory of the gamma-active `(6,8)` scale-zero endpoint cell

Untracked working note. No tracked file was edited.

`FiveToSixCuspZetaFirstGammaActiveResidual68` is the unique `(6,8)`
scale-zero endpoint packet that no previous scratch has attacked.  It is
the endpoint-cell residual on `4N-G≤S`, the branch retained by
`fiveToSix_zetaFirst_endpoint_B3_equality_or_gamma68` after the B3
stopping argument (`G<2S` and the three `G=2S` wall packets) has fired
on the complementary cell.  Closed neighbours, cited not re-proved:
`fiveToSix_zetaFirst_B3_strict_false68`,
`fiveToSix_zetaFirst_sparse_endpoint_false68`, and the three `G=2S`
wall packets of `Grok68B3EqualityWallPacketsFalseScratch.lean`.

CAS `derive_68_gamma_active_leadings.py` records the exact cusp edges
`deg A=2N`, `deg B=3N-G`, `deg c=4N-G`, `deg d=5N-G-S`, `deg e=6N-G-S`
and the four homogeneous leadings of `H=Be+cd`, `Q=Bc²-(1/9)AB³`, and
`Y=-2AB²c+3Ad²+2c³-9e²`.  The five-to-six window forces `S<7N-2G<G`,
so both `B³` and `γd` lie strictly below `H` at `9N-2G-S`.  Compensated
I4 therefore kills that top: the gamma-pair leading is `b e+c d=0`.
On the same edges `Q` has exact degree `11N-3G` with leading
`-(4/9)a b³≠0`.  The `G=2S` four-scalar system still generates `e⁴`,
but the gamma loads reach the one-form tops once `4N-G≤S`, so that
comparison is not available here.

This file consumes the gamma pair (the first unused source identity on
this cell) as the I4 coefficient at `9N-2G-S`.  It does not claim
`False`.  The next unused Keller row is loaded uniform row one at
`12N-2G-2S-1` (equally the first coefficient of `Y` against `A F'`).

Exact gain: the gamma-active packet is replaced by the named residual
below, with exact degrees, `H_(9N-2G-S)=0`, the `Q` leading, and the
two-case `F` profile.  Next unused row: loaded uniform row one at
`12N-2G-2S-1`.  Residual:
`FiveToSixCuspZetaFirstGammaActiveInventoryResidual68`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointGammaActiveInventory68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## Degree dictionary on `4N-G≤S` -/

/-- Exact comparisons used by every leading-jet extraction on a
gamma-active cell.  The support window `5N<2G≤6N` with `S<7N-2G`
already forces `S<G`, so `B³` and `d` both lie strictly below `H`. -/
theorem fiveToSix_gammaActive_degree_arith68
    (N G S : ℕ) (hN : 0 < N) (hgt : 5 * N < 2 * G) (hle : 2 * G ≤ 6 * N)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G) (hGamma : 4 * N - G ≤ S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let TH := 9 * N - 2 * G - S
    let TQ := 11 * N - 3 * G
    let TY0 := 12 * N - 3 * G
    let TY1 := 12 * N - 2 * G - 2 * S
    0 < D ∧ 0 < Cc ∧ 0 < V ∧ 0 < E ∧
      S < G ∧ D < V ∧ V < TH ∧ 3 * D < TH ∧
      D + E = TH ∧ Cc + V = TH ∧
      2 * N + 3 * D = TQ ∧ D + 2 * Cc = TQ ∧
      2 * N + 2 * D + Cc = TY0 ∧ 3 * Cc = TY0 ∧
      2 * N + 2 * V = TY1 ∧ 2 * E = TY1 ∧
      1 ≤ TH ∧ G < 3 * N ∧ S < 2 * N := by
  omega

/-! ## Source exact degrees -/

/-- Recover the support witness from the named gamma-active packet. -/
theorem fiveToSix_zetaFirst_support_of_gammaActive68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S :=
  fiveToSix_zetaFirst_support_of_endpoint_cells_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hgamma.1

/-- On every gamma-active cell the five cusp edges are exact. -/
theorem fiveToSix_zetaFirst_gammaActive_exact_degrees68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    0 < N ∧ 0 < S ∧ 5 * N < 2 * G ∧ 2 * G ≤ 6 * N ∧
      S < 7 * N - 2 * G ∧ 4 * N - G ≤ S ∧
      0 < D ∧ 0 < Cc ∧ 0 < V ∧ 0 < E ∧ S < G ∧ D < V ∧
      A.natDegree = 2 * N ∧ B.natDegree = D ∧ c.natDegree = Cc ∧
      d.natDegree = V ∧ e.natDegree = E ∧
      A.coeff (2 * N) ≠ 0 ∧ B.coeff D ≠ 0 ∧ c.coeff Cc ≠ 0 ∧
      d.coeff V ≠ 0 ∧ e.coeff E ≠ 0 ∧
      A.coeff (2 * N) * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 ∧
      FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  have hGamma := hgamma.2
  have hs :=
    fiveToSix_zetaFirst_support_of_gammaActive68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S hgamma
  have hp0 := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have harith :=
    fiveToSix_gammaActive_degree_arith68 N G S hN hgt hle hS hSR hGamma
  rcases harith with
    ⟨hDpos, hCpos, hVpos, hEpos, hSltG, hDltV, _, _, _, _, _, _, _, _, _, _,
      _, _, _⟩
  have hB' : B.natDegree ≤ D := by simpa [D] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc] using hc
  have hd' : d.natDegree ≤ V := by simpa [V] using hd
  have he' : e.natDegree ≤ E := by simpa [E] using he
  have hb0 : B.coeff D ≠ 0 := by dsimp only [D]; exact hBtop
  have hc0 : c.coeff Cc ≠ 0 := by dsimp only [Cc]; exact hctop
  have hd0' : d.coeff V ≠ 0 := by dsimp only [V]; exact hdtop
  have he0' : e.coeff E ≠ 0 := by dsimp only [E]; exact hetop
  have hcuspEq' :
      A.coeff (2 * N) * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    dsimp only [D, Cc]; exact hcuspEq
  exact ⟨hN, hS, hgt, hle, hSR, hGamma, hDpos, hCpos, hVpos, hEpos, hSltG,
    hDltV, natDegree_eq_of_le_of_coeff_ne_zero hA hatop,
    natDegree_eq_of_le_of_coeff_ne_zero hB' hb0,
    natDegree_eq_of_le_of_coeff_ne_zero hc' hc0,
    natDegree_eq_of_le_of_coeff_ne_zero hd' hd0',
    natDegree_eq_of_le_of_coeff_ne_zero he' he0', hatop, hb0, hc0, hd0',
    he0', hcuspEq', hs⟩

/-! ## Compensated I4 and the gamma-pair leading -/

/-- Compensated I4 is a constant, independently of the B3 cell. -/
theorem fiveToSix_zetaFirst_gammaActive_Fce_constant68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    ∃ i4 : k, Fce = (3 / 8 : k) • C i4 := by
  have hs :=
    fiveToSix_zetaFirst_support_of_gammaActive68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S hgamma
  rcases fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
      ⟨i4, hi4⟩
  refine ⟨i4, ?_⟩
  linear_combination hi4

/-- The gamma pair vanishes at the common top of `Be` and `cd`.  This is
the first unused source identity on the cell. -/
theorem fiveToSix_zetaFirst_gammaActive_H_top68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let TH := 9 * N - 2 * G - S
    let H := B * e + c * d
    H.coeff TH = 0 ∧
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V = 0 ∧
      H.natDegree ≤ TH - 1 := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let TH := 9 * N - 2 * G - S
  let H := B * e + c * d
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg,
      hddeg, hedeg, _, _, _, _, _, _, hs⟩
  have harith :=
    fiveToSix_gammaActive_degree_arith68 N G S hN hgt hle hS hSR hGamma
  rcases harith with
    ⟨_, _, _, _, _, _, _, _, hDE, hCV, _, _, _, _, _, _, _, _, _⟩
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have he' : e.natDegree ≤ E := hedeg.le
  rcases fiveToSix_zetaFirst_gammaActive_Fce_constant68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma with ⟨i4, hFce⟩
  have hH :
      H = (1 / 9 : k) • B ^ 3 - (3 / 4 * epsilon : k) • B -
        (3 / 2 * gamma : k) • d + (3 / 8 : k) • C i4 := by
    dsimp only [H]
    linear_combination hFce
  have hHle : H.natDegree ≤ TH - 1 := by
    rw [hH]
    compute_degree
    omega
  have hcoeff0 : H.coeff TH = 0 :=
    coeff_eq_zero_of_natDegree_lt (hHle.trans_lt (by omega))
  have hBe := coeff_mul_at_bounds68 B e D E hB' he'
  have hcd := coeff_mul_at_bounds68 c d Cc V hc' hd'
  have hsum : H.coeff TH =
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V := by
    have hBe' : (B * e).coeff TH = B.coeff D * e.coeff E := by
      dsimp only [TH, D, E] at hDE ⊢
      rw [← hDE, hBe]
    have hcd' : (c * d).coeff TH = c.coeff Cc * d.coeff V := by
      dsimp only [TH, Cc, V] at hCV ⊢
      rw [← hCV, hcd]
    dsimp only [H]
    rw [coeff_add, hBe', hcd']
  exact ⟨hcoeff0, hsum.symm.trans hcoeff0, hHle⟩

/-! ## `Q` leading scalar -/

/-- `Q=Bc²-(1/9)AB³` has exact degree `11N-3G` and leading
`-(4/9) A_(2N) B_D³`. -/
theorem fiveToSix_zetaFirst_gammaActive_Q_leading68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let TQ := 11 * N - 3 * G
    let Q := B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)
    Q.natDegree = TQ ∧
      Q.coeff TQ =
        (-4 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let TQ := 11 * N - 3 * G
  let Q := B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg,
      _, _, ha0, hb0, _, _, _, hcusp0, _⟩
  have harith :=
    fiveToSix_gammaActive_degree_arith68 N G S hN hgt hle hS hSR hGamma
  rcases harith with
    ⟨_, _, _, _, _, _, _, _, _, _, hAB3sum, hBc2sum, _, _, _, _, _, _, _⟩
  have hA' : A.natDegree ≤ 2 * N := hAdeg.le
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 2 * Cc := by
    compute_degree
    omega
  have hB3top : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 :=
    coeff_pow_at_bound68 B D 3 hB'
  have hc2top : (c ^ 2).coeff (2 * Cc) = c.coeff Cc ^ 2 :=
    coeff_pow_at_bound68 c Cc 2 hc'
  have hBc2 := coeff_mul_at_bounds68 B (c ^ 2) D (2 * Cc) hB' hc2deg
  have hAB3 :=
    coeff_mul_at_bounds68 A (B ^ 3) (2 * N) (3 * D) hA' hB3deg
  have hBc2top : (B * c ^ 2).coeff TQ = B.coeff D * c.coeff Cc ^ 2 := by
    have hidx : D + 2 * Cc = TQ := by
      dsimp only [D, Cc, TQ] at hBc2sum ⊢
      exact hBc2sum
    rw [← hidx, hBc2, hc2top]
  have hAB3top : (A * B ^ 3).coeff TQ =
      A.coeff (2 * N) * B.coeff D ^ 3 := by
    have hidx : 2 * N + 3 * D = TQ := by
      dsimp only [D, TQ] at hAB3sum ⊢
      exact hAB3sum
    rw [← hidx, hAB3, hB3top]
  have hQexp : Q.coeff TQ =
      B.coeff D * c.coeff Cc ^ 2 -
        (1 / 9 : k) * (A.coeff (2 * N) * B.coeff D ^ 3) := by
    dsimp only [Q]
    simp only [coeff_sub, coeff_smul, smul_eq_mul, hBc2top, hAB3top]
  have hbC :
      B.coeff D * c.coeff Cc ^ 2 +
        (1 / 3 : k) * (A.coeff (2 * N) * B.coeff D ^ 3) = 0 := by
    linear_combination (1 / 3 : k) * B.coeff D * hcusp0
  have hQlead' : Q.coeff TQ =
      (-4 / 9 : k) * (A.coeff (2 * N) * B.coeff D ^ 3) := by
    rw [hQexp, eq_neg_of_add_eq_zero_left hbC]
    ring
  have hQlead : Q.coeff TQ =
      (-4 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 := by
    convert hQlead' using 1
    ring
  have hQle : Q.natDegree ≤ TQ := by
    dsimp only [Q]
    compute_degree
    omega
  have hQne : Q.coeff TQ ≠ 0 := by
    rw [hQlead]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha0) (pow_ne_zero 3 hb0)
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero hQle hQne, hQlead⟩

/-! ## Two-case `F` profile -/

/-- If `gamma=0` then `deg F ≤ D`; if `gamma≠0` then `deg F = V`. -/
theorem fiveToSix_zetaFirst_gammaActive_F_degree_cases68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let D := 3 * N - G
    let V := 5 * N - G - S
    (gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V) := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let D := 3 * N - G
  let V := 5 * N - G - S
  change (gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V)
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, hDltV, _, hBdeg, _,
      hddeg, _, _, _, _, hd0, _, _, _⟩
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  rcases fiveToSix_zetaFirst_gammaActive_Fce_constant68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma with ⟨i4, hFce⟩
  have hFeq :
      F = (3 / 8 : k) • C i4 - (3 / 2 * gamma : k) • d -
        (3 / 4 * epsilon : k) • B := by
    dsimp only [F]
    linear_combination hFce
  by_cases hgamma0 : gamma = 0
  · left
    refine ⟨hgamma0, ?_⟩
    rw [hFeq, hgamma0]
    simp only [mul_zero, zero_smul, sub_zero]
    compute_degree
    omega
  · right
    refine ⟨hgamma0, ?_⟩
    have hFle : F.natDegree ≤ V := by
      rw [hFeq]
      compute_degree
      omega
    have hC : ((3 / 8 : k) • C i4).coeff V = 0 := by
      rw [coeff_smul, coeff_C]
      split_ifs with hCeq
      · omega
      · simp only [smul_zero]
    have hBhigh : B.coeff V = 0 :=
      coeff_eq_zero_of_natDegree_lt (hB'.trans_lt hDltV)
    have hFV : F.coeff V = -((3 / 2 * gamma : k) * d.coeff V) := by
      rw [hFeq]
      simp only [coeff_sub, coeff_smul, smul_eq_mul, hC, hBhigh, mul_zero,
        sub_zero, zero_sub]
    have h32 : (3 / 2 : k) ≠ 0 := by norm_num
    have hFcoeff : F.coeff V ≠ 0 := by
      rw [hFV]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h32 hgamma0) hd0)
    exact natDegree_eq_of_le_of_coeff_ne_zero hFle hFcoeff

/-! ## `Y` leading scalars -/

/-- On `G<2S` the homogeneous `Y` top is `AB²c` and `c³`. -/
theorem fiveToSix_zetaFirst_gammaActive_Y_leading_B3loaded68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : G < 2 * S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let TY0 := 12 * N - 3 * G
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff TY0 =
      -(2 : k) * A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc +
        (2 : k) * c.coeff Cc ^ 3 := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let TY0 := 12 * N - 3 * G
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg,
      hddeg, hedeg, _, _, _, _, _, _, _⟩
  have harith :=
    fiveToSix_gammaActive_degree_arith68 N G S hN hgt hle hS hSR hGamma
  rcases harith with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAB2csum, hc3sum, hAd2sum, he2sum,
      _, _, _⟩
  have hA' : A.natDegree ≤ 2 * N := hAdeg.le
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have he' : e.natDegree ≤ E := hedeg.le
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hd2deg : (d ^ 2).natDegree ≤ 2 * V := by
    compute_degree
    omega
  have he2deg : (e ^ 2).natDegree ≤ 2 * E := by
    compute_degree
    omega
  have hB2top : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 :=
    coeff_pow_at_bound68 B D 2 hB'
  have hc3top : (c ^ 3).coeff (3 * Cc) = c.coeff Cc ^ 3 :=
    coeff_pow_at_bound68 c Cc 3 hc'
  have hAB2c :=
    coeff_mul_mul_at_bounds68 A (B ^ 2) c (2 * N) (2 * D) Cc hA' hB2deg hc'
  have hAd2below : (A * d ^ 2).coeff TY0 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have : 2 * N + 2 * V < TY0 := by
      dsimp only [V, TY0]
      omega
    compute_degree
    omega
  have he2below : (e ^ 2).coeff TY0 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have : 2 * E < TY0 := by
      dsimp only [E, TY0]
      omega
    compute_degree
    omega
  have hAB2ctop : (A * B ^ 2 * c).coeff TY0 =
      A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc := by
    have hidx : 2 * N + 2 * D + Cc = TY0 := by
      dsimp only [D, Cc, TY0] at hAB2csum ⊢
      exact hAB2csum
    rw [← hidx, hAB2c, hB2top]
  have hc3top' : (c ^ 3).coeff TY0 = c.coeff Cc ^ 3 := by
    have hidx : 3 * Cc = TY0 := by
      dsimp only [Cc, TY0] at hc3sum ⊢
      exact hc3sum
    rw [← hidx, hc3top]
  have hYexp : Y.coeff TY0 =
      -(2 : k) * (A * B ^ 2 * c).coeff TY0 +
        (3 : k) * (A * d ^ 2).coeff TY0 +
        (2 : k) * (c ^ 3).coeff TY0 -
        (9 : k) * (e ^ 2).coeff TY0 := by
    dsimp only [Y]
    simp only [coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul]
  rw [hAB2ctop, hAd2below, hc3top', he2below] at hYexp
  convert hYexp using 1
  ring

/-- On `G>2S` the homogeneous `Y` top is `Ad²` and `e²`. -/
theorem fiveToSix_zetaFirst_gammaActive_Y_leading_B3absent68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : 2 * S < G) :
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let TY1 := 12 * N - 2 * G - 2 * S
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff TY1 =
      (3 : k) * A.coeff (2 * N) * d.coeff V ^ 2 -
        (9 : k) * e.coeff E ^ 2 := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let TY1 := 12 * N - 2 * G - 2 * S
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg,
      hddeg, hedeg, _, _, _, _, _, _, _⟩
  have harith :=
    fiveToSix_gammaActive_degree_arith68 N G S hN hgt hle hS hSR hGamma
  rcases harith with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hAd2sum, he2sum, _, _, _⟩
  have hA' : A.natDegree ≤ 2 * N := hAdeg.le
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have he' : e.natDegree ≤ E := hedeg.le
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hd2deg : (d ^ 2).natDegree ≤ 2 * V := by
    compute_degree
    omega
  have he2deg : (e ^ 2).natDegree ≤ 2 * E := by
    compute_degree
    omega
  have hd2top : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 :=
    coeff_pow_at_bound68 d V 2 hd'
  have he2top : (e ^ 2).coeff (2 * E) = e.coeff E ^ 2 :=
    coeff_pow_at_bound68 e E 2 he'
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2) (2 * N) (2 * V) hA' hd2deg
  have hAB2cbelow : (A * B ^ 2 * c).coeff TY1 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hc3below : (c ^ 3).coeff TY1 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hAd2top : (A * d ^ 2).coeff TY1 =
      A.coeff (2 * N) * d.coeff V ^ 2 := by
    have hidx : 2 * N + 2 * V = TY1 := by
      dsimp only [V, TY1] at hAd2sum ⊢
      exact hAd2sum
    rw [← hidx, hAd2, hd2top]
  have he2top' : (e ^ 2).coeff TY1 = e.coeff E ^ 2 := by
    have hidx : 2 * E = TY1 := by
      dsimp only [E, TY1] at he2sum ⊢
      exact he2sum
    rw [← hidx, he2top]
  have hYexp : Y.coeff TY1 =
      -(2 : k) * (A * B ^ 2 * c).coeff TY1 +
        (3 : k) * (A * d ^ 2).coeff TY1 +
        (2 : k) * (c ^ 3).coeff TY1 -
        (9 : k) * (e ^ 2).coeff TY1 := by
    dsimp only [Y]
    simp only [coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul]
  rw [hAB2cbelow, hAd2top, hc3below, he2top'] at hYexp
  convert hYexp using 1
  ring

/-- On `G=2S` the four homogeneous `Y` edges share the top `12N-6S`. -/
theorem fiveToSix_zetaFirst_gammaActive_Y_leading_G2S68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hGS : G = 2 * S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let TY := 12 * N - 6 * S
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff TY =
      -(2 : k) * A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc +
        (3 : k) * A.coeff (2 * N) * d.coeff V ^ 2 +
        (2 : k) * c.coeff Cc ^ 3 - (9 : k) * e.coeff E ^ 2 := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let TY := 12 * N - 6 * S
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg,
      hddeg, hedeg, _, _, _, _, _, _, _⟩
  have harith :=
    fiveToSix_gammaActive_degree_arith68 N G S hN hgt hle hS hSR hGamma
  rcases harith with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAB2csum, hc3sum, hAd2sum, he2sum,
      _, _, _⟩
  have hA' : A.natDegree ≤ 2 * N := hAdeg.le
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have he' : e.natDegree ≤ E := hedeg.le
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hd2deg : (d ^ 2).natDegree ≤ 2 * V := by
    compute_degree
    omega
  have he2deg : (e ^ 2).natDegree ≤ 2 * E := by
    compute_degree
    omega
  have hB2top : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 :=
    coeff_pow_at_bound68 B D 2 hB'
  have hd2top : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 :=
    coeff_pow_at_bound68 d V 2 hd'
  have hc3top : (c ^ 3).coeff (3 * Cc) = c.coeff Cc ^ 3 :=
    coeff_pow_at_bound68 c Cc 3 hc'
  have he2top : (e ^ 2).coeff (2 * E) = e.coeff E ^ 2 :=
    coeff_pow_at_bound68 e E 2 he'
  have hAB2c :=
    coeff_mul_mul_at_bounds68 A (B ^ 2) c (2 * N) (2 * D) Cc hA' hB2deg hc'
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2) (2 * N) (2 * V) hA' hd2deg
  have hAB2ctop : (A * B ^ 2 * c).coeff TY =
      A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc := by
    have hidx : 2 * N + 2 * D + Cc = TY := by
      dsimp only [D, Cc, TY]; omega
    rw [← hidx, hAB2c, hB2top]
  have hAd2top : (A * d ^ 2).coeff TY =
      A.coeff (2 * N) * d.coeff V ^ 2 := by
    have hidx : 2 * N + 2 * V = TY := by
      dsimp only [V, TY]; omega
    rw [← hidx, hAd2, hd2top]
  have hc3top' : (c ^ 3).coeff TY = c.coeff Cc ^ 3 := by
    have hidx : 3 * Cc = TY := by
      dsimp only [Cc, TY]; omega
    rw [← hidx, hc3top]
  have he2top' : (e ^ 2).coeff TY = e.coeff E ^ 2 := by
    have hidx : 2 * E = TY := by
      dsimp only [E, TY]; omega
    rw [← hidx, he2top]
  have hYexp : Y.coeff TY =
      -(2 : k) * (A * B ^ 2 * c).coeff TY +
        (3 : k) * (A * d ^ 2).coeff TY +
        (2 : k) * (c ^ 3).coeff TY -
        (9 : k) * (e ^ 2).coeff TY := by
    dsimp only [Y]
    simp only [coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul]
  rw [hAB2ctop, hAd2top, hc3top', he2top'] at hYexp
  convert hYexp using 1
  ring

/-! ## Residual packet -/

/-- Residual after consuming the gamma-pair I4 leading.  Not a closure. -/
def FiveToSixCuspZetaFirstGammaActiveInventoryResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let TH := 9 * N - 2 * G - S
  let TQ := 11 * N - 3 * G
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fce := F + (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let Q := B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)
  FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    A.natDegree = 2 * N ∧ B.natDegree = D ∧ c.natDegree = Cc ∧
    d.natDegree = V ∧ e.natDegree = E ∧
    (B * e + c * d).coeff TH = 0 ∧
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V = 0 ∧
      (B * e + c * d).natDegree ≤ TH - 1 ∧
    Q.natDegree = TQ ∧
      Q.coeff TQ = (-4 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 ∧
    ((gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V)) ∧
    (∃ i4 : k, Fce = (3 / 8 : k) • C i4)

/-- Source-backed inventory of the gamma-active packet.  Not a closure. -/
theorem fiveToSix_zetaFirst_gammaActive_inventory68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstGammaActiveInventoryResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S := by
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  have hH :=
    fiveToSix_zetaFirst_gammaActive_H_top68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S hgamma
  have hQ :=
    fiveToSix_zetaFirst_gammaActive_Q_leading68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S hgamma
  have hF :=
    fiveToSix_zetaFirst_gammaActive_F_degree_cases68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  have hFce :=
    fiveToSix_zetaFirst_gammaActive_Fce_constant68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg, hddeg, hedeg,
      _, _, _, _, _, _, _⟩
  dsimp only [FiveToSixCuspZetaFirstGammaActiveInventoryResidual68]
  exact ⟨hgamma, hAdeg, hBdeg, hcdeg, hddeg, hedeg, hH.1, hH.2.1, hH.2.2,
    hQ.1, hQ.2, hF, hFce⟩

#print axioms fiveToSix_gammaActive_degree_arith68
#print axioms fiveToSix_zetaFirst_support_of_gammaActive68
#print axioms fiveToSix_zetaFirst_gammaActive_exact_degrees68
#print axioms fiveToSix_zetaFirst_gammaActive_Fce_constant68
#print axioms fiveToSix_zetaFirst_gammaActive_H_top68
#print axioms fiveToSix_zetaFirst_gammaActive_Q_leading68
#print axioms fiveToSix_zetaFirst_gammaActive_F_degree_cases68
#print axioms fiveToSix_zetaFirst_gammaActive_Y_leading_B3loaded68
#print axioms fiveToSix_zetaFirst_gammaActive_Y_leading_B3absent68
#print axioms fiveToSix_zetaFirst_gammaActive_Y_leading_G2S68
#print axioms fiveToSix_zetaFirst_gammaActive_inventory68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointGammaActiveInventory68

end Max11DegreeRoutes
