import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeadingScratch

/-! # Off-wall support `0<q`

Chamber 2 of `Grok68TerminalClosurePropagationScratch` is the residual of
`fiveToSix_zetaFirst_B3_equality_support_i4_split68` /
`fiveToSix_zetaFirst_B3_equality_support_leading_packet68` on `0<q`.
The wall `9N=7S` is already closed on the zero-`Fce` branch and reduced on
vanishing-`A`; this file does not touch that wall.

The compensated I4 identity is an equality of polynomials
`Fce=(3/8) C i4`.  Off the wall the leading `B` is exact of degree `D`,
and the chamber arithmetic `3S<4N` puts `deg(B^3)=3D` strictly above
`deg d` and `deg B`.  Degree comparison therefore forces
`deg(Be+cd)=3D` with leading coefficient `(1/9) B_D^3`, consuming the
entire stack of `S` I4 product coefficients above `3D` (the split had
used only the top).  The companion I3 identity likewise forces
`deg Rce ≤ 2D`.  The leading packet's quadratic resultant drops
`4 B^2 c+9 d^2` one degree from `10N-6S`.  The two-case profile of
`F:=Be+cd-(1/9)B^3` is recorded: `gamma=0` implies `deg F ≤ D`, while
`gamma≠0` implies `deg F=V`.  Neither case contradicts the known
leading edges of `A,B,c,d,e`.

This is not a closure, and `q` is not forced into a bounded set.

Exact degree bookkeeping: `deg A=2N`, `deg B=D`, `deg c=Cc`, `deg d=V`,
`deg e=E` remain exact; `deg(Be+cd)` drops from `9N-5S` to `3D=9N-6S`;
`deg Rce` drops from `10N-5S` to at most `2D`; `deg(4 B^2 c+9 d^2)`
drops from `10N-6S` to at most `10N-6S-1`; `deg J ≤ 11N-7S` is the
already-retained support state.

Next unused row: the first subleading discriminant coefficient at
`8N-4S-1` (the `A_(2N-1)` jet), equally `J.coeff (11N-7S)`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportOffWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic `0<9N-7S` -/

/-- Degree dictionary off the wall: `3D>V>D>0`, so `B^3` strictly
dominates the linear `Fce` summands. -/
theorem fiveToSix_offWall_degree_arith68
    (N S : ℕ) (hN : 0 < N) (hS : 0 < S)
    (hgt : 5 * N < 4 * S) (hle : 4 * S ≤ 6 * N) (hGamma : 3 * S < 4 * N)
    (hq : 0 < 9 * N - 7 * S) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    0 < D ∧ 0 < Cc ∧ 0 < V ∧ 0 < E ∧ D < V ∧ V < 3 * D ∧
      7 * S < 9 * N ∧ 2 * D + Cc = 2 * V ∧ 2 * V = 10 * N - 6 * S ∧
      D + E = 9 * N - 5 * S ∧ 3 * D = 9 * N - 6 * S ∧
      2 * N + D + V = 10 * N - 5 * S ∧ Cc + E = 10 * N - 5 * S ∧
      2 * D + Cc = 10 * N - 6 * S ∧ 1 ≤ 10 * N - 6 * S := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  change 0 < D ∧ 0 < Cc ∧ 0 < V ∧ 0 < E ∧ D < V ∧ V < 3 * D ∧
    7 * S < 9 * N ∧ 2 * D + Cc = 2 * V ∧ 2 * V = 10 * N - 6 * S ∧
    D + E = 9 * N - 5 * S ∧ 3 * D = 9 * N - 6 * S ∧
    2 * N + D + V = 10 * N - 5 * S ∧ Cc + E = 10 * N - 5 * S ∧
    2 * D + Cc = 10 * N - 6 * S ∧ 1 ≤ 10 * N - 6 * S
  dsimp only [D, Cc, V, E]
  omega

/-! ## Source exact degrees -/

/-- Off-wall the five cusp edges are exact, and `3D>V>D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    G = 2 * S ∧ 0 < N ∧ 0 < S ∧ 5 * N < 4 * S ∧ 4 * S ≤ 6 * N ∧
      3 * S < 4 * N ∧ 0 < D ∧ D < V ∧ V < 3 * D ∧
      A.natDegree = 2 * N ∧ B.natDegree = D ∧ c.natDegree = Cc ∧
      d.natDegree = V ∧ e.natDegree = E ∧
      A.coeff (2 * N) * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 ∧
      FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  change G = 2 * S ∧ 0 < N ∧ 0 < S ∧ 5 * N < 4 * S ∧ 4 * S ≤ 6 * N ∧
    3 * S < 4 * N ∧ 0 < D ∧ D < V ∧ V < 3 * D ∧
    A.natDegree = 2 * N ∧ B.natDegree = D ∧ c.natDegree = Cc ∧
    d.natDegree = V ∧ e.natDegree = E ∧
    A.coeff (2 * N) * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 ∧
    FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma0, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hgt' : 5 * N < 4 * S := by omega
  have hle' : 4 * S ≤ 6 * N := by omega
  have hGamma : 3 * S < 4 * N := by omega
  dsimp only [D, Cc, V, E]
  have hDpos : 0 < D := by omega
  have hDltV : D < V := by omega
  have hVlt3D : V < 3 * D := by omega
  have hA' : A.natDegree ≤ 2 * N := hA
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hd' : d.natDegree ≤ V := by
    dsimp only [V]; rw [hGS] at hd; omega
  have he' : e.natDegree ≤ E := by
    dsimp only [E]; rw [hGS] at he; omega
  have ha0 : A.coeff (2 * N) ≠ 0 := hatop
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hc0 : c.coeff Cc ≠ 0 := by simpa [Cc, hGS] using hctop
  have hd0' : d.coeff V ≠ 0 := by
    have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
    rw [hdidx]; exact hdtop
  have he0' : e.coeff E ≠ 0 := by
    have heidx : E = 6 * N - G - S := by dsimp only [E]; omega
    rw [heidx]; exact hetop
  have hcuspEq' :
      A.coeff (2 * N) * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    simpa [D, Cc, hGS] using hcuspEq
  exact ⟨hGS, hN, hS, hgt', hle', hGamma, hDpos, hDltV, hVlt3D,
    natDegree_eq_of_le_of_coeff_ne_zero hA' ha0,
    natDegree_eq_of_le_of_coeff_ne_zero hB' hb0,
    natDegree_eq_of_le_of_coeff_ne_zero hc' hc0,
    natDegree_eq_of_le_of_coeff_ne_zero hd' hd0',
    natDegree_eq_of_le_of_coeff_ne_zero he' he0',
    hcuspEq', hsource⟩

/-! ## Exact identities -/

/-- Compensated I4 is a constant polynomial, independently of `q`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_Fce_constant68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    ∃ i4 : k, Fce = (3 / 8 : k) • C i4 := by
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  rcases fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hsource with
      ⟨i4, hi4⟩
  refine ⟨i4, ?_⟩
  change ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B =
    (3 / 8 : k) • C i4
  linear_combination hi4

/-- Compensated I3 is `(3/4) gamma B^2` plus a constant. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_Rce_identity68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let R := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rce := R + (9 / 2 * gamma : k) • e + (9 / 4 * epsilon : k) • c
    ∃ i3 : k, Rce = (3 / 4 * gamma : k) • B ^ 2 + (9 / 8 : k) • C i3 := by
  let R := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
    (3 / 2 : k) • d ^ 2
  let Rce := R + (9 / 2 * gamma : k) • e + (9 / 4 * epsilon : k) • c
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  rcases fiveToSix_zetaFirst_B3_compensatedI3_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hsource with
      ⟨i3, hi3⟩
  refine ⟨i3, ?_⟩
  change ((-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2) + (9 / 2 * gamma : k) • e +
      (9 / 4 * epsilon : k) • c =
    (3 / 4 * gamma : k) • B ^ 2 + (9 / 8 : k) • C i3
  linear_combination hi3

/-- The leading packet on `0<q`, including the quadratic resultant. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_leading68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    4 * A.coeff (2 * N) * B.coeff D ^ 3 + 27 * d.coeff V * e.coeff E = 0 ∧
      A.coeff (2 * N) * B.coeff D ^ 2 * d.coeff V -
        (3 : k) * B.coeff D * c.coeff Cc * e.coeff E = 0 ∧
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V = 0 ∧
      4 * B.coeff D ^ 2 * c.coeff Cc + 9 * d.coeff V ^ 2 = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  have hpack := fiveToSix_zetaFirst_B3_equality_support_leading_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  dsimp only [D, Cc, V, E] at hpack ⊢
  rcases hpack with ⟨hJtop, hsplit⟩
  rcases hsplit with hq0 | hpos
  · exact False.elim ((Nat.ne_of_gt hq) hq0)
  · exact ⟨hJtop, hpos.2.1, hpos.2.2.1, hpos.2.2.2⟩

/-! ## Degree comparison -/

/-- `Be+cd` has exact degree `3D` and leading coefficient `(1/9) B_D^3`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_H_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let D := 3 * N - 2 * S
    (B * e + c * d).natDegree = 3 * D ∧
      (B * e + c * d).coeff (3 * D) = (1 / 9 : k) * B.coeff D ^ 3 := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let H := B * e + c * d
  change H.natDegree = 3 * D ∧
    H.coeff (3 * D) = (1 / 9 : k) * B.coeff D ^ 3
  have hdeg :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  rcases hdeg with ⟨_, _, _, _, _, _, hDpos, _, hVlt, _, hBdeg, _, hddeg, _, _, _⟩
  have hBdeg : B.natDegree = D := by dsimp only [D]; exact hBdeg
  have hddeg : d.natDegree = V := by dsimp only [V]; exact hddeg
  have hVlt : V < 3 * D := by dsimp only [D, V]; exact hVlt
  have hDpos : 0 < D := by dsimp only [D]; exact hDpos
  have hb0 : B.coeff D ≠ 0 := by
    intro h0
    have hlead : B.leadingCoeff = 0 := by rw [leadingCoeff, hBdeg, h0]
    have hB0 : B = 0 := leadingCoeff_eq_zero.mp hlead
    have : D = 0 := by rw [← hBdeg, hB0, natDegree_zero]
    omega
  rcases fiveToSix_zetaFirst_B3_equality_support_offWall_Fce_constant68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq with
      ⟨i4, hFce⟩
  have hH :
      H = (1 / 9 : k) • B ^ 3 - (3 / 4 * epsilon : k) • B -
        (3 / 2 * gamma : k) • d + (3 / 8 : k) • C i4 := by
    have hFce' :
        ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
          (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B =
        (3 / 8 : k) • C i4 := hFce
    dsimp only [H]
    linear_combination hFce'
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 := by
    simpa only [Nat.mul_comm] using coeff_pow_at_bound68 B D 3 hB'
  have hBhigh : B.coeff (3 * D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB'.trans_lt (by omega))
  have hdhigh : d.coeff (3 * D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd'.trans_lt hVlt)
  have hC : ((3 / 8 : k) • C i4).coeff (3 * D) = 0 := by
    rw [coeff_smul, coeff_C]
    split_ifs with hCeq
    · omega
    · simp only [smul_zero]
  have hcoeff : H.coeff (3 * D) = (1 / 9 : k) * B.coeff D ^ 3 := by
    rw [hH]
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hB3, hBhigh,
      hdhigh, hC, mul_zero, sub_zero, add_zero]
  have hle : H.natDegree ≤ 3 * D := by
    rw [hH]
    compute_degree
    omega
  have hne : H.coeff (3 * D) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hb0)
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero hle hne, hcoeff⟩

/-- If `gamma=0` then `deg F ≤ D`; if `gamma≠0` then `deg F = V`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_F_degree_cases68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    (gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V) := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fce := F + (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  change (gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V)
  have hdeg :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  rcases hdeg with
    ⟨_, _, _, _, _, _, _, hDltV, _, _, hBdeg, _, hddeg, _, _, _⟩
  have hBdeg : B.natDegree = D := by dsimp only [D]; exact hBdeg
  have hddeg : d.natDegree = V := by dsimp only [V]; exact hddeg
  have hDltV : D < V := by dsimp only [D, V]; exact hDltV
  have hVpos : 0 < V := by dsimp only [V]; omega
  have hd0 : d.coeff V ≠ 0 := by
    intro h0
    have hlead : d.leadingCoeff = 0 := by rw [leadingCoeff, hddeg, h0]
    have hd00 : d = 0 := leadingCoeff_eq_zero.mp hlead
    have : V = 0 := by rw [← hddeg, hd00, natDegree_zero]
    omega
  rcases fiveToSix_zetaFirst_B3_equality_support_offWall_Fce_constant68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq with
      ⟨i4, hFce⟩
  have hFeq :
      F = (3 / 8 : k) • C i4 - (3 / 2 * gamma : k) • d -
        (3 / 4 * epsilon : k) • B := by
    have hFce' :
        ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
          (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B =
        (3 / 8 : k) • C i4 := hFce
    dsimp only [F]
    linear_combination hFce'
  by_cases hgamma : gamma = 0
  · left
    refine ⟨hgamma, ?_⟩
    rw [hFeq, hgamma]
    simp only [mul_zero, zero_smul, sub_zero]
    compute_degree
    omega
  · right
    refine ⟨hgamma, ?_⟩
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
      coeff_eq_zero_of_natDegree_lt (hBdeg.le.trans_lt hDltV)
    have hFV : F.coeff V = -((3 / 2 * gamma : k) * d.coeff V) := by
      rw [hFeq]
      simp only [coeff_sub, coeff_smul, smul_eq_mul, hC, hBhigh, mul_zero,
        sub_zero, zero_sub]
    have h32 : (3 / 2 : k) ≠ 0 := by norm_num
    have hFcoeff : F.coeff V ≠ 0 := by
      rw [hFV]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h32 hgamma) hd0)
    exact natDegree_eq_of_le_of_coeff_ne_zero hFle hFcoeff

/-- Compensated I3 drops to degree at most `2D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_Rce_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let D := 3 * N - 2 * S
    let R := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rce := R + (9 / 2 * gamma : k) • e + (9 / 4 * epsilon : k) • c
    Rce.natDegree ≤ 2 * D := by
  let D := 3 * N - 2 * S
  let R := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
    (3 / 2 : k) • d ^ 2
  let Rce := R + (9 / 2 * gamma : k) • e + (9 / 4 * epsilon : k) • c
  have hdeg :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  rcases hdeg with ⟨_, _, _, _, _, _, _, _, _, _, hBdeg, _, _, _, _, _⟩
  have hBdeg : B.natDegree = D := by dsimp only [D]; exact hBdeg
  rcases fiveToSix_zetaFirst_B3_equality_support_offWall_Rce_identity68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq with
      ⟨i3, hRce⟩
  change Rce.natDegree ≤ 2 * D
  have hRce' : Rce = (3 / 4 * gamma : k) • B ^ 2 + (9 / 8 : k) • C i3 :=
    hRce
  rw [hRce']
  compute_degree
  omega

/-- The quadratic comparison polynomial drops at least one degree. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_W_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    ((4 : k) • (B ^ 2 * c) + (9 : k) • d ^ 2).natDegree ≤
      10 * N - 6 * S - 1 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let W := (4 : k) • (B ^ 2 * c) + (9 : k) • d ^ 2
  let K := 10 * N - 6 * S
  change W.natDegree ≤ K - 1
  have hdeg :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  rcases hdeg with
    ⟨_, hN, hS, hgt, hleN, hGamma, _, _, _, _, hBdeg, hcdeg, hddeg, _, _, _⟩
  have hBdeg : B.natDegree = D := by dsimp only [D]; exact hBdeg
  have hcdeg : c.natDegree = Cc := by dsimp only [Cc]; exact hcdeg
  have hddeg : d.natDegree = V := by dsimp only [V]; exact hddeg
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have hlead :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_leading68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hlead
  have hquad : 4 * B.coeff D ^ 2 * c.coeff Cc + 9 * d.coeff V ^ 2 = 0 := by
    dsimp only [D, Cc, V]; exact hlead.2.2.2
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hB2c : (B ^ 2 * c).coeff (2 * D + Cc) =
      B.coeff D ^ 2 * c.coeff Cc := by
    have hB2 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 :=
      coeff_pow_at_bound68 B D 2 hB'
    have h := coeff_mul_at_bounds68 (B ^ 2) c (2 * D) Cc hB2deg hc'
    rw [hB2] at h
    exact h
  have hd2 : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 :=
    coeff_pow_at_bound68 d V 2 hd'
  have hidx : 2 * D + Cc = K := by
    dsimp only [D, Cc, K]
    omega
  have hidx' : 2 * V = K := by
    dsimp only [V, K]
    omega
  have htop : W.coeff K = 0 := by
    dsimp only [W]
    simp only [coeff_add, coeff_smul, smul_eq_mul]
    have h1 : (B ^ 2 * c).coeff K = B.coeff D ^ 2 * c.coeff Cc := by
      rw [← hidx, hB2c]
    have h2 : (d ^ 2).coeff K = d.coeff V ^ 2 := by
      rw [← hidx', hd2]
    rw [h1, h2]
    linear_combination hquad
  have hWle : W.natDegree ≤ K := by
    dsimp only [W]
    compute_degree
    omega
  have hKpos : 1 ≤ K := by
    dsimp only [K]
    omega
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt' : K < n
  · exact coeff_eq_zero_of_natDegree_lt (hWle.trans_lt hgt')
  · have : n = K := by omega
    simpa [this] using htop

/-- The already-retained `J` state, written at the off-wall index. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_J_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    let p := 11 * N - 7 * S
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    J.natDegree ≤ p := by
  let D := 3 * N - 2 * S
  let p := 11 * N - 7 * S
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hloaded with ⟨hsupport, hrows⟩
  rcases hsupport with ⟨hstop, hTD⟩
  rcases hstop with ⟨hcur, ht, hstate, hclass, hraw0, hraw2⟩
  let w := 2 * D
  let T := S - w
  let t := min D T
  have htT : t = T := by dsimp only [t]; exact Nat.min_eq_right hTD
  have hstate' := hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
  have hjidx : 5 * N - 2 * S - (t - 1) - 1 = p := by
    dsimp only [D, w, T] at htT
    dsimp only [p]
    omega
  rw [hjidx] at hstate'
  dsimp only [J, p]
  exact hstate'.2

/-! ## Residual packet -/

/-- Residual after consuming the off-wall I4/I3 identities and the
leading quadratic.  Not a closure. -/
def FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let p := 11 * N - 7 * S
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fce := F + (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let R := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
    (3 / 2 : k) • d ^ 2
  let Rce := R + (9 / 2 * gamma : k) • e + (9 / 4 * epsilon : k) • c
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let W := (4 : k) • (B ^ 2 * c) + (9 : k) • d ^ 2
  0 < 9 * N - 7 * S ∧
    A.natDegree = 2 * N ∧ B.natDegree = D ∧ c.natDegree = Cc ∧
    d.natDegree = V ∧ e.natDegree = E ∧
    (B * e + c * d).natDegree = 3 * D ∧
    (B * e + c * d).coeff (3 * D) = (1 / 9 : k) * B.coeff D ^ 3 ∧
    ((gamma = 0 ∧ F.natDegree ≤ D) ∨ (gamma ≠ 0 ∧ F.natDegree = V)) ∧
    (∃ i4 : k, Fce = (3 / 8 : k) • C i4) ∧
    (∃ i3 : k, Rce = (3 / 4 * gamma : k) • B ^ 2 + (9 / 8 : k) • C i3) ∧
    Rce.natDegree ≤ 2 * D ∧
    W.natDegree ≤ 10 * N - 6 * S - 1 ∧
    J.natDegree ≤ p ∧
    4 * B.coeff D ^ 2 * c.coeff Cc + 9 * d.coeff V ^ 2 = 0

/-- Source-backed residual of chamber 2.  Not a closure. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68
      gamma epsilon A B c d e N S := by
  have hdeg :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hH :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_H_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hF :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_F_degree_cases68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hFce :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hRce :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_Rce_identity68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hRceDeg :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_Rce_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hW :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_W_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hJ :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_J_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hlead :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_leading68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  rcases hdeg with
    ⟨_, _, _, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg, hddeg, hedeg, _, _⟩
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68]
  exact ⟨hq, hAdeg, hBdeg, hcdeg, hddeg, hedeg, hH.1, hH.2, hF, hFce, hRce,
    hRceDeg, hW, hJ, hlead.2.2.2⟩

/-- Same residual from the support-loaded parent of the row-one packet. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68
      gamma epsilon A B c d e N S :=
  fiveToSix_zetaFirst_B3_equality_support_offWall68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    (fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs)
    hq

#print axioms fiveToSix_offWall_degree_arith68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_Fce_constant68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_Rce_identity68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_leading68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_H_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_F_degree_cases68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_Rce_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_W_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_J_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall68
#print axioms fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportOffWall68

end Max11DegreeRoutes
