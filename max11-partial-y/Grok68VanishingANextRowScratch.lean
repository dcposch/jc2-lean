import Grok68VanishingARemainderClosureScratch

/-! # Charged-integral top of `H` on the `q=0` vanishing-A remainders

Matching through `D` and the charged `Δ`/`H` profiles are already landed
(`Grok68VanishingARemainderClosureScratch.lean`).  This file does not
redo that matching.  It consumes the charged row-two integral `(S)`
(`P+3 Fce_0 A=C(κ)`) against those profiles.

The multiplier identity
`B(P+3 Fce_0 A)=-(2/3)B²Δ+2cH+4B³d+9γ(B²c+3d²)+3 Fce_0(AB-6d)`
is evaluated at degree `D+p`.  On the wall that index is the common top
of `B²Δ`, of `cH`, and of `B³d`.  The `γ`/`ε` summands and `d Fce_0`
lie strictly below it.  Clearing `B_D` and the cusp
`A_p B_D²+3 c_Cc²=0` therefore writes the degree-`p` coefficient of
`(S)` as
`2 c_Cc B_D H_N + 2 B_D⁴ d_V - 9 Fce_0 c_Cc²`.
Constancy of `(S)` kills that coefficient (`p=2N>0`), so
`2 c_Cc B_D H_N + 2 B_D⁴ d_V = 9 Fce_0 c_Cc²`.
Equivalently `H` attains the previously free slot `N` with this exact
value (or a lower degree, if the right-hand side vanishes).

CAS (`scripts/max11_cas_run.py`, `vanishing-a-next-row` and
`vanishing-a-Sp0-gb`) on the charts `m=1,2` with `Fce_0≠0`:

* The identity above is independent of the remaining `s`-low of `A`
  (degrees `0..5m-1`).  It is the unique `s`-free coefficient of `(S)`.
* Jets of `Δ` at orders `D+1..4m` are already implied by
  `deg Δ=11m`.  Case I remains empty.  Compensated `I3` is the landed
  exact `Rce`.  Load-free row two is the derivative of `(S)`.
* On the slice `B=X³+X+1` with `d=(d_0,0,0,0,0,3,3,0,2)`, Groebner of
  the remaining `(S)` and `Rce` coefficients in `(d_0,s_0..s_4)`
  together with the relation above is `{1}`.  That is a chart, not a
  uniform combination, and is not promoted to `False`.

This is not a closure.  The committed
`vanishingA_zero_remainder_impossible68` still needs `R_c=R_e=0`.
Named residual: the remainder profile, together with the exact `H_N`
relation from `(S)`.  Next unused row: the remaining coefficients of
loaded row one (the coefficient at `12N-7S-1` is already consumed).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingANextRow68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Degree-`p` coefficient of `(S)` from the multiplier -/

/-- On the residual degrees, the multiplier of `(S)` against `B` at
`D+p` sees only `cH`, `B²Δ`, `B³d`, and `A_p B_D`. -/
theorem fiveToSix_qZero_charged_S_mulB_top_algebra68
    (gamma epsilon Fce0 : k) (A B c d e : k[X]) (N D Cc V p : ℕ)
    (hFce : ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
        (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B = C Fce0)
    (hDp : D + p = 2 * D + (3 * D + Cc - V))
    (hCH : D + p = Cc + N)
    (hB3d : D + p = 3 * D + V)
    (hAB : D + p = p + D)
    (hB2clt : 2 * D + Cc < D + p)
    (hd2lt : 2 * V < D + p)
    (hdlt : V < D + p)
    (hB : B.natDegree ≤ D)
    (hA : A.natDegree ≤ p)
    (hc : c.natDegree ≤ Cc)
    (hd : d.natDegree ≤ V)
    (hH : (FiveToSixQZeroFceZeroH68 B c d).natDegree ≤ N)
    (hDelta : (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree ≤
      3 * D + Cc - V)
    (hDeltaTop : (fiveToSixCuspDiscriminantPolynomial68 A B c).coeff
        (3 * D + Cc - V) =
      (3 : k) * B.coeff D * d.coeff V)
    (hSch : (FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
        (3 * Fce0 : k) • A).natDegree ≤ p) :
    let Sch := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
      (3 * Fce0 : k) • A
    let H := FiveToSixQZeroFceZeroH68 B c d
    let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
    (B * Sch).coeff (D + p) =
      (2 : k) * c.coeff Cc * H.coeff N +
        (2 : k) * B.coeff D ^ 3 * d.coeff V +
        (3 : k) * Fce0 * A.coeff p * B.coeff D := by
  let Sch := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
    (3 * Fce0 : k) • A
  let H := FiveToSixQZeroFceZeroH68 B c d
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let L := 3 * D + Cc - V
  have hmul :=
    fiveToSix_qZero_charged_integral_mulB_of_Fce_const_algebra68
      gamma epsilon Fce0 A B c d e hFce
  dsimp only at hmul
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hB2 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_pow_at_bound68 B D 2 hB
    simpa only [Nat.mul_comm, pow_two] using h
  have hB2Delta : (B ^ 2 * Delta).coeff (D + p) =
      B.coeff D ^ 2 * Delta.coeff L := by
    have h := coeff_mul_at_bounds68 (B ^ 2) Delta (2 * D) L hB2deg hDelta
    have hsum : 2 * D + L = D + p := by
      dsimp only [L]
      exact hDp.symm
    rw [hsum, hB2] at h
    exact h
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by compute_degree; omega
  have hB3 : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 := by
    have h := coeff_pow_at_bound68 B D 3 hB
    simpa only [Nat.mul_comm] using h
  have hB3d' : (B ^ 3 * d).coeff (D + p) =
      B.coeff D ^ 3 * d.coeff V := by
    have h := coeff_mul_at_bounds68 (B ^ 3) d (3 * D) V hB3deg hd
    rw [hB3d.symm, hB3] at h
    exact h
  have hcH : (c * H).coeff (D + p) = c.coeff Cc * H.coeff N := by
    have h := coeff_mul_at_bounds68 c H Cc N hc hH
    rw [hCH.symm] at h
    exact h
  have hAB' : (A * B).coeff (D + p) = A.coeff p * B.coeff D := by
    have h := coeff_mul_at_bounds68 A B p D hA hB
    rw [hAB.symm] at h
    exact h
  have hB2c : (B ^ 2 * c).natDegree < D + p := by
    have hle : (B ^ 2 * c).natDegree ≤ 2 * D + Cc := by
      compute_degree
      omega
    exact hle.trans_lt hB2clt
  have hd2 : (d ^ 2).natDegree < D + p := by
    have hle : (d ^ 2).natDegree ≤ 2 * V := by
      compute_degree
      omega
    exact hle.trans_lt hd2lt
  have hdlow : d.natDegree < D + p := hd.trans_lt hdlt
  have hcoeff := congrArg (fun P : k[X] => P.coeff (D + p)) hmul
  dsimp only [Sch, H, Delta] at hcoeff ⊢ hB2Delta hcH hB3d' hAB'
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hB2c,
    coeff_eq_zero_of_natDegree_lt hd2,
    coeff_eq_zero_of_natDegree_lt hdlow, mul_zero, add_zero, sub_zero] at hcoeff
  rw [hB2Delta, hB3d', hcH, hAB', hDeltaTop] at hcoeff
  linear_combination hcoeff

/-- Clearing `B_D` and the cusp turns the multiplier top into the
degree-`p` coefficient of `(S)` without division. -/
theorem fiveToSix_qZero_charged_S_top_cleared_algebra68
    (gamma epsilon Fce0 : k) (A B c d e : k[X]) (N D Cc V p : ℕ)
    (hFce : ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
        (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B = C Fce0)
    (hDp : D + p = 2 * D + (3 * D + Cc - V))
    (hCH : D + p = Cc + N)
    (hB3d : D + p = 3 * D + V)
    (hAB : D + p = p + D)
    (hB2clt : 2 * D + Cc < D + p)
    (hd2lt : 2 * V < D + p)
    (hdlt : V < D + p)
    (hB : B.natDegree ≤ D)
    (hA : A.natDegree ≤ p)
    (hc : c.natDegree ≤ Cc)
    (hd : d.natDegree ≤ V)
    (hH : (FiveToSixQZeroFceZeroH68 B c d).natDegree ≤ N)
    (hDelta : (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree ≤
      3 * D + Cc - V)
    (hDeltaTop : (fiveToSixCuspDiscriminantPolynomial68 A B c).coeff
        (3 * D + Cc - V) =
      (3 : k) * B.coeff D * d.coeff V)
    (hSch : (FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
        (3 * Fce0 : k) • A).natDegree ≤ p)
    (hcusp : A.coeff p * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0) :
    let Sch := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
      (3 * Fce0 : k) • A
    let H := FiveToSixQZeroFceZeroH68 B c d
    B.coeff D ^ 2 * Sch.coeff p =
      (2 : k) * c.coeff Cc * B.coeff D * H.coeff N +
        (2 : k) * B.coeff D ^ 4 * d.coeff V -
        (9 : k) * Fce0 * c.coeff Cc ^ 2 := by
  let Sch := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
    (3 * Fce0 : k) • A
  let H := FiveToSixQZeroFceZeroH68 B c d
  have htop :=
    fiveToSix_qZero_charged_S_mulB_top_algebra68
      gamma epsilon Fce0 A B c d e N D Cc V p
      hFce hDp hCH hB3d hAB hB2clt hd2lt hdlt hB hA hc hd hH hDelta
      hDeltaTop hSch
  dsimp only at htop
  have hBJ : (B * Sch).coeff (D + p) =
      B.coeff D * Sch.coeff p :=
    coeff_mul_at_bounds68 B Sch D p hB hSch
  have h1 :
      B.coeff D * Sch.coeff p =
        (2 : k) * c.coeff Cc * H.coeff N +
          (2 : k) * B.coeff D ^ 3 * d.coeff V +
          (3 : k) * Fce0 * A.coeff p * B.coeff D := by
    rw [← hBJ, htop]
  have hcusp' : A.coeff p * B.coeff D ^ 2 = -((3 : k) * c.coeff Cc ^ 2) := by
    linear_combination hcusp
  calc
    B.coeff D ^ 2 * Sch.coeff p =
        B.coeff D * (B.coeff D * Sch.coeff p) := by ring
    _ = B.coeff D *
          ((2 : k) * c.coeff Cc * H.coeff N +
            (2 : k) * B.coeff D ^ 3 * d.coeff V +
            (3 : k) * Fce0 * A.coeff p * B.coeff D) := by
      rw [h1]
    _ = (2 : k) * c.coeff Cc * B.coeff D * H.coeff N +
          (2 : k) * B.coeff D ^ 4 * d.coeff V +
          (3 : k) * Fce0 * (A.coeff p * B.coeff D ^ 2) := by
      ring
    _ = (2 : k) * c.coeff Cc * B.coeff D * H.coeff N +
          (2 : k) * B.coeff D ^ 4 * d.coeff V +
          (3 : k) * Fce0 * (-((3 : k) * c.coeff Cc ^ 2)) := by
      rw [hcusp']
    _ = (2 : k) * c.coeff Cc * B.coeff D * H.coeff N +
          (2 : k) * B.coeff D ^ 4 * d.coeff V -
          (9 : k) * Fce0 * c.coeff Cc ^ 2 := by
      ring

/-! ## Source: `(S)` pins `H_N` -/

/-- Constancy of `(S)` kills the degree-`p` slot, so the cleared top
becomes an identity among `H_N`, `Fce_0`, and the cusp/resultant
edges. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_H_N_of_S68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    let H := FiveToSixQZeroFceZeroH68 B c d
    (2 : k) * c.coeff Cc * B.coeff D * H.coeff N +
        (2 : k) * B.coeff D ^ 4 * d.coeff V =
      (9 : k) * Fce.coeff 0 * c.coeff Cc ^ 2 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let H := FiveToSixQZeroFceZeroH68 B c d
  let P := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e
  let Sch := P + (3 * Fce.coeff 0 : k) • A
  let Fce0 := Fce.coeff 0
  have hFconst :
      Fce = C Fce0 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hS :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_charged_rowTwo_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hS
  rcases hS with ⟨kappa, hSch0⟩
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hcusp⟩
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hSpos, hSR, hd, hedeg, hpacket, hrestSource⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcuspP, had⟩
  have htop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_top68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at htop
  have hHdeg :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_H_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hHdeg
  have hH : H.natDegree ≤ N := by
    have hle : D + p - Cc ≤ N := by
      dsimp only [D, p, Cc]
      omega
    exact hHdeg.trans hle
  have hDelta : (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree ≤
      3 * D + Cc - V := le_of_eq htop.2
  have hidxDp : D + p = 2 * D + (3 * D + Cc - V) := by
    dsimp only [D, p, Cc, V]
    omega
  have hidxCH : D + p = Cc + N := by
    dsimp only [D, p, Cc]
    omega
  have hidxB3 : D + p = 3 * D + V := by
    dsimp only [D, p, V]
    omega
  have hidxAB : D + p = p + D := by omega
  have hB2clt : 2 * D + Cc < D + p := by
    dsimp only [D, p, Cc]
    omega
  have hd2lt : 2 * V < D + p := by
    dsimp only [D, p, V]
    omega
  have hdlt : V < D + p := by
    dsimp only [D, p, V]
    omega
  have hppos : 0 < p := by dsimp only [p]; omega
  have hC : Sch = C kappa := by
    simpa [Sch, P, Fce, Fce0] using hSch0
  have hSchdeg : Sch.natDegree ≤ p := by
    rw [hC, natDegree_C]
    exact Nat.zero_le _
  have hcleared :=
    fiveToSix_qZero_charged_S_top_cleared_algebra68
      gamma epsilon Fce0 A B c d e N D Cc V p
      hFconst hidxDp hidxCH hidxB3 hidxAB hB2clt hd2lt hdlt hB' hA' hc'
      hd' hH hDelta htop.1 hSchdeg hcusp
  dsimp only at hcleared
  have hSp : Sch.coeff p = 0 := by
    rw [hC, coeff_C]
    split_ifs with h0
    · omega
    · rfl
  have hzero : B.coeff D ^ 2 * Sch.coeff p = 0 := by
    rw [hSp, mul_zero]
  have hcleared' :
      B.coeff D ^ 2 *
          (FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
            (3 * Fce0 : k) • A).coeff p =
        (2 : k) * c.coeff Cc * B.coeff D * H.coeff N +
          (2 : k) * B.coeff D ^ 4 * d.coeff V -
          (9 : k) * Fce0 * c.coeff Cc ^ 2 :=
    hcleared
  have hzero' :
      B.coeff D ^ 2 *
          (FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e +
            (3 * Fce0 : k) • A).coeff p = 0 := by
    simpa [Sch] using hzero
  rw [hzero'] at hcleared'
  linear_combination -hcleared'

/-! ## Residual packet

The comparison remainders, the charged `Δ`/`H` profiles, and the exact
`H_N` identity from `(S)`.  Not `R_c=R_e=0`, and not `False`. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingANextRowResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let H := FiveToSixQZeroFceZeroH68 B c d
  FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingARemainderClosureResidual68
      gamma epsilon A B c d e N S ∧
    (2 : k) * c.coeff Cc * B.coeff D * H.coeff N +
        (2 : k) * B.coeff D ^ 4 * d.coeff V =
      (9 : k) * Fce.coeff 0 * c.coeff Cc ^ 2

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_next_row68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingANextRowResidual68
      gamma epsilon A B c d e N S := by
  refine ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_closure68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq, ?_⟩
  simpa using
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_H_N_of_S68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq

#print axioms fiveToSix_qZero_charged_S_mulB_top_algebra68
#print axioms fiveToSix_qZero_charged_S_top_cleared_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_H_N_of_S68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_next_row68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingANextRow68

end Max11DegreeRoutes
