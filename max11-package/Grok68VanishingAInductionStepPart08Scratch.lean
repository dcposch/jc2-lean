import Grok68VanishingAInductionStepPart07Scratch

/-! # Uniform producing induction on the `q=0` vanishing-A chamber

Committed green through `k=4` produces vanishing `A_(2N-j)=0` for
`j≤4`, and matching from a granted vanishing depth is already uniform
(`Grok68VanishingAUniformCompanionScratch.lean`).

The order-`k` producing companion, under vanishing through `k-1`, does
not take per-`k` input:

* only the `A_p` slot of `A'` reaches the companion remainder index
  (the `A_(p-k)` slot overshoots `deg(Bc)`);
* remainder cancel reduces to the pair `W0_(2p-k-1)` and `A_p W2_(p-k-1)`,
  which cancel by the companion weights against `(B c)_(p-k)`;
* load cancel is the two-generator combination of the order-`k` disc
  and I4 jets with cofactors `(25P-14k)` and `(15P-14k)` (CAS leftover
  `0` on `k=2..7`, and the same closed form for general `k`).

This file lands remainder cancel, the load identity, and the producing
step uniformly on `1≤k≤D`.  Induction from the committed `k≤4` base
gives vanishing of `A` through `k=D` for every `m`.  Matching through
`k=D` is then a theorem of granted vanishing, so the comparison
polynomials drop to degree at most `N-1` and `E-D-1`.  Those degree
bounds are not the identities `r_c=r_e=0`, so the committed
`vanishingA_zero_remainder_impossible68` does not fire.

This is not a closure.  Named gap: the comparison remainders after
matching through `D`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Two-endpoint Cauchy products -/

/-! ## Remainder transport at an arbitrary positive index -/

/-! ## `A'` against a shorter right factor, after vanishing through `r-1` -/

/-! ## Remainder cancel under vanishing through `r-1` -/

/-! ## Row-two load as a derivative -/

/-! ## Derivative Cauchy products and the row-zero load splitting -/

/-! ## Source: order-`r` disc with vanishing through `r-1` -/

/-! ## Companion reduction under vanishing through `r-1` -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_step68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0)
    (hload :
      let p := 2 * N
      let D := 3 * N - 2 * S
      let V := 5 * N - 3 * S
      let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
      let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
      (6 : k) * ((p - r : ℕ) : k) * L0.coeff (2 * p - r - 1) +
        ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
        (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
          B.coeff D ^ 2 * d.coeff V = 0) :
    A.coeff (2 * N - r) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let i0 := 2 * p - r - 1
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hFne := fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hrem :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_step68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hs hq hr hrD hAvan
  dsimp only at hrem hload
  have hr2 : r < 2 * N := by omega
  have hrow2 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S r hs hq hr2
  dsimp only at hrow2
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
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrowTwo, hpos, hiff⟩
  have hi0pos : 0 < i0 := by dsimp only [i0, p]; omega
  have hfull0 := hpos i0 hi0pos
  have hfactor := fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k := k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hdecomp0 :
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
          alpha gamma epsilon zeta eta A B c d e =
        (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e +
          (3 / 2 * gamma : k) • (A * derivative A * d) +
          (3 / 4 * epsilon : k) • (A * B * derivative A) + L0) + W0 := by
    dsimp only [W0, L0,
      FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68]
    module
  change (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
    alpha gamma epsilon zeta eta A B c d e).coeff i0 = 0 at hfull0
  rw [hdecomp0, hfactor.1] at hfull0
  change (A * derivative A * Fce - derivative A * J + L0 + W0).coeff i0 = 0
    at hfull0
  have hdA : (derivative A).natDegree ≤ p - 1 :=
    (natDegree_derivative_le A).trans (by dsimp only [p]; omega)
  have hJdeg : J.natDegree ≤ p := by
    have hloaded' := hs.1
    rcases hloaded' with ⟨hsupport, hrows⟩
    rcases hsupport with ⟨hstop, hTD⟩
    rcases hstop with ⟨hcur, ht, hstate, hclass, hraw0, hraw2⟩
    let T := S - 2 * D
    let t := min D T
    have htT : t = T := by dsimp only [t]; exact Nat.min_eq_right hTD
    have hstate' := hstate
    dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
    have hjidx : 5 * N - 2 * S - (t - 1) - 1 = p := by
      dsimp only [D, T] at htT
      dsimp only [p]; omega
    rw [hjidx] at hstate'
    exact hstate'.2
  have hvanA : ∀ j, 1 ≤ j → j < r → A.coeff (p - j) = 0 := by
    intro j hj1 hj2
    simpa [p] using hAvan j hj1 hj2
  have hvanA' : ∀ j, 1 ≤ j → j < r →
      (derivative A).coeff ((p - 1) - j) = 0 := by
    intro j hj1 hj2
    have hidx : p - 1 - j + 1 = p - j := by omega
    rw [coeff_derivative, hidx]
    have hAj : A.coeff (p - j) = 0 := hvanA j hj1 hj2
    rw [hAj, zero_mul]
  have hrA : r ≤ p - 1 := by dsimp only [p]; omega
  have hrJ : r ≤ p := by dsimp only [p]; omega
  have hAJ := coeff_mul_sub_bounds_vanishing_left68
    (derivative A) J (p - 1) p r hr hrA hrJ hdA hJdeg hvanA'
  have hidxAJ : p - 1 + p - r = i0 := by dsimp only [i0, p]; omega
  rw [hidxAJ] at hAJ
  have hdAp : (derivative A).coeff (p - 1) =
      A.coeff p * ((p : ℕ) : k) := by
    rw [coeff_derivative, show p - 1 + 1 = p by omega]
    congr 1
    exact_mod_cast (show p - 1 + 1 = p by omega)
  have hdApr : (derivative A).coeff ((p - 1) - r) =
      A.coeff (p - r) * ((p - r : ℕ) : k) := by
    have hidx : p - 1 - r + 1 = p - r := by omega
    rw [coeff_derivative, hidx]
    congr 1
    exact_mod_cast hidx
  rw [hdAp, hdApr] at hAJ
  have hAA := coeff_mul_sub_bounds_vanishing_left68
    A (derivative A) p (p - 1) r hr (by dsimp only [p]; omega) hrA hA' hdA
    hvanA
  have hidxAA : p + (p - 1) - r = i0 := by dsimp only [i0, p]; omega
  rw [hidxAA, hdAp, hdApr] at hAA
  have hAAF : (A * derivative A * Fce).coeff i0 =
      Fce.coeff 0 * (A * derivative A).coeff i0 := by
    have heq : A * derivative A * Fce = Fce.coeff 0 • (A * derivative A) := by
      calc
        A * derivative A * Fce = (A * derivative A) * C (Fce.coeff 0) := by
          conv_lhs => rw [hFconst]
        _ = Fce.coeff 0 • (A * derivative A) := by
          simp only [smul_eq_C_mul]
          ring
    rw [heq, coeff_smul]
    rfl
  simp only [coeff_add, coeff_sub, hAAF, hAJ] at hfull0
  have hrow0 :
      Fce.coeff 0 *
          (A.coeff p * (A.coeff (p - r) * ((p - r : ℕ) : k)) +
            A.coeff (p - r) * (A.coeff p * ((p : ℕ) : k))) -
        (A.coeff p * ((p : ℕ) : k) * J.coeff (p - r) +
          A.coeff (p - r) * ((p - r : ℕ) : k) * J.coeff p) +
        L0.coeff i0 + W0.coeff i0 = 0 := by
    rw [hAA] at hfull0
    linear_combination hfull0
  have hcontract := fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68]
    at hcontract
  have htop := hcontract.2.1
  have hpOld : 11 * N - 7 * S = p := by dsimp only [p]; omega
  rw [hq, hpOld] at htop
  simp only [Nat.cast_zero, sub_zero] at htop
  have hNk : ((N : ℕ) : k) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpcast : ((p : ℕ) : k) = (2 : k) * ((N : ℕ) : k) := by
    dsimp only [p]; push_cast; rfl
  have htopReduced :
      A.coeff p * Fce.coeff 0 +
        (2 : k) * (J.coeff p + B.coeff D ^ 2 * d.coeff V) = 0 := by
    have hprod : ((N : ℕ) : k) * (A.coeff p * Fce.coeff 0 +
        (2 : k) * (J.coeff p + B.coeff D ^ 2 * d.coeff V)) = 0 := by
      dsimp only [p, D, V, Fce, J] at htop ⊢
      rw [hpcast] at htop
      linear_combination htop
    exact (mul_eq_zero.mp hprod).resolve_left hNk
  have hpr : ((p - r : ℕ) : k) ≠ 0 := by
    exact_mod_cast (show p - r ≠ 0 by dsimp only [p]; omega)
  -- Clear denominators: multiply the row-zero identity by `6(p-r)`.
  have hcleared :
      (6 : k) * ((p - r : ℕ) : k) * Fce.coeff 0 *
          (A.coeff p * A.coeff (p - r) * ((p - r : ℕ) : k) +
            A.coeff (p - r) * A.coeff p * ((p : ℕ) : k)) -
        (6 : k) * ((p - r : ℕ) : k) *
          (A.coeff p * ((p : ℕ) : k) * J.coeff (p - r) +
            A.coeff (p - r) * ((p - r : ℕ) : k) * J.coeff p) +
        (6 : k) * ((p - r : ℕ) : k) * (L0.coeff i0 + W0.coeff i0) = 0 := by
    linear_combination (6 : k) * ((p - r : ℕ) : k) * hrow0
  -- Row-two supplies `6(p-r) J_(p-r)`.
  have hJpr :
      (6 : k) * ((p - r : ℕ) : k) * J.coeff (p - r) =
        -((3 : k) * ((p - r : ℕ) : k) * A.coeff (p - r) * Fce.coeff 0) -
          (L2.coeff (p - r - 1) + W2.coeff (p - r - 1)) := by
    have : (((p - r : ℕ) : k)) *
        ((3 : k) * A.coeff (p - r) * Fce.coeff 0 +
          (6 : k) * J.coeff (p - r)) +
        L2.coeff (p - r - 1) + W2.coeff (p - r - 1) = 0 := hrow2
    linear_combination this
  have hmain :
      (9 : k) * ((p - r : ℕ) : k) * ((2 : k) * ((p : ℕ) : k) - (r : k)) *
          Fce.coeff 0 * A.coeff p * A.coeff (p - r) +
        (6 : k) * ((p - r : ℕ) : k) * L0.coeff i0 +
        ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
        (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
          B.coeff D ^ 2 * d.coeff V +
        (6 : k) * ((p - r : ℕ) : k) * W0.coeff i0 +
        ((p : ℕ) : k) * A.coeff p * W2.coeff (p - r - 1) = 0 := by
    have hrC : ((r : ℕ) : k) = ((p : ℕ) : k) - ((p - r : ℕ) : k) := by
      have hle : p - r ≤ p := Nat.sub_le p r
      have h : ((p - (p - r) : ℕ) : k) = ((p : ℕ) : k) - ((p - r : ℕ) : k) :=
        Nat.cast_sub hle
      have heq : p - (p - r) = r := by omega
      rw [heq] at h
      exact h
    have hJp : J.coeff p +
        (1 / 2 : k) * A.coeff p * Fce.coeff 0 + B.coeff D ^ 2 * d.coeff V = 0 := by
      linear_combination (1 / 2 : k) * htopReduced
    have h2pr_sum :
        (2 : k) * ((p : ℕ) : k) - (r : k) =
          ((p : ℕ) : k) + ((p - r : ℕ) : k) := by
      linear_combination -hrC
    have hmain' :
        (9 : k) * ((p - r : ℕ) : k) *
            (((p : ℕ) : k) + ((p - r : ℕ) : k)) *
            Fce.coeff 0 * A.coeff p * A.coeff (p - r) +
          (6 : k) * ((p - r : ℕ) : k) * L0.coeff i0 +
          ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
          (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
            B.coeff D ^ 2 * d.coeff V +
          (6 : k) * ((p - r : ℕ) : k) * W0.coeff i0 +
          ((p : ℕ) : k) * A.coeff p * W2.coeff (p - r - 1) = 0 := by
      linear_combination hcleared +
        ((p : ℕ) : k) * A.coeff p * hJpr -
        (12 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) * hJp +
        (9 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) * htopReduced
    rw [h2pr_sum]
    exact hmain'
  have hFceA :
      (9 : k) * ((p - r : ℕ) : k) *
          ((2 : k) * ((p : ℕ) : k) - (r : k)) *
          Fce.coeff 0 * A.coeff p * A.coeff (p - r) = 0 := by
    linear_combination hmain - hload - hrem
  have h9 : (9 : k) ≠ 0 := by norm_num
  have h2pr : (2 : k) * ((p : ℕ) : k) - (r : k) ≠ 0 := by
    have h2p : (2 : ℕ) * p - r ≠ 0 := by dsimp only [p]; omega
    have : (2 : k) * ((p : ℕ) : k) - (r : k) = ((2 * p - r : ℕ) : k) := by
      have hle : r ≤ 2 * p := by dsimp only [p]; omega
      have h : ((2 * p - r : ℕ) : k) = ((2 * p : ℕ) : k) - (r : k) :=
        Nat.cast_sub hle
      push_cast at h
      exact h.symm
    rw [this]
    exact_mod_cast h2p
  have hfac : (9 : k) * ((p - r : ℕ) : k) *
      ((2 : k) * ((p : ℕ) : k) - (r : k)) * Fce.coeff 0 *
      A.coeff p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h9 hpr) h2pr) hFne) ha0
  have hmul : ((9 : k) * ((p - r : ℕ) : k) *
      ((2 : k) * ((p : ℕ) : k) - (r : k)) * Fce.coeff 0 *
      A.coeff p) * A.coeff (p - r) = 0 := by
    linear_combination hFceA
  have hAr : A.coeff (p - r) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hfac
  simpa [p] using hAr

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
