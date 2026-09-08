import Grok68VanishingAOrder4CompanionSplitPart6Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 7 of 26, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact division-free elimination of `J_(p-4)` and all higher `J` jets. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68
      alpha gamma epsilon zeta eta A B c d e N S := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let i0 := 2 * p - 5
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
    (3 / 4 * epsilon : k) • B
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  rcases hnxt with ⟨harith, hexact, hrow2old, hp1cast⟩
  rcases hexact with ⟨i4, i3, hFce, hRce, hRceDeg⟩
  have hEq : 9 * N = 7 * S := harith.1
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
  have hA' : A.natDegree ≤ p := by simpa [p] using hA
  have hdA : (derivative A).natDegree ≤ p - 1 := by
    have h := natDegree_derivative_le A
    dsimp only [p]; omega
  have hJ : J.natDegree ≤ p := by
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
  have hp4 : 4 ≤ p := by dsimp only [p]; omega
  have hpm1 : 4 ≤ p - 1 := by dsimp only [p]; omega
  have hAAraw := coeff_mul_four_below_bounds68 A (derivative A) p (p - 1)
    hp4 hpm1 hA' hdA
  rw [show p + (p - 1) - 4 = i0 by dsimp only [i0]; omega] at hAAraw
  have hdA0 : (derivative A).coeff (p - 1) = A.coeff p * ((p : ℕ) : k) := by
    rw [coeff_derivative, show p - 1 + 1 = p by omega]
    congr 1
    exact_mod_cast (show p - 1 + 1 = p by omega)
  have hdA1 : (derivative A).coeff (p - 2) =
      A.coeff (p - 1) * ((p - 1 : ℕ) : k) := by
    rw [coeff_derivative, show p - 2 + 1 = p - 1 by omega]
    congr 1
    exact_mod_cast (show p - 2 + 1 = p - 1 by omega)
  have hdA2 : (derivative A).coeff (p - 3) =
      A.coeff (p - 2) * ((p - 2 : ℕ) : k) := by
    rw [coeff_derivative, show p - 3 + 1 = p - 2 by omega]
    congr 1
    exact_mod_cast (show p - 3 + 1 = p - 2 by omega)
  have hdA3 : (derivative A).coeff (p - 4) =
      A.coeff (p - 3) * ((p - 3 : ℕ) : k) := by
    rw [coeff_derivative, show p - 4 + 1 = p - 3 by omega]
    congr 1
    exact_mod_cast (show p - 4 + 1 = p - 3 by omega)
  have hdA4 : (derivative A).coeff (p - 5) =
      A.coeff (p - 4) * ((p - 4 : ℕ) : k) := by
    rw [coeff_derivative, show p - 5 + 1 = p - 4 by omega]
    congr 1
    exact_mod_cast (show p - 5 + 1 = p - 4 by omega)
  rw [show p - 1 - 1 = p - 2 by omega, show p - 1 - 2 = p - 3 by omega,
    show p - 1 - 3 = p - 4 by omega, show p - 1 - 4 = p - 5 by omega,
    hdA0, hdA1, hdA2, hdA3, hdA4] at hAAraw
  have hAA : (A * derivative A).coeff i0 =
      ((p - 2 : ℕ) : k) *
        ((2 : k) * A.coeff p * A.coeff (p - 4) +
          (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
          A.coeff (p - 2) ^ 2) := by
    have hc04 : ((p : ℕ) : k) + ((p - 4 : ℕ) : k) =
        (2 : k) * ((p - 2 : ℕ) : k) := by
      exact_mod_cast (show p + (p - 4) = 2 * (p - 2) by omega)
    have hc13 : ((p - 1 : ℕ) : k) + ((p - 3 : ℕ) : k) =
        (2 : k) * ((p - 2 : ℕ) : k) := by
      exact_mod_cast (show (p - 1) + (p - 3) = 2 * (p - 2) by omega)
    linear_combination hAAraw + A.coeff p * A.coeff (p - 4) * hc04 +
      A.coeff (p - 1) * A.coeff (p - 3) * hc13
  have hAJraw := coeff_mul_four_below_bounds68 (derivative A) J (p - 1) p
    hpm1 hp4 hdA hJ
  rw [show (p - 1) + p - 4 = i0 by dsimp only [i0]; omega,
    show p - 1 - 1 = p - 2 by omega, show p - 1 - 2 = p - 3 by omega,
    show p - 1 - 3 = p - 4 by omega, show p - 1 - 4 = p - 5 by omega,
    hdA0, hdA1, hdA2, hdA3, hdA4] at hAJraw
  have hAJ : (derivative A * J).coeff i0 =
      ((p : ℕ) : k) * A.coeff p * J.coeff (p - 4) +
        ((p - 1 : ℕ) : k) * A.coeff (p - 1) * J.coeff (p - 3) +
        ((p - 2 : ℕ) : k) * A.coeff (p - 2) * J.coeff (p - 2) +
        ((p - 3 : ℕ) : k) * A.coeff (p - 3) * J.coeff (p - 1) +
        ((p - 4 : ℕ) : k) * A.coeff (p - 4) * J.coeff p := by
    linear_combination hAJraw
  have hFconst : Fce = C (Fce.coeff 0) := by
    apply eq_C_of_natDegree_le_zero
    have hFce' : Fce = (3 / 8 : k) • C i4 := hFce
    rw [hFce']
    compute_degree
  have hAAF : (A * derivative A * Fce).coeff i0 = Fce.coeff 0 *
      ((p - 2 : ℕ) : k) *
        ((2 : k) * A.coeff p * A.coeff (p - 4) +
          (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
          A.coeff (p - 2) ^ 2) := by
    have heq : A * derivative A * Fce = Fce.coeff 0 • (A * derivative A) := by
      calc
        A * derivative A * Fce = (A * derivative A) * C (Fce.coeff 0) := by
          conv_lhs => rw [hFconst]
        _ = Fce.coeff 0 • (A * derivative A) := by
          simp only [smul_eq_C_mul]
          ring
    rw [heq, coeff_smul, hAA]
    ring
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrowTwo, hpos, hiff⟩
  have hfull0 := hpos i0 (by dsimp only [i0, p]; omega)
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
  simp only [coeff_add, coeff_sub, hAAF, hAJ] at hfull0
  have hrow0main :
      Fce.coeff 0 * ((p - 2 : ℕ) : k) *
          ((2 : k) * A.coeff p * A.coeff (p - 4) +
            (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
            A.coeff (p - 2) ^ 2) -
        (((p : ℕ) : k) * A.coeff p * J.coeff (p - 4) +
          ((p - 1 : ℕ) : k) * A.coeff (p - 1) * J.coeff (p - 3) +
          ((p - 2 : ℕ) : k) * A.coeff (p - 2) * J.coeff (p - 2) +
          ((p - 3 : ℕ) : k) * A.coeff (p - 3) * J.coeff (p - 1) +
          ((p - 4 : ℕ) : k) * A.coeff (p - 4) * J.coeff p) +
        L0.coeff i0 + W0.coeff i0 = 0 := by
    linear_combination hfull0
  have hr1 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 1 hs hq
      (by dsimp only [p] at *; omega)
  have hr2 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 2 hs hq
      (by dsimp only [p] at *; omega)
  have hr3 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 3 hs hq
      (by dsimp only [p] at *; omega)
  have hr4 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 4 hs hq
      (by dsimp only [p] at *; omega)
  dsimp only at hr1 hr2 hr3 hr4
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
  have hp1c : ((p - 1 : ℕ) : k) = ((p : ℕ) : k) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hp2c : ((p - 2 : ℕ) : k) = ((p : ℕ) : k) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
  have hp3c : ((p - 3 : ℕ) : k) = ((p : ℕ) : k) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ p)]; norm_num
  have hp4c : ((p - 4 : ℕ) : k) = ((p : ℕ) : k) - 4 := by
    rw [Nat.cast_sub hp4]; norm_num
  have hresult :
      (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
          ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k) * Fce.coeff 0 *
          ((2 : k) * A.coeff p * A.coeff (p - 4) +
            (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
            A.coeff (p - 2) ^ 2) +
        (6 : k) * ((p - 4 : ℕ) : k) ^ 2 * ((p - 3 : ℕ) : k) *
          ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) *
          A.coeff (p - 4) * B.coeff D ^ 2 * d.coeff V +
        (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
          ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) *
          (L0.coeff i0 + W0.coeff i0) +
        ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
          ((p - 1 : ℕ) : k) * A.coeff p * (L2.coeff (p - 5) + W2.coeff (p - 5)) +
        ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
          A.coeff (p - 1) * (L2.coeff (p - 4) + W2.coeff (p - 4)) +
        ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
          ((p - 1 : ℕ) : k) * A.coeff (p - 2) *
          (L2.coeff (p - 3) + W2.coeff (p - 3)) +
        ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
          A.coeff (p - 3) * (L2.coeff (p - 2) + W2.coeff (p - 2)) = 0 := by
    rw [hp1c, hp2c, hp3c, hp4c] at hrow0main ⊢
    rw [hp1c] at hr1
    rw [hp2c] at hr2
    rw [hp3c] at hr3
    rw [hp4c] at hr4
    linear_combination
      (6 : k) * (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 3) *
        (((p : ℕ) : k) - 2) * (((p : ℕ) : k) - 1) * hrow0main +
      ((p : ℕ) : k) * (((p : ℕ) : k) - 3) * (((p : ℕ) : k) - 2) *
        (((p : ℕ) : k) - 1) * A.coeff p * hr4 +
      (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 2) *
        (((p : ℕ) : k) - 1) ^ 2 * A.coeff (p - 1) * hr3 +
      (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 3) * (((p : ℕ) : k) - 2) *
        (((p : ℕ) : k) - 1) * A.coeff (p - 2) * hr2 +
      (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 3) ^ 2 *
        (((p : ℕ) : k) - 2) * A.coeff (p - 3) * hr1 +
      (3 : k) * (((p : ℕ) : k) - 4) ^ 2 * (((p : ℕ) : k) - 3) *
        (((p : ℕ) : k) - 2) * (((p : ℕ) : k) - 1) * A.coeff (p - 4) *
        htopReduced
  dsimp only
    [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68,
      p, D, V, Fce, L0, W0, L2, W2]
  simpa only [i0] using hresult


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
