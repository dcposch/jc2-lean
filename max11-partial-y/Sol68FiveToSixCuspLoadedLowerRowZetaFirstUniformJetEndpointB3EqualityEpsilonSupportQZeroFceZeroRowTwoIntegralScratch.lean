import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDeltaTopScratch

/-! # The global row-two integral on the zero-`Fce` branch -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroRowTwoIntegral68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixQZeroFceZeroRowTwoIntegral68
    (gamma epsilon : k) (A B c d e : k[X]) : k[X] :=
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  (6 : k) • (J + B ^ 2 * d) + (9 * gamma : k) • (B * c) -
    (27 / 2 * epsilon : k) • d

/-- Once `Fce` vanishes globally, the exact row-two source equation is the
derivative of a single polynomial.  Hence that polynomial is constant. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_rowTwo_integral68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    ∃ kappa : k,
      FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e = C kappa := by
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let P := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e
  have hglobal :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3, hFzero, hRce, hK⟩
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
    ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with
    ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hz : zeta = 0 := hrest.2.2.1
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrow2, hpos, hiff⟩
  have hfull : FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
      alpha gamma epsilon 0 eta A B c d e = 0 := by
    rw [show FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon 0 eta A B c d e =
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e by rfl]
    simpa only [hz] using hrow2
  have hexp :=
    fiveToSix_zetaFirst_B3_equality_support_clean_rowTwo_expansion68
      (k := k) alpha gamma epsilon eta A B c d e
  rw [hfull, smul_zero] at hexp
  have hfactor := fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k := k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  rw [hfactor.2] at hexp
  change Fce = 0 at hFzero
  change 0 =
    ((-(6 : k) • (A * derivative Fce) +
        (3 : k) • (derivative A * Fce) + (6 : k) • derivative J) +
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d) +
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
        gamma epsilon B c d at hexp
  rw [hFzero, derivative_zero, mul_zero, smul_zero, zero_add] at hexp
  have hzero :
      (6 : k) • derivative J +
          FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d +
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
          gamma epsilon B c d = 0 := by
    simpa only [mul_zero, smul_zero, zero_add] using hexp.symm
  have hder : derivative P = 0 := by
    calc
      derivative P =
          (6 : k) • derivative J +
              FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d +
            FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
              gamma epsilon B c d := by
        dsimp only [P, FiveToSixQZeroFceZeroRowTwoIntegral68, J,
          FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68,
          FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68]
        simp only [derivative_add, derivative_sub, derivative_smul,
          derivative_mul, derivative_pow]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_natCast, map_one]
        ring
      _ = 0 := hzero
  exact ⟨P.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hder⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_rowTwo_integral68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroRowTwoIntegral68

end Max11DegreeRoutes
