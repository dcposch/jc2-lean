import Grok68QZeroVanishingAJetScratch

/-! # Charged I4 Case I emptiness and the charged row-two integral

On the `q=0` wall, `Fce` is constant.  The vanishing-A chamber is the
nonzero-constant side of that split.

This file lands two identities from the coordinator-reviewed hunt
`xmodel/max11-68-vanishing-a-identity-hunt-grok46-20260901.md`.

* Case I of the charged I4 fibre is empty: `B` cannot divide
  `2c+C(3γ)`, because that factorisation writes a nonzero constant as
  `B` times a polynomial.
* The charged row-two integral `(S)`: `P+3 Fce_0 A` is constant.  The
  load-factor rewrite used here is the committed theorem
  `fiveToSix_zetaFirst_B3_equality_support_load_factor68`, checked as a
  polynomial identity against the committed row-two core.

The hunt's first named closure route is a uniform two-case degree
comparison of `(S)` against I4.  Pairing `(S)` with I4 produces the
exact multiplier identity `B(P+3 Fce_0 A)=candidate`.  After the
resultant the leftover terms share degrees, so both remainder cases
are not impossible.  The second named route (`r_c=r_e=0`, then `(*)`
kills at degree `9m`) is not forced by the landed identities.  This is
not a closure.  The next unused source row remains `A_(2N-4)`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAChargedIntegral68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Ring identities -/

/-- If `2c+C(3γ)=Bv`, the charged I4 polynomial factorises through `B`.
The identity is recorded in difference form so the generating
combination is visible. -/
theorem fiveToSix_qZero_charged_Fce_factor_algebra68
    (gamma epsilon : k) (B c d e v : k[X]) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    let Cg := (2 : k) • c + C (3 * gamma)
    let Q := e + (1 / 2 : k) • (v * d) - (1 / 9 : k) • B ^ 2 +
      C (3 / 4 * epsilon)
    Fce - B * Q = (1 / 2 : k) • (d * (Cg - B * v)) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one, map_natCast]
  ring

/-- Specialisation: a genuine quotient `2c+C(3γ)=Bv` writes `Fce` as
`B` times a polynomial. -/
theorem fiveToSix_qZero_charged_Fce_factor_of_Cg_algebra68
    (gamma epsilon : k) (B c d e v : k[X])
    (hv : (2 : k) • c + C (3 * gamma) = B * v) :
    ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
        (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B =
      B * (e + (1 / 2 : k) • (v * d) - (1 / 9 : k) • B ^ 2 +
        C (3 / 4 * epsilon)) := by
  have halg :=
    fiveToSix_qZero_charged_Fce_factor_algebra68 gamma epsilon B c d e v
  dsimp only at halg
  rw [hv, sub_self, mul_zero, smul_zero, sub_eq_zero] at halg
  exact halg

/-- Derivative of the named row-two integral.  Independent of `Fce`. -/
theorem fiveToSix_qZero_charged_rowTwo_P_derivative_algebra68
    (gamma epsilon : k) (A B c d e : k[X]) :
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    derivative (FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e) =
      (6 : k) • derivative J +
        FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d +
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
          gamma epsilon B c d := by
  dsimp only [FiveToSixQZeroFceZeroRowTwoIntegral68,
    FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68,
    FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68]
  simp only [derivative_add, derivative_sub, derivative_smul, derivative_mul,
    derivative_pow]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- Pairing of `P+3 Fce_0 A` with I4, as a ring identity.  The leftover
is `18 d(Fce-C(Fce_0))`. -/
theorem fiveToSix_qZero_charged_integral_mulB_algebra68
    (gamma epsilon Fce0 : k) (A B c d e : k[X]) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    let P := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e
    let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
    let H := FiveToSixQZeroFceZeroH68 B c d
    B * (P + (3 * Fce0 : k) • A) -
        (-(2 / 3 : k) • (B ^ 2 * Delta) + (2 : k) • (c * H) +
          (4 : k) • (B ^ 3 * d) +
          (9 * gamma : k) • (B ^ 2 * c + (3 : k) • d ^ 2) +
          (3 * Fce0 : k) • (A * B - (6 : k) • d)) =
      -(18 : k) • (d * (Fce - C Fce0)) := by
  dsimp only [FiveToSixQZeroFceZeroRowTwoIntegral68,
    fiveToSixCuspDiscriminantPolynomial68, FiveToSixQZeroFceZeroH68]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- On `Fce=C(Fce_0)`, the multiplier identity has no leftover. -/
theorem fiveToSix_qZero_charged_integral_mulB_of_Fce_const_algebra68
    (gamma epsilon Fce0 : k) (A B c d e : k[X])
    (hFce : ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
        (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B = C Fce0) :
    let P := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e
    let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
    let H := FiveToSixQZeroFceZeroH68 B c d
    B * (P + (3 * Fce0 : k) • A) =
      -(2 / 3 : k) • (B ^ 2 * Delta) + (2 : k) • (c * H) +
        (4 : k) • (B ^ 3 * d) +
        (9 * gamma : k) • (B ^ 2 * c + (3 : k) • d ^ 2) +
        (3 * Fce0 : k) • (A * B - (6 : k) • d) := by
  have halg :=
    fiveToSix_qZero_charged_integral_mulB_algebra68
      gamma epsilon Fce0 A B c d e
  dsimp only at halg
  rw [hFce, sub_self, mul_zero, smul_zero] at halg
  exact sub_eq_zero.mp halg

/-! ## Source: `Fce` is constant on the `q=0` wall -/

/-- `next68` writes `Fce` as a scalar multiple of `C(i_4)`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    Fce = C (Fce.coeff 0) := by
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  change Fce = C (Fce.coeff 0)
  have hnxt :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt.2.1 with ⟨i4, i3, hFce, hRce, hRceDeg⟩
  have hFce' : Fce = (3 / 8 : k) • C i4 := hFce
  apply eq_C_of_natDegree_le_zero
  rw [hFce']
  compute_degree

/-! ## Source: Case I is empty -/

/-- A nonzero constant cannot be `B` times a polynomial on this wall. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_empty68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e v : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hv : (2 : k) • c + C (3 * gamma) = B * v) :
    False := by
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let Q := e + (1 / 2 : k) • (v * d) - (1 / 9 : k) • B ^ 2 +
    C (3 / 4 * epsilon)
  let D := 3 * N - 2 * S
  have hFce0 :
      Fce.coeff 0 ≠ 0 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hfac :
      Fce = B * Q :=
    fiveToSix_qZero_charged_Fce_factor_of_Cg_algebra68
      gamma epsilon B c d e v hv
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
    ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
  rcases hpacket with
    ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hnxt :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hDpos : 0 < D := by
    dsimp only [D]
    omega
  have hB' : B.natDegree ≤ D := by
    dsimp only [D]
    simpa [hGS] using hB
  have hbidx : D = 3 * N - G := by
    dsimp only [D]
    omega
  have hbcoeff : B.coeff D ≠ 0 := by
    rw [hbidx]
    exact hBtop
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
  have hBne : B ≠ 0 := by
    intro hz
    apply hbcoeff
    rw [hz, coeff_zero]
  have hQne : Q ≠ 0 := by
    intro hQ
    have hzero : C (Fce.coeff 0) = 0 := by
      calc
        C (Fce.coeff 0) = Fce := hFconst.symm
        _ = B * Q := hfac
        _ = B * 0 := by rw [hQ]
        _ = 0 := mul_zero B
    exact hFce0 (C_eq_zero.mp hzero)
  have hdeg :
      D + Q.natDegree = 0 := by
    have hmul := natDegree_mul hBne hQne
    rw [← hfac, hFconst, natDegree_C, hBdeg] at hmul
    exact hmul.symm
  omega

/-- Case I in divisor form. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_not_dvd68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    ¬ B ∣ ((2 : k) • c + C (3 * gamma)) := by
  intro hdiv
  obtain ⟨v, hv⟩ := hdiv
  exact
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_empty68
      alpha gamma epsilon zeta eta terminal A B c d e v N G S
      hterminal hs hq hv

/-! ## Source: charged row-two integral `(S)` -/

/-- On the whole `q=0` wall, `FullRowTwo=0` is the derivative of
`P+3 Fce_0 A`.  Hence that polynomial is constant.  This is the
`Fce_0`-charged form of the landed terminal integral `P=C(κ)`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_charged_rowTwo_integral68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    let P := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e
    ∃ kappa : k, P + (3 * Fce.coeff 0 : k) • A = C kappa := by
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let P := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e
  let Scharged := P + (3 * Fce.coeff 0 : k) • A
  change ∃ kappa : k, Scharged = C kappa
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
    ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
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
  change 0 =
    ((-(6 : k) • (A * derivative Fce) +
        (3 : k) • (derivative A * Fce) + (6 : k) • derivative J) +
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d) +
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
        gamma epsilon B c d at hexp
  have hFder : derivative Fce = 0 := by
    rw [hFconst, derivative_C]
  have hA'F : derivative A * Fce = Fce.coeff 0 • derivative A := by
    calc
      derivative A * Fce = derivative A * C (Fce.coeff 0) := by
        conv_lhs => rw [hFconst]
      _ = Fce.coeff 0 • derivative A := by
        simp only [smul_eq_C_mul]
        exact mul_comm _ _
  rw [hFder, mul_zero, smul_zero, zero_add, hA'F] at hexp
  have h3 :
      (3 : k) • (Fce.coeff 0 • derivative A) =
        (3 * Fce.coeff 0 : k) • derivative A := by
    simp only [smul_smul]
  rw [h3] at hexp
  have hPder :=
    fiveToSix_qZero_charged_rowTwo_P_derivative_algebra68
      gamma epsilon A B c d e
  dsimp only at hPder
  have hder : derivative Scharged = 0 := by
    dsimp only [Scharged]
    rw [derivative_add, derivative_smul, hPder]
    convert hexp.symm using 1
    abel
  exact ⟨Scharged.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hder⟩

/-! ## Residual packet -/

/-- Residual after landing Case I emptiness and the charged integral.
Matching through `k=3` is unchanged.  The next unused source
coefficient is still `A_(2N-4)`.  Not a closure: the multiplier
identity `B(P+3 Fce_0 A)=candidate` does not yield a two-case degree
kill, and `(S)+I4` does not force `r_c=r_e=0`. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAChargedIntegralResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let P := FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e
  Fce.coeff 0 ≠ 0 ∧
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAJetResidual68
      A B c d e N S ∧
    ¬ B ∣ ((2 : k) • c + C (3 * gamma)) ∧
    (∃ kappa : k, P + (3 * Fce.coeff 0 : k) • A = C kappa)

/-- Source-backed residual of the vanishing-A chamber after Case I and
`(S)`.  `Fce.coeff 0` remains nonzero.  Not a closure. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_integral68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAChargedIntegralResidual68
      gamma epsilon A B c d e N S := by
  refine ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq, ?_, ?_, ?_⟩
  · exact (fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_jet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hs hq).2
  · exact
      fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_not_dvd68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hs hq
  · exact
      fiveToSix_zetaFirst_B3_equality_support_qZero_charged_rowTwo_integral68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq

#print axioms fiveToSix_qZero_charged_Fce_factor_algebra68
#print axioms fiveToSix_qZero_charged_Fce_factor_of_Cg_algebra68
#print axioms fiveToSix_qZero_charged_rowTwo_P_derivative_algebra68
#print axioms fiveToSix_qZero_charged_integral_mulB_algebra68
#print axioms fiveToSix_qZero_charged_integral_mulB_of_Fce_const_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_empty68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_not_dvd68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_charged_rowTwo_integral68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_integral68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAChargedIntegral68

end Max11DegreeRoutes
