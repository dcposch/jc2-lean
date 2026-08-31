import Grok68TerminalClosurePropagationScratch

/-! # Vanishing-A jet on the `q=0` support wall

Chamber 1 of `Grok68TerminalClosurePropagationScratch` is the nonzero-`Fce`
vanishing-A residual of
`fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68`.
The unused rows there are exactly `A_(2N-1)=A_(2N-2)=A_(2N-3)=0`.

This file consumes those three rows.  Substituting them into the cusp and
the first three discriminant jets forces the logarithmic jets of `B` and
`c` to agree through order three.  The first three compensated-`I4`
product jets then force the same agreement between `e` and `-c_Cc d / B_D`.

Exact degree bookkeeping: `deg A` remains `2N` (the leading coefficient is
untouched).  The comparison polynomials
`c_Cc X^N B - B_D c` and `B_D e + c_Cc X^N d` drop from degree `Cc` and `E`
to at most `Cc-4` and `E-4`.

This is not a closure.  The next unused source row is `A_(2N-4)`, equally
the coefficient `Cc-4` of the `B`/`c` comparison polynomial.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAJet68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Algebraic jet matching -/

/-- Order-one discriminant plus the cusp, after `A_(p-1)=0`, equate the
first logarithmic jets of `B` and `c`. -/
theorem fiveToSix_qZero_vanishingA_Bc_jet_one_algebra68
    (a b c b1 c1 : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hD1 : (2 : k) * a * b * b1 + (6 : k) * c * c1 = 0) :
    c * b1 - b * c1 = 0 := by
  have hmul : a * b * (c * b1 - b * c1) = 0 := by
    linear_combination (c * (1 / 2 : k)) * hD1 - c1 * hcusp
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero ha hb)

/-- The quadratic form `a b1² + 3 c1²` vanishes once the first jets match. -/
theorem fiveToSix_qZero_vanishingA_Bc_sq_algebra68
    (a b c b1 c1 : k)
    (hb : b ≠ 0)
    (hD1half : a * b * b1 + (3 : k) * c * c1 = 0)
    (h1 : c * b1 - b * c1 = 0) :
    a * b1 ^ 2 + (3 : k) * c1 ^ 2 = 0 := by
  have hmul : b * (a * b1 ^ 2 + (3 : k) * c1 ^ 2) = 0 := by
    linear_combination b1 * hD1half - (3 : k) * c1 * h1
  exact (mul_eq_zero.mp hmul).resolve_left hb

/-- Order-two discriminant after `A_(p-1)=A_(p-2)=0`. -/
theorem fiveToSix_qZero_vanishingA_Bc_jet_two_algebra68
    (a b c b1 c1 b2 c2 : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hD1 : (2 : k) * a * b * b1 + (6 : k) * c * c1 = 0)
    (hD2 : a * ((2 : k) * b * b2 + b1 ^ 2) +
      (3 : k) * ((2 : k) * c * c2 + c1 ^ 2) = 0)
    (h1 : c * b1 - b * c1 = 0) :
    c * b2 - b * c2 = 0 := by
  have hD1half : a * b * b1 + (3 : k) * c * c1 = 0 := by
    linear_combination (1 / 2 : k) * hD1
  have hsq : a * b1 ^ 2 + (3 : k) * c1 ^ 2 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_sq_algebra68 a b c b1 c1 hb hD1half h1
  have hmul : (2 : k) * a * b * (c * b2 - b * c2) = 0 := by
    linear_combination c * hD2 - (2 : k) * c2 * hcusp - c * hsq
  have h2 : (2 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hmul).resolve_left
    (mul_ne_zero (mul_ne_zero h2 ha) hb)

/-- The mixed product `a b1 b2 + 3 c1 c2` vanishes once both jets match. -/
theorem fiveToSix_qZero_vanishingA_Bc_cross_algebra68
    (a b c b1 c1 b2 c2 : k)
    (hb : b ≠ 0)
    (hD1half : a * b * b1 + (3 : k) * c * c1 = 0)
    (h2 : c * b2 - b * c2 = 0) :
    a * b1 * b2 + (3 : k) * c1 * c2 = 0 := by
  have hmul : b * (a * b1 * b2 + (3 : k) * c1 * c2) = 0 := by
    linear_combination b2 * hD1half - (3 : k) * c1 * h2
  exact (mul_eq_zero.mp hmul).resolve_left hb

/-- Order-three discriminant after `A_(p-1)=A_(p-2)=A_(p-3)=0`. -/
theorem fiveToSix_qZero_vanishingA_Bc_jet_three_algebra68
    (a b c b1 c1 b2 c2 b3 c3 : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hD1 : (2 : k) * a * b * b1 + (6 : k) * c * c1 = 0)
    (hD3 : a * ((2 : k) * b * b3 + (2 : k) * b1 * b2) +
      (6 : k) * (c * c3 + c1 * c2) = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0) :
    c * b3 - b * c3 = 0 := by
  have hD1half : a * b * b1 + (3 : k) * c * c1 = 0 := by
    linear_combination (1 / 2 : k) * hD1
  have hD3half : a * (b * b3 + b1 * b2) +
      (3 : k) * (c * c3 + c1 * c2) = 0 := by
    linear_combination (1 / 2 : k) * hD3
  have hcross : a * b1 * b2 + (3 : k) * c1 * c2 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_cross_algebra68
      a b c b1 c1 b2 c2 hb hD1half h2
  have hmul : a * b * (c * b3 - b * c3) = 0 := by
    linear_combination c * hD3half - c3 * hcusp - c * hcross
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero ha hb)

/-- Convolution identity: a `B`/`c` matching and an `e`/`d` incidence
produce the crossed incidence. -/
theorem fiveToSix_qZero_vanishingA_ed_cross_algebra68
    (b c b' c' e' d' : k)
    (hb : b ≠ 0)
    (hBe : b * e' + c * d' = 0)
    (hBc : c * b' - b * c' = 0) :
    b' * e' + c' * d' = 0 := by
  have hmul : b * (b' * e' + c' * d') = 0 := by
    linear_combination b' * hBe - d' * hBc
  exact (mul_eq_zero.mp hmul).resolve_left hb

/-- Order-one compensated `I4` after the first `B`/`c` matching. -/
theorem fiveToSix_qZero_vanishingA_ed_jet_one_algebra68
    (b c b1 c1 e0 e1 d0 d1 : k)
    (hb : b ≠ 0)
    (hI40 : b * e0 + c * d0 = 0)
    (hI41 : b1 * e0 + b * e1 + c1 * d0 + c * d1 = 0)
    (h1 : c * b1 - b * c1 = 0) :
    b * e1 + c * d1 = 0 := by
  have hmul : b * (b * e1 + c * d1) = 0 := by
    linear_combination b * hI41 - b1 * hI40 + d0 * h1
  exact (mul_eq_zero.mp hmul).resolve_left hb

/-- Order-two compensated `I4` after the first two `B`/`c` matchings. -/
theorem fiveToSix_qZero_vanishingA_ed_jet_two_algebra68
    (b c b1 c1 b2 c2 e0 e1 e2 d0 d1 d2 : k)
    (hb : b ≠ 0)
    (hI40 : b * e0 + c * d0 = 0)
    (hI42 : b2 * e0 + b1 * e1 + b * e2 +
      c2 * d0 + c1 * d1 + c * d2 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (hE1 : b * e1 + c * d1 = 0) :
    b * e2 + c * d2 = 0 := by
  have hcross : b1 * e1 + c1 * d1 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68
      b c b1 c1 e1 d1 hb hE1 h1
  have hmul : b * (b * e2 + c * d2) = 0 := by
    linear_combination b * hI42 - b2 * hI40 + d0 * h2 - b * hcross
  exact (mul_eq_zero.mp hmul).resolve_left hb

/-- Order-three compensated `I4` after the first three `B`/`c` matchings. -/
theorem fiveToSix_qZero_vanishingA_ed_jet_three_algebra68
    (b c b1 c1 b2 c2 b3 c3 e0 e1 e2 e3 d0 d1 d2 d3 : k)
    (hb : b ≠ 0)
    (hI40 : b * e0 + c * d0 = 0)
    (hI43 : b3 * e0 + b2 * e1 + b1 * e2 + b * e3 +
      c3 * d0 + c2 * d1 + c1 * d2 + c * d3 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (h3 : c * b3 - b * c3 = 0)
    (hE1 : b * e1 + c * d1 = 0)
    (hE2 : b * e2 + c * d2 = 0) :
    b * e3 + c * d3 = 0 := by
  have hcross21 : b2 * e1 + c2 * d1 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68
      b c b2 c2 e1 d1 hb hE1 h2
  have hcross12 : b1 * e2 + c1 * d2 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68
      b c b1 c1 e2 d2 hb hE2 h1
  have hmul : b * (b * e3 + c * d3) = 0 := by
    linear_combination b * hI43 - b3 * hI40 + d0 * h3 -
      b * hcross21 - b * hcross12
  exact (mul_eq_zero.mp hmul).resolve_left hb

/-! ## Coefficient of the monomial comparison polynomials -/

theorem fiveToSix_qZero_C_X_pow_mul_coeff68
    (r : k) (p : k[X]) (n m : ℕ) :
    (C r * X ^ n * p).coeff (n + m) = r * p.coeff m := by
  rw [mul_assoc, coeff_C_mul, add_comm n m, coeff_X_pow_mul]

/-! ## Source-backed jets -/

/-- The three vanishing `A` rows force `B`/`c` matching through order
three. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    c.coeff Cc * B.coeff (D - 1) - B.coeff D * c.coeff (Cc - 1) = 0 ∧
      c.coeff Cc * B.coeff (D - 2) - B.coeff D * c.coeff (Cc - 2) = 0 ∧
      c.coeff Cc * B.coeff (D - 3) - B.coeff D * c.coeff (Cc - 3) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  change c.coeff Cc * B.coeff (D - 1) - B.coeff D * c.coeff (Cc - 1) = 0 ∧
    c.coeff Cc * B.coeff (D - 2) - B.coeff D * c.coeff (Cc - 2) = 0 ∧
    c.coeff Cc * B.coeff (D - 3) - B.coeff D * c.coeff (Cc - 3) = 0
  have hAvan :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68]
    at hAvan
  rcases hAvan with ⟨ha1, ha2, ha3⟩
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
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have ha0 : A.coeff p ≠ 0 := by simpa [p] using hatop
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hD0 : A.coeff p * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    simpa [p, D, Cc, hGS] using hcuspEq
  have hD1raw :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD2raw :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD3raw :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_third68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hD1raw hD2raw hD3raw
  have hD1 : (2 : k) * A.coeff p * B.coeff D * B.coeff (D - 1) +
      (6 : k) * c.coeff Cc * c.coeff (Cc - 1) = 0 := by
    rw [ha1] at hD1raw
    linear_combination hD1raw
  have hD2 : A.coeff p *
        ((2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2) +
      (3 : k) * ((2 : k) * c.coeff Cc * c.coeff (Cc - 2) +
        c.coeff (Cc - 1) ^ 2) = 0 := by
    rw [ha1, ha2] at hD2raw
    linear_combination hD2raw
  have hD3 : A.coeff p *
        ((2 : k) * B.coeff D * B.coeff (D - 3) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 2)) +
      (6 : k) * (c.coeff Cc * c.coeff (Cc - 3) +
        c.coeff (Cc - 1) * c.coeff (Cc - 2)) = 0 := by
    rw [ha1, ha2, ha3] at hD3raw
    linear_combination hD3raw
  have h1 : c.coeff Cc * B.coeff (D - 1) -
      B.coeff D * c.coeff (Cc - 1) = 0 :=
    fiveToSix_qZero_vanishingA_Bc_jet_one_algebra68
      (A.coeff p) (B.coeff D) (c.coeff Cc)
      (B.coeff (D - 1)) (c.coeff (Cc - 1)) ha0 hb0 hD0 hD1
  have h2 : c.coeff Cc * B.coeff (D - 2) -
      B.coeff D * c.coeff (Cc - 2) = 0 :=
    fiveToSix_qZero_vanishingA_Bc_jet_two_algebra68
      (A.coeff p) (B.coeff D) (c.coeff Cc)
      (B.coeff (D - 1)) (c.coeff (Cc - 1))
      (B.coeff (D - 2)) (c.coeff (Cc - 2)) ha0 hb0 hD0 hD1 hD2 h1
  have h3 : c.coeff Cc * B.coeff (D - 3) -
      B.coeff D * c.coeff (Cc - 3) = 0 :=
    fiveToSix_qZero_vanishingA_Bc_jet_three_algebra68
      (A.coeff p) (B.coeff D) (c.coeff Cc)
      (B.coeff (D - 1)) (c.coeff (Cc - 1))
      (B.coeff (D - 2)) (c.coeff (Cc - 2))
      (B.coeff (D - 3)) (c.coeff (Cc - 3)) ha0 hb0 hD0 hD1 hD3 h1 h2
  exact ⟨h1, h2, h3⟩

/-- The three `B`/`c` matchings force `e`/`d` incidence through order
three. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    B.coeff D * e.coeff (E - 1) + c.coeff Cc * d.coeff (V - 1) = 0 ∧
      B.coeff D * e.coeff (E - 2) + c.coeff Cc * d.coeff (V - 2) = 0 ∧
      B.coeff D * e.coeff (E - 3) + c.coeff Cc * d.coeff (V - 3) = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  change B.coeff D * e.coeff (E - 1) + c.coeff Cc * d.coeff (V - 1) = 0 ∧
    B.coeff D * e.coeff (E - 2) + c.coeff Cc * d.coeff (V - 2) = 0 ∧
    B.coeff D * e.coeff (E - 3) + c.coeff Cc * d.coeff (V - 3) = 0
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc
  rcases hBc with ⟨h1, h2, h3⟩
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
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hI41 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI42 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI43 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_I4_third68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hI40 hI41 hI42 hI43
  have hE1 : B.coeff D * e.coeff (E - 1) +
      c.coeff Cc * d.coeff (V - 1) = 0 :=
    fiveToSix_qZero_vanishingA_ed_jet_one_algebra68
      (B.coeff D) (c.coeff Cc)
      (B.coeff (D - 1)) (c.coeff (Cc - 1))
      (e.coeff E) (e.coeff (E - 1))
      (d.coeff V) (d.coeff (V - 1)) hb0 hI40 hI41 h1
  have hE2 : B.coeff D * e.coeff (E - 2) +
      c.coeff Cc * d.coeff (V - 2) = 0 :=
    fiveToSix_qZero_vanishingA_ed_jet_two_algebra68
      (B.coeff D) (c.coeff Cc)
      (B.coeff (D - 1)) (c.coeff (Cc - 1))
      (B.coeff (D - 2)) (c.coeff (Cc - 2))
      (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2))
      (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2))
      hb0 hI40 hI42 h1 h2 hE1
  have hE3 : B.coeff D * e.coeff (E - 3) +
      c.coeff Cc * d.coeff (V - 3) = 0 :=
    fiveToSix_qZero_vanishingA_ed_jet_three_algebra68
      (B.coeff D) (c.coeff Cc)
      (B.coeff (D - 1)) (c.coeff (Cc - 1))
      (B.coeff (D - 2)) (c.coeff (Cc - 2))
      (B.coeff (D - 3)) (c.coeff (Cc - 3))
      (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
      (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
      hb0 hI40 hI43 h1 h2 h3 hE1 hE2
  exact ⟨hE1, hE2, hE3⟩

/-! ## Degree bookkeeping -/

/-- `A` keeps exact degree `2N`; only the three subleading coefficients
vanish. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    A.natDegree = p ∧ A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧
      A.coeff (p - 3) = 0 := by
  let p := 2 * N
  change A.natDegree = p ∧ A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧
    A.coeff (p - 3) = 0
  have hAvan :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingA68]
    at hAvan
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
  have ha0 : A.coeff p ≠ 0 := by simpa [p] using hatop
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero hA' ha0, hAvan⟩

/-- The `B`/`c` comparison polynomial drops at least four degrees. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ Cc - 4 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let R := C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c
  change R.natDegree ≤ Cc - 4
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc
  rcases hBc with ⟨h1, h2, h3⟩
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
  rcases hpacket with ⟨hN, hgt, hle, hA, hBdeg, hcdeg, hd0, he0, hatop,
    hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hBdeg
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hcdeg
  have hND : N + D = Cc := by dsimp only [D, Cc]; omega
  have hle : R.natDegree ≤ Cc := by
    dsimp only [R]
    compute_degree
    omega
  have hcoeff0 : R.coeff Cc = 0 := by
    dsimp only [R]
    have hL : (C (c.coeff Cc) * X ^ N * B).coeff Cc =
        c.coeff Cc * B.coeff D := by
      rw [← hND, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_sub, hL, coeff_C_mul]
    ring
  have hcoeff1 : R.coeff (Cc - 1) = 0 := by
    dsimp only [R]
    have hidx : Cc - 1 = N + (D - 1) := by omega
    have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - 1) =
        c.coeff Cc * B.coeff (D - 1) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_sub, hL, coeff_C_mul]
    linear_combination h1
  have hcoeff2 : R.coeff (Cc - 2) = 0 := by
    dsimp only [R]
    have hidx : Cc - 2 = N + (D - 2) := by omega
    have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - 2) =
        c.coeff Cc * B.coeff (D - 2) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_sub, hL, coeff_C_mul]
    linear_combination h2
  have hcoeff3 : R.coeff (Cc - 3) = 0 := by
    dsimp only [R]
    have hidx : Cc - 3 = N + (D - 3) := by omega
    have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - 3) =
        c.coeff Cc * B.coeff (D - 3) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_sub, hL, coeff_C_mul]
    linear_combination h3
  have h4 : 4 ≤ Cc := by dsimp only [Cc]; omega
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : Cc < n
  · exact coeff_eq_zero_of_natDegree_lt (hle.trans_lt hgt)
  · have : n = Cc ∨ n = Cc - 1 ∨ n = Cc - 2 ∨ n = Cc - 3 := by omega
    rcases this with hn0 | hn1 | hn2 | hn3
    · simpa [hn0] using hcoeff0
    · simpa [hn1] using hcoeff1
    · simpa [hn2] using hcoeff2
    · simpa [hn3] using hcoeff3

/-- The `e`/`d` comparison polynomial drops at least four degrees. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - 4 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let R := C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d
  change R.natDegree ≤ E - 4
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hEd
  rcases hEd with ⟨hE1, hE2, hE3⟩
  have hI40 :
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V = 0 := by
    simpa [D, Cc, V, E] using
      (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hBdeg, hcdeg, hd0, he0, hatop,
    hcusp, had⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hd' : d.natDegree ≤ V := by
    dsimp only [V]; rw [hGS] at hd; omega
  have he' : e.natDegree ≤ E := by
    dsimp only [E]; rw [hGS] at hedeg; omega
  have hNV : N + V = E := by dsimp only [V, E]; omega
  have hle : R.natDegree ≤ E := by
    dsimp only [R]
    compute_degree
    omega
  have hcoeff0 : R.coeff E = 0 := by
    dsimp only [R]
    have hR : (C (c.coeff Cc) * X ^ N * d).coeff E =
        c.coeff Cc * d.coeff V := by
      rw [← hNV, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_add, coeff_C_mul, hR]
    linear_combination hI40
  have hcoeff1 : R.coeff (E - 1) = 0 := by
    dsimp only [R]
    have hidx : E - 1 = N + (V - 1) := by omega
    have hR : (C (c.coeff Cc) * X ^ N * d).coeff (E - 1) =
        c.coeff Cc * d.coeff (V - 1) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_add, coeff_C_mul, hR]
    linear_combination hE1
  have hcoeff2 : R.coeff (E - 2) = 0 := by
    dsimp only [R]
    have hidx : E - 2 = N + (V - 2) := by omega
    have hR : (C (c.coeff Cc) * X ^ N * d).coeff (E - 2) =
        c.coeff Cc * d.coeff (V - 2) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_add, coeff_C_mul, hR]
    linear_combination hE2
  have hcoeff3 : R.coeff (E - 3) = 0 := by
    dsimp only [R]
    have hidx : E - 3 = N + (V - 3) := by omega
    have hR : (C (c.coeff Cc) * X ^ N * d).coeff (E - 3) =
        c.coeff Cc * d.coeff (V - 3) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_add, coeff_C_mul, hR]
    linear_combination hE3
  have h4 : 4 ≤ E := by dsimp only [E]; omega
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : E < n
  · exact coeff_eq_zero_of_natDegree_lt (hle.trans_lt hgt)
  · have : n = E ∨ n = E - 1 ∨ n = E - 2 ∨ n = E - 3 := by omega
    rcases this with hn0 | hn1 | hn2 | hn3
    · simpa [hn0] using hcoeff0
    · simpa [hn1] using hcoeff1
    · simpa [hn2] using hcoeff2
    · simpa [hn3] using hcoeff3

/-! ## Residual packet -/

/-- Residual after consuming `A_(2N-1)=A_(2N-2)=A_(2N-3)=0`.  The three
vanishing `A` rows remain recorded; the new content is the order-three
`B`/`c` and `e`/`d` jets together with the two degree drops.  The next
unused source coefficient is `A_(2N-4)`. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAJetResidual68
    (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  A.natDegree = p ∧
    A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧ A.coeff (p - 3) = 0 ∧
    c.coeff Cc * B.coeff (D - 1) - B.coeff D * c.coeff (Cc - 1) = 0 ∧
    c.coeff Cc * B.coeff (D - 2) - B.coeff D * c.coeff (Cc - 2) = 0 ∧
    c.coeff Cc * B.coeff (D - 3) - B.coeff D * c.coeff (Cc - 3) = 0 ∧
    B.coeff D * e.coeff (E - 1) + c.coeff Cc * d.coeff (V - 1) = 0 ∧
    B.coeff D * e.coeff (E - 2) + c.coeff Cc * d.coeff (V - 2) = 0 ∧
    B.coeff D * e.coeff (E - 3) + c.coeff Cc * d.coeff (V - 3) = 0 ∧
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ Cc - 4 ∧
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - 4

/-- Source-backed residual of chamber 1 after consuming the three vanishing
top rows of `A`.  `Fce.coeff 0` remains nonzero.  Not a closure. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_jet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
        (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 ≠ 0 ∧
      FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAJetResidual68
        A B c d e N S := by
  refine ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq, ?_⟩
  have hA :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hBcDeg :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hEdDeg :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only
    [FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAJetResidual68]
    at hA hBc hEd hBcDeg hEdDeg ⊢
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hBc.1, hBc.2.1, hBc.2.2,
    hEd.1, hEd.2.1, hEd.2.2, hBcDeg, hEdDeg⟩

#print axioms fiveToSix_qZero_vanishingA_Bc_jet_one_algebra68
#print axioms fiveToSix_qZero_vanishingA_Bc_sq_algebra68
#print axioms fiveToSix_qZero_vanishingA_Bc_jet_two_algebra68
#print axioms fiveToSix_qZero_vanishingA_Bc_cross_algebra68
#print axioms fiveToSix_qZero_vanishingA_Bc_jet_three_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_cross_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_jet_one_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_jet_two_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_jet_three_algebra68
#print axioms fiveToSix_qZero_C_X_pow_mul_coeff68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_jet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAJet68

end Max11DegreeRoutes
