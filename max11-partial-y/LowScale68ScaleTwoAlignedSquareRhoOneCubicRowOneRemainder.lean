import LowScale68ScaleTwoAlignedSquareRhoOneCubicComponentOne

/-! # Source-valid lower-row-one remainder on the zero-septic cubic branch -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicRowOneRemainder68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicRowOneRemainderHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Algebraic form of the improved-weight-eleven lower-row-one face. -/
def lowerRowOneCubicWeightElevenAlg68
    (A B C D E dA dB dC dD dE : k) : k :=
  (8 / 3 : k) * E * dE + (4 / 27 : k) * A ^ 2 * B ^ 2 * dA -
  (8 / 27 : k) * A ^ 2 * C * dC -
  (8 / 27 : k) * A ^ 2 * D * dB -
  (8 / 27 : k) * A ^ 2 * B * dD +
  (16 / 81 : k) * A ^ 3 * B * dB -
  (8 / 9 : k) * C * E * dA - (4 / 9 : k) * D ^ 2 * dA

/-- All monomials of improved weight strictly below eleven in lower row one. -/
def lowerRowOneCubicLowerAlg68
    (beta gamma delta epsilon zeta : k)
    (A B C D E dA dB dC dD dE : k) : k :=
  zeta * dD - delta * C * dB - (2 / 3 : k) * epsilon * C * dA +
  2 * epsilon * dE - (1 / 2 : k) * delta * D * dA -
  (1 / 3 : k) * delta * A ^ 2 * dB -
  (2 / 3 : k) * gamma * D * dB - (4 / 3 : k) * gamma * C * dC +
  (1 / 2 : k) * delta * A * dD + (2 / 3 : k) * gamma * B * dD -
  (4 / 9 : k) * gamma * A * C * dA -
  (4 / 9 : k) * gamma * A ^ 2 * dC -
  (5 / 6 : k) * beta * C * dD - (5 / 6 : k) * beta * D * dC +
  (4 / 3 : k) * gamma * A * dE +
  (5 / 18 : k) * beta * A * C * dB +
  (5 / 18 : k) * beta * B * C * dA +
  (5 / 3 : k) * beta * B * dE -
  (25 / 72 : k) * beta * A ^ 2 * dD -
  (5 / 12 : k) * beta * A * D * dA +
  (5 / 18 : k) * beta * A ^ 2 * B * dA +
  (5 / 54 : k) * beta * A ^ 3 * dB -
  (4 / 3 : k) * C * D * dB - (4 / 9 : k) * B * C * dD -
  (4 / 9 : k) * B * D * dC - (8 / 9 : k) * C ^ 2 * dC +
  (16 / 27 : k) * A * B * C * dB +
  (4 / 9 : k) * B ^ 2 * dE + (8 / 27 : k) * B ^ 2 * C * dA

/-- After introducing the cubic defects, the complete lower row one is
its weight-eleven face plus a strict lower-weight remainder. -/
theorem lowerRowOneCubic_decomposition68
    {R : Type*} [Field R] [CharZero R] [Algebra k R]
    (d : Derivation k R R)
    (A B C D E alpha beta gamma delta epsilon zeta eta : R)
    (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) :
    let C0 := A ^ 2 / 3 + C
    let E0 := A ^ 3 / 27 + E
    let T := integratedT68 0 A B C0 D E0 alpha beta gamma epsilon
    let U := integratedU68 0 A B C0 D E0 alpha beta gamma delta zeta
    let V := integratedV68 0 A B C0 D E0 alpha beta gamma delta epsilon eta
    U * d D + 2 * T * d E0 - 2 * C0 * d V - D * d U =
      lowerRowOneCubicWeightElevenAlg68 A B C D E (d A) (d B) (d C)
        (d D) (d E) +
      lowerRowOneCubicLowerAlg68 beta gamma delta epsilon zeta
        A B C D E (d A) (d B) (d C) (d D) (d E) := by
  dsimp only
  simp only [integratedT68, integratedU68, integratedV68,
    map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_div, Derivation.leibniz_inv, nsmul_eq_mul,
    smul_eq_mul, map_zero, halpha, hbeta, hgamma, hdelta, hepsilon,
    hzeta, heta]
  simp [derivation_ofNat_zero68 d]
  simp only [lowerRowOneCubicWeightElevenAlg68,
    lowerRowOneCubicLowerAlg68]
  ring

/-- Weighted-monomial presentation of the strict lower-row-one remainder. -/
def lowerRowOneCubicLowerHahn68
    (beta gamma delta epsilon zeta : k)
    (A B C D E dA dB dC dD dE : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 zeta dD A B C D 1 0 0 0 0 +
  weightedMonomial68 (-delta) C dB A B D 1 1 0 0 0 +
  weightedMonomial68 (-(2 / 3 : k) * epsilon) C dA A B D 1 1 0 0 0 +
  weightedMonomial68 (2 * epsilon) dE A B C D 1 0 0 0 0 +
  weightedMonomial68 (-(1 / 2 : k) * delta) D dA A B C 1 1 0 0 0 +
  weightedMonomial68 (-(1 / 3 : k) * delta) A dB B C D 2 1 0 0 0 +
  weightedMonomial68 (-(2 / 3 : k) * gamma) D dB A B C 1 1 0 0 0 +
  weightedMonomial68 (-(4 / 3 : k) * gamma) C dC A B D 1 1 0 0 0 +
  weightedMonomial68 ((1 / 2 : k) * delta) A dD B C D 1 1 0 0 0 +
  weightedMonomial68 ((2 / 3 : k) * gamma) B dD A C D 1 1 0 0 0 +
  weightedMonomial68 (-(4 / 9 : k) * gamma) A C dA B D 1 1 1 0 0 +
  weightedMonomial68 (-(4 / 9 : k) * gamma) A dC B C D 2 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) C dD A B D 1 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) D dC A B C 1 1 0 0 0 +
  weightedMonomial68 ((4 / 3 : k) * gamma) A dE B C D 1 1 0 0 0 +
  weightedMonomial68 ((5 / 18 : k) * beta) A C dB B D 1 1 1 0 0 +
  weightedMonomial68 ((5 / 18 : k) * beta) B C dA A D 1 1 1 0 0 +
  weightedMonomial68 ((5 / 3 : k) * beta) B dE A C D 1 1 0 0 0 +
  weightedMonomial68 (-(25 / 72 : k) * beta) A dD B C D 2 1 0 0 0 +
  weightedMonomial68 (-(5 / 12 : k) * beta) A D dA B C 1 1 1 0 0 +
  weightedMonomial68 ((5 / 18 : k) * beta) A B dA C D 2 1 1 0 0 +
  weightedMonomial68 ((5 / 54 : k) * beta) A dB B C D 3 1 0 0 0 +
  weightedMonomial68 (-4 / 3 : k) C D dB A B 1 1 1 0 0 +
  weightedMonomial68 (-4 / 9 : k) B C dD A D 1 1 1 0 0 +
  weightedMonomial68 (-4 / 9 : k) B D dC A C 1 1 1 0 0 +
  weightedMonomial68 (-8 / 9 : k) C dC A B D 2 1 0 0 0 +
  weightedMonomial68 (16 / 27 : k) A B C dB D 1 1 1 1 0 +
  weightedMonomial68 (4 / 9 : k) B dE A C D 2 1 0 0 0 +
  weightedMonomial68 (8 / 27 : k) B C dA A D 2 1 1 0 0

/-- Every strict lower monomial has zero coefficient at exponent `-11`. -/
theorem lowerRowOneCubicLowerHahn68_coeff_neg11
    (beta gamma delta epsilon zeta : k)
    (A B C D E dA dB dC dD dE : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-5 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (↑(-3 : ℚ) : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (↑(-4 : ℚ) : WithTop ℚ) ≤ dC.orderTop)
    (hdD : (↑(-5 : ℚ) : WithTop ℚ) ≤ dD.orderTop)
    (hdE : (↑(-6 : ℚ) : WithTop ℚ) ≤ dE.orderTop) :
    (lowerRowOneCubicLowerHahn68 beta gamma delta epsilon zeta
      A B C D E dA dB dC dD dE).coeff (-11 : ℚ) = 0 := by
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (-11 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5 n1 n2 n3 n4 n5).coeff
        (-11 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (-11) h1 h2 h3 h4 h5 hlt
  have h1 := hz zeta dD A B C D 1 0 0 0 0 (-5) (-2) (-2) (-3) (-4)
    hdD hA hB hC hD (by norm_num)
  have h2 := hz (-delta) C dB A B D 1 1 0 0 0 (-3) (-3) (-2) (-2) (-4)
    hC hdB hA hB hD (by norm_num)
  have h3 := hz (-(2 / 3 : k) * epsilon) C dA A B D 1 1 0 0 0
    (-3) (-3) (-2) (-2) (-4) hC hdA hA hB hD (by norm_num)
  have h4 := hz (2 * epsilon) dE A B C D 1 0 0 0 0 (-6) (-2) (-2) (-3) (-4)
    hdE hA hB hC hD (by norm_num)
  have h5 := hz (-(1 / 2 : k) * delta) D dA A B C 1 1 0 0 0
    (-4) (-3) (-2) (-2) (-3) hD hdA hA hB hC (by norm_num)
  have h6 := hz (-(1 / 3 : k) * delta) A dB B C D 2 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hA hdB hB hC hD (by norm_num)
  have h7 := hz (-(2 / 3 : k) * gamma) D dB A B C 1 1 0 0 0
    (-4) (-3) (-2) (-2) (-3) hD hdB hA hB hC (by norm_num)
  have h8 := hz (-(4 / 3 : k) * gamma) C dC A B D 1 1 0 0 0
    (-3) (-4) (-2) (-2) (-4) hC hdC hA hB hD (by norm_num)
  have h9 := hz ((1 / 2 : k) * delta) A dD B C D 1 1 0 0 0
    (-2) (-5) (-2) (-3) (-4) hA hdD hB hC hD (by norm_num)
  have h10 := hz ((2 / 3 : k) * gamma) B dD A C D 1 1 0 0 0
    (-2) (-5) (-2) (-3) (-4) hB hdD hA hC hD (by norm_num)
  have h11 := hz (-(4 / 9 : k) * gamma) A C dA B D 1 1 1 0 0
    (-2) (-3) (-3) (-2) (-4) hA hC hdA hB hD (by norm_num)
  have h12 := hz (-(4 / 9 : k) * gamma) A dC B C D 2 1 0 0 0
    (-2) (-4) (-2) (-3) (-4) hA hdC hB hC hD (by norm_num)
  have h13 := hz (-(5 / 6 : k) * beta) C dD A B D 1 1 0 0 0
    (-3) (-5) (-2) (-2) (-4) hC hdD hA hB hD (by norm_num)
  have h14 := hz (-(5 / 6 : k) * beta) D dC A B C 1 1 0 0 0
    (-4) (-4) (-2) (-2) (-3) hD hdC hA hB hC (by norm_num)
  have h15 := hz ((4 / 3 : k) * gamma) A dE B C D 1 1 0 0 0
    (-2) (-6) (-2) (-3) (-4) hA hdE hB hC hD (by norm_num)
  have h16 := hz ((5 / 18 : k) * beta) A C dB B D 1 1 1 0 0
    (-2) (-3) (-3) (-2) (-4) hA hC hdB hB hD (by norm_num)
  have h17 := hz ((5 / 18 : k) * beta) B C dA A D 1 1 1 0 0
    (-2) (-3) (-3) (-2) (-4) hB hC hdA hA hD (by norm_num)
  have h18 := hz ((5 / 3 : k) * beta) B dE A C D 1 1 0 0 0
    (-2) (-6) (-2) (-3) (-4) hB hdE hA hC hD (by norm_num)
  have h19 := hz (-(25 / 72 : k) * beta) A dD B C D 2 1 0 0 0
    (-2) (-5) (-2) (-3) (-4) hA hdD hB hC hD (by norm_num)
  have h20 := hz (-(5 / 12 : k) * beta) A D dA B C 1 1 1 0 0
    (-2) (-4) (-3) (-2) (-3) hA hD hdA hB hC (by norm_num)
  have h21 := hz ((5 / 18 : k) * beta) A B dA C D 2 1 1 0 0
    (-2) (-2) (-3) (-3) (-4) hA hB hdA hC hD (by norm_num)
  have h22 := hz ((5 / 54 : k) * beta) A dB B C D 3 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hA hdB hB hC hD (by norm_num)
  have h23 := hz (-4 / 3 : k) C D dB A B 1 1 1 0 0
    (-3) (-4) (-3) (-2) (-2) hC hD hdB hA hB (by norm_num)
  have h24 := hz (-4 / 9 : k) B C dD A D 1 1 1 0 0
    (-2) (-3) (-5) (-2) (-4) hB hC hdD hA hD (by norm_num)
  have h25 := hz (-4 / 9 : k) B D dC A C 1 1 1 0 0
    (-2) (-4) (-4) (-2) (-3) hB hD hdC hA hC (by norm_num)
  have h26 := hz (-8 / 9 : k) C dC A B D 2 1 0 0 0
    (-3) (-4) (-2) (-2) (-4) hC hdC hA hB hD (by norm_num)
  have h27 := hz (16 / 27 : k) A B C dB D 1 1 1 1 0
    (-2) (-2) (-3) (-3) (-4) hA hB hC hdB hD (by norm_num)
  have h28 := hz (4 / 9 : k) B dE A C D 2 1 0 0 0
    (-2) (-6) (-2) (-3) (-4) hB hdE hA hC hD (by norm_num)
  have h29 := hz (8 / 27 : k) B C dA A D 2 1 1 0 0
    (-2) (-3) (-3) (-2) (-4) hB hC hdA hA hD (by norm_num)
  simp only [lowerRowOneCubicLowerHahn68, HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h28, h29]
  ring

end AlignedSquareRhoOneCubicRowOneRemainder68

end Max11DegreeRoutes
