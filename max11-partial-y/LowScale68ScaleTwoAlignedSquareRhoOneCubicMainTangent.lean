import LowScale68ScaleTwoAlignedSquareRhoOneCubicRowOneSource

/-! # The next lower-row-one face on the zero-septic main tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicMainTangent68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicMainTangentHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def rhoOneTangentDDefectHahn68
    (A B D : HahnSeries ℚ k) : HahnSeries ℚ k :=
  D - HahnSeries.C (1 / 3 : k) * A * B

def rhoOneTangentEDefectHahn68
    (A C E : HahnSeries ℚ k) : HahnSeries ℚ k :=
  E - HahnSeries.C (1 / 3 : k) * A * C

/-- Scalar of the first lower-row-one face after removing the entire
main tangent, with `f,g` the two transverse tangent-defect coefficients. -/
def rhoOneZeroLCubicMainTangentOne68 (a b c f g : k) : k :=
  -2 * a * b ^ 2 * c + 9 * c ^ 3 + 7 * a ^ 2 * b * f -
    21 * a * c * g

def lowerRowOneMainTangentWeightTenAlg68
    (A B C F G dA dB dC dF dG : k) : k :=
  (-8 / 27 : k) * A * B * F * dA -
  (8 / 27 : k) * A ^ 2 * B * dF -
  (8 / 27 : k) * A ^ 2 * F * dB -
  (8 / 9 : k) * C ^ 2 * dC +
  (8 / 27 : k) * B ^ 2 * C * dA +
  (8 / 9 : k) * A * C * dG + (8 / 9 : k) * A * G * dC

def lowerRowOneMainTangentLowerAlg68
    (beta gamma delta epsilon zeta : k)
    (A B C F G dA dB dC dF dG : k) : k :=
  zeta * dF + (1 / 3 : k) * A * zeta * dB +
  (1 / 3 : k) * B * zeta * dA + 2 * epsilon * dG -
  delta * C * dB - (1 / 2 : k) * delta * F * dA -
  (2 / 3 : k) * gamma * F * dB +
  (1 / 2 : k) * delta * A * dF +
  (2 / 3 : k) * epsilon * A * dC +
  (2 / 3 : k) * gamma * B * dF -
  (1 / 6 : k) * delta * A ^ 2 * dB -
  (4 / 3 : k) * gamma * C * dC -
  (5 / 6 : k) * beta * C * dF -
  (5 / 6 : k) * beta * F * dC +
  (2 / 9 : k) * gamma * B ^ 2 * dA +
  (4 / 3 : k) * gamma * A * dG +
  (5 / 3 : k) * beta * B * dG -
  (25 / 72 : k) * beta * A ^ 2 * dF -
  (5 / 12 : k) * beta * A * F * dA +
  (5 / 18 : k) * beta * A * B * dC +
  (5 / 9 : k) * beta * B * C * dA -
  (4 / 3 : k) * C * F * dB - (4 / 9 : k) * B * C * dF -
  (4 / 9 : k) * B * F * dC - (4 / 9 : k) * F ^ 2 * dA -
  (5 / 216 : k) * beta * A ^ 3 * dB +
  (4 / 9 : k) * B ^ 2 * dG +
  (5 / 216 : k) * beta * A ^ 2 * B * dA +
  (8 / 3 : k) * G * dG

theorem lowerRowOneMainTangent_decomposition68
    {R : Type*} [Field R] [CharZero R] [Algebra k R]
    (d : Derivation k R R)
    (A B C F G alpha beta gamma delta epsilon zeta eta : R)
    (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) :
    let C0 := A ^ 2 / 3 + C
    let D := A * B / 3 + F
    let E := A ^ 3 / 27 + A * C / 3 + G
    let T := integratedT68 0 A B C0 D E alpha beta gamma epsilon
    let U := integratedU68 0 A B C0 D E alpha beta gamma delta zeta
    let V := integratedV68 0 A B C0 D E alpha beta gamma delta epsilon eta
    U * d D + 2 * T * d E - 2 * C0 * d V - D * d U =
      lowerRowOneMainTangentWeightTenAlg68 A B C F G
        (d A) (d B) (d C) (d F) (d G) +
      lowerRowOneMainTangentLowerAlg68 beta gamma delta epsilon zeta
        A B C F G (d A) (d B) (d C) (d F) (d G) := by
  dsimp only
  simp only [integratedT68, integratedU68, integratedV68,
    map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_div, Derivation.leibniz_inv, nsmul_eq_mul,
    smul_eq_mul, map_zero, halpha, hbeta, hgamma, hdelta, hepsilon,
    hzeta, heta]
  simp [derivation_ofNat_zero68 d]
  simp only [lowerRowOneMainTangentWeightTenAlg68,
    lowerRowOneMainTangentLowerAlg68]
  ring

def lowerRowOneMainTangentWeightTenHahn68
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 (-8 / 27 : k) A B F dA G 1 1 1 1 0 +
  weightedMonomial68 (-8 / 27 : k) A B dF C G 2 1 1 0 0 +
  weightedMonomial68 (-8 / 27 : k) A F dB C G 2 1 1 0 0 +
  weightedMonomial68 (-8 / 9 : k) C dC A B G 2 1 0 0 0 +
  weightedMonomial68 (8 / 27 : k) B C dA A G 2 1 1 0 0 +
  weightedMonomial68 (8 / 9 : k) A C dG B G 1 1 1 0 0 +
  weightedMonomial68 (8 / 9 : k) A G dC B F 1 1 1 0 0

def lowerRowOneMainTangentLowerHahn68
    (beta gamma delta epsilon zeta : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 zeta dF A B C F 1 0 0 0 0 +
  weightedMonomial68 ((1 / 3 : k) * zeta) A dB B C F 1 1 0 0 0 +
  weightedMonomial68 ((1 / 3 : k) * zeta) B dA A C F 1 1 0 0 0 +
  weightedMonomial68 (2 * epsilon) dG A B C F 1 0 0 0 0 +
  weightedMonomial68 (-delta) C dB A B F 1 1 0 0 0 +
  weightedMonomial68 (-(1 / 2 : k) * delta) F dA A B C 1 1 0 0 0 +
  weightedMonomial68 (-(2 / 3 : k) * gamma) F dB A B C 1 1 0 0 0 +
  weightedMonomial68 ((1 / 2 : k) * delta) A dF B C F 1 1 0 0 0 +
  weightedMonomial68 ((2 / 3 : k) * epsilon) A dC B C F 1 1 0 0 0 +
  weightedMonomial68 ((2 / 3 : k) * gamma) B dF A C F 1 1 0 0 0 +
  weightedMonomial68 (-(1 / 6 : k) * delta) A dB B C F 2 1 0 0 0 +
  weightedMonomial68 (-(4 / 3 : k) * gamma) C dC A B F 1 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) C dF A B F 1 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) F dC A B C 1 1 0 0 0 +
  weightedMonomial68 ((2 / 9 : k) * gamma) B dA A C F 2 1 0 0 0 +
  weightedMonomial68 ((4 / 3 : k) * gamma) A dG B C F 1 1 0 0 0 +
  weightedMonomial68 ((5 / 3 : k) * beta) B dG A C F 1 1 0 0 0 +
  weightedMonomial68 (-(25 / 72 : k) * beta) A dF B C F 2 1 0 0 0 +
  weightedMonomial68 (-(5 / 12 : k) * beta) A F dA B C 1 1 1 0 0 +
  weightedMonomial68 ((5 / 18 : k) * beta) A B dC C F 1 1 1 0 0 +
  weightedMonomial68 ((5 / 9 : k) * beta) B C dA A F 1 1 1 0 0 +
  weightedMonomial68 (-4 / 3 : k) C F dB A B 1 1 1 0 0 +
  weightedMonomial68 (-4 / 9 : k) B C dF A F 1 1 1 0 0 +
  weightedMonomial68 (-4 / 9 : k) B F dC A C 1 1 1 0 0 +
  weightedMonomial68 (-4 / 9 : k) F dA A B C 2 1 0 0 0 +
  weightedMonomial68 (-(5 / 216 : k) * beta) A dB B C F 3 1 0 0 0 +
  weightedMonomial68 (4 / 9 : k) B dG A C F 2 1 0 0 0 +
  weightedMonomial68 ((5 / 216 : k) * beta) A B dA C F 2 1 1 0 0 +
  weightedMonomial68 (8 / 3 : k) G dG A B C 1 1 0 0 0

theorem lowerRowOneMainTangentLowerHahn68_coeff_neg10
    (beta gamma delta epsilon zeta : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-4 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (↑(-3 : ℚ) : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (↑(-4 : ℚ) : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (↑(-4 : ℚ) : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-5 : ℚ) : WithTop ℚ) ≤ dG.orderTop) :
    (lowerRowOneMainTangentLowerHahn68 beta gamma delta epsilon zeta
      A B C F G dA dB dC dF dG).coeff (-10 : ℚ) = 0 := by
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (-10 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5 n1 n2 n3 n4 n5).coeff
        (-10 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (-10) h1 h2 h3 h4 h5 hlt
  have h1 := hz zeta dF A B C F 1 0 0 0 0 (-4) (-2) (-2) (-3) (-3)
    hdF hA hB hC hF (by norm_num)
  have h2 := hz ((1 / 3 : k) * zeta) A dB B C F 1 1 0 0 0
    (-2) (-3) (-2) (-3) (-3) hA hdB hB hC hF (by norm_num)
  have h3 := hz ((1 / 3 : k) * zeta) B dA A C F 1 1 0 0 0
    (-2) (-3) (-2) (-3) (-3) hB hdA hA hC hF (by norm_num)
  have h4 := hz (2 * epsilon) dG A B C F 1 0 0 0 0
    (-5) (-2) (-2) (-3) (-3) hdG hA hB hC hF (by norm_num)
  have h5 := hz (-delta) C dB A B F 1 1 0 0 0
    (-3) (-3) (-2) (-2) (-3) hC hdB hA hB hF (by norm_num)
  have h6 := hz (-(1 / 2 : k) * delta) F dA A B C 1 1 0 0 0
    (-3) (-3) (-2) (-2) (-3) hF hdA hA hB hC (by norm_num)
  have h7 := hz (-(2 / 3 : k) * gamma) F dB A B C 1 1 0 0 0
    (-3) (-3) (-2) (-2) (-3) hF hdB hA hB hC (by norm_num)
  have h8 := hz ((1 / 2 : k) * delta) A dF B C F 1 1 0 0 0
    (-2) (-4) (-2) (-3) (-3) hA hdF hB hC hF (by norm_num)
  have h9 := hz ((2 / 3 : k) * epsilon) A dC B C F 1 1 0 0 0
    (-2) (-4) (-2) (-3) (-3) hA hdC hB hC hF (by norm_num)
  have h10 := hz ((2 / 3 : k) * gamma) B dF A C F 1 1 0 0 0
    (-2) (-4) (-2) (-3) (-3) hB hdF hA hC hF (by norm_num)
  have h11 := hz (-(1 / 6 : k) * delta) A dB B C F 2 1 0 0 0
    (-2) (-3) (-2) (-3) (-3) hA hdB hB hC hF (by norm_num)
  have h12 := hz (-(4 / 3 : k) * gamma) C dC A B F 1 1 0 0 0
    (-3) (-4) (-2) (-2) (-3) hC hdC hA hB hF (by norm_num)
  have h13 := hz (-(5 / 6 : k) * beta) C dF A B F 1 1 0 0 0
    (-3) (-4) (-2) (-2) (-3) hC hdF hA hB hF (by norm_num)
  have h14 := hz (-(5 / 6 : k) * beta) F dC A B C 1 1 0 0 0
    (-3) (-4) (-2) (-2) (-3) hF hdC hA hB hC (by norm_num)
  have h15 := hz ((2 / 9 : k) * gamma) B dA A C F 2 1 0 0 0
    (-2) (-3) (-2) (-3) (-3) hB hdA hA hC hF (by norm_num)
  have h16 := hz ((4 / 3 : k) * gamma) A dG B C F 1 1 0 0 0
    (-2) (-5) (-2) (-3) (-3) hA hdG hB hC hF (by norm_num)
  have h17 := hz ((5 / 3 : k) * beta) B dG A C F 1 1 0 0 0
    (-2) (-5) (-2) (-3) (-3) hB hdG hA hC hF (by norm_num)
  have h18 := hz (-(25 / 72 : k) * beta) A dF B C F 2 1 0 0 0
    (-2) (-4) (-2) (-3) (-3) hA hdF hB hC hF (by norm_num)
  have h19 := hz (-(5 / 12 : k) * beta) A F dA B C 1 1 1 0 0
    (-2) (-3) (-3) (-2) (-3) hA hF hdA hB hC (by norm_num)
  have h20 := hz ((5 / 18 : k) * beta) A B dC C F 1 1 1 0 0
    (-2) (-2) (-4) (-3) (-3) hA hB hdC hC hF (by norm_num)
  have h21 := hz ((5 / 9 : k) * beta) B C dA A F 1 1 1 0 0
    (-2) (-3) (-3) (-2) (-3) hB hC hdA hA hF (by norm_num)
  have h22 := hz (-4 / 3 : k) C F dB A B 1 1 1 0 0
    (-3) (-3) (-3) (-2) (-2) hC hF hdB hA hB (by norm_num)
  have h23 := hz (-4 / 9 : k) B C dF A F 1 1 1 0 0
    (-2) (-3) (-4) (-2) (-3) hB hC hdF hA hF (by norm_num)
  have h24 := hz (-4 / 9 : k) B F dC A C 1 1 1 0 0
    (-2) (-3) (-4) (-2) (-3) hB hF hdC hA hC (by norm_num)
  have h25 := hz (-4 / 9 : k) F dA A B C 2 1 0 0 0
    (-3) (-3) (-2) (-2) (-3) hF hdA hA hB hC (by norm_num)
  have h26 := hz (-(5 / 216 : k) * beta) A dB B C F 3 1 0 0 0
    (-2) (-3) (-2) (-3) (-3) hA hdB hB hC hF (by norm_num)
  have h27 := hz (4 / 9 : k) B dG A C F 2 1 0 0 0
    (-2) (-5) (-2) (-3) (-3) hB hdG hA hC hF (by norm_num)
  have h28 := hz ((5 / 216 : k) * beta) A B dA C F 2 1 1 0 0
    (-2) (-2) (-3) (-3) (-3) hA hB hdA hC hF (by norm_num)
  have h29 := hz (8 / 3 : k) G dG A B C 1 1 0 0 0
    (-4) (-5) (-2) (-2) (-3) hG hdG hA hB hC (by norm_num)
  simp only [lowerRowOneMainTangentLowerHahn68, HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h28, h29]
  ring

theorem lowerRowOneMainTangentWeightTenHahn68_coeff_neg10
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-4 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (↑(-3 : ℚ) : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (↑(-4 : ℚ) : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (↑(-4 : ℚ) : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-5 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ))
    (hdBco : dB.coeff (-3 : ℚ) = (-2 : k) * B.coeff (-2 : ℚ))
    (hdCco : dC.coeff (-4 : ℚ) = (-3 : k) * C.coeff (-3 : ℚ))
    (hdFco : dF.coeff (-4 : ℚ) = (-3 : k) * F.coeff (-3 : ℚ))
    (hdGco : dG.coeff (-5 : ℚ) = (-4 : k) * G.coeff (-4 : ℚ)) :
    (lowerRowOneMainTangentWeightTenHahn68 A B C F G
      dA dB dC dF dG).coeff (-10 : ℚ) =
      (8 / 27 : k) * rhoOneZeroLCubicMainTangentOne68
        (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
        (C.coeff (-3 : ℚ)) (F.coeff (-3 : ℚ))
        (G.coeff (-4 : ℚ)) := by
  have h1 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A B F dA G 1 1 1 1 0
      (-2) (-2) (-3) (-3) (-4) hA hB hF hdA hG
  have h2 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A B dF C G 2 1 1 0 0
      (-2) (-2) (-4) (-3) (-4) hA hB hdF hC hG
  have h3 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A F dB C G 2 1 1 0 0
      (-2) (-3) (-3) (-3) (-4) hA hF hdB hC hG
  have h4 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 9 : k) C dC A B G 2 1 0 0 0
      (-3) (-4) (-2) (-2) (-4) hC hdC hA hB hG
  have h5 := weightedMonomial68_coeff_at_general_lower_next
    (8 / 27 : k) B C dA A G 2 1 1 0 0
      (-2) (-3) (-3) (-2) (-4) hB hC hdA hA hG
  have h6 := weightedMonomial68_coeff_at_general_lower_next
    (8 / 9 : k) A C dG B G 1 1 1 0 0
      (-2) (-3) (-5) (-2) (-4) hA hC hdG hB hG
  have h7 := weightedMonomial68_coeff_at_general_lower_next
    (8 / 9 : k) A G dC B F 1 1 1 0 0
      (-2) (-4) (-4) (-2) (-3) hA hG hdC hB hF
  norm_num at h1 h2 h3 h4 h5 h6 h7
  simp only [lowerRowOneMainTangentWeightTenHahn68, HahnSeries.coeff_add]
  norm_num only
  rw [h1, h2, h3, h4, h5, h6, h7, hdAco, hdBco, hdCco, hdFco, hdGco]
  simp only [rhoOneZeroLCubicMainTangentOne68]
  ring

/-- Exact finite residual of the new face.  On `b=0` it either improves
the cubic defect or fixes the new `E`-tangent defect; away from `b=0` it
solves linearly for the new `D`-tangent defect. -/
theorem rhoOneZeroLCubicMainTangentOne_split68
    (a b c f g : k)
    (h : rhoOneZeroLCubicMainTangentOne68 a b c f g = 0) :
    (b = 0 ∧ (c = 0 ∨ 3 * c ^ 2 = 7 * a * g)) ∨
      (b ≠ 0 ∧ 7 * a ^ 2 * b * f =
        2 * a * b ^ 2 * c - 9 * c ^ 3 + 21 * a * c * g) := by
  by_cases hb : b = 0
  · left
    refine ⟨hb, ?_⟩
    rw [hb, rhoOneZeroLCubicMainTangentOne68] at h
    norm_num at h
    have hfac : c * (3 * c ^ 2 - 7 * a * g) = 0 := by
      linear_combination (1 / 3 : k) * h
    rcases mul_eq_zero.mp hfac with hc | hg
    · exact Or.inl hc
    · right
      linear_combination hg
  · right
    refine ⟨hb, ?_⟩
    simp only [rhoOneZeroLCubicMainTangentOne68] at h
    linear_combination h

/-- The actual source lower row one vanishes also at the next exponent. -/
theorem SquareZeroLIntegratedLocalRootData68.lowerRowOne_actual_coeff_neg10_zero
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    let C0 := ratFuncAtHahn46 T0.root T0.source.C0
    let D := ratFuncAtHahn46 T0.root T0.source.D
    let TT := ratFuncAtHahn46 T0.root
      (integratedT68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.epsilon))
    let U := ratFuncAtHahn46 T0.root
      (integratedU68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.zeta))
    let V := ratFuncAtHahn46 T0.root
      (integratedV68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
        (RatFunc.C T0.source.eta))
    let dD := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.D)
    let dE := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.E)
    let dU := ratFuncAtHahn46 T0.root (Differential.deriv
      (integratedU68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.zeta)))
    let dV := ratFuncAtHahn46 T0.root (Differential.deriv
      (integratedV68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
        (RatFunc.C T0.source.eta)))
    (U * dD + 2 * TT * dE - 2 * C0 * dV - D * dU).coeff (-10 : ℚ) = 0 := by
  dsimp only
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T0.source.A T0.source.B
      T0.source.C0 T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
      (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
      (RatFunc.C T0.source.zeta) (RatFunc.C T0.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T0.source.alpha) (hconst T0.source.beta)
      (hconst T0.source.gamma) (hconst T0.source.delta)
      (hconst T0.source.epsilon) (hconst T0.source.zeta)
      (hconst T0.source.eta) T0.source.bracket_eq
  have hrowH := congrArg (ratFuncAtHahn46 T0.root) hlow.2.2.2.1
  have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-10 : ℚ)) hrowH
  simpa only [ratFuncDerivation46_apply, map_add, map_sub, map_mul,
    map_ofNat, map_zero, HahnSeries.coeff_zero] using hcoeff

/-- The main tangent has a source-valid next scalar depending only on its
two transverse tangent defects. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_nextOne_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hmain :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) = 3 * D.coeff (-4 : ℚ) ∧
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ)) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    rhoOneZeroLCubicMainTangentOne68
      (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ)) (C.coeff (-3 : ℚ))
      (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 := by
  dsimp only at hmain ⊢
  have hbranch := P.1
  obtain ⟨cs, t, v, z, hcs, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ :=
    hbranch
  have hv' : v = z ^ 2 / 3 := by
    have h := (div_eq_iff (pow_ne_zero 2 hz)).mp hvcore
    calc v = (1 / 3 : k) * z ^ 2 := h
         _ = z ^ 2 / 3 := by ring
  have ht' : t = z ^ 3 / 27 := by
    have h := (div_eq_iff (pow_ne_zero 3 hz)).mp htcore
    calc t = (1 / 27 : k) * z ^ 3 := h
         _ = z ^ 3 / 27 := by ring
  have hgval : g.eval T.root = cs * z := by rw [hzdef]; field_simp [hcs]
  have huval : u.eval T.root = cs ^ 2 * v := by rw [hv]; field_simp [hcs]
  have hp3val : (p.coeff 3).eval T.root = cs ^ 3 * t := by
    rw [ht]; field_simp [hcs]
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let CH := ratFuncAtHahn46 T.root C0R
  let DH := ratFuncAtHahn46 T.root DR
  let EH := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let FRH := ratFuncAtHahn46 T.root FR
  let GRH := ratFuncAtHahn46 T.root GR
  let dAH := ratFuncAtHahn46 T.root (Differential.deriv AR)
  let dBH := ratFuncAtHahn46 T.root (Differential.deriv BR)
  let dCRH := ratFuncAtHahn46 T.root (Differential.deriv CR)
  let dFRH := ratFuncAtHahn46 T.root (Differential.deriv FR)
  let dGRH := ratFuncAtHahn46 T.root (Differential.deriv GR)
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C0 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
  let E0 := localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
  let Cdef0 : k[X] := C0 - C (1 / 3 : k) * A0 ^ 2
  let Edef0 : k[X] := E0 - C (1 / 27 : k) * A0 ^ 3
  obtain ⟨hAclear, hBclear, hCclear, hDclear, hEclear⟩ :=
    T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
  change algebraMap k[X] (RatFunc k) A0 = _ at hAclear
  change algebraMap k[X] (RatFunc k) B0 = _ at hBclear
  change algebraMap k[X] (RatFunc k) C0 = _ at hCclear
  change algebraMap k[X] (RatFunc k) D0 = _ at hDclear
  change algebraMap k[X] (RatFunc k) E0 = _ at hEclear
  have hB0root : B0.eval T.root = 0 := by
    simp [B0, localClearedB68RhoOne, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hD0root : D0.eval T.root = 0 := by
    simp [D0, localClearedD68RhoOne, T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hCdef0root : Cdef0.eval T.root = 0 := by
    simp [Cdef0, C0, A0, localClearedC68RhoOne, localClearedA68RhoOne,
      T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hEdef0root : Edef0.eval T.root = 0 := by
    simp [Edef0, E0, A0, localClearedE68RhoOne, localClearedA68RhoOne,
      T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  obtain ⟨B1, hB1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 B0 T.root T.scale_degree T.root_eq hB0root
  obtain ⟨C1, hC1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 Cdef0 T.root T.scale_degree T.root_eq hCdef0root
  obtain ⟨D1, hD1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 D0 T.root T.scale_degree T.root_eq hD0root
  obtain ⟨E1, hE1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 Edef0 T.root T.scale_degree T.root_eq hEdef0root
  have hCdefclear : algebraMap k[X] (RatFunc k) Cdef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * CR := by
    dsimp only [Cdef0, CR, C0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hCclear, hAclear]; ring
  have hEdefclear : algebraMap k[X] (RatFunc k) Edef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * ER := by
    dsimp only [Edef0, ER, E0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hEclear, hAclear]; ring
  have hBclear1 : algebraMap k[X] (RatFunc k) B1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * BR := by
    have hc := algebraMap_cancel_factoredClearing
      h0 B0 B1 BR 1 2 1 T.scale_ne_zero (by simpa using hB1) (by
        simpa only [Nat.mul_one, show 2 + 1 = 3 by omega] using hBclear)
    simpa only [Nat.mul_one] using hc
  have hCclear1 : algebraMap k[X] (RatFunc k) C1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * CR := by
    have hc := algebraMap_cancel_factoredClearing
      h0 Cdef0 C1 CR 1 3 1 T.scale_ne_zero (by simpa using hC1) (by
        simpa only [Nat.mul_one, show 3 + 1 = 4 by omega] using hCdefclear)
    simpa only [Nat.mul_one] using hc
  have hDclear1 : algebraMap k[X] (RatFunc k) D1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * DR := by
    have hc := algebraMap_cancel_factoredClearing
      h0 D0 D1 DR 1 4 1 T.scale_ne_zero (by simpa using hD1) (by
        simpa only [Nat.mul_one, show 4 + 1 = 5 by omega] using hDclear)
    simpa only [Nat.mul_one] using hc
  have hEclear1 : algebraMap k[X] (RatFunc k) E1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * ER := by
    have hc := algebraMap_cancel_factoredClearing
      h0 Edef0 E1 ER 1 5 1 T.scale_ne_zero (by simpa using hE1) (by
        simpa only [Nat.mul_one, show 5 + 1 = 6 by omega] using hEdefclear)
    simpa only [Nat.mul_one] using hc
  let F0 : k[X] := D1 - C (1 / 3 : k) * A0 * B1
  let G0 : k[X] := E1 - C (1 / 3 : k) * A0 * C1
  have hFclear : algebraMap k[X] (RatFunc k) F0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * FR := by
    dsimp only [F0, FR]
    simp only [map_sub, map_mul, RatFunc.algebraMap_C]
    rw [hDclear1, hAclear, hBclear1]; ring
  have hGclear : algebraMap k[X] (RatFunc k) G0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * GR := by
    dsimp only [G0, GR]
    simp only [map_sub, map_mul, RatFunc.algebraMap_C]
    rw [hEclear1, hAclear, hCclear1]; ring
  obtain ⟨cs', hcs', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 T.root T.scale_degree T.root_eq
  have hcseq : cs' = cs := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst cs'
  dsimp only [RhoOneZeroLCubicNextSourcePacket68,
    RhoOneZeroLCubicImprovedHahnBounds68] at P
  rcases P with ⟨_, ⟨hAord, hBord, hCord, hCRord0, hDord, hEord,
    hERord0⟩, hAne, htaut, h4, h3, hsplit⟩
  have hCRmap : CRH = rhoOneCDefectHahn68 AH CH := by
    dsimp only [CRH, CR, AH, CH, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH EH := by
    dsimp only [ERH, ER, AH, EH, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : FRH = rhoOneTangentDDefectHahn68 AH BH DH := by
    dsimp only [FRH, FR, AH, BH, DH, AR, BR, DR,
      rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap : GRH = rhoOneTangentEDefectHahn68 AH CRH ERH := by
    dsimp only [GRH, GR, ERH, AH, CRH, AR,
      rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hABco := weightedMonomial68_coeff_at_general_lower_next
    (1 / 3 : k) AH BH AH BH CH 1 1 0 0 0
      (-2) (-2) (-2) (-2) (-4) hAord hBord hAord hBord hCord
  have hACco := weightedMonomial68_coeff_at_general_lower_next
    (1 / 3 : k) AH CRH AH BH CH 1 1 0 0 0
      (-2) (-3) (-2) (-2) (-4) hAord
      (by rw [hCRmap]; exact hCRord0) hAord hBord hCord
  norm_num at hABco hACco
  have hABco' : (HahnSeries.C (1 / 3 : k) * AH * BH).coeff (-4 : ℚ) =
      (1 / 3 : k) * AH.coeff (-2 : ℚ) * BH.coeff (-2 : ℚ) := by
    simpa [weightedMonomial68] using hABco
  have hACco' : (HahnSeries.C (1 / 3 : k) * AH * CRH).coeff (-5 : ℚ) =
      (1 / 3 : k) * AH.coeff (-2 : ℚ) * CRH.coeff (-3 : ℚ) := by
    simpa [weightedMonomial68] using hACco
  have hFRlead : FRH.coeff (-4 : ℚ) = 0 := by
    rw [hFRmap]
    simp only [rhoOneTangentDDefectHahn68, HahnSeries.coeff_sub]
    change DH.coeff (-4 : ℚ) - (HahnSeries.C (1 / 3 : k) * AH * BH).coeff
      (-4 : ℚ) = 0
    rw [hABco']
    linear_combination (-1 / 3 : k) * hmain.1
  have hGRlead : GRH.coeff (-5 : ℚ) = 0 := by
    rw [hGRmap]
    simp only [rhoOneTangentEDefectHahn68, HahnSeries.coeff_sub]
    change ERH.coeff (-5 : ℚ) - (HahnSeries.C (1 / 3 : k) * AH * CRH).coeff
      (-5 : ℚ) = 0
    rw [hACco']
    rw [hCRmap, hERmap]
    linear_combination (1 / 3 : k) * hmain.2
  have hFco := localHahn_coeff_neg_of_cleared T.root cs h0 F0 FR 4
    hcs hsingle hFclear
  have hGco := localHahn_coeff_neg_of_cleared T.root cs h0 G0 GR 5
    hcs hsingle hGclear
  norm_num at hFco hGco
  have hF0root : F0.eval T.root = 0 := by
    change FRH.coeff (-4 : ℚ) = _ at hFco
    rw [hFRlead] at hFco
    exact (mul_eq_zero.mp hFco.symm).resolve_left
      (inv_ne_zero (pow_ne_zero 4 hcs))
  have hG0root : G0.eval T.root = 0 := by
    change GRH.coeff (-5 : ℚ) = _ at hGco
    rw [hGRlead] at hGco
    exact (mul_eq_zero.mp hGco.symm).resolve_left
      (inv_ne_zero (pow_ne_zero 5 hcs))
  have hFRord := localHahn_orderTop_ge_one_better_of_cleared_root_zero
    T.root h0 F0 FR 4 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      T.scale_order hFclear hF0root
  have hGRord := localHahn_orderTop_ge_one_better_of_cleared_root_zero
    T.root h0 G0 GR 5 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      T.scale_order hGclear hG0root
  obtain ⟨hdFRord, hdFRco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 F0 FR 4 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      hsingle T.scale_order hderiv' hcs hFclear hF0root
  obtain ⟨hdGRord, hdGRco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 G0 GR 5 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      hsingle T.scale_order hderiv' hcs hGclear hG0root
  norm_num at hFRord hGRord hdFRord hdFRco hdGRord hdGRco
  change (↑(-3 : ℚ) : WithTop ℚ) ≤ FRH.orderTop at hFRord
  change (↑(-4 : ℚ) : WithTop ℚ) ≤ GRH.orderTop at hGRord
  change (↑(-4 : ℚ) : WithTop ℚ) ≤ dFRH.orderTop at hdFRord
  change (↑(-5 : ℚ) : WithTop ℚ) ≤ dGRH.orderTop at hdGRord
  have hdFRco' : dFRH.coeff (-4 : ℚ) = (-3 : k) * FRH.coeff (-3 : ℚ) := by
    simpa only [dFRH, FRH, neg_mul] using hdFRco
  have hdGRco' : dGRH.coeff (-5 : ℚ) = (-4 : k) * GRH.coeff (-4 : ℚ) := by
    simpa only [dGRH, GRH, neg_mul] using hdGRco
  have hdAord : (↑(-3 : ℚ) : WithTop ℚ) ≤ dAH.orderTop := by
    dsimp only [dAH, AR]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdAco : dAH.coeff (-3 : ℚ) = (-2 : k) * AH.coeff (-2 : ℚ) := by
    dsimp only [dAH, AH, AR]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root cs h0 A0
      T.source.A 2 hcs hsingle hderiv' hAclear using 1 <;> norm_num
  obtain ⟨hdBord, hdBco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 B0 T.source.B 3 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq hsingle T.scale_order hderiv' hcs hBclear hB0root
  obtain ⟨hdCRord, hdCRco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 Cdef0 CR 4 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq hsingle T.scale_order hderiv' hcs hCdefclear hCdef0root
  norm_num at hdBord hdBco hdCRord hdCRco
  change (↑(-3 : ℚ) : WithTop ℚ) ≤ dBH.orderTop at hdBord
  change (↑(-4 : ℚ) : WithTop ℚ) ≤ dCRH.orderTop at hdCRord
  have hdBco' : dBH.coeff (-3 : ℚ) = (-2 : k) * BH.coeff (-2 : ℚ) := by
    simpa only [dBH, BH, BR, neg_mul] using hdBco
  have hdCRco' : dCRH.coeff (-4 : ℚ) = (-3 : k) * CRH.coeff (-3 : ℚ) := by
    simpa only [dCRH, CRH, neg_mul] using hdCRco
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hdecR := lowerRowOneMainTangent_decomposition68 (k := k)
    ratFuncDerivation68 AR BR CR FR GR
      (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
      (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta)
      (RatFunc.C T.source.eta)
      (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta) (hconst T.source.eta)
  dsimp only at hdecR
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR]; simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]; norm_num; ring
  have hDrec : AR * BR / 3 + FR = DR := by
    dsimp only [FR]; simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]; norm_num; ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
    dsimp only [GR, ER, CR]; simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [show (27 : RatFunc k) = RatFunc.C (27 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 27).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]; norm_num; ring
  rw [hCrec, hDrec, hErec] at hdecR
  simp only [ratFuncDerivation46_apply] at hdecR
  have hdecH := congrArg (ratFuncAtHahn46 T.root) hdecR
  simp only [map_add, map_sub, map_mul, map_ofNat] at hdecH
  have hdecH' :
      let TT := ratFuncAtHahn46 T.root
        (integratedT68 0 AR BR C0R DR E0R (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.epsilon))
      let U := ratFuncAtHahn46 T.root
        (integratedU68 0 AR BR C0R DR E0R (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta))
      let V := ratFuncAtHahn46 T.root
        (integratedV68 0 AR BR C0R DR E0R (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
          (RatFunc.C T.source.eta))
      let dD := ratFuncAtHahn46 T.root (Differential.deriv DR)
      let dE := ratFuncAtHahn46 T.root (Differential.deriv E0R)
      let dU := ratFuncAtHahn46 T.root (Differential.deriv
        (integratedU68 0 AR BR C0R DR E0R (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta)))
      let dV := ratFuncAtHahn46 T.root (Differential.deriv
        (integratedV68 0 AR BR C0R DR E0R (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
          (RatFunc.C T.source.eta)))
      U * dD + 2 * TT * dE - 2 * CH * dV - DH * dU =
        lowerRowOneMainTangentWeightTenHahn68 AH BH CRH FRH GRH
          dAH dBH dCRH dFRH dGRH +
        lowerRowOneMainTangentLowerHahn68 T.source.beta T.source.gamma
          T.source.delta T.source.epsilon T.source.zeta
          AH BH CRH FRH GRH dAH dBH dCRH dFRH dGRH := by
    dsimp only
    rw [hdecH]
    simp only [AR, BR, C0R, DR, E0R, AH, BH, CH, DH, CRH, FRH, GRH,
      dAH, dBH, dCRH, dFRH, dGRH,
      lowerRowOneMainTangentWeightTenHahn68,
      lowerRowOneMainTangentLowerHahn68,
      lowerRowOneMainTangentWeightTenAlg68,
      lowerRowOneMainTangentLowerAlg68, weightedMonomial68, map_add,
      map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      ratFuncAtHahn46_C]
    ring
  have hlower := lowerRowOneMainTangentLowerHahn68_coeff_neg10
    T.source.beta T.source.gamma T.source.delta T.source.epsilon T.source.zeta
      AH BH CRH FRH GRH dAH dBH dCRH dFRH dGRH hAord hBord
      (by rw [hCRmap]; exact hCRord0) hFRord hGRord hdAord hdBord hdCRord
      hdFRord hdGRord
  have hactual := T.lowerRowOne_actual_coeff_neg10_zero
  dsimp only at hactual hdecH'
  simp only [map_zero] at hactual
  have hcoeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-10 : ℚ)) hdecH'
  rw [hactual, HahnSeries.coeff_add, hlower, add_zero] at hcoeff
  have hface := lowerRowOneMainTangentWeightTenHahn68_coeff_neg10
    AH BH CRH FRH GRH dAH dBH dCRH dFRH dGRH hAord hBord
      (by rw [hCRmap]; exact hCRord0) hFRord hGRord hdAord hdBord hdCRord
      hdFRord hdGRord hdAco hdBco' hdCRco' hdFRco' hdGRco'
  rw [hface] at hcoeff
  have hscalar : (8 / 27 : k) ≠ 0 := by norm_num
  have hout := (mul_eq_zero.mp hcoeff.symm).resolve_left hscalar
  rw [hFRmap, hGRmap, hCRmap, hERmap] at hout
  simpa only [AH, BH, CH, DH, EH, AR, BR, C0R, DR, E0R] using hout

end AlignedSquareRhoOneCubicMainTangent68

end Max11DegreeRoutes
