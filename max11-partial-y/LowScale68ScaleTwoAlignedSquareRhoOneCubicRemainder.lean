import LowScale68ScaleTwoAlignedSquareRhoOneCubicComponents

/-! # Vanishing of the lower-weight cubic row-two remainder -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicRemainder68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicRemainderHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Algebraic form of the weight-ten face. -/
def lowerRowTwoCubicWeightTenAlg68
    (A B C D E dA dB dC dD dE : k) : k :=
  (8 / 27 : k) * A * B * C * dA + (8 / 3 : k) * E * dD +
  (8 / 3 : k) * D * dE - (4 / 3 : k) * B * E * dA -
  (8 / 27 : k) * A ^ 2 * C * dB -
  (8 / 27 : k) * A ^ 2 * B * dC - (4 / 3 : k) * C * D * dA

/-- All terms strictly below improved weight ten. -/
def lowerRowTwoCubicLowerAlg68
    (beta gamma delta epsilon zeta : k)
    (A B C D E dA dB dC dD dE : k) : k :=
  zeta * dC + (2 / 3 : k) * zeta * A * dA + 2 * epsilon * dD -
  (3 / 2 : k) * delta * B * dB - epsilon * B * dA -
  (4 / 3 : k) * gamma * B * dC + (1 / 2 : k) * delta * A * dC +
  3 * delta * dE - (4 / 3 : k) * gamma * C * dB - delta * C * dA -
  (5 / 6 : k) * beta * C * dC - (2 / 9 : k) * gamma * A * B * dA +
  (1 / 3 : k) * delta * A ^ 2 * dA -
  (5 / 6 : k) * beta * B * dD + (4 / 3 : k) * gamma * A * dD +
  (5 / 12 : k) * beta * B ^ 2 * dA +
  (5 / 12 : k) * beta * A * B * dB -
  (4 / 9 : k) * gamma * A ^ 2 * dB -
  (5 / 6 : k) * beta * D * dB - (2 / 3 : k) * gamma * D * dA -
  (25 / 72 : k) * beta * A ^ 2 * dC -
  (5 / 18 : k) * beta * A * C * dA +
  (5 / 2 : k) * beta * A * dE - (16 / 9 : k) * B * C * dC +
  (5 / 36 : k) * beta * A ^ 3 * dA -
  (8 / 9 : k) * B ^ 2 * dD - (16 / 9 : k) * B * D * dB +
  (4 / 9 : k) * B ^ 3 * dA + (8 / 9 : k) * A * B ^ 2 * dB -
  (8 / 9 : k) * C ^ 2 * dB

/-- Pure algebra: after introducing the cubic defects, the complete
differentiated row two is its weight-ten face plus the displayed lower
remainder. -/
theorem lowerRowTwoCubic_decomposition68
    {R : Type*} [Field R] [CharZero R] [Algebra k R]
    (d : Derivation k R R)
    (A B C D E alpha beta gamma delta epsilon zeta eta : R)
    (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) :
    let C0 := A ^ 2 / 3 + C
    let E0 := A ^ 3 / 27 + E
    let S := integratedS68 0 A B C0 D alpha beta delta
    let T := integratedT68 0 A B C0 D E0 alpha beta gamma epsilon
    let U := integratedU68 0 A B C0 D E0 alpha beta gamma delta zeta
    let V := integratedV68 0 A B C0 D E0 alpha beta gamma delta epsilon eta
    U * d C0 + 2 * T * d D + 3 * S * d E0 - 3 * B * d V -
        2 * C0 * d U - D * d T =
      lowerRowTwoCubicWeightTenAlg68 A B C D E (d A) (d B) (d C)
        (d D) (d E) +
      lowerRowTwoCubicLowerAlg68 beta gamma delta epsilon zeta
        A B C D E (d A) (d B) (d C) (d D) (d E) := by
  dsimp only
  have h1 : d (1 : R) = 0 := by
    simpa only [Nat.cast_one] using d.map_natCast 1
  simp only [integratedS68, integratedT68, integratedU68, integratedV68,
    map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_div, Derivation.leibniz_inv, nsmul_eq_mul,
    smul_eq_mul, map_zero, halpha, hbeta, hgamma, hdelta, hepsilon,
    hzeta, heta]
  simp [derivation_ofNat_zero68 d, h1]
  simp only [lowerRowTwoCubicWeightTenAlg68, lowerRowTwoCubicLowerAlg68]
  ring

/-- Weighted-monomial presentation of the strict lower remainder. -/
def lowerRowTwoCubicLowerHahn68
    (beta gamma delta epsilon zeta : k)
    (A B C D E dA dB dC dD dE : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 zeta dC A B C D 1 0 0 0 0 +
  weightedMonomial68 ((2 / 3 : k) * zeta) A dA B C D 1 1 0 0 0 +
  weightedMonomial68 (2 * epsilon) dD A B C D 1 0 0 0 0 +
  weightedMonomial68 (-(3 / 2 : k) * delta) B dB A C D 1 1 0 0 0 +
  weightedMonomial68 (-epsilon) B dA A C D 1 1 0 0 0 +
  weightedMonomial68 (-(4 / 3 : k) * gamma) B dC A C D 1 1 0 0 0 +
  weightedMonomial68 ((1 / 2 : k) * delta) A dC B C D 1 1 0 0 0 +
  weightedMonomial68 (3 * delta) dE A B C D 1 0 0 0 0 +
  weightedMonomial68 (-(4 / 3 : k) * gamma) C dB A B D 1 1 0 0 0 +
  weightedMonomial68 (-delta) C dA A B D 1 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) C dC A B D 1 1 0 0 0 +
  weightedMonomial68 (-(2 / 9 : k) * gamma) A B dA C D 1 1 1 0 0 +
  weightedMonomial68 ((1 / 3 : k) * delta) A dA B C D 2 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) B dD A C D 1 1 0 0 0 +
  weightedMonomial68 ((4 / 3 : k) * gamma) A dD B C D 1 1 0 0 0 +
  weightedMonomial68 ((5 / 12 : k) * beta) B dA A C D 2 1 0 0 0 +
  weightedMonomial68 ((5 / 12 : k) * beta) A B dB C D 1 1 1 0 0 +
  weightedMonomial68 (-(4 / 9 : k) * gamma) A dB B C D 2 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) D dB A B C 1 1 0 0 0 +
  weightedMonomial68 (-(2 / 3 : k) * gamma) D dA A B C 1 1 0 0 0 +
  weightedMonomial68 (-(25 / 72 : k) * beta) A dC B C D 2 1 0 0 0 +
  weightedMonomial68 (-(5 / 18 : k) * beta) A C dA B D 1 1 1 0 0 +
  weightedMonomial68 ((5 / 2 : k) * beta) A dE B C D 1 1 0 0 0 +
  weightedMonomial68 (-16 / 9 : k) B C dC A D 1 1 1 0 0 +
  weightedMonomial68 ((5 / 36 : k) * beta) A dA B C D 3 1 0 0 0 +
  weightedMonomial68 (-8 / 9 : k) B dD A C D 2 1 0 0 0 +
  weightedMonomial68 (-16 / 9 : k) B D dB A C 1 1 1 0 0 +
  weightedMonomial68 (4 / 9 : k) B dA A C D 3 1 0 0 0 +
  weightedMonomial68 (8 / 9 : k) A B dB C D 1 2 1 0 0 +
  weightedMonomial68 (-8 / 9 : k) C dB A B D 2 1 0 0 0

/-- Every strict lower monomial has zero coefficient at exponent `-10`. -/
theorem lowerRowTwoCubicLowerHahn68_coeff_neg10
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
    (lowerRowTwoCubicLowerHahn68 beta gamma delta epsilon zeta
      A B C D E dA dB dC dD dE).coeff (-10 : ℚ) = 0 := by
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
  have h1 := hz zeta dC A B C D 1 0 0 0 0 (-4) (-2) (-2) (-3) (-4)
    hdC hA hB hC hD (by norm_num)
  have h2 := hz ((2 / 3 : k) * zeta) A dA B C D 1 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hA hdA hB hC hD (by norm_num)
  have h3 := hz (2 * epsilon) dD A B C D 1 0 0 0 0
    (-5) (-2) (-2) (-3) (-4) hdD hA hB hC hD (by norm_num)
  have h4 := hz (-(3 / 2 : k) * delta) B dB A C D 1 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hB hdB hA hC hD (by norm_num)
  have h5 := hz (-epsilon) B dA A C D 1 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hB hdA hA hC hD (by norm_num)
  have h6 := hz (-(4 / 3 : k) * gamma) B dC A C D 1 1 0 0 0
    (-2) (-4) (-2) (-3) (-4) hB hdC hA hC hD (by norm_num)
  have h7 := hz ((1 / 2 : k) * delta) A dC B C D 1 1 0 0 0
    (-2) (-4) (-2) (-3) (-4) hA hdC hB hC hD (by norm_num)
  have h8 := hz (3 * delta) dE A B C D 1 0 0 0 0
    (-6) (-2) (-2) (-3) (-4) hdE hA hB hC hD (by norm_num)
  have h9 := hz (-(4 / 3 : k) * gamma) C dB A B D 1 1 0 0 0
    (-3) (-3) (-2) (-2) (-4) hC hdB hA hB hD (by norm_num)
  have h10 := hz (-delta) C dA A B D 1 1 0 0 0
    (-3) (-3) (-2) (-2) (-4) hC hdA hA hB hD (by norm_num)
  have h11 := hz (-(5 / 6 : k) * beta) C dC A B D 1 1 0 0 0
    (-3) (-4) (-2) (-2) (-4) hC hdC hA hB hD (by norm_num)
  have h12 := hz (-(2 / 9 : k) * gamma) A B dA C D 1 1 1 0 0
    (-2) (-2) (-3) (-3) (-4) hA hB hdA hC hD (by norm_num)
  have h13 := hz ((1 / 3 : k) * delta) A dA B C D 2 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hA hdA hB hC hD (by norm_num)
  have h14 := hz (-(5 / 6 : k) * beta) B dD A C D 1 1 0 0 0
    (-2) (-5) (-2) (-3) (-4) hB hdD hA hC hD (by norm_num)
  have h15 := hz ((4 / 3 : k) * gamma) A dD B C D 1 1 0 0 0
    (-2) (-5) (-2) (-3) (-4) hA hdD hB hC hD (by norm_num)
  have h16 := hz ((5 / 12 : k) * beta) B dA A C D 2 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hB hdA hA hC hD (by norm_num)
  have h17 := hz ((5 / 12 : k) * beta) A B dB C D 1 1 1 0 0
    (-2) (-2) (-3) (-3) (-4) hA hB hdB hC hD (by norm_num)
  have h18 := hz (-(4 / 9 : k) * gamma) A dB B C D 2 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hA hdB hB hC hD (by norm_num)
  have h19 := hz (-(5 / 6 : k) * beta) D dB A B C 1 1 0 0 0
    (-4) (-3) (-2) (-2) (-3) hD hdB hA hB hC (by norm_num)
  have h20 := hz (-(2 / 3 : k) * gamma) D dA A B C 1 1 0 0 0
    (-4) (-3) (-2) (-2) (-3) hD hdA hA hB hC (by norm_num)
  have h21 := hz (-(25 / 72 : k) * beta) A dC B C D 2 1 0 0 0
    (-2) (-4) (-2) (-3) (-4) hA hdC hB hC hD (by norm_num)
  have h22 := hz (-(5 / 18 : k) * beta) A C dA B D 1 1 1 0 0
    (-2) (-3) (-3) (-2) (-4) hA hC hdA hB hD (by norm_num)
  have h23 := hz ((5 / 2 : k) * beta) A dE B C D 1 1 0 0 0
    (-2) (-6) (-2) (-3) (-4) hA hdE hB hC hD (by norm_num)
  have h24 := hz (-16 / 9 : k) B C dC A D 1 1 1 0 0
    (-2) (-3) (-4) (-2) (-4) hB hC hdC hA hD (by norm_num)
  have h25 := hz ((5 / 36 : k) * beta) A dA B C D 3 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hA hdA hB hC hD (by norm_num)
  have h26 := hz (-8 / 9 : k) B dD A C D 2 1 0 0 0
    (-2) (-5) (-2) (-3) (-4) hB hdD hA hC hD (by norm_num)
  have h27 := hz (-16 / 9 : k) B D dB A C 1 1 1 0 0
    (-2) (-4) (-3) (-2) (-3) hB hD hdB hA hC (by norm_num)
  have h28 := hz (4 / 9 : k) B dA A C D 3 1 0 0 0
    (-2) (-3) (-2) (-3) (-4) hB hdA hA hC hD (by norm_num)
  have h29 := hz (8 / 9 : k) A B dB C D 1 2 1 0 0
    (-2) (-2) (-3) (-3) (-4) hA hB hdB hC hD (by norm_num)
  have h30 := hz (-8 / 9 : k) C dB A B D 2 1 0 0 0
    (-3) (-3) (-2) (-2) (-4) hC hdB hA hB hD (by norm_num)
  simp only [lowerRowTwoCubicLowerHahn68, HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h28, h29, h30]
  ring

/-- One-step improved derivative order and boundary coefficient from a
clearing whose polynomial numerator vanishes at the local root. -/
theorem localHahn_deriv_improved_of_cleared_root_zero
    (a c : k) (h0 A0 : k[X]) (A : RatFunc k) (n : ℕ) (hn : 0 < n)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hscale :
      ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c)
    (horder :
      (ratFuncAtHahn46 a
        (algebraMap k[X] (RatFunc k) h0)).orderTop =
          (↑(1 : ℚ) : WithTop ℚ))
    (hderiv :
      ratFuncAtHahn46 a
          (Differential.deriv (algebraMap k[X] (RatFunc k) h0)) =
        HahnSeries.C c)
    (hc : c ≠ 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * A)
    (hA0root : A0.eval a = 0) :
    (↑(-(((n - 1) + 1 : ℕ) : ℚ)) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a (Differential.deriv A)).orderTop ∧
    (ratFuncAtHahn46 a (Differential.deriv A)).coeff
        (-((n - 1 : ℕ) : ℚ) - 1) =
      (-(n - 1 : ℕ) : k) * (ratFuncAtHahn46 a A).coeff
        (-((n - 1 : ℕ) : ℚ)) := by
  obtain ⟨A1, hA1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 A0 a hdegree hroot hA0root
  have hclear1 : algebraMap k[X] (RatFunc k) A1 =
      (algebraMap k[X] (RatFunc k) h0) ^ (n - 1) * A := by
    have hcancel := algebraMap_cancel_factoredClearing
      h0 A0 A1 A 1 (n - 1) 1 hh0 (by simpa using hA1) (by
        simpa only [Nat.mul_one, show n - 1 + 1 = n by omega] using hclear)
    simpa only [Nat.mul_one] using hcancel
  exact ⟨
    localHahn_deriv_orderTop_ge_of_cleared a h0 A1 A (n - 1)
      horder hclear1,
    (by
      convert localHahn_deriv_coeff_neg_succ_of_cleared
        a c h0 A1 A (n - 1) hc hscale hderiv hclear1 using 1 <;>
        push_cast <;> ring)⟩

/-- Source-level vanishing of the new weight-ten scalar. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_cubicBranch_nextTwo_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbranch : RhoOneZeroLCubicSourcePacket68 T g u) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    rhoOneZeroLCubicNextTwo68 (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
      ((rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ))
      (D.coeff (-4 : ℚ))
      ((rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)) = 0 := by
  dsimp only
  have hbranch0 := hbranch
  obtain ⟨cs, t, v, z, hcs, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ :=
    hbranch
  have hv' : v = z ^ 2 / 3 := by
    have h := (div_eq_iff (pow_ne_zero 2 hz)).mp hvcore
    calc
      v = (1 / 3 : k) * z ^ 2 := h
      _ = z ^ 2 / 3 := by ring
  have ht' : t = z ^ 3 / 27 := by
    have h := (div_eq_iff (pow_ne_zero 3 hz)).mp htcore
    calc
      t = (1 / 27 : k) * z ^ 3 := h
      _ = z ^ 3 / 27 := by ring
  have hgval : g.eval T.root = cs * z := by
    rw [hzdef]
    field_simp [hcs]
  have huval : u.eval T.root = cs ^ 2 * v := by
    rw [hv]
    field_simp [hcs]
  have hp3val : (p.coeff 3).eval T.root = cs ^ 3 * t := by
    rw [ht]
    field_simp [hcs]
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let CH := ratFuncAtHahn46 T.root C0R
  let DH := ratFuncAtHahn46 T.root DR
  let EH := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let dAH := ratFuncAtHahn46 T.root (Differential.deriv AR)
  let dBH := ratFuncAtHahn46 T.root (Differential.deriv BR)
  let dCRH := ratFuncAtHahn46 T.root (Differential.deriv CR)
  let dDH := ratFuncAtHahn46 T.root (Differential.deriv DR)
  let dERH := ratFuncAtHahn46 T.root (Differential.deriv ER)
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C0 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
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
    field_simp [hcs]
    ring
  have hD0root : D0.eval T.root = 0 := by
    simp [D0, localClearedD68RhoOne, T.root_eq, hgval, huval, hp3val,
      hv', ht']
    field_simp [hcs]
    ring
  have hCdef0root : Cdef0.eval T.root = 0 := by
    simp [Cdef0, C0, A0, localClearedC68RhoOne,
      localClearedA68RhoOne, T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]
    ring
  have hEdef0root : Edef0.eval T.root = 0 := by
    simp [Edef0, E0, A0, localClearedE68RhoOne,
      localClearedA68RhoOne, T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]
    ring
  have hCdefclear : algebraMap k[X] (RatFunc k) Cdef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * CR := by
    dsimp only [Cdef0, CR, C0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hCclear, hAclear]
    ring
  have hEdefclear : algebraMap k[X] (RatFunc k) Edef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * ER := by
    dsimp only [Edef0, ER, E0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hEclear, hAclear]
    ring
  obtain ⟨cs', hcs', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  have hcseq : cs' = cs := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst cs'
  have hnext := T.rhoOne_cubicBranch_nextPacket
    hp hH hp6 hp5 hp4 hbranch0
  dsimp only [RhoOneZeroLCubicNextSourcePacket68,
    RhoOneZeroLCubicImprovedHahnBounds68] at hnext
  rcases hnext with ⟨_, ⟨hAord, hBord, hCord, hCdeford, hDord,
    hEord, hEdeford⟩, hAne, htaut, h4, h3, hsplit⟩
  have hCRmap : CRH = rhoOneCDefectHahn68 AH CH := by
    dsimp only [CRH, CR, AH, CH, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH EH := by
    dsimp only [ERH, ER, AH, EH, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
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
  obtain ⟨hdDord, hdDco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 D0 T.source.D 5 (by omega) T.scale_ne_zero T.scale_degree
    T.root_eq hsingle T.scale_order hderiv' hcs hDclear hD0root
  obtain ⟨hdERord, hdERco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 Edef0 ER 6 (by omega) T.scale_ne_zero T.scale_degree
    T.root_eq hsingle T.scale_order hderiv' hcs hEdefclear hEdef0root
  norm_num at hdBord hdBco hdCRord hdCRco hdDord hdDco hdERord hdERco
  change (↑(-3 : ℚ) : WithTop ℚ) ≤ dBH.orderTop at hdBord
  change (↑(-4 : ℚ) : WithTop ℚ) ≤ dCRH.orderTop at hdCRord
  change (↑(-5 : ℚ) : WithTop ℚ) ≤ dDH.orderTop at hdDord
  change (↑(-6 : ℚ) : WithTop ℚ) ≤ dERH.orderTop at hdERord
  have hdBco' : dBH.coeff (-3 : ℚ) = (-2 : k) * BH.coeff (-2 : ℚ) := by
    simpa only [dBH, BH, BR, neg_mul] using hdBco
  have hdCRco' : dCRH.coeff (-4 : ℚ) =
      (-3 : k) * CRH.coeff (-3 : ℚ) := by
    simpa only [dCRH, CRH, neg_mul] using hdCRco
  have hdDco' : dDH.coeff (-5 : ℚ) = (-4 : k) * DH.coeff (-4 : ℚ) := by
    simpa only [dDH, DH, DR, neg_mul] using hdDco
  have hdERco' : dERH.coeff (-6 : ℚ) =
      (-5 : k) * ERH.coeff (-5 : ℚ) := by
    simpa only [dERH, ERH, neg_mul] using hdERco
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hdecR := lowerRowTwoCubic_decomposition68 (k := k)
    ratFuncDerivation68 AR BR CR DR ER
      (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
      (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta)
      (RatFunc.C T.source.eta)
      (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta)
  dsimp only at hdecR
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR]
    simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    norm_num
    ring
  have hErec : AR ^ 3 / 27 + ER = E0R := by
    dsimp only [ER]
    simp only [div_eq_mul_inv]
    rw [show (27 : RatFunc k) = RatFunc.C (27 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 27).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    norm_num
    ring
  rw [hCrec, hErec] at hdecR
  simp only [ratFuncDerivation46_apply] at hdecR
  have hdecH := congrArg (ratFuncAtHahn46 T.root) hdecR
  simp only [map_add, map_sub, map_mul, map_ofNat] at hdecH
  have hdecH' :
      let S := ratFuncAtHahn46 T.root
        (integratedS68 0 AR BR C0R DR
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.delta))
      let TT := ratFuncAtHahn46 T.root
        (integratedT68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon))
      let U := ratFuncAtHahn46 T.root
        (integratedU68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.zeta))
      let V := ratFuncAtHahn46 T.root
        (integratedV68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.epsilon) (RatFunc.C T.source.eta))
      let dC0 := ratFuncAtHahn46 T.root (Differential.deriv C0R)
      let dD := ratFuncAtHahn46 T.root (Differential.deriv DR)
      let dE0 := ratFuncAtHahn46 T.root (Differential.deriv E0R)
      let dT := ratFuncAtHahn46 T.root (Differential.deriv
        (integratedT68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)))
      let dU := ratFuncAtHahn46 T.root (Differential.deriv
        (integratedU68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.zeta)))
      let dV := ratFuncAtHahn46 T.root (Differential.deriv
        (integratedV68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.epsilon) (RatFunc.C T.source.eta)))
      U * dC0 + 2 * TT * dD + 3 * S * dE0 - 3 * BH * dV -
          2 * CH * dU - DH * dT =
        lowerRowTwoCubicWeightTenHahn68 AH BH CRH DH ERH
          dAH dBH dCRH dDH dERH +
        lowerRowTwoCubicLowerHahn68 T.source.beta T.source.gamma
          T.source.delta T.source.epsilon T.source.zeta
          AH BH CRH DH ERH dAH dBH dCRH dDH dERH := by
    dsimp only
    rw [hdecH]
    simp only [AR, BR, C0R, DR, E0R, AH, BH, CH, DH, CRH, ERH,
      dAH, dBH, dCRH, dDH, dERH, lowerRowTwoCubicWeightTenHahn68,
      lowerRowTwoCubicLowerHahn68, lowerRowTwoCubicWeightTenAlg68,
      lowerRowTwoCubicLowerAlg68, weightedMonomial68, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      ratFuncAtHahn46_C]
    ring
  have hlower := lowerRowTwoCubicLowerHahn68_coeff_neg10
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CRH DH ERH dAH dBH dCRH dDH dERH
      hAord hBord (by rw [hCRmap]; exact hCdeford) hDord
      (by rw [hERmap]; exact hEdeford) hdAord hdBord hdCRord hdDord hdERord
  have hactual := T.lowerRowTwo_actual_coeff_neg10_zero
  dsimp only at hactual hdecH'
  simp only [map_zero] at hactual
  have hcoeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-10 : ℚ))
    hdecH'
  rw [hactual, HahnSeries.coeff_add, hlower, add_zero] at hcoeff
  have hface := lowerRowTwoCubicWeightTenHahn68_coeff_neg10
    AH BH CRH DH ERH dAH dBH dCRH dDH dERH
      hAord hBord (by rw [hCRmap]; exact hCdeford) hDord
      (by rw [hERmap]; exact hEdeford) hdAord hdBord hdCRord hdDord hdERord
      hdAco hdBco' hdCRco' hdDco' hdERco'
  rw [hface] at hcoeff
  have hscalar : (8 / 9 : k) ≠ 0 := by norm_num
  have hout := (mul_eq_zero.mp hcoeff.symm).resolve_left hscalar
  rw [hCRmap, hERmap] at hout
  simpa only [AH, BH, CH, DH, EH, AR, BR, C0R, DR, E0R] using hout

/-- The two cubic-next components after the new differential row. -/
def RhoOneZeroLCubicRemainderSourcePacket68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
  rhoOneZeroLCubicNextTwo68 a b c d e = 0 ∧
  a ^ 2 * b * c = 9 * d * e ∧
  ((a * b = 3 * d ∧ (b = 0 ∨ 3 * e = a * c)) ∨
    (a * b ^ 2 - b * d + 2 * c ^ 2 = 0 ∧ a ^ 2 * b * c = 9 * d * e))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_cubicBranch_remainderPacket
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbranch : RhoOneZeroLCubicSourcePacket68 T g u) :
    RhoOneZeroLCubicRemainderSourcePacket68 T g u := by
  have P := T.rhoOne_cubicBranch_nextPacket hp hH hp6 hp5 hp4 hbranch
  have h2 := T.rhoOne_cubicBranch_nextTwo_zero hp hH hp6 hp5 hp4 hbranch
  dsimp only [RhoOneZeroLCubicRemainderSourcePacket68] at h2 ⊢
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  have h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0 := by
    simpa only [A, B, C0, D, E, a, b, c, d, e] using P.2.2.2.2.1
  have hforce := rhoOneZeroLCubic_nextFour_nextTwo_force68 a b c d e h4 h2
  have hcomponents :
      (a * b = 3 * d ∧ (b = 0 ∨ 3 * e = a * c)) ∨
      (a * b ^ 2 - b * d + 2 * c ^ 2 = 0 ∧
        a ^ 2 * b * c = 9 * d * e) := by
    rcases P.2.2.2.2.2.2 with hfirst | hsecond
    · exact Or.inl ⟨hfirst,
        rhoOneZeroLCubic_firstComponent_split68 a b c d e h4 hfirst⟩
    · exact Or.inr ⟨hsecond, hforce⟩
  exact ⟨P, h2, hforce, hcomponents⟩

/-- Exhaustive rho-one split with the cubic branch upgraded and the
degree-ten noncubic branch left explicit. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_component_split_with_cubic_remainder
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
      RhoOneZeroLCubicRemainderSourcePacket68 T g u ∨
      RhoOneZeroLNoncubicSourcePacket68 T g u := by
  rcases T.rhoOne_component_split hp hH hp6 hp5 hp4 with hdesc | hcubic | hnon
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl
      (T.rhoOne_cubicBranch_remainderPacket hp hH hp6 hp5 hp4 hcubic))
  · exact Or.inr (Or.inr hnon)

end AlignedSquareRhoOneCubicRemainder68

end Max11DegreeRoutes
