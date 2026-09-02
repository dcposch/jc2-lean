import Sol68ScaleTwoAlignedNonsquareTerminalKOneNextScratch

/-! # The first derivative below the surviving terminal G component -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

section TerminalGJetAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalGNextP68
    (h r x y u rd xd yd ud v : k) : k :=
  -3 * r ^ 6 * xd - r ^ 4 * rd * y + r ^ 5 * yd +
    162 * r ^ 3 * rd * u - 81 * r ^ 4 * ud + 243 * h * r ^ 3 * v +
    27 * h * r * y * u - 4374 * h * u ^ 2

def terminalGNextQ68
    (h r x y u rd xd yd ud v : k) : k :=
  27 * r ^ 4 * xd * y + 9 * r ^ 2 * rd * y ^ 2 -
    15 * h * r * x * y ^ 2 - 9 * r ^ 3 * y * yd +
    14580 * h * r * x ^ 2 * u - 4374 * r ^ 3 * xd * u +
    h * y ^ 3 - 2916 * r * rd * y * u - 972 * h * x * y * u +
    1458 * r ^ 2 * yd * u + 729 * r ^ 2 * y * ud -
    2187 * h * r * y * v + 236196 * rd * u ^ 2 -
    118098 * r * u * ud + 354294 * h * u * v

def terminalGNextEliminant68 (r x y u : k) : k :=
  -15 * r ^ 4 * x * y ^ 2 + 14580 * r ^ 4 * x ^ 2 * u +
    r ^ 3 * y ^ 3 - 972 * r ^ 3 * x * y * u +
    243 * r ^ 2 * y ^ 2 * u - 78732 * r * y * u ^ 2 +
    6377292 * u ^ 3

/-- The differentiated `I₄` and last-row faces have a compact resultant.
On the G component it forces the transverse factor itself to vanish. -/
theorem terminalG_nextJets_force_transverse_zero_68
    (h r x y u rd xd yd ud v : k) (hh : h ≠ 0)
    (hG : 3 * r ^ 2 * x - r * y + 81 * u = 0)
    (hP : terminalGNextP68 h r x y u rd xd yd ud v = 0)
    (hQ : terminalGNextQ68 h r x y u rd xd yd ud v = 0) :
    -r * y + 162 * u = 0 := by
  let T := terminalGNextEliminant68 r x y u
  have hTscaled : h ^ 2 * T = 0 := by
    dsimp only [terminalGNextP68] at hP
    dsimp only [terminalGNextQ68] at hQ
    dsimp only [T, terminalGNextEliminant68]
    linear_combination
      (-9 * h * (-r * y + 162 * u)) * hP + (h * r ^ 3) * hQ
  have hT : T = 0 := by
    exact (mul_eq_zero.mp hTscaled).resolve_left (pow_ne_zero 2 hh)
  have hz3 : (-r * y + 162 * u) ^ 3 = 0 := by
    dsimp only [T, terminalGNextEliminant68] at hT
    linear_combination (1 / 4 : k) * hT -
      (1 / 4 : k) *
        (-5 * r ^ 2 * y ^ 2 + 4860 * r ^ 2 * x * u +
          1296 * r * y * u - 131220 * u ^ 2) * hG
  by_contra hz
  exact (pow_ne_zero 3 hz) hz3

theorem terminalG_nextJets_delete_nonzero_b_68
    (h r x y u b rd xd yd ud v : k) (hh : h ≠ 0) (hr : r ≠ 0)
    (hb : b = (y - 6 * r * x) / 27)
    (hG : 3 * r ^ 2 * x - r * y + 81 * u = 0)
    (hP : terminalGNextP68 h r x y u rd xd yd ud v = 0)
    (hQ : terminalGNextQ68 h r x y u rd xd yd ud v = 0) :
    b = 0 := by
  have hz := terminalG_nextJets_force_transverse_zero_68
    h r x y u rd xd yd ud v hh hG hP hQ
  have hrb : 27 * r * b = 0 := by
    rw [hb]
    linear_combination hz - 2 * hG
  have h27r : 27 * r ≠ 0 := mul_ne_zero (by norm_num) hr
  exact (mul_eq_zero.mp hrb).resolve_left h27r

end TerminalGJetAlgebra68

section TerminalGReducedPolynomials68

variable {k : Type*} [Field k] [CharZero k]

def terminalGReducedA68 (H r X : k[X]) : k[X] :=
  -C (1 / 12 : k) * r ^ 2 + C (1 / 3 : k) * H * X

def terminalGReducedB68 (r X Yd : k[X]) : k[X] :=
  C (1 / 27 : k) * (Yd - (6 : k[X]) * r * X)

def terminalGReducedC68
    (H r X Yd p2 : k[X]) : k[X] :=
  H * p2 - C (1 / 54 : k) * r * (r ^ 3 + H * Yd) +
    C (1 / 18 : k) * (r ^ 2 + H * X) * r ^ 2 -
    C (5 / 144 : k) * r ^ 4

def terminalGReducedD68
    (H r X Yd p1 p2 : k[X]) : k[X] :=
  H * p1 - C (1 / 3 : k) * r * p2 +
    C (1 / 324 : k) * r ^ 2 * Yd - C (1 / 162 : k) * r ^ 3 * X

def terminalGReducedE68
    (H r X Yd p0 p1 p2 : k[X]) : k[X] :=
  H ^ 3 * p0 - C (1 / 6 : k) * H ^ 2 * p1 * r +
    C (1 / 36 : k) * H * p2 * r ^ 2 -
    C (1 / 5832 : k) * (r ^ 3 + H * Yd) * r ^ 3 +
    C (1 / 3888 : k) * (r ^ 2 + H * X) * r ^ 4 -
    C (5 / 46656 : k) * r ^ 6

def terminalGReducedW68
    (H r X Yd p2 : k[X]) (gamma : k) : k[X] :=
  C (4 / 9 : k) * p2 - C (2 / 243 : k) * r * Yd +
    C (8 / 243 : k) * r ^ 2 * X +
    H * (-C (4 / 243 : k) * X ^ 2 + C (2 / 3 * gamma : k))

def terminalGReducedPhi68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon : k) : k[X] :=
  C (2 / 9 : k) * r ^ 2 * p2 - C (7 / 2187 : k) * r ^ 3 * Yd +
    C (8 / 729 : k) * r ^ 4 * X +
    H * (-C (134 / 2187 : k) * r ^ 2 * X ^ 2 +
      C (104 / 6561 : k) * r * X * Yd + C (1 / 9 * gamma : k) * r ^ 2 -
      C (8 / 19683 : k) * Yd ^ 2 - C (4 / 9 : k) * r * p1 -
      C (16 / 27 : k) * X * p2) +
    H ^ 2 * (C (40 / 2187 : k) * X ^ 3 - C (4 / 9 * gamma : k) * X +
      C (8 / 3 : k) * p0 + C (2 * epsilon : k))

def terminalGReducedKOne68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let A := terminalGReducedA68 H r X
  let b := terminalGReducedB68 r X Yd
  let C0 := terminalGReducedC68 H r X Yd p2
  let d := terminalGReducedD68 H r X Yd p1 p2
  let E0 := terminalGReducedE68 H r X Yd p0 p1 p2
  let w := terminalGReducedW68 H r X Yd p2 gamma
  let phi := terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon
  let c := terminalCShiftNumerator68 H A alpha
  let V := terminalVNumerator68 H A b C0 d E0 alpha gamma epsilon eta
  let R := terminalKDotLoadQuotient68 H A b C0 d E0 w phi
    alpha gamma epsilon eta
  terminalKDotNext68 H E0 V c R

def terminalGReducedEDot68
    (H r X Yd p0 p1 p2 : k[X]) : k[X] :=
  terminalEDerivativeNumerator68 H
    (terminalGReducedE68 H r X Yd p0 p1 p2)

/-- Mechanical first-derivative factor of the quotient `I₄` row. -/
theorem terminalG_reduced_I4_derivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0)
    (hG : 3 * (r.eval a) ^ 2 * X.eval a - r.eval a * Yd.eval a +
      81 * p2.eval a = 0) :
    ((terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2).derivative).eval a =
      -(8 / 531441 : k) * terminalGNextQ68
        (H.derivative.eval a) (r.eval a) (X.eval a) (Yd.eval a)
        (p2.eval a) (r.derivative.eval a) (X.derivative.eval a)
        (Yd.derivative.eval a) (p2.derivative.eval a) (p1.eval a) := by
  have hu : p2.eval a =
      (r.eval a * Yd.eval a - 3 * (r.eval a) ^ 2 * X.eval a) / 81 := by
    linear_combination (1 / 81 : k) * hG
  simp only [terminalGReducedB68, terminalGReducedPhi68,
    terminalGReducedW68, terminalGReducedD68, terminalGNextQ68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly, eval_add,
    eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
    ha, zero_mul, zero_add, add_zero, mul_zero, zero_pow]
  rw [hu]
  ring

/-- Mechanical first-derivative factor of the five-times-cancelled last row. -/
theorem terminalG_reduced_lastRow_derivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0)
    (hG : 3 * (r.eval a) ^ 2 * X.eval a - r.eval a * Yd.eval a +
      81 * p2.eval a = 0) :
    let b := terminalGReducedB68 r X Yd
    let d := terminalGReducedD68 H r X Yd p1 p2
    let w := terminalGReducedW68 H r X Yd p2 gamma
    let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
    let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
      alpha gamma epsilon eta
    ((b * w * eDot - d * k1).derivative).eval a =
      -(1 / 19131876 : k) * H.derivative.eval a * r.eval a *
        (-r.eval a * Yd.eval a + 162 * p2.eval a) *
        terminalGNextP68
          (H.derivative.eval a) (r.eval a) (X.eval a) (Yd.eval a)
          (p2.eval a) (r.derivative.eval a) (X.derivative.eval a)
          (Yd.derivative.eval a) (p2.derivative.eval a) (p1.eval a) := by
  dsimp only
  have hu : p2.eval a =
      (r.eval a * Yd.eval a - 3 * (r.eval a) ^ 2 * X.eval a) / 81 := by
    linear_combination (1 / 81 : k) * hG
  simp only [terminalGReducedKOne68, terminalGReducedEDot68,
    terminalGReducedA68, terminalGReducedB68, terminalGReducedC68,
    terminalGReducedD68, terminalGReducedE68, terminalGReducedW68,
    terminalGReducedPhi68, terminalKDotNext68,
    terminalCShiftNumerator68, terminalVNumerator68,
    terminalKDotLoadQuotient68, terminalEDerivativeNumerator68,
    terminalGNextP68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, zero_mul, zero_add, add_zero, mul_zero,
    zero_pow]
  rw [hu]
  ring

end TerminalGReducedPolynomials68

section TerminalGNextSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- After the first differentiated terminal packet, both transverse
components have disappeared: at every core root either `r` or the odd
quotient `b₁` vanishes.  Consequently `H | r*b₁`. -/
theorem NonsquareAlignedSourceCurveData68.terminalGNextSourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t X Yd b1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      (∀ a : k, H.eval a = 0 → r.eval a = 0 ∨ b1.eval a = 0) ∧
      H ∣ r * b1 := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, hg, hr, ht, hX, hY,
      hb1, hd1, hw1, hphi1, hkdef, hrowdef, hbranches⟩ :=
    S.terminalKOneNextSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let c0 := terminalCShiftNumerator68 H A0 S.alpha
  let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
    S.epsilon S.eta
  let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
    S.alpha S.gamma S.epsilon S.eta
  let eDot := terminalEDerivativeNumerator68 H E0
  have hkcanonical : k1 = terminalKDotNext68 H E0 V0 c0 R1 := by
    simpa only [A0, C0, E0, c0, V0, R1] using hkdef
  have hrow5 : b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    simpa only [A0, C0, E0, eDot] using hrowdef
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hI4source := S.terminalI4_cleared_source_identity (H := H)
    hp hp6 hg hr ht
  rw [hb1, hd1, hw1, hphi1] at hI4source
  have hI4factor : H ^ 2 * (b1 * phi1 + (6 : k[X]) * w1 * d1) = 0 := by
    linear_combination hI4source
  have hI4 : b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 :=
    (mul_eq_zero.mp hI4factor).resolve_left (pow_ne_zero 2 hH)
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi1
  rcases hfactor with ⟨hbform, hdform, hwform, hphiform⟩
  let AR := terminalGReducedA68 H r X
  let bR := terminalGReducedB68 r X Yd
  let CR := terminalGReducedC68 H r X Yd (p.coeff 2)
  let dR := terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2)
  let ER := terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2)
  let wR := terminalGReducedW68 H r X Yd (p.coeff 2) S.gamma
  let phiR := terminalGReducedPhi68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2) S.gamma S.epsilon
  let eR := terminalGReducedEDot68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2)
  let kR := terminalGReducedKOne68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2) S.alpha S.gamma S.epsilon S.eta
  have hbR : b1 = bR := by
    simpa only [bR, terminalGReducedB68] using hbform
  have hdR : d1 = dR := by
    simpa only [dR, terminalGReducedD68] using hdform
  have hwR : w1 = wR := by
    simpa only [wR, terminalGReducedW68] using hwform
  have hphiR : phi1 = phiR := by
    simpa only [phiR, terminalGReducedPhi68] using hphiform
  have hunit3 : C (1 / 3 : k) * (3 : k[X]) = 1 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_mul, map_one, RatFunc.algebraMap_C, map_div₀, map_ofNat]
    ring
  have ht' : t = C (1 / 3 : k) * (r ^ 2 + H * X) := by
    calc
      t = (C (1 / 3 : k) * (3 : k[X])) * t := by rw [hunit3, one_mul]
      _ = C (1 / 3 : k) * (r ^ 2 + H * X) := by
        rw [mul_assoc]
        congr 1
        linear_combination hX
  have hunit27 : C (1 / 27 : k) * (27 : k[X]) = 1 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_mul, map_one, RatFunc.algebraMap_C, map_div₀, map_ofNat]
    ring
  have hp3' : p.coeff 3 = C (1 / 27 : k) * (r ^ 3 + H * Yd) := by
    calc
      p.coeff 3 = (C (1 / 27 : k) * (27 : k[X])) * p.coeff 3 := by
        rw [hunit27, one_mul]
      _ = C (1 / 27 : k) * (r ^ 3 + H * Yd) := by
        rw [mul_assoc]
        congr 1
        linear_combination hY
  have hAR : A0 = AR := by
    dsimp only [A0, AR, cubicANumerator68, terminalGReducedA68]
    rw [ht']
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
    ring
  have hCR : C0 = CR := by
    dsimp only [C0, CR, cubicCNumerator68, terminalGReducedC68]
    rw [ht', hp3']
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
    ring
  have hER : E0 = ER := by
    dsimp only [E0, ER, cubicENumerator68, terminalGReducedE68]
    rw [ht', hp3']
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
    ring
  have heR : eDot = eR := by
    dsimp only [eDot, eR, terminalGReducedEDot68]
    rw [hER]
  have hkR : k1 = kR := by
    rw [hkcanonical]
    dsimp only [kR, terminalGReducedKOne68]
    rw [show terminalGReducedA68 H r X = A0 from hAR.symm,
      show terminalGReducedB68 r X Yd = b1 from hbR.symm,
      show terminalGReducedC68 H r X Yd (p.coeff 2) = C0 from hCR.symm,
      show terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) = d1
        from hdR.symm,
      show terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1)
          (p.coeff 2) = E0 from hER.symm,
      show terminalGReducedW68 H r X Yd (p.coeff 2) S.gamma = w1
        from hwR.symm,
      show terminalGReducedPhi68 H r X Yd (p.coeff 0) (p.coeff 1)
          (p.coeff 2) S.gamma S.epsilon = phi1 from hphiR.symm]
  have hI4R : bR * phiR + (6 : k[X]) * wR * dR = 0 := by
    simpa only [← hbR, ← hphiR, ← hwR, ← hdR] using hI4
  have hrowR : bR * wR * eR - dR * kR = C j * H ^ 5 := by
    simpa only [← hbR, ← hwR, ← heR, ← hdR, ← hkR] using hrow5
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hroot : ∀ a : k, H.eval a = 0 → r.eval a = 0 ∨ b1.eval a = 0 := by
    intro a ha
    rcases hbranches a ha with hr0 | hF | hG
    · exact Or.inl hr0
    · exact Or.inr hF.2
    · rcases eq_or_ne (r.eval a) 0 with hr0 | hrne
      · exact Or.inl hr0
      · right
        rcases hG.2 with hb0 | _hkG
        · exact hb0
        · by_contra hbne
          have hbRne : bR.eval a ≠ 0 := by simpa only [← hbR] using hbne
          have hGscalar := hG.1
          have hzrel : -r.eval a * Yd.eval a + 162 * (p.coeff 2).eval a =
              27 * r.eval a * bR.eval a := by
            dsimp only [bR, terminalGReducedB68]
            simp only [eval_mul, eval_sub, eval_C, eval_ofNat]
            linear_combination 2 * hGscalar
          have hznie : -r.eval a * Yd.eval a + 162 * (p.coeff 2).eval a ≠ 0 := by
            rw [hzrel]
            exact mul_ne_zero (mul_ne_zero (by norm_num) hrne) hbRne
          have hI4d :
              ((bR * phiR + (6 : k[X]) * wR * dR).derivative).eval a = 0 := by
            rw [hI4R, derivative_zero, eval_zero]
          have hQfactor := terminalG_reduced_I4_derivative_factor_68
            H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
            S.gamma S.epsilon a ha hGscalar
          have hQeq : 0 = -(8 / 531441 : k) * terminalGNextQ68
              (H.derivative.eval a) (r.eval a) (X.eval a) (Yd.eval a)
              ((p.coeff 2).eval a) (r.derivative.eval a) (X.derivative.eval a)
              (Yd.derivative.eval a) ((p.coeff 2).derivative.eval a)
              ((p.coeff 1).eval a) := by
            calc
              0 = ((bR * phiR + (6 : k[X]) * wR * dR).derivative).eval a :=
                hI4d.symm
              _ = _ := by
                simpa only [bR, phiR, wR, dR] using hQfactor
          have hQzero : terminalGNextQ68
              (H.derivative.eval a) (r.eval a) (X.eval a) (Yd.eval a)
              ((p.coeff 2).eval a) (r.derivative.eval a) (X.derivative.eval a)
              (Yd.derivative.eval a) ((p.coeff 2).derivative.eval a)
              ((p.coeff 1).eval a) = 0 := by
            have hc : -(8 / 531441 : k) ≠ 0 := by norm_num
            exact (mul_eq_zero.mp hQeq.symm).resolve_left hc
          have hrowd : ((bR * wR * eR - dR * kR).derivative).eval a = 0 := by
            have hd := congrArg (fun f : k[X] => f.derivative.eval a) hrowR
            simpa [derivative_mul, derivative_pow, derivative_C, ha] using hd
          have hPfactor := terminalG_reduced_lastRow_derivative_factor_68
            H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
            S.alpha S.gamma S.epsilon S.eta a ha hGscalar
          dsimp only [bR, dR, wR, eR, kR] at hPfactor
          rw [hrowd] at hPfactor
          have hPzero : terminalGNextP68
              (H.derivative.eval a) (r.eval a) (X.eval a) (Yd.eval a)
              ((p.coeff 2).eval a) (r.derivative.eval a) (X.derivative.eval a)
              (Yd.derivative.eval a) ((p.coeff 2).derivative.eval a)
              ((p.coeff 1).eval a) = 0 := by
            have hc : -(1 / 19131876 : k) * H.derivative.eval a * r.eval a *
                (-r.eval a * Yd.eval a + 162 * (p.coeff 2).eval a) ≠ 0 :=
              mul_ne_zero
                (mul_ne_zero (mul_ne_zero (by norm_num) (hsimple a ha)) hrne)
                hznie
            exact (mul_eq_zero.mp hPfactor.symm).resolve_left hc
          have hbRzero := terminalG_nextJets_delete_nonzero_b_68
            (H.derivative.eval a) (r.eval a) (X.eval a) (Yd.eval a)
            ((p.coeff 2).eval a) (bR.eval a) (r.derivative.eval a)
            (X.derivative.eval a) (Yd.derivative.eval a)
            ((p.coeff 2).derivative.eval a) ((p.coeff 1).eval a)
            (hsimple a ha) hrne (by
              dsimp only [bR, terminalGReducedB68]
              simp only [eval_mul, eval_sub, eval_C, eval_ofNat]
              ring) hGscalar hPzero hQzero
          exact hbRne hbRzero
  have hdvd : H ∣ r * b1 := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    rcases hroot a ha with hr0 | hb0
    · simp [eval_mul, hr0]
    · simp [eval_mul, hb0]
  exact ⟨g, r, t, X, Yd, b1, hg, hr, ht, hX, hY, hb1, hroot, hdvd⟩

end TerminalGNextSource68

end Max11DegreeRoutes
