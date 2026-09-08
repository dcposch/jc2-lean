import LowScale68ScaleTwoAlignedNonsquarePolynomialEndgame

/-! # Exact even-cleared divisibility and face products for aligned
nonsquare `(6,8)`

The even-cleared closed forms of `A,C₀,E`, generic monic integrality of
`k[x]`, exact division, the `D=0` polynomial last-row product, and the
`B=0` even formulae for `V` and the `I₃` remainder are taken from
`LowScale68ScaleTwoAlignedNonsquarePolynomialEndgame`.  The input packet
is `NonsquareAlignedSourceCurveData68.polynomialEndgamePacket`.

Degree-specific `(4,6)` residuals are not used: not the aligned shift
`V=0`, not the boundary quartic, not `K=B²` reconstruction from that
quartic, and not the last-row restriction to `(-3/4) B² dB`.  No
twice-prime or total-degree argument is used.

The strongest exact `(6,8)` eliminant available without a new source
input is the even-cleared ratio `N/H^n` together with the division
criterion `H^n ∣ N`.  After that divisibility the linear polynomial
`Z-Q` is monic over `k[x]` and feeds both coordinate faces `D=0` and
`B=0`.  The three `H`-power divisibilities themselves are the smallest
missing input.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section EvenClearedRelation68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact `(6,8)` relation for the even coordinate `A`: not monic unless
`H^5` is a unit. -/
def evenClearedRelationA68 (H a5 a4 : k[X]) : (k[X])[X] :=
  C (H ^ 5) * X - C (evenClearedA68 H a5 a4)

/-- Exact `(6,8)` relation for the even coordinate `C₀`. -/
def evenClearedRelationC68 (H a5 a4 a3 a2 : k[X]) : (k[X])[X] :=
  C (H ^ 10) * X - C (evenClearedC68 H a5 a4 a3 a2)

/-- Exact `(6,8)` relation for the even coordinate `E`. -/
def evenClearedRelationE68 (H a5 a4 a3 a2 a1 a0 : k[X]) : (k[X])[X] :=
  C (H ^ 15) * X - C (evenClearedE68 H a5 a4 a3 a2 a1 a0)

theorem evenClearedRelationA68_eval
    (H a5 a4 : k[X]) (hH : H ≠ 0) :
    eval₂ (algebraMap k[X] (RatFunc k))
        (algebraMap k[X] (RatFunc k) (evenClearedA68 H a5 a4) /
          algebraMap k[X] (RatFunc k) (H ^ 5))
        (evenClearedRelationA68 H a5 a4) = 0 := by
  have hD : algebraMap k[X] (RatFunc k) (H ^ 5) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 5 hH)
  simp only [evenClearedRelationA68, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X]
  field_simp [hD]
  ring

theorem evenClearedRelationC68_eval
    (H a5 a4 a3 a2 : k[X]) (hH : H ≠ 0) :
    eval₂ (algebraMap k[X] (RatFunc k))
        (algebraMap k[X] (RatFunc k) (evenClearedC68 H a5 a4 a3 a2) /
          algebraMap k[X] (RatFunc k) (H ^ 10))
        (evenClearedRelationC68 H a5 a4 a3 a2) = 0 := by
  have hD : algebraMap k[X] (RatFunc k) (H ^ 10) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 10 hH)
  simp only [evenClearedRelationC68, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X]
  field_simp [hD]
  ring

theorem evenClearedRelationE68_eval
    (H a5 a4 a3 a2 a1 a0 : k[X]) (hH : H ≠ 0) :
    eval₂ (algebraMap k[X] (RatFunc k))
        (algebraMap k[X] (RatFunc k)
            (evenClearedE68 H a5 a4 a3 a2 a1 a0) /
          algebraMap k[X] (RatFunc k) (H ^ 15))
        (evenClearedRelationE68 H a5 a4 a3 a2 a1 a0) = 0 := by
  have hD : algebraMap k[X] (RatFunc k) (H ^ 15) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 15 hH)
  simp only [evenClearedRelationE68, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X]
  field_simp [hD]
  ring

/-- After `H^5 ∣ N_A` the even-cleared relation reduces to a monic
linear eliminant `Z-Q` over `k[x]`. -/
theorem evenClearedMonicEliminantA68_of_dvd
    (H a5 a4 : k[X]) (hH : H ≠ 0)
    (hdvd : H ^ 5 ∣ evenClearedA68 H a5 a4) :
    ∃ Q : k[X],
      (X - C Q).Monic ∧
      algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (evenClearedA68 H a5 a4) /
          algebraMap k[X] (RatFunc k) (H ^ 5) ∧
      eval₂ (algebraMap k[X] (RatFunc k))
          (algebraMap k[X] (RatFunc k) (evenClearedA68 H a5 a4) /
            algebraMap k[X] (RatFunc k) (H ^ 5))
          (X - C Q) = 0 := by
  obtain ⟨Q, hQ⟩ := (ratFunc_div_isPolynomial_iff_dvd68
      (evenClearedA68 H a5 a4) (H ^ 5) (pow_ne_zero 5 hH)).mpr hdvd
  refine ⟨Q, monic_X_sub_C Q, hQ, ?_⟩
  simp only [eval₂_sub, eval₂_X, eval₂_C, hQ, sub_self]

theorem evenClearedMonicEliminantC68_of_dvd
    (H a5 a4 a3 a2 : k[X]) (hH : H ≠ 0)
    (hdvd : H ^ 10 ∣ evenClearedC68 H a5 a4 a3 a2) :
    ∃ Q : k[X],
      (X - C Q).Monic ∧
      algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (evenClearedC68 H a5 a4 a3 a2) /
          algebraMap k[X] (RatFunc k) (H ^ 10) ∧
      eval₂ (algebraMap k[X] (RatFunc k))
          (algebraMap k[X] (RatFunc k) (evenClearedC68 H a5 a4 a3 a2) /
            algebraMap k[X] (RatFunc k) (H ^ 10))
          (X - C Q) = 0 := by
  obtain ⟨Q, hQ⟩ := (ratFunc_div_isPolynomial_iff_dvd68
      (evenClearedC68 H a5 a4 a3 a2) (H ^ 10)
      (pow_ne_zero 10 hH)).mpr hdvd
  refine ⟨Q, monic_X_sub_C Q, hQ, ?_⟩
  simp only [eval₂_sub, eval₂_X, eval₂_C, hQ, sub_self]

theorem evenClearedMonicEliminantE68_of_dvd
    (H a5 a4 a3 a2 a1 a0 : k[X]) (hH : H ≠ 0)
    (hdvd : H ^ 15 ∣ evenClearedE68 H a5 a4 a3 a2 a1 a0) :
    ∃ Q : k[X],
      (X - C Q).Monic ∧
      algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k)
            (evenClearedE68 H a5 a4 a3 a2 a1 a0) /
          algebraMap k[X] (RatFunc k) (H ^ 15) ∧
      eval₂ (algebraMap k[X] (RatFunc k))
          (algebraMap k[X] (RatFunc k)
              (evenClearedE68 H a5 a4 a3 a2 a1 a0) /
            algebraMap k[X] (RatFunc k) (H ^ 15))
          (X - C Q) = 0 := by
  obtain ⟨Q, hQ⟩ := (ratFunc_div_isPolynomial_iff_dvd68
      (evenClearedE68 H a5 a4 a3 a2 a1 a0) (H ^ 15)
      (pow_ne_zero 15 hH)).mpr hdvd
  refine ⟨Q, monic_X_sub_C Q, hQ, ?_⟩
  simp only [eval₂_sub, eval₂_X, eval₂_C, hQ, sub_self]

/-- Direct polynomial representative of the `B=0` first-integral
remainder. -/
theorem ratFunc_I3rem_of_B_zero_polynomial68
    (aR cR eR remR : RatFunc k) (A0 C0p E0 : k[X])
    (gamma epsilon : k)
    (hA : algebraMap k[X] (RatFunc k) A0 = aR)
    (hC : algebraMap k[X] (RatFunc k) C0p = cR)
    (hE : algebraMap k[X] (RatFunc k) E0 = eR)
    (hrem :
      remR =
        (-16 / 243 : RatFunc k) * aR ^ 5 +
          (2 : RatFunc k) * cR * algebraMap k (RatFunc k) epsilon +
          (4 : RatFunc k) * eR * algebraMap k (RatFunc k) gamma -
          (8 / 9 : RatFunc k) * aR * cR ^ 2 -
          (8 / 9 : RatFunc k) * aR ^ 2 * eR -
          (2 / 3 : RatFunc k) * aR ^ 2 *
            algebraMap k (RatFunc k) epsilon +
          (8 / 3 : RatFunc k) * cR * eR +
          (8 / 27 : RatFunc k) * aR ^ 3 *
            algebraMap k (RatFunc k) gamma +
          (40 / 81 : RatFunc k) * aR ^ 3 * cR -
          (4 / 3 : RatFunc k) * aR * cR *
            algebraMap k (RatFunc k) gamma) :
    ∃ Rem0 : k[X], algebraMap k[X] (RatFunc k) Rem0 = remR := by
  refine ⟨C (-16 / 243 : k) * A0 ^ 5 +
      C (2 : k) * C0p * C epsilon + C (4 : k) * E0 * C gamma -
      C (8 / 9 : k) * A0 * C0p ^ 2 - C (8 / 9 : k) * A0 ^ 2 * E0 -
      C (2 / 3 : k) * A0 ^ 2 * C epsilon +
      C (8 / 3 : k) * C0p * E0 +
      C (8 / 27 : k) * A0 ^ 3 * C gamma +
      C (40 / 81 : k) * A0 ^ 3 * C0p -
      C (4 / 3 : k) * A0 * C0p * C gamma, ?_⟩
  simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
    hA, hC, hE]
  simp only [← RatFunc.algebraMap_eq_C]
  have hdiv (a b : ℕ) :
      algebraMap k (RatFunc k) ((a : k) / (b : k)) =
        (a : RatFunc k) / (b : RatFunc k) := by
    rw [map_div₀, map_natCast, map_natCast]
  have h16243 : algebraMap k (RatFunc k) (-16 / 243 : k) =
      (-16 / 243 : RatFunc k) := by
    simp only [map_div₀, map_neg, map_ofNat]
  have h2 : algebraMap k (RatFunc k) (2 : k) = (2 : RatFunc k) := by
    rw [map_ofNat]
  have h4 : algebraMap k (RatFunc k) (4 : k) = (4 : RatFunc k) := by
    rw [map_ofNat]
  have h89 : algebraMap k (RatFunc k) (8 / 9 : k) =
      (8 / 9 : RatFunc k) := by
    simpa using hdiv 8 9
  have h23 : algebraMap k (RatFunc k) (2 / 3 : k) =
      (2 / 3 : RatFunc k) := by
    simpa using hdiv 2 3
  have h83 : algebraMap k (RatFunc k) (8 / 3 : k) =
      (8 / 3 : RatFunc k) := by
    simpa using hdiv 8 3
  have h827 : algebraMap k (RatFunc k) (8 / 27 : k) =
      (8 / 27 : RatFunc k) := by
    simpa using hdiv 8 27
  have h4081 : algebraMap k (RatFunc k) (40 / 81 : k) =
      (40 / 81 : RatFunc k) := by
    simpa using hdiv 40 81
  have h43 : algebraMap k (RatFunc k) (4 / 3 : k) =
      (4 / 3 : RatFunc k) := by
    simpa using hdiv 4 3
  rw [h16243, h2, h4, h89, h23, h83, h827, h4081, h43]
  exact hrem.symm

end EvenClearedRelation68

section QuadraticMonicEliminant68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticMonicEliminantCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

theorem algebraMap_C_ground_F68 (c : k) :
    algebraMap k[X] F68 (C c) = algebraMap k F68 c := by
  simpa using (IsScalarTower.algebraMap_apply k k[X] F68 c).symm

theorem algebraMap_C_eq_F68 (c : k) {z : F68}
    (h : algebraMap k F68 c = z) :
    algebraMap k[X] F68 (C c) = z :=
  (algebraMap_C_ground_F68 (H := H) c).trans h

theorem map_evenClearedA68_quadratic (a5 a4 : k[X]) :
    let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
    quadraticCoefficientMap46 H a4 * (h ^ 2) ^ 3 -
        (5 / 12 : F68) * (quadraticCoefficientMap46 H a5) ^ 2 =
      algebraMap k[X] F68 (evenClearedA68 H a5 a4) := by
  intro h
  have hroot : h ^ 2 = algebraMap k[X] F68 H := by
    rw [← quadraticCoefficientMap46_eq_algebraMap H H]
    exact alignedQuadraticRoot_sq46 H
  simp only [evenClearedA68, map_sub, map_mul, map_pow,
    quadraticCoefficientMap46_eq_algebraMap]
  have h512 : algebraMap k[X] F68 (C (5 / 12 : k)) =
      (5 / 12 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_ofNat, map_ofNat])
  rw [hroot, h512]

theorem map_evenClearedC68_quadratic (a5 a4 a3 a2 : k[X]) :
    let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
    quadraticCoefficientMap46 H a2 * (h ^ 2) ^ 9 -
        (1 / 2 : F68) * quadraticCoefficientMap46 H a3 *
          quadraticCoefficientMap46 H a5 * (h ^ 2) ^ 6 +
        (1 / 6 : F68) * quadraticCoefficientMap46 H a4 *
          (quadraticCoefficientMap46 H a5) ^ 2 * (h ^ 2) ^ 3 -
        (5 / 144 : F68) * (quadraticCoefficientMap46 H a5) ^ 4 =
      algebraMap k[X] F68 (evenClearedC68 H a5 a4 a3 a2) := by
  intro h
  have hroot : h ^ 2 = algebraMap k[X] F68 H := by
    rw [← quadraticCoefficientMap46_eq_algebraMap H H]
    exact alignedQuadraticRoot_sq46 H
  simp only [evenClearedC68, map_sub, map_add, map_mul, map_pow,
    quadraticCoefficientMap46_eq_algebraMap]
  have h12 : algebraMap k[X] F68 (C (1 / 2 : k)) = (1 / 2 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_one, map_ofNat])
  have h16 : algebraMap k[X] F68 (C (1 / 6 : k)) = (1 / 6 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_one, map_ofNat])
  have h5144 : algebraMap k[X] F68 (C (5 / 144 : k)) =
      (5 / 144 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_ofNat, map_ofNat])
  rw [hroot, h12, h16, h5144]

set_option maxHeartbeats 2000000 in
theorem map_evenClearedE68_quadratic
    (a5 a4 a3 a2 a1 a0 : k[X]) :
    let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
    quadraticCoefficientMap46 H a0 * (h ^ 2) ^ 15 -
        (1 / 6 : F68) * quadraticCoefficientMap46 H a1 *
          quadraticCoefficientMap46 H a5 * (h ^ 2) ^ 12 +
        (1 / 36 : F68) * quadraticCoefficientMap46 H a2 *
          (quadraticCoefficientMap46 H a5) ^ 2 * (h ^ 2) ^ 9 -
        (1 / 216 : F68) * quadraticCoefficientMap46 H a3 *
          (quadraticCoefficientMap46 H a5) ^ 3 * (h ^ 2) ^ 6 +
        (1 / 1296 : F68) * quadraticCoefficientMap46 H a4 *
          (quadraticCoefficientMap46 H a5) ^ 4 * (h ^ 2) ^ 3 -
        (5 / 46656 : F68) * (quadraticCoefficientMap46 H a5) ^ 6 =
      algebraMap k[X] F68 (evenClearedE68 H a5 a4 a3 a2 a1 a0) := by
  intro h
  have hroot : h ^ 2 = algebraMap k[X] F68 H := by
    rw [← quadraticCoefficientMap46_eq_algebraMap H H]
    exact alignedQuadraticRoot_sq46 H
  simp only [evenClearedE68, map_sub, map_add, map_mul, map_pow,
    quadraticCoefficientMap46_eq_algebraMap]
  have h16 : algebraMap k[X] F68 (C (1 / 6 : k)) = (1 / 6 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_one, map_ofNat])
  have h136 : algebraMap k[X] F68 (C (1 / 36 : k)) =
      (1 / 36 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_one, map_ofNat])
  have h1216 : algebraMap k[X] F68 (C (1 / 216 : k)) =
      (1 / 216 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_one, map_ofNat])
  have h11296 : algebraMap k[X] F68 (C (1 / 1296 : k)) =
      (1 / 1296 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_one, map_ofNat])
  have h546656 : algebraMap k[X] F68 (C (5 / 46656 : k)) =
      (5 / 46656 : F68) :=
    algebraMap_C_eq_F68 (H := H) _ (by rw [map_div₀, map_ofNat, map_ofNat])
  rw [hroot, h16, h136, h1216, h11296, h546656]

/-- A ratio of polynomial images in the quadratic field is polynomial
if and only if the denominator divides the numerator. -/
theorem algebraMap_div_isPolynomial_iff_dvdF68
    (N D : k[X]) (z : F68) (hD : D ≠ 0)
    (hz : z = algebraMap k[X] F68 N / algebraMap k[X] F68 D) :
    (∃ Q : k[X], algebraMap k[X] F68 Q = z) ↔ D ∣ N := by
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hN : algebraMap k[X] F68 N =
      algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) N) :=
    IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 N
  have hDmap : algebraMap k[X] F68 D =
      algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) D) :=
    IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 D
  have hQmap (Q : k[X]) : algebraMap k[X] F68 Q =
      algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) Q) :=
    IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 Q
  have hratio :
      z = algebraMap (RatFunc k) F68
        (algebraMap k[X] (RatFunc k) N /
          algebraMap k[X] (RatFunc k) D) := by
    rw [hz, hN, hDmap, map_div₀]
  constructor
  · intro ⟨Q, hQz⟩
    have hRat : algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) N /
          algebraMap k[X] (RatFunc k) D := by
      apply hι
      rw [← hQmap, hQz, hratio]
    exact (ratFunc_div_isPolynomial_iff_dvd68 N D hD).mp ⟨Q, hRat⟩
  · intro hdvd
    obtain ⟨Q, hQ⟩ :=
      (ratFunc_div_isPolynomial_iff_dvd68 N D hD).mpr hdvd
    refine ⟨Q, ?_⟩
    rw [hQmap, hQ]
    exact hratio.symm

/-- Source identification of `A` with the even-cleared ratio `N_A/H⁵`. -/
theorem NonsquareAlignedSourceCurveData68.A_eq_evenClearedDiv
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    S.A =
      algebraMap k[X] F68 (evenClearedA68 H (p.coeff 5) (p.coeff 4)) /
        algebraMap k[X] F68 (H ^ 5) := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 := quadraticCoefficientMap46 H (p.coeff 4)
  have hA : S.A = depressedA68 h S.r a5 a4 :=
    (S.eq_depressed (H := H) hp hp6).1
  have hr := S.r_eq_depression (H := H) hp hp6
  have hh : h ≠ 0 := S.scale_ne_zero
  have heven := depressedA68_evenCleared h S.r a5 a4 hh hr
  have hnum := map_evenClearedA68_quadratic (H := H) (p.coeff 5)
    (p.coeff 4)
  have hroot : h ^ 2 = algebraMap k[X] F68 H := by
    rw [← quadraticCoefficientMap46_eq_algebraMap H H]
    exact alignedQuadraticRoot_sq46 H
  have hden : (h ^ 2) ^ 5 = algebraMap k[X] F68 (H ^ 5) := by
    rw [hroot, map_pow]
  rw [hA, heven, hnum, hden]

/-- Source identification of `C₀` with the even-cleared ratio
`N_C/H¹⁰`. -/
theorem NonsquareAlignedSourceCurveData68.C0_eq_evenClearedDiv
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    S.C0 =
      algebraMap k[X] F68
          (evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2)) /
        algebraMap k[X] F68 (H ^ 10) := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 := quadraticCoefficientMap46 H (p.coeff 4)
  let a3 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 := quadraticCoefficientMap46 H (p.coeff 2)
  have hC : S.C0 = depressedC68 h S.r a5 a4 a3 a2 :=
    (S.eq_depressed (H := H) hp hp6).2.1
  have hr := S.r_eq_depression (H := H) hp hp6
  have hh : h ≠ 0 := S.scale_ne_zero
  have heven := depressedC68_evenCleared h S.r a5 a4 a3 a2 hh hr
  have hnum := map_evenClearedC68_quadratic (H := H) (p.coeff 5)
    (p.coeff 4) (p.coeff 3) (p.coeff 2)
  have hroot : h ^ 2 = algebraMap k[X] F68 H := by
    rw [← quadraticCoefficientMap46_eq_algebraMap H H]
    exact alignedQuadraticRoot_sq46 H
  have hden : (h ^ 2) ^ 10 = algebraMap k[X] F68 (H ^ 10) := by
    rw [hroot, map_pow]
  rw [hC, heven, hnum, hden]

/-- Source identification of `E` with the even-cleared ratio
`N_E/H¹⁵`. -/
theorem NonsquareAlignedSourceCurveData68.E_eq_evenClearedDiv
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    S.E =
      algebraMap k[X] F68
          (evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0)) /
        algebraMap k[X] F68 (H ^ 15) := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 := quadraticCoefficientMap46 H (p.coeff 4)
  let a3 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 := quadraticCoefficientMap46 H (p.coeff 2)
  let a1 := quadraticCoefficientMap46 H (p.coeff 1)
  let a0 := quadraticCoefficientMap46 H (p.coeff 0)
  have hE : S.E = depressedE68 h S.r a5 a4 a3 a2 a1 a0 :=
    (S.eq_depressed (H := H) hp hp6).2.2
  have hr := S.r_eq_depression (H := H) hp hp6
  have hh : h ≠ 0 := S.scale_ne_zero
  have heven := depressedE68_evenCleared h S.r a5 a4 a3 a2 a1 a0 hh hr
  have hnum := map_evenClearedE68_quadratic (H := H) (p.coeff 5)
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
  have hroot : h ^ 2 = algebraMap k[X] F68 H := by
    rw [← quadraticCoefficientMap46_eq_algebraMap H H]
    exact alignedQuadraticRoot_sq46 H
  have hden : (h ^ 2) ^ 15 = algebraMap k[X] F68 (H ^ 15) := by
    rw [hroot, map_pow]
  rw [hE, heven, hnum, hden]

theorem NonsquareAlignedSourceCurveData68.A_isPolynomial_iff_evenClearedDvd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    (∃ A0 : k[X], algebraMap k[X] F68 A0 = S.A) ↔
      H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) :=
  algebraMap_div_isPolynomial_iff_dvdF68 (H := H)
    (evenClearedA68 H (p.coeff 5) (p.coeff 4)) (H ^ 5) S.A
    (pow_ne_zero 5 (H_ne_zero_of_nonsquare68 (H := H)))
    (S.A_eq_evenClearedDiv (H := H) hp hp6)

theorem NonsquareAlignedSourceCurveData68.C0_isPolynomial_iff_evenClearedDvd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    (∃ C0p : k[X], algebraMap k[X] F68 C0p = S.C0) ↔
      H ^ 10 ∣
        evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) :=
  algebraMap_div_isPolynomial_iff_dvdF68 (H := H)
    (evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2))
    (H ^ 10) S.C0
    (pow_ne_zero 10 (H_ne_zero_of_nonsquare68 (H := H)))
    (S.C0_eq_evenClearedDiv (H := H) hp hp6)

theorem NonsquareAlignedSourceCurveData68.E_isPolynomial_iff_evenClearedDvd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    (∃ E0 : k[X], algebraMap k[X] F68 E0 = S.E) ↔
      H ^ 15 ∣
        evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) :=
  algebraMap_div_isPolynomial_iff_dvdF68 (H := H)
    (evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
      (p.coeff 1) (p.coeff 0))
    (H ^ 15) S.E
    (pow_ne_zero 15 (H_ne_zero_of_nonsquare68 (H := H)))
    (S.E_eq_evenClearedDiv (H := H) hp hp6)

theorem NonsquareAlignedSourceCurveData68.polynomialEven_of_evenClearedDvd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    (hA : H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4))
    (hC : H ^ 10 ∣
      evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2))
    (hE : H ^ 15 ∣
      evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)) :
    ∃ A0 C0p E0 : k[X],
      algebraMap k[X] F68 A0 = S.A ∧
      algebraMap k[X] F68 C0p = S.C0 ∧
      algebraMap k[X] F68 E0 = S.E := by
  obtain ⟨A0, hA0⟩ :=
    (S.A_isPolynomial_iff_evenClearedDvd (H := H) hp hp6).mpr hA
  obtain ⟨C0p, hC0⟩ :=
    (S.C0_isPolynomial_iff_evenClearedDvd (H := H) hp hp6).mpr hC
  obtain ⟨E0, hE0⟩ :=
    (S.E_isPolynomial_iff_evenClearedDvd (H := H) hp hp6).mpr hE
  exact ⟨A0, C0p, E0, hA0, hC0, hE0⟩

/-- The `D=0` endgame from the even-cleared divisibilities. -/
theorem NonsquareAlignedSourceCurveData68.impossible_of_D_zero_evenClearedDvd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    (hA : H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4))
    (hC : H ^ 10 ∣
      evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2))
    (hE : H ^ 15 ∣
      evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0))
    (hD : S.D = 0) : False := by
  obtain ⟨A0, C0p, E0, hA0, hC0, hE0⟩ :=
    S.polynomialEven_of_evenClearedDvd (H := H) hp hp6 hA hC hE
  exact S.impossible_of_D_zero_polynomial_even (H := H) hj hD
    A0 C0p E0 hA0 hC0 hE0

/-- On the face `B=0`, last-row nonvanishing forces `D≠0` and `W=0`, and
the descended last row is the single `D`-core product
`M_D (((4/9)A+α) E' - V') = j`. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_B_zero_W
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hB : S.B = 0) :
    S.D ≠ 0 ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) = 0 ∧
      ∃ mD aR eR vR : RatFunc k,
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
          algebraMap (RatFunc k) F68 mD ∧
        S.A = algebraMap (RatFunc k) F68 aR ∧
        S.E = algebraMap (RatFunc k) F68 eR ∧
        integratedV68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
            (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
          algebraMap (RatFunc k) F68 vR ∧
        mD *
            (((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha) *
              Differential.deriv eR -
              Differential.deriv vR) =
          algebraMap k (RatFunc k) j := by
  have hDne : S.D ≠ 0 := by
    intro hD0
    exact NonsquareAlignedSourceCurveData68.B_D_ne (H := H) S hj
      ⟨hB, hD0⟩
  have hW :
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        0 := by
    have hI4 := S.I4_factor
    simp only [hB, zero_mul, zero_add] at hI4
    have h6 : (6 : F68) ≠ 0 := by norm_num
    have hassoc :
        (6 : F68) *
            (alignedLastRowShiftW68 S.A S.C0
              (algebraMap k F68 S.gamma) * S.D) = 0 := by
      convert hI4 using 1
      ring
    have hWD :
        alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) *
          S.D = 0 :=
      (mul_eq_zero.mp hassoc).resolve_left h6
    exact (mul_eq_zero.mp hWD).resolve_right hDne
  obtain ⟨mB, wR, eR, mD, aR, vR, hmB, hwR, heR, hmD, haR, hvR,
      hlast⟩ := S.lastRow_W_ratFunc
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hmB0 : mB = 0 := by
    apply hι
    rw [← hmB, hB]
    simp
  refine ⟨hDne, hW, mD, aR, eR, vR, hmD, haR, heR, hvR, ?_⟩
  rw [hmB0] at hlast
  convert hlast using 1
  ring

set_option maxHeartbeats 2000000 in
/-- On `B=0`, polynomial even coordinates produce a polynomial
representative of the octic constant `V`. -/
theorem NonsquareAlignedSourceCurveData68.polynomialV_of_B_zero
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hB : S.B = 0) (A0 C0p E0 : k[X])
    (hA : algebraMap k[X] F68 A0 = S.A)
    (hC : algebraMap k[X] F68 C0p = S.C0)
    (hE : algebraMap k[X] F68 E0 = S.E) :
    ∃ V0 : k[X], algebraMap k[X] F68 V0 =
      integratedV68 0 S.A S.B S.C0 S.D S.E
        (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
        (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) := by
  refine ⟨C (2 / 9 : k) * C0p ^ 2 + C (4 / 9 : k) * A0 * E0 -
      C (4 / 27 : k) * A0 ^ 2 * C0p + C (5 / 243 : k) * A0 ^ 4 +
      C S.alpha * E0 +
      C S.gamma * (C (2 / 3 : k) * C0p - C (1 / 9 : k) * A0 ^ 2) +
      C (1 / 3 : k) * C S.epsilon * A0 + C S.eta, ?_⟩
  have hshape := integratedV68_B_zero S.A S.C0 S.D S.E
    (algebraMap k F68 S.alpha) (algebraMap k F68 S.gamma)
    (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta)
  rw [hB, hshape]
  simp only [map_add, map_sub, map_mul, map_pow]
  rw [algebraMap_C_eq_F68 (H := H) (2 / 9 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (4 / 9 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (4 / 27 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (5 / 243 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (2 / 3 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (1 / 9 : k)
      (by rw [map_div₀, map_one, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (1 / 3 : k)
      (by rw [map_div₀, map_one, map_ofNat]),
    algebraMap_C_ground_F68 (H := H) S.alpha,
    algebraMap_C_ground_F68 (H := H) S.gamma,
    algebraMap_C_ground_F68 (H := H) S.epsilon,
    algebraMap_C_ground_F68 (H := H) S.eta, hA, hC, hE]

set_option maxHeartbeats 2000000 in
/-- On `B=0`, polynomial even coordinates produce a polynomial
representative of `K_D=D²` from the constant `I₃`. -/
theorem NonsquareAlignedSourceCurveData68.polynomialKD_of_B_zero
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hB : S.B = 0) (A0 C0p E0 : k[X])
    (hA : algebraMap k[X] F68 A0 = S.A)
    (hC : algebraMap k[X] F68 C0p = S.C0)
    (hE : algebraMap k[X] F68 E0 = S.E) :
    ∃ K0 : k[X], algebraMap k[X] F68 K0 = S.D ^ 2 := by
  obtain ⟨i3, hi3⟩ := (S.residualPacket).2.1
  refine ⟨C (3 / 4 : k) * (C i3 -
      (C (-16 / 243 : k) * A0 ^ 5 +
        C (2 : k) * C0p * C S.epsilon + C (4 : k) * E0 * C S.gamma -
        C (8 / 9 : k) * A0 * C0p ^ 2 - C (8 / 9 : k) * A0 ^ 2 * E0 -
        C (2 / 3 : k) * A0 ^ 2 * C S.epsilon +
        C (8 / 3 : k) * C0p * E0 +
        C (8 / 27 : k) * A0 ^ 3 * C S.gamma +
        C (40 / 81 : k) * A0 ^ 3 * C0p -
        C (4 / 3 : k) * A0 * C0p * C S.gamma)), ?_⟩
  have hshape := alignedFirstIntegralThreeWithoutDsq68_B_zero
    S.A S.C0 S.D S.E (algebraMap k F68 S.gamma)
    (algebraMap k F68 S.epsilon)
  have hDsq := Dsq_of_firstIntegralThree68 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
    (algebraMap k F68 i3) hi3
  have h16243 : algebraMap k[X] F68 (C (-16 / 243 : k)) =
      (-16 / 243 : F68) :=
    algebraMap_C_eq_F68 (H := H) _
      (by simp only [map_div₀, map_neg, map_ofNat])
  rw [hDsq, hB, hshape]
  simp only [map_mul, map_sub, map_add, map_pow]
  rw [algebraMap_C_eq_F68 (H := H) (3 / 4 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_ground_F68 (H := H) i3, h16243,
    algebraMap_C_eq_F68 (H := H) (2 : k) (by rw [map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (4 : k) (by rw [map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (8 / 9 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (2 / 3 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (8 / 3 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (8 / 27 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (40 / 81 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_eq_F68 (H := H) (4 / 3 : k)
      (by rw [map_div₀, map_ofNat, map_ofNat]),
    algebraMap_C_ground_F68 (H := H) S.gamma,
    algebraMap_C_ground_F68 (H := H) S.epsilon, hA, hC, hE]

set_option maxHeartbeats 4000000 in
/-- On `B=0`, polynomial even coordinates reduce the last row to a
polynomial unit product `M_D P = j`. -/
theorem NonsquareAlignedSourceCurveData68.impossible_of_B_zero_polynomial_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hB : S.B = 0)
    (A0 C0p E0 : k[X])
    (hA : algebraMap k[X] F68 A0 = S.A)
    (hC : algebraMap k[X] F68 C0p = S.C0)
    (hE : algebraMap k[X] F68 E0 = S.E) : False := by
  obtain ⟨_hDne, _hW0, mD, aR, eR, vR, hmD, haR, heR, hvR, hlast⟩ :=
    NonsquareAlignedSourceCurveData68.lastRow_B_zero_W (H := H) S hj hB
  obtain ⟨V0, hVfield⟩ :=
    NonsquareAlignedSourceCurveData68.polynomialV_of_B_zero (H := H)
      S hB A0 C0p E0 hA hC hE
  obtain ⟨K0, hK⟩ :=
    NonsquareAlignedSourceCurveData68.polynomialKD_of_B_zero (H := H)
      S hB A0 C0p E0 hA hC hE
  obtain ⟨M0, hM, hMK⟩ :=
    NonsquareAlignedSourceCurveData68.polynomialMD_of_polynomialKD
      (H := H) S K0 hK
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hQmap (Q : k[X]) : algebraMap k[X] F68 Q =
      algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) Q) :=
    IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 Q
  have haRpoly : aR = algebraMap k[X] (RatFunc k) A0 := by
    apply hι
    rw [← hQmap, hA, haR]
  have heRpoly : eR = algebraMap k[X] (RatFunc k) E0 := by
    apply hι
    rw [← hQmap, hE, heR]
  have hvRpoly : vR = algebraMap k[X] (RatFunc k) V0 := by
    apply hι
    rw [← hQmap, hVfield, hvR]
  have hmDpoly : mD = algebraMap k[X] (RatFunc k) M0 := by
    apply hι
    rw [← hQmap, hM, hmD]
  have hderE : Differential.deriv eR =
      algebraMap k[X] (RatFunc k) E0.derivative := by
    rw [heRpoly, GCD369RatFuncDerivative]
  have hderV : Differential.deriv vR =
      algebraMap k[X] (RatFunc k) V0.derivative := by
    rw [hvRpoly, GCD369RatFuncDerivative]
  have hαR : algebraMap k (RatFunc k) S.alpha =
      algebraMap k[X] (RatFunc k) (C S.alpha) := by
    simp only [RatFunc.algebraMap_C]
    rw [RatFunc.algebraMap_eq_C]
  have h49 : algebraMap k (RatFunc k) (4 / 9 : k) =
      (4 / 9 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have hP0 :
      algebraMap k[X] (RatFunc k)
          ((C (4 / 9 : k) * A0 + C S.alpha) * E0.derivative -
            V0.derivative) =
        ((4 / 9 : RatFunc k) * aR +
            algebraMap k (RatFunc k) S.alpha) *
          Differential.deriv eR -
          Differential.deriv vR := by
    simp only [map_sub, map_mul, map_add, RatFunc.algebraMap_C]
    simp only [← RatFunc.algebraMap_eq_C, ← haRpoly, hderE, hderV, hαR,
      h49]
  have hprodRat :
      algebraMap k[X] (RatFunc k)
          (M0 * ((C (4 / 9 : k) * A0 + C S.alpha) * E0.derivative -
            V0.derivative)) =
        algebraMap k (RatFunc k) j := by
    simp only [map_mul, ← hmDpoly, hP0]
    exact hlast
  have hCj : algebraMap k (RatFunc k) j =
      algebraMap k[X] (RatFunc k) (C j) := by
    simp only [RatFunc.algebraMap_C]
    rw [RatFunc.algebraMap_eq_C]
  have hpoly :
      M0 * ((C (4 / 9 : k) * A0 + C S.alpha) * E0.derivative -
          V0.derivative) = C j :=
    FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
      (hprodRat.trans hCj.symm)
  exact nonsquare_polynomial_product_impossible68 H K0 M0
    ((C (4 / 9 : k) * A0 + C S.alpha) * E0.derivative - V0.derivative)
    j hj NonsquarePolynomial46.not_sq hMK hpoly

/-- The `B=0` face from the even-cleared divisibilities. -/
theorem NonsquareAlignedSourceCurveData68.impossible_of_B_zero_evenClearedDvd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    (hA : H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4))
    (hC : H ^ 10 ∣
      evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2))
    (hE : H ^ 15 ∣
      evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0))
    (hB : S.B = 0) : False := by
  obtain ⟨A0, C0p, E0, hA0, hC0, hE0⟩ :=
    S.polynomialEven_of_evenClearedDvd (H := H) hp hp6 hA hC hE
  exact S.impossible_of_B_zero_polynomial_even (H := H) hj hB
    A0 C0p E0 hA0 hC0 hE0

/-- Residual packet after the even-cleared divisibility layer.  The
even coordinates are the displayed ratios `N/H^n`.  They are polynomial
if and only if those `H`-powers divide the numerators, in which case
both faces `D=0` and `B=0` close.  The three divisibilities are the
smallest missing input; the mixed two-term last row remains. -/
theorem NonsquareAlignedSourceCurveData68.monicEliminantPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    S.A =
        algebraMap k[X] F68
            (evenClearedA68 H (p.coeff 5) (p.coeff 4)) /
          algebraMap k[X] F68 (H ^ 5) ∧
      S.C0 =
        algebraMap k[X] F68
            (evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2)) /
          algebraMap k[X] F68 (H ^ 10) ∧
      S.E =
        algebraMap k[X] F68
            (evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0)) /
          algebraMap k[X] F68 (H ^ 15) ∧
      ((∃ A0 : k[X], algebraMap k[X] F68 A0 = S.A) ↔
        H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4)) ∧
      ((∃ C0p : k[X], algebraMap k[X] F68 C0p = S.C0) ↔
        H ^ 10 ∣
          evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2)) ∧
      ((∃ E0 : k[X], algebraMap k[X] F68 E0 = S.E) ↔
        H ^ 15 ∣
          evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0)) ∧
      (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) →
        H ^ 10 ∣
            evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) →
          H ^ 15 ∣
              evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (p.coeff 0) →
            S.D = 0 → False) ∧
      (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) →
        H ^ 10 ∣
            evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) →
          H ^ 15 ∣
              evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (p.coeff 0) →
            S.B = 0 → False) := by
  refine ⟨S.A_eq_evenClearedDiv (H := H) hp hp6,
    S.C0_eq_evenClearedDiv (H := H) hp hp6,
    S.E_eq_evenClearedDiv (H := H) hp hp6,
    S.A_isPolynomial_iff_evenClearedDvd (H := H) hp hp6,
    S.C0_isPolynomial_iff_evenClearedDvd (H := H) hp hp6,
    S.E_isPolynomial_iff_evenClearedDvd (H := H) hp hp6, ?_, ?_⟩
  · intro hA hC hE hD
    exact S.impossible_of_D_zero_evenClearedDvd (H := H) hj hp hp6
      hA hC hE hD
  · intro hA hC hE hB
    exact S.impossible_of_B_zero_evenClearedDvd (H := H) hj hp hp6
      hA hC hE hB

end QuadraticMonicEliminant68

#print axioms evenClearedRelationA68_eval
#print axioms evenClearedMonicEliminantA68_of_dvd
#print axioms algebraMap_div_isPolynomial_iff_dvdF68
#print axioms NonsquareAlignedSourceCurveData68.A_eq_evenClearedDiv
#print axioms NonsquareAlignedSourceCurveData68.C0_eq_evenClearedDiv
#print axioms NonsquareAlignedSourceCurveData68.E_eq_evenClearedDiv
#print axioms NonsquareAlignedSourceCurveData68.A_isPolynomial_iff_evenClearedDvd
#print axioms NonsquareAlignedSourceCurveData68.lastRow_B_zero_W
#print axioms NonsquareAlignedSourceCurveData68.impossible_of_D_zero_evenClearedDvd
#print axioms NonsquareAlignedSourceCurveData68.impossible_of_B_zero_polynomial_even
#print axioms NonsquareAlignedSourceCurveData68.monicEliminantPacket

end Max11DegreeRoutes
