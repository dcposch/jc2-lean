import LowScale46WeightedInfinity
import LowScale46AlignedRegularLoads
import LowScale46QuadraticEndgame

/-! # Complete scale-two exclusion for the normalized `(4,6)` leaf

The mismatch branch is closed in `LowScale46WeightedInfinity`.  Here the
aligned source is passed through the same weighted-infinity normalization,
then dispatched to the three regular-load aligned pole exclusions.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSourcePoleSpecialization

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance scaleTwoHahnCharZero46 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- An aligned source package is the zero-`L` instance of the general
constant-`L` package. -/
def SquareAlignedSourceCurveData46.toConstantLZero
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (S : SquareAlignedSourceCurveData46 p q j h0) :
    SquareConstantLSourceCurveData46 p q j h0 0 where
  r := S.r
  A := S.A
  B := S.B
  C0 := S.C0
  alpha := S.alpha
  beta := S.beta
  gamma := S.gamma
  delta := S.delta
  epsilon := S.epsilon
  k2 := S.k2
  k1 := S.k1
  center_eq := S.center_eq
  quartic_eq := S.quartic_eq
  sextic_eq := by simpa using S.sextic_eq
  curveTwo := by simpa using S.curveTwo
  curveOne := by simpa using S.curveOne
  boundaryD := S.boundaryD
  boundaryE := by simpa using S.boundaryE
  lastRow := by simpa using S.lastRow

/-- At a root of the degree-one common core, an aligned source yields a
positive normalized local trajectory.  The source-level nonfinal-stratum
dichotomy then contradicts the appropriate regular-load pole theorem. -/
theorem SquareAlignedSourceCurveData46.impossible_at_root
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (S : SquareAlignedSourceCurveData46 p q j h0)
    (a : k) (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0)
    (hj : j ≠ 0) : False := by
  let T : SquareConstantLSourceCurveData46 p q j h0 0 := S.toConstantLZero
  let rH : HahnSeries ℚ k := ratFuncAtHahn46 a S.r
  let qH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (translatedQ46 S.r S.A)
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a S.A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 a S.B
  let UH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (S.A ^ 2 - 4 * S.C0)
  let D : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) (p.coeff 0))
  let E : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k)
      (q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon))
  have hA : AH = 2 * qH - 2 * rH ^ 2 := by
    dsimp only [AH, qH, rH]
    simp only [translatedQ46, map_add, map_mul, map_pow,
      map_div₀, map_ofNat, map_one]
    ring
  have hDreg : (0 : WithTop ℚ) ≤ D.orderTop := by
    dsimp only [D]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a (p.coeff 0)
  have hEreg : (0 : WithTop ℚ) ≤ E.orderTop := by
    dsimp only [E]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a
      (q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon)
  have hD : boundaryD46 rH qH BH UH = D := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.boundaryD
    simpa only [rH, qH, BH, UH, D, boundaryD46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_ofNat, map_one] using hmapped
  have hE : boundaryE46 0 rH qH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = E := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.boundaryE
    simpa only [rH, qH, BH, UH, E, boundaryE46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C, map_zero] using hmapped
  have hJ2A : coefficientCurveTwo46 0 AH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k2 := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.curveTwo
    simpa only [AH, BH, UH, coefficientCurveTwo46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C, map_zero] using hmapped
  have hJ1A : coefficientCurveOne46 0 AH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k1 := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.curveOne
    simpa only [AH, BH, UH, coefficientCurveOne46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C, map_zero] using hmapped
  rcases T.weightedInfinity_dominant_at_root a hh0 hroot hj with
    ⟨rho, hrho, hrPole, hqPole, hBPole, hUPole⟩
  change rH.orderTop = (↑(-rho) : WithTop ℚ) at hrPole
  change (↑(-2 * rho) : WithTop ℚ) < qH.orderTop at hqPole
  change (↑(-3 * rho) : WithTop ℚ) < BH.orderTop at hBPole
  change (↑(-4 * rho) : WithTop ℚ) < UH.orderTop at hUPole
  have hrHne : rH ≠ 0 := by
    intro hr0
    rw [hr0, HahnSeries.orderTop_zero] at hrPole
    exact WithTop.coe_ne_top hrPole.symm
  let s0 : HahnSeries ℚ k := rH⁻¹
  let Q0 : HahnSeries ℚ k := qH * s0 ^ 2
  let Y0 : HahnSeries ℚ k := BH * s0 ^ 3
  let Z0 : HahnSeries ℚ k := UH * s0 ^ 4
  have hs0ne : s0 ≠ 0 := inv_ne_zero hrHne
  have hs0Order : s0.orderTop = (↑rho : WithTop ℚ) := by
    dsimp only [s0]
    simpa only [neg_neg] using
      hahnOrderTop_inv_eq_neg46 rH (-rho) hrHne hrPole
  have hs02 : (s0 ^ 2).orderTop = (↑(2 * rho) : WithTop ℚ) := by
    simpa using hahnOrderTop_pow_eq46 s0 rho 2 hs0Order
  have hs03 : (s0 ^ 3).orderTop = (↑(3 * rho) : WithTop ℚ) := by
    simpa using hahnOrderTop_pow_eq46 s0 rho 3 hs0Order
  have hs04 : (s0 ^ 4).orderTop = (↑(4 * rho) : WithTop ℚ) := by
    simpa using hahnOrderTop_pow_eq46 s0 rho 4 hs0Order
  have hQ0pos : (0 : WithTop ℚ) < Q0.orderTop := by
    dsimp only [Q0]
    rw [HahnSeries.orderTop_mul, hs02]
    have h : (↑(-2 * rho) : WithTop ℚ) + ↑(2 * rho) <
        qH.orderTop + ↑(2 * rho) :=
      (add_lt_add_iff_left_of_ne_top WithTop.coe_ne_top).mpr hqPole
    rw [← WithTop.coe_add, show -2 * rho + 2 * rho = 0 by ring] at h
    exact h
  have hY0pos : (0 : WithTop ℚ) < Y0.orderTop := by
    dsimp only [Y0]
    rw [HahnSeries.orderTop_mul, hs03]
    have h : (↑(-3 * rho) : WithTop ℚ) + ↑(3 * rho) <
        BH.orderTop + ↑(3 * rho) :=
      (add_lt_add_iff_left_of_ne_top WithTop.coe_ne_top).mpr hBPole
    rw [← WithTop.coe_add, show -3 * rho + 3 * rho = 0 by ring] at h
    exact h
  have hZ0pos : (0 : WithTop ℚ) < Z0.orderTop := by
    dsimp only [Z0]
    rw [HahnSeries.orderTop_mul, hs04]
    have h : (↑(-4 * rho) : WithTop ℚ) + ↑(4 * rho) <
        UH.orderTop + ↑(4 * rho) :=
      (add_lt_add_iff_left_of_ne_top WithTop.coe_ne_top).mpr hUPole
    rw [← WithTop.coe_add, show -4 * rho + 4 * rho = 0 by ring] at h
    exact h
  have hrRecover : localChartR46 s0 = rH := by
    simp [localChartR46, s0]
  have hqRecover : localChartQ46 s0 Q0 = qH := by
    dsimp only [localChartQ46, Q0, s0]
    field_simp [hrHne]
  have hBRecover : localChartB46 s0 Y0 = BH := by
    dsimp only [localChartB46, Y0, s0]
    field_simp [hrHne]
  have hURecover : localChartU46 s0 Z0 = UH := by
    dsimp only [localChartU46, Z0, s0]
    field_simp [hrHne]
  have hARecover : localChartA46 s0 Q0 = AH := by
    simp only [localChartA46, hqRecover, hrRecover]
    exact hA.symm
  have hF0 : localChartF46 s0 Q0 Y0 Z0 D = 0 := by
    rw [← clear_boundaryD46_localChart s0 Q0 Y0 Z0 D hs0ne,
      hrRecover, hqRecover, hBRecover, hURecover, hD, sub_self, mul_zero]
  have hG0 : localChartG46 0 s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) E = 0 := by
    rw [← clear_boundaryE46_localChart 0 s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) E hs0ne,
      hrRecover, hqRecover, hBRecover, hURecover, hE, sub_self, mul_zero]
  have hJ20 : localChartJTwo46 0 s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k2) = 0 := by
    rw [← clear_coefficientCurveTwo46_localChart 0
      s0 Q0 Y0 Z0 (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k2) hs0ne,
      hARecover, hBRecover, hURecover, hJ2A, sub_self, mul_zero]
  have hJ10 : localChartJOne46 0 s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k1) = 0 := by
    rw [← clear_coefficientCurveOne46_localChart 0
      s0 Q0 Y0 Z0 (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k1) hs0ne,
      hARecover, hBRecover, hURecover, hJ1A, sub_self, mul_zero]
  let N := normalizeHahnOrder46 (k := k) rho hrho
  let s := N s0
  let Q := N Q0
  let Y := N Y0
  let Z := N Z0
  let DN := N D
  let EN := N E
  have hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    dsimp only [s, N]
    exact normalizeHahnOrder46_orderTop_eq_one rho hrho s0 hs0Order
  have hQcase : PositiveFiniteOrZero46 Q := by
    dsimp only [Q, N]
    exact normalizeHahnOrder46_positiveFiniteOrZero rho hrho Q0 hQ0pos
  have hYcase : PositiveFiniteOrZero46 Y := by
    dsimp only [Y, N]
    exact normalizeHahnOrder46_positiveFiniteOrZero rho hrho Y0 hY0pos
  have hZcase : PositiveFiniteOrZero46 Z := by
    dsimp only [Z, N]
    exact normalizeHahnOrder46_positiveFiniteOrZero rho hrho Z0 hZ0pos
  have hDN : (0 : WithTop ℚ) ≤ DN.orderTop := by
    dsimp only [DN, N]
    exact normalizeHahnOrder46_orderTop_nonneg rho hrho D hDreg
  have hEN : (0 : WithTop ℚ) ≤ EN.orderTop := by
    dsimp only [EN, N]
    exact normalizeHahnOrder46_orderTop_nonneg rho hrho E hEreg
  have hF : localChartF46 s Q Y Z DN = 0 := by
    have hmapped := congrArg N hF0
    simpa only [s, Q, Y, Z, DN, N, localChartF46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_ofNat, map_one, map_zero] using hmapped
  have hGlocal : localChartG46 0 s Q Y Z
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) EN = 0 := by
    have hmapped := congrArg N hG0
    simpa only [s, Q, Y, Z, EN, N, localChartG46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one, map_zero,
      normalizeHahnOrder46_C] using hmapped
  have hJ2local : localChartJTwo46 0 s Q Y Z
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k2) = 0 := by
    have hmapped := congrArg N hJ20
    simpa only [s, Q, Y, Z, N, localChartJTwo46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one, map_zero,
      normalizeHahnOrder46_C] using hmapped
  have hJ1local : localChartJOne46 0 s Q Y Z
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k1) = 0 := by
    have hmapped := congrArg N hJ10
    simpa only [s, Q, Y, Z, N, localChartJOne46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one, map_zero,
      normalizeHahnOrder46_C] using hmapped
  have hZ : Z = alignedLocalZ46 s Q Y DN := by
    simp only [localChartF46] at hF
    simp only [alignedLocalZ46]
    linear_combination (-4) * hF
  have hG : alignedLocalG46 s Q Y (HahnSeries.C S.beta)
      (HahnSeries.C S.gamma) (HahnSeries.C S.delta) DN EN = 0 := by
    rw [alignedLocalG46_eq, ← hZ, hGlocal, mul_zero]
  have hJ2 : alignedLocalJTwo46 s Q Y (HahnSeries.C S.beta)
      (HahnSeries.C S.gamma) (HahnSeries.C S.delta) DN
      (HahnSeries.C S.k2) = 0 := by
    rw [alignedLocalJTwo46_eq, ← hZ, hJ2local, mul_zero]
  have hJ1 : alignedLocalJOne46 s Q Y (HahnSeries.C S.beta)
      (HahnSeries.C S.gamma) (HahnSeries.C S.delta) DN
      (HahnSeries.C S.k1) = 0 := by
    rw [alignedLocalJOne46_eq, ← hZ, hJ1local, mul_zero]
  rcases S.nonfinalStratum hj with hbeta | hdelta | hk2
  · exact alignedBetaFinitePole46_exhaustive_regular
      S.beta S.gamma S.delta S.k2 S.k1 DN EN s Q Y hbeta hDN hEN hs
      hQcase hYcase hG hJ2 hJ1
  · exact alignedDeltaFinitePole46_exhaustive_regular
      S.gamma S.delta S.k2 S.k1 DN EN s Q Y hdelta.2 hDN hEN hs
      hQcase hYcase (by simpa [hdelta.1] using hG)
      (by simpa [hdelta.1] using hJ2) (by simpa [hdelta.1] using hJ1)
  · exact alignedZeroFinitePole46_exhaustive_regular
      S.gamma S.k2 S.k1 DN EN s Q Y hk2.2.2 hDN hEN hs hQcase hYcase
      (by simpa [hk2.1, hk2.2.1] using hG)
      (by simpa [hk2.1, hk2.2.1] using hJ2)
      (by simpa [hk2.1, hk2.2.1] using hJ1)

open scoped Polynomial.Bivariate

/-- The square-core aligned branch of a normalized scale-two source is
impossible: its square root is linear and hence supplies the finite root used
by the aligned source-pole theorem. -/
theorem normalized46ScaleTwo_alignedSquareBranch_impossible
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized46LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (3 : k[X]) * p.coeff 3 * H - (2 : k[X]) * q.coeff 5 = 0) : False := by
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp4, hq6, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 6 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq6' : q.coeff 6 = H ^ 3 := by simpa only [q] using hq6
  have haligned' : (3 : k[X]) * p.coeff 3 * H -
      (2 : k[X]) * q.coeff 5 = 0 := by
    simpa only [p, q] using haligned
  have hh0degree : h0.natDegree = 1 := by
    have hdeg := congrArg Polynomial.natDegree hH
    rw [hHdegree, natDegree_pow] at hdeg
    omega
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hh0degree
  let a : k := -d / c
  have hroot : h0.eval a = 0 := by
    rw [← hlinear]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    dsimp only [a]
    field_simp [hc]
    ring
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨S⟩ := squareAlignedSourceCurveData46
    p q H h0 j hp hq hh0 hH hp4' hq6' haligned' hD
  exact S.impossible_at_root a hh0 hroot hj

/-- The aligned nonsquare-core branch maps into `k(x)(√H)`, where the deck
descent and boundary-integrality endgame exclude its final component. -/
theorem normalized46ScaleTwo_alignedNonsquareBranch_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized46LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (3 : k[X]) * p.coeff 3 * H - (2 : k[X]) * q.coeff 5 = 0) : False := by
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp4, hq6, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 6 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq6' : q.coeff 6 = H ^ 3 := by simpa only [q] using hq6
  have haligned' : (3 : k[X]) * p.coeff 3 * H -
      (2 : k[X]) * q.coeff 5 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData46 H
    p q j hp hq hp4' hq6' haligned' hD
  exact S.impossible H hj

/-- The aligned scale-two branch is exhaustive in the square/nonsquare
dichotomy for its quadratic common core. -/
theorem normalized46ScaleTwo_alignedBranch_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized46LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (3 : k[X]) * p.coeff 3 * H - (2 : k[X]) * q.coeff 5 = 0) : False := by
  by_cases hsquare : ∃ h0 : k[X], H = h0 ^ 2
  · obtain ⟨h0, hH⟩ := hsquare
    have hh0 : h0 ≠ 0 := by
      intro hzero
      have hHzero : H = 0 := by simp [hH, hzero]
      exact hsource.1 hHzero
    exact normalized46ScaleTwo_alignedSquareBranch_impossible
      hsource hh0 hH haligned
  · have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := by
      intro h0 hH
      exact hsquare ⟨h0, hH⟩
    exact normalized46ScaleTwo_alignedNonsquareBranch_impossible
      hsource hnsq haligned

/-- Every normalized `(4,6)` source at common scale two is impossible.  The
imprimitive discriminator sends the nonaligned branch to the square-core
weighted-infinity theorem and the aligned branch to the exhaustive
square/nonsquare closure above. -/
theorem normalized46ScaleTwo_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized46LeadingCoreSource P Q H 2) : False := by
  have hs := hsource
  rcases hs with
    ⟨hHne, _hHdegree, hPdegree, hQdegree, hp4, hq6, hKeller⟩
  have hdich := planeKellerPair_46_imprimitiveDiscriminatorDichotomy
    hPdegree hQdegree hKeller hHne hp4 hq6
  dsimp only at hdich
  rcases hdich with haligned |
      ⟨h0, lambda, hh0, hlambda, hH, hmismatch⟩
  · exact normalized46ScaleTwo_alignedBranch_impossible hsource haligned
  · exact normalized46ScaleTwo_squareBranch_impossible
      hsource hh0 hlambda hH hmismatch

/-- The proved scale-two exclusion supplies the route interface used by the
Max-11 assembly. -/
theorem proved_planeKellerNormalized46ScaleTwoRoute :
    PlaneKellerNormalized46ScaleTwoRoute (k := k) := by
  intro P Q H hsource
  exact (normalized46ScaleTwo_impossible hsource).elim

/-- Both normalized low scales for `(4,6)` are now closed internally. -/
theorem proved_planeKellerNormalized46LowScaleRoute :
    PlaneKellerNormalized46LowScaleRoute (K := k) :=
  planeKellerNormalized46LowScaleRoute_of_scaleTwo
    proved_planeKellerNormalized46ScaleTwoRoute

end AlignedSourcePoleSpecialization

end Max11DegreeRoutes
