import LowScale46GeneralSourceBridge

/-! # Constant-core closure for the aligned `(4,6)` source

At common scale zero the square root of the leading core is a nonzero
scalar.  The depressed rational coefficients therefore have polynomial
representatives, so the already-proved polynomial endgames apply directly.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section PolynomialMap

variable {k : Type*} [Field k] [CharZero k]

/-- The rational-function embedding preserves the first polynomial
coefficient-curve row exactly. -/
theorem algebraMap_coefficientCurveTwoPolynomial46
    (L beta gamma delta : k) (A B U : k[X]) :
    algebraMap k[X] (RatFunc k)
        (coefficientCurveTwoPolynomial46 L beta gamma delta A B U) =
      coefficientCurveTwo46 (RatFunc.C L)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) U)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta) := by
  simp only [coefficientCurveTwoPolynomial46, coefficientCurveTwo46,
    map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

/-- The analogous exact map for the second coefficient-curve row. -/
theorem algebraMap_coefficientCurveOnePolynomial46
    (L beta gamma delta : k) (A B U : k[X]) :
    algebraMap k[X] (RatFunc k)
        (coefficientCurveOnePolynomial46 L beta gamma delta A B U) =
      coefficientCurveOne46 (RatFunc.C L)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) U)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta) := by
  simp only [coefficientCurveOnePolynomial46, coefficientCurveOne46,
    map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

/-- The polynomial final-row one-form maps to the standard differential
one-form on `k(x)`. -/
theorem algebraMap_etaPolynomial46
    (L beta gamma delta : k) (A B U : k[X]) :
    algebraMap k[X] (RatFunc k)
        (etaPolynomial46 L beta gamma delta A B U) =
      eta46 (RatFunc.C L)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) U)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (ratFuncDerivation46 (algebraMap k[X] (RatFunc k) A))
        (ratFuncDerivation46 (algebraMap k[X] (RatFunc k) B))
        (ratFuncDerivation46 (algebraMap k[X] (RatFunc k) U)) := by
  rw [ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial,
    ratFuncDerivation46_polynomial]
  simp only [etaPolynomial46, etaAPolynomial46, etaBPolynomial46,
    etaUPolynomial46, eta46, etaA46, etaB46, etaU46,
    map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

end PolynomialMap

section PolynomialEndgameAssembly

variable {k : Type*} [Field k] [CharZero k]

/-- The mismatch and all three aligned polynomial endgames combine into one
exhaustive statement, allowing a nonzero scalar factor on the last row. -/
theorem coefficientCurvePolynomialTrajectory_scaled_impossible46
    (L beta gamma delta k2 k1 h j : k) (A B U : k[X])
    (hh : h ≠ 0) (hj : j ≠ 0)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A B U = C k1)
    (hlast : C h * etaPolynomial46 L beta gamma delta A B U = C j) : False := by
  have hjh : j / h ≠ 0 := div_ne_zero hj hh
  have hlast' : etaPolynomial46 L beta gamma delta A B U = C (j / h) := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hh)
    calc
      C h * etaPolynomial46 L beta gamma delta A B U = C j := hlast
      _ = C h * C (j / h) := by
        rw [← C_mul]
        congr 1
        field_simp
  by_cases hL : L = 0
  · subst L
    by_cases hbeta : beta = 0
    · subst beta
      by_cases hdelta : delta = 0
      · subst delta
        exact alignedZeroOriginalPolynomialTrajectory_impossible46
          gamma k2 k1 (j / h) A B U hjh hJ2 hJ1 hlast'
      · exact alignedDeltaOriginalPolynomialTrajectory_impossible46
          gamma delta k2 k1 (j / h) A B U hdelta hjh hJ2 hJ1 hlast'
    · exact alignedBetaOriginalPolynomialTrajectory_impossible46
        beta gamma delta k2 k1 (j / h) A B U hbeta hjh hJ2 hJ1 hlast'
  · exact mismatchPolynomialTrajectory_impossible46
      L beta gamma delta k2 k1 (j / h) A B U hL hjh hJ2 hJ1 hlast'

end PolynomialEndgameAssembly

section ConstantScaleRepresentatives

variable {k : Type*} [Field k] [CharZero k]

/-- When the square root of the core is a scalar, all three coefficient-curve
coordinates have explicit polynomial representatives. -/
theorem SquareAlignedSourceCurveData46.polynomialRepresentatives_of_C
    {p q : k[X][X]} {j t : k}
    (S : SquareAlignedSourceCurveData46 p q j (C t)) (ht : t ≠ 0) :
    ∃ r0 A0 B0 U0 : k[X],
      algebraMap k[X] (RatFunc k) r0 = S.r ∧
      algebraMap k[X] (RatFunc k) A0 = S.A ∧
      algebraMap k[X] (RatFunc k) B0 = S.B ∧
      algebraMap k[X] (RatFunc k) U0 = S.A ^ 2 - 4 * S.C0 := by
  let r0 : k[X] := C ((4 * t ^ 3)⁻¹) * p.coeff 3
  have hr : algebraMap k[X] (RatFunc k) r0 = S.r := by
    rw [S.center_eq]
    simp only [quarticDepressionR46, r0, map_mul, RatFunc.algebraMap_C]
    have hc : RatFunc.C ((4 * t ^ 3)⁻¹) =
        ((4 : RatFunc k) * (RatFunc.C t) ^ 3)⁻¹ := by
      rw [map_inv₀, map_mul, map_ofNat, map_pow]
    rw [hc]
    ring
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  have hpmap : p0.map (algebraMap k[X] (RatFunc k)) =
      depressedQuartic46 S.A S.B S.C0 := by
    rw [← S.quartic_eq]
    symm
    rw [← hr]
    exact affineDepress_source_constantScale_map46 p t r0 ht
  let A0 : k[X] := p0.coeff 2
  let B0 : k[X] := p0.coeff 1
  let C00 : k[X] := p0.coeff 0
  let U0 : k[X] := A0 ^ 2 - 4 * C00
  have hA : algebraMap k[X] (RatFunc k) A0 = S.A := by
    have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hpmap
    simpa [A0, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  have hB : algebraMap k[X] (RatFunc k) B0 = S.B := by
    have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hpmap
    simpa [B0, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  have hC0 : algebraMap k[X] (RatFunc k) C00 = S.C0 := by
    have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hpmap
    simpa [C00, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  refine ⟨r0, A0, B0, U0, hr, hA, hB, ?_⟩
  simp only [U0, map_sub, map_mul, map_pow, hA, hC0, map_ofNat]

/-- Hence no aligned literal square-core source can have a nonzero constant
square root. -/
theorem SquareAlignedSourceCurveData46.impossible_of_C
    {p q : k[X][X]} {j t : k}
    (S : SquareAlignedSourceCurveData46 p q j (C t))
    (ht : t ≠ 0) (hj : j ≠ 0) : False := by
  obtain ⟨r0, A0, B0, U0, _hr, hA, hB, hU⟩ :=
    S.polynomialRepresentatives_of_C ht
  have hJ2 : coefficientCurveTwoPolynomial46 0 S.beta S.gamma S.delta
      A0 B0 U0 = C S.k2 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_coefficientCurveTwoPolynomial46]
    simpa only [RatFunc.algebraMap_eq_C, hA, hB, hU,
      RatFunc.algebraMap_C, map_zero] using S.curveTwo
  have hJ1 : coefficientCurveOnePolynomial46 0 S.beta S.gamma S.delta
      A0 B0 U0 = C S.k1 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_coefficientCurveOnePolynomial46]
    simpa only [RatFunc.algebraMap_eq_C, hA, hB, hU,
      RatFunc.algebraMap_C, map_zero] using S.curveOne
  have hlast : C t * etaPolynomial46 0 S.beta S.gamma S.delta
      A0 B0 U0 = C j := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [map_mul, RatFunc.algebraMap_C, algebraMap_etaPolynomial46]
    simpa only [RatFunc.algebraMap_eq_C, hA, hB, hU,
      RatFunc.algebraMap_C, map_zero] using S.lastRow
  exact coefficientCurvePolynomialTrajectory_scaled_impossible46
    0 S.beta S.gamma S.delta S.k2 S.k1 t j A0 B0 U0
      ht hj hJ2 hJ1 hlast

end ConstantScaleRepresentatives

section GeneralConstantScaleRepresentatives

variable {k : Type*} [Field k] [CharZero k]

/-- The same polynomial-representative bridge for an arbitrary constant
depressed quintic coefficient. -/
theorem SquareConstantLSourceCurveData46.polynomialRepresentatives_of_C
    {p q : k[X][X]} {j t l : k}
    (S : SquareConstantLSourceCurveData46 p q j (C t) l) (ht : t ≠ 0) :
    ∃ r0 A0 B0 U0 : k[X],
      algebraMap k[X] (RatFunc k) r0 = S.r ∧
      algebraMap k[X] (RatFunc k) A0 = S.A ∧
      algebraMap k[X] (RatFunc k) B0 = S.B ∧
      algebraMap k[X] (RatFunc k) U0 = S.A ^ 2 - 4 * S.C0 := by
  let r0 : k[X] := C ((4 * t ^ 3)⁻¹) * p.coeff 3
  have hr : algebraMap k[X] (RatFunc k) r0 = S.r := by
    rw [S.center_eq]
    simp only [quarticDepressionR46, r0, map_mul, RatFunc.algebraMap_C]
    have hc : RatFunc.C ((4 * t ^ 3)⁻¹) =
        ((4 : RatFunc k) * (RatFunc.C t) ^ 3)⁻¹ := by
      rw [map_inv₀, map_mul, map_ofNat, map_pow]
    rw [hc]
    ring
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  have hpmap : p0.map (algebraMap k[X] (RatFunc k)) =
      depressedQuartic46 S.A S.B S.C0 := by
    rw [← S.quartic_eq]
    symm
    rw [← hr]
    exact affineDepress_source_constantScale_map46 p t r0 ht
  let A0 : k[X] := p0.coeff 2
  let B0 : k[X] := p0.coeff 1
  let C00 : k[X] := p0.coeff 0
  let U0 : k[X] := A0 ^ 2 - 4 * C00
  have hA : algebraMap k[X] (RatFunc k) A0 = S.A := by
    have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hpmap
    simpa [A0, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  have hB : algebraMap k[X] (RatFunc k) B0 = S.B := by
    have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hpmap
    simpa [B0, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  have hC0 : algebraMap k[X] (RatFunc k) C00 = S.C0 := by
    have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hpmap
    simpa [C00, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  refine ⟨r0, A0, B0, U0, hr, hA, hB, ?_⟩
  simp only [U0, map_sub, map_mul, map_pow, hA, hC0, map_ofNat]

/-- A literal source with scalar square root and arbitrary constant `L` is
impossible by the combined polynomial endgame. -/
theorem SquareConstantLSourceCurveData46.impossible_of_C
    {p q : k[X][X]} {j t l : k}
    (S : SquareConstantLSourceCurveData46 p q j (C t) l)
    (ht : t ≠ 0) (hj : j ≠ 0) : False := by
  obtain ⟨r0, A0, B0, U0, _hr, hA, hB, hU⟩ :=
    S.polynomialRepresentatives_of_C ht
  have hJ2 : coefficientCurveTwoPolynomial46 l S.beta S.gamma S.delta
      A0 B0 U0 = C S.k2 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_coefficientCurveTwoPolynomial46]
    simpa only [RatFunc.algebraMap_eq_C, hA, hB, hU,
      RatFunc.algebraMap_C] using S.curveTwo
  have hJ1 : coefficientCurveOnePolynomial46 l S.beta S.gamma S.delta
      A0 B0 U0 = C S.k1 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_coefficientCurveOnePolynomial46]
    simpa only [RatFunc.algebraMap_eq_C, hA, hB, hU,
      RatFunc.algebraMap_C] using S.curveOne
  have hlast : C t * etaPolynomial46 l S.beta S.gamma S.delta
      A0 B0 U0 = C j := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [map_mul, RatFunc.algebraMap_C, algebraMap_etaPolynomial46]
    simpa only [RatFunc.algebraMap_eq_C, hA, hB, hU,
      RatFunc.algebraMap_C] using S.lastRow
  exact coefficientCurvePolynomialTrajectory_scaled_impossible46
    l S.beta S.gamma S.delta S.k2 S.k1 t j A0 B0 U0
      ht hj hJ2 hJ1 hlast

end GeneralConstantScaleRepresentatives

section LiteralMismatchScaleZero

open scoped Polynomial.Bivariate

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- A normalized scale-zero `(4,6)` source is impossible whenever its
imprimitive discriminator is written as a scalar times the fifth power of a
square root of the leading core.  The scalar may be zero: that specialization
is automatically routed through the aligned polynomial endgames. -/
theorem normalized46ScaleZero_squareBranch_impossible
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]} {lambda : k}
    (hsource : Normalized46LeadingCoreSource P Q H 0)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hmismatch :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (3 : k[X]) * p.coeff 3 * H - (2 : k[X]) * q.coeff 5 =
        C lambda * h0 ^ 5) : False := by
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
  have hmismatch' : (3 : k[X]) * p.coeff 3 * H -
      (2 : k[X]) * q.coeff 5 = C lambda * h0 ^ 5 := by
    simpa only [p, q] using hmismatch
  have hh0degree : h0.natDegree = 0 := by
    have hdeg := congrArg Polynomial.natDegree hH
    rw [hHdegree, natDegree_pow] at hdeg
    omega
  obtain ⟨t, ht⟩ := natDegree_eq_zero.mp hh0degree
  have htne : t ≠ 0 := by
    intro hzero
    apply hh0
    rw [← ht, hzero, C_0]
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hmismatch'
  have hmapped' :
      3 * algebraMap k[X] (RatFunc k) (p.coeff 3) *
          (algebraMap k[X] (RatFunc k) h0) ^ 2 -
        2 * algebraMap k[X] (RatFunc k) (q.coeff 5) =
      RatFunc.C lambda * (algebraMap k[X] (RatFunc k) h0) ^ 5 := by
    simpa only [hH, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hhRat : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hLraw := depressedL46_eq_of_mismatch
    (algebraMap k[X] (RatFunc k) h0)
    (algebraMap k[X] (RatFunc k) (p.coeff 3))
    (algebraMap k[X] (RatFunc k) (q.coeff 5))
    (RatFunc.C lambda) hhRat hmapped'
  have hL : depressedL46
      (algebraMap k[X] (RatFunc k) h0)
      (quarticDepressionR46 (algebraMap k[X] (RatFunc k) h0)
        (algebraMap k[X] (RatFunc k) (p.coeff 3)))
      (algebraMap k[X] (RatFunc k) (q.coeff 5)) =
      algebraMap k (RatFunc k) (-lambda / 2) := by
    rw [hLraw]
    simp only [RatFunc.algebraMap_eq_C, map_neg, map_div₀, map_ofNat]
  obtain ⟨S⟩ := squareConstantLSourceCurveData46
    p q H h0 j (-lambda / 2) hp hq hh0 hH hp4' hq6' hL hD
  rw [← ht] at S
  exact S.impossible_of_C htne hj

end LiteralMismatchScaleZero

section LiteralAlignedScaleZero

open scoped Polynomial.Bivariate

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The aligned branch of a normalized `(4,6)` source at common scale zero
is impossible.  Algebraic closure is used only to take the square root of
the nonzero scalar leading core. -/
theorem normalized46ScaleZero_aligned_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized46LeadingCoreSource P Q H 0)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (3 : k[X]) * p.coeff 3 * H - (2 : k[X]) * q.coeff 5 = 0) : False := by
  rcases hsource with
    ⟨hHne, hHdegree, hPdegree, hQdegree, hp4, hq6, hKeller⟩
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
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hcne : c ≠ 0 := by
    intro hzero
    apply hHne
    rw [← hc, hzero, C_0]
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c
    (by norm_num : 0 < 2)
  have htne : t ≠ 0 := by
    intro hzero
    apply hcne
    rw [← ht, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  have hHsquare : H = (C t : k[X]) ^ 2 := by
    rw [← hc, ← C_pow, ht]
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨S⟩ := squareAlignedSourceCurveData46
    p q H (C t) j hp hq (C_ne_zero.mpr htne) hHsquare
      hp4' hq6' haligned' hD
  exact S.impossible_of_C htne hj

/-- The complete normalized `(4,6)` source at common scale zero is
impossible.  The genuine imprimitive-discriminator dichotomy routes its
aligned branch to the aligned source bridge and its nonaligned branch to the
general constant-`L` bridge. -/
theorem normalized46ScaleZero_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized46LeadingCoreSource P Q H 0) : False := by
  have hs := hsource
  rcases hs with
    ⟨hHne, _hHdegree, hPdegree, hQdegree, hp4, hq6, hKeller⟩
  have hdich := planeKellerPair_46_imprimitiveDiscriminatorDichotomy
    hPdegree hQdegree hKeller hHne hp4 hq6
  dsimp only at hdich
  rcases hdich with haligned | ⟨h0, lambda, hh0, _hlambda, hH, hmismatch⟩
  · exact normalized46ScaleZero_aligned_impossible hsource haligned
  · exact normalized46ScaleZero_squareBranch_impossible
      hsource hh0 hH hmismatch

/-- The only remaining normalized `(4,6)` low-scale input is now scale two. -/
def PlaneKellerNormalized46ScaleTwoRoute : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) k) (H : k[X]),
    Normalized46LeadingCoreSource P Q H 2 → PlanePairGenerates P Q

/-- Scale-zero exclusion upgrades any scale-two route to the full normalized
`(4,6)` low-scale interface used by the Max-11 assembly. -/
theorem planeKellerNormalized46LowScaleRoute_of_scaleTwo
    (hscaleTwo : PlaneKellerNormalized46ScaleTwoRoute (k := k)) :
    PlaneKellerNormalized46LowScaleRoute (K := k) := by
  intro P Q H n hn hsource
  rcases hn with rfl | rfl
  · exact (normalized46ScaleZero_impossible hsource).elim
  · exact hscaleTwo P Q H hsource

end LiteralAlignedScaleZero

end Max11DegreeRoutes
