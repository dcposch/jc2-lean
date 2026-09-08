import LowScale68ScaleZero
import LowScaleCore
import HistoryDegree
import TotalDegreeRoutes

/-!
# Common constant-scale source adapter for the remaining low-scale leaves

The normalized `(4,10)`, `(6,10)`, and `(8,10)` sources all have a literal
nonzero scalar common core at scale zero.  This file packages the part of the
`(4,6)` and `(6,8)` constant-scale bridges which is independent of the two
outer degrees: after any polynomial-centered affine depression, every
coefficient of both transformed source polynomials still has a literal
representative in `k[x]`.
-/

noncomputable section

open scoped Polynomial.Bivariate

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ConstantScaleCoefficientAdapter

variable {k : Type*} [Field k] [CharZero k]

/-- Every coefficient of a constant-scale affine depression of a literal
source polynomial is the image of an explicit coefficient polynomial.  This
is the degree-independent form of the coefficient-by-coefficient bridges
previously written for depressed quartics, sextics, and octics. -/
theorem constantScale_affineDepress_coefficient_hasPolynomialRepresentative
    (f : k[X][X]) (t : k) (r0 : k[X]) (ht : t ≠ 0) (n : ℕ) :
    ∃ fn : k[X],
      algebraMap k[X] (RatFunc k) fn =
        (affineDepress46 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc46 f)).coeff n := by
  let f0 : k[X][X] := f.comp
    ((Polynomial.X - Polynomial.C r0) *
      Polynomial.C (Polynomial.C t⁻¹))
  refine ⟨f0.coeff n, ?_⟩
  have hmap := congrArg (fun g : (RatFunc k)[X] => g.coeff n)
    (affineDepress_source_constantScale_map46 f t r0 ht)
  simpa only [f0, Polynomial.coeff_map] using hmap.symm

/-- A nonzero degree-zero common core gives a single scalar scale for which
all coefficients of both depressed source polynomials have polynomial
representatives, uniformly in the chosen polynomial center. -/
theorem scaleZero_pair_affineDepress_coefficients_havePolynomialRepresentatives
    (P Q : MvPolynomial (Fin 2) k) (h : k[X])
    (hh : h ≠ 0) (hdegree : h.natDegree = 0) :
    ∃ t : k, t ≠ 0 ∧ h = Polynomial.C t ∧
      ∀ (r0 : k[X]) (n : ℕ), ∃ pn qn : k[X],
        algebraMap k[X] (RatFunc k) pn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P))).coeff n ∧
          algebraMap k[X] (RatFunc k) qn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q))).coeff n := by
  obtain ⟨t, htcore⟩ := Polynomial.natDegree_eq_zero.mp hdegree
  have ht : t ≠ 0 := by
    intro hzero
    apply hh
    rw [← htcore, hzero, Polynomial.C_0]
  refine ⟨t, ht, htcore.symm, ?_⟩
  intro r0 n
  obtain ⟨pn, hpn⟩ :=
    constantScale_affineDepress_coefficient_hasPolynomialRepresentative
      ((Polynomial.Bivariate.equivMvPolynomial k).symm P) t r0 ht n
  obtain ⟨qn, hqn⟩ :=
    constantScale_affineDepress_coefficient_hasPolynomialRepresentative
      ((Polynomial.Bivariate.equivMvPolynomial k).symm Q) t r0 ht n
  exact ⟨pn, qn, hpn, hqn⟩

/-- Source adapter covering the scale-zero `(4,10)` and `(6,10)` normalized
leaves (and, in fact, every normalized coprime reduced-weight source). -/
theorem normalizedCoprimeScaleZero_affineDepress_polynomialRepresentatives
    {r s : ℕ} {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : NormalizedCoprimeLeadingCoreSource r s P Q h 0) :
    ∃ t : k, t ≠ 0 ∧ h = Polynomial.C t ∧
      ∀ (r0 : k[X]) (n : ℕ), ∃ pn qn : k[X],
        algebraMap k[X] (RatFunc k) pn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P))).coeff n ∧
          algebraMap k[X] (RatFunc k) qn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q))).coeff n := by
  exact scaleZero_pair_affineDepress_coefficients_havePolynomialRepresentatives
    P Q h hsource.1 hsource.2.1

/-- Source adapter covering the scale-zero `(8,10)` normalized leaf (and
every normalized consecutive reduced-weight source). -/
theorem normalizedConsecutiveScaleZero_affineDepress_polynomialRepresentatives
    {r : ℕ} {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : NormalizedConsecutiveLeadingCoreSource r P Q h 0) :
    ∃ t : k, t ≠ 0 ∧ h = Polynomial.C t ∧
      ∀ (r0 : k[X]) (n : ℕ), ∃ pn qn : k[X],
        algebraMap k[X] (RatFunc k) pn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P))).coeff n ∧
          algebraMap k[X] (RatFunc k) qn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q))).coeff n := by
  exact scaleZero_pair_affineDepress_coefficients_havePolynomialRepresentatives
    P Q h hsource.1 hsource.2.1

end ConstantScaleCoefficientAdapter

section LargeSourceShearAdapter

variable {k : Type*} [Field k] [CharZero k]

/-- Degree-independent source adapter for a pair whose normalized leading
coefficients are powers `h^r,h^s` and whose outer degrees are `2r,2s`.
Every sufficiently large triangular source shear has the displayed exact
total degrees. -/
theorem leadingPowerPair_largeSourceShear_exactTotalDegrees
    {r s H : ℕ} (hr : 0 < r) (hs : 0 < s)
    (P Q : MvPolynomial (Fin 2) k) (h : k[X])
    (hh : h ≠ 0) (hdegree : h.natDegree = H)
    (hPdegree : degreeOf 1 P = 2 * r)
    (hQdegree : degreeOf 1 Q = 2 * s)
    (hPtop : ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff
      (2 * r) = h ^ r)
    (hQtop : ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff
      (2 * s) = h ^ s) :
    ∃ B, ∀ L, B < L →
      (planeSourceShear k L P).totalDegree = r * (H + 2 * L) ∧
      (planeSourceShear k L Q).totalDegree = s * (H + 2 * L) := by
  refine ⟨max P.totalDegree Q.totalDegree, ?_⟩
  intro L hL
  have hPlarge : P.totalDegree < L :=
    (Nat.le_max_left P.totalDegree Q.totalDegree).trans_lt hL
  have hQlarge : Q.totalDegree < L :=
    (Nat.le_max_right P.totalDegree Q.totalDegree).trans_lt hL
  have hPexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    P (h ^ r) (2 * r) (r * H) L (by omega) hPdegree hPtop
    (pow_ne_zero r hh) (by rw [Polynomial.natDegree_pow, hdegree]) hPlarge
  have hQexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    Q (h ^ s) (2 * s) (s * H) L (by omega) hQdegree hQtop
    (pow_ne_zero s hh) (by rw [Polynomial.natDegree_pow, hdegree]) hQlarge
  constructor
  · rw [planeSourceShear_apply, hPexact]
    ring
  · rw [planeSourceShear_apply, hQexact]
    ring

/-- For coprime reduced weights, the common total-degree gcd after a large
source shear is exactly the common scale `H + 2L`.  Thus the six remaining
low-scale leaves reduce uniformly to the classical `2p` total-gcd route
after choosing the shear exponent. -/
theorem leadingPowerPair_largeSourceShear_exactGCD
    {r s H : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r.Coprime s)
    (P Q : MvPolynomial (Fin 2) k) (h : k[X])
    (hh : h ≠ 0) (hdegree : h.natDegree = H)
    (hPdegree : degreeOf 1 P = 2 * r)
    (hQdegree : degreeOf 1 Q = 2 * s)
    (hPtop : ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff
      (2 * r) = h ^ r)
    (hQtop : ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff
      (2 * s) = h ^ s) :
    ∃ B, ∀ L, B < L →
      Nat.gcd (planeSourceShear k L P).totalDegree
        (planeSourceShear k L Q).totalDegree = H + 2 * L := by
  obtain ⟨B, hB⟩ := leadingPowerPair_largeSourceShear_exactTotalDegrees
    hr hs P Q h hh hdegree hPdegree hQdegree hPtop hQtop
  refine ⟨B, ?_⟩
  intro L hL
  obtain ⟨hP, hQ⟩ := hB L hL
  rw [hP, hQ, Nat.gcd_mul_right, hrs.gcd_eq_one, one_mul]

/-- Large-source-shear adapter for all normalized coprime low-scale sources;
in particular this covers both scales of `(4,10)` and `(6,10)`. -/
theorem normalizedCoprimeLowScale_largeSourceShear_exactGCD
    {r s H : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r.Coprime s)
    {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : NormalizedCoprimeLeadingCoreSource r s P Q h H) :
    ∃ B, ∀ L, B < L →
      Nat.gcd (planeSourceShear k L P).totalDegree
        (planeSourceShear k L Q).totalDegree = H + 2 * L := by
  exact leadingPowerPair_largeSourceShear_exactGCD hr hs hrs P Q h
    hsource.1 hsource.2.1 hsource.2.2.1 hsource.2.2.2.1
    hsource.2.2.2.2.1 hsource.2.2.2.2.2.1

/-- Large-source-shear adapter for all normalized consecutive low-scale
sources; in particular this covers both scales of `(8,10)`. -/
theorem normalizedConsecutiveLowScale_largeSourceShear_exactGCD
    {r H : ℕ} (hr : 0 < r)
    {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : NormalizedConsecutiveLeadingCoreSource r P Q h H) :
    ∃ B, ∀ L, B < L →
      Nat.gcd (planeSourceShear k L P).totalDegree
        (planeSourceShear k L Q).totalDegree = H + 2 * L := by
  apply leadingPowerPair_largeSourceShear_exactGCD
    (r := r) (s := r + 1) (H := H) hr (by omega)
    (by simpa [Nat.add_comm] using
      (Nat.coprime_add_self_right.mpr (Nat.coprime_one_right r))) P Q h
  · exact hsource.1
  · exact hsource.2.1
  · exact hsource.2.2.1
  · simpa [Nat.mul_add] using hsource.2.2.2.1
  · exact hsource.2.2.2.2.1
  · simpa [Nat.mul_add] using hsource.2.2.2.2.2.1

/-- Concrete two-scale adapter for the normalized `(4,10)` leaves. -/
theorem normalized410LowScale_largeSourceShear_exactGCD
    {H : ℕ} {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q h H) :
    ∃ B, ∀ L, B < L →
      Nat.gcd (planeSourceShear k L P).totalDegree
        (planeSourceShear k L Q).totalDegree = H + 2 * L := by
  exact normalizedCoprimeLowScale_largeSourceShear_exactGCD
    (r := 2) (s := 5) (by norm_num) (by norm_num) (by norm_num) hsource

/-- Concrete two-scale adapter for the normalized `(6,10)` leaves. -/
theorem normalized610LowScale_largeSourceShear_exactGCD
    {H : ℕ} {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q h H) :
    ∃ B, ∀ L, B < L →
      Nat.gcd (planeSourceShear k L P).totalDegree
        (planeSourceShear k L Q).totalDegree = H + 2 * L := by
  exact normalizedCoprimeLowScale_largeSourceShear_exactGCD
    (r := 3) (s := 5) (by norm_num) (by norm_num) (by norm_num) hsource

/-- Concrete two-scale adapter for the normalized `(8,10)` leaves. -/
theorem normalized810LowScale_largeSourceShear_exactGCD
    {H : ℕ} {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q h H) :
    ∃ B, ∀ L, B < L →
      Nat.gcd (planeSourceShear k L P).totalDegree
        (planeSourceShear k L Q).totalDegree = H + 2 * L := by
  exact normalizedConsecutiveLowScale_largeSourceShear_exactGCD
    (r := 4) (by norm_num) hsource

/-- Once the classical twice-prime total-gcd theorem is supplied, an exact
large-shear gcd calculation at scale zero or two closes the original source
pair.  The proof includes prime selection, Keller transport, and descent of
generation through the triangular automorphism. -/
theorem planePairGenerates_of_lowScale_largeSourceShear_exactGCD
    (hroute : PlaneKellerTwicePrimeTotalDegreeGCDRoute (K := k))
    {P Q : MvPolynomial (Fin 2) k} {H : ℕ}
    (hscale : H = 0 ∨ H = 2) (hKeller : IsPlaneKellerPair P Q)
    (hexact : ∃ B, ∀ L, B < L →
      Nat.gcd (planeSourceShear k L P).totalDegree
        (planeSourceShear k L Q).totalDegree = H + 2 * L) :
    PlanePairGenerates P Q := by
  obtain ⟨B, hB⟩ := hexact
  obtain ⟨p, hBp, hp⟩ := Nat.exists_infinite_primes (B + 2)
  rcases hscale with rfl | rfl
  · have hBL : B < p := by omega
    have hgcd :
        Nat.gcd (planeSourceShear k p P).totalDegree
          (planeSourceShear k p Q).totalDegree = 2 * p := by
      simpa using hB p hBL
    have hgenerated := hroute (planeSourceShear k p P)
      (planeSourceShear k p Q) p (IsPlaneKellerPair.sourceShear hKeller p) hp hgcd
    exact (planePairGenerates_sourceShear_iff p P Q).mp hgenerated
  · let L := p - 1
    have hBL : B < L := by
      dsimp only [L]
      omega
    have hgcd :
        Nat.gcd (planeSourceShear k L P).totalDegree
          (planeSourceShear k L Q).totalDegree = 2 * p := by
      have := hB L hBL
      dsimp only [L] at this ⊢
      omega
    have hgenerated := hroute (planeSourceShear k L P)
      (planeSourceShear k L Q) p (IsPlaneKellerPair.sourceShear hKeller L) hp hgcd
    exact (planePairGenerates_sourceShear_iff L P Q).mp hgenerated

/-- Conditional closure of every normalized coprime low-scale route.  This
simultaneously closes `(4,10)` and `(6,10)` at both scales once the reviewed
twice-prime theorem is available. -/
theorem planeKellerNormalizedCoprimeLowScaleRoute_of_twicePrimeGCD
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r.Coprime s)
    (hroute : PlaneKellerTwicePrimeTotalDegreeGCDRoute (K := k)) :
    PlaneKellerNormalizedCoprimeLowScaleRoute (K := k) r s := by
  intro P Q h H hscale hsource
  apply planePairGenerates_of_lowScale_largeSourceShear_exactGCD hroute
    hscale hsource.2.2.2.2.2.2
  exact normalizedCoprimeLowScale_largeSourceShear_exactGCD
    hr hs hrs hsource

/-- Conditional closure of every normalized consecutive low-scale route;
this closes `(8,10)` at both scales under the same classical input. -/
theorem planeKellerNormalizedConsecutiveLowScaleRoute_of_twicePrimeGCD
    {r : ℕ} (hr : 0 < r)
    (hroute : PlaneKellerTwicePrimeTotalDegreeGCDRoute (K := k)) :
    PlaneKellerNormalizedConsecutiveLowScaleRoute (K := k) r := by
  intro P Q h H hscale hsource
  apply planePairGenerates_of_lowScale_largeSourceShear_exactGCD hroute
    hscale hsource.2.2.2.2.2.2
  exact normalizedConsecutiveLowScale_largeSourceShear_exactGCD hr hsource

end LargeSourceShearAdapter

#print axioms constantScale_affineDepress_coefficient_hasPolynomialRepresentative
#print axioms scaleZero_pair_affineDepress_coefficients_havePolynomialRepresentatives
#print axioms normalizedCoprimeScaleZero_affineDepress_polynomialRepresentatives
#print axioms normalizedConsecutiveScaleZero_affineDepress_polynomialRepresentatives
#print axioms leadingPowerPair_largeSourceShear_exactTotalDegrees
#print axioms leadingPowerPair_largeSourceShear_exactGCD
#print axioms normalizedCoprimeLowScale_largeSourceShear_exactGCD
#print axioms normalizedConsecutiveLowScale_largeSourceShear_exactGCD
#print axioms normalized410LowScale_largeSourceShear_exactGCD
#print axioms normalized610LowScale_largeSourceShear_exactGCD
#print axioms normalized810LowScale_largeSourceShear_exactGCD
#print axioms planePairGenerates_of_lowScale_largeSourceShear_exactGCD
#print axioms planeKellerNormalizedCoprimeLowScaleRoute_of_twicePrimeGCD
#print axioms planeKellerNormalizedConsecutiveLowScaleRoute_of_twicePrimeGCD

end Max11DegreeRoutes
