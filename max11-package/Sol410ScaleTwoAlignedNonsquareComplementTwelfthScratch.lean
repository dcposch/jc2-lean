import Sol410ScaleTwoAlignedNonsquareComplementEleventhScratch

/-! # Twelfth-row descent on the complementary `(4,10)` divisor -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- The part of the cancelled twelfth row which survives at a root of `H`.
It is independent of the complementary quotient `l` and of `g`. -/
def alignedTwelfthComplementV410
    (p0 f : K[X]) (κ3 κ7 κ11 : K) : K[X] :=
  -(838860800 : K[X]) * p0 ^ 3 +
    (39321600 : K[X]) * p0 ^ 2 * f ^ 2 +
    (7864320 : K[X]) * p0 ^ 2 * Polynomial.C κ3 -
    (614400 : K[X]) * p0 * f ^ 4 -
    (245760 : K[X]) * p0 * f ^ 2 * Polynomial.C κ3 +
    (10240 : K[X]) * p0 * Polynomial.C κ7 +
    (3200 : K[X]) * f ^ 6 +
    (1920 : K[X]) * f ^ 4 * Polynomial.C κ3 -
    (160 : K[X]) * f ^ 2 * Polynomial.C κ7 + Polynomial.C κ11

/-- Coefficient of `H⁴` before the common `H³` is cancelled. -/
def alignedTwelfthComplementH4Coefficient410
    (p0 g f l : K[X]) (κ3 : K) : K[X] :=
  -(15360 : K[X]) * f * l ^ 2 *
    ((320 : K[X]) * p0 - (5 : K[X]) * f ^ 2 -
      (10 : K[X]) * g * l - Polynomial.C κ3)

/-- Coefficient of `H⁵` in the complementary twelfth-row substitution. -/
def alignedTwelfthComplementH5Coefficient410 (l : K[X]) : K[X] :=
  (25600 : K[X]) * l ^ 4

set_option maxHeartbeats 8000000 in
/-- Exact `H³` cancellation after the simultaneous substitutions
`4p₂ = g²-Hf` and `8p₁ = Hl-gf` in the twelfth block. -/
theorem alignedNonsquareTwelfth_complementSolved_410
    (H p0 p1 p2 g f l : K[X]) (κ3 κ7 κ11 : K)
    (hH : H ≠ 0)
    (hgf : g ^ 2 - (4 : K[X]) * p2 = H * f)
    (hL : g * f + (8 : K[X]) * p1 = H * l)
    (hblk :
      (3200 : K[X]) * ((143 : K[X]) * g ^ 6 -
            (572 : K[X]) * p2 * g ^ 4 +
            (528 : K[X]) * p2 ^ 2 * g ^ 2 -
            (64 : K[X]) * p2 ^ 3) * f ^ 3 +
        (51200 : K[X]) * p1 * g *
          ((187 : K[X]) * g ^ 4 - (664 : K[X]) * p2 * g ^ 2 +
            (432 : K[X]) * p2 ^ 2) * f ^ 2 +
        (314572800 : K[X]) * p1 ^ 2 * p2 ^ 2 * f +
        (209715200 : K[X]) * p1 ^ 3 * p2 * g =
      H * (-(334233600 : K[X]) * p1 ^ 2 * p2 * f ^ 2 -
        (183500800 : K[X]) * p1 ^ 3 * g * f +
        (78643200 : K[X]) * p0 * p2 ^ 2 * f ^ 2 +
        (314572800 : K[X]) * p0 * p1 * p2 * g * f -
        (104857600 : K[X]) * p1 ^ 4 +
        (1258291200 : K[X]) * p0 * p1 ^ 2 * p2 -
        Polynomial.C κ3 * ((245760 : K[X]) * p2 ^ 2 * f ^ 2) -
        Polynomial.C κ3 * ((983040 : K[X]) * p1 * p2 * g * f) -
        Polynomial.C κ3 * ((3932160 : K[X]) * p1 ^ 2 * p2) +
      H * (-(68812800 : K[X]) * p1 ^ 2 * f ^ 3 +
          (68812800 : K[X]) * p0 * p2 * f ^ 3 +
          (176947200 : K[X]) * p0 * p1 * g * f ^ 2 +
          (629145600 : K[X]) * p0 * p1 ^ 2 * f -
          (314572800 : K[X]) * p0 ^ 2 * p2 * f -
          (629145600 : K[X]) * p0 ^ 2 * p1 * g +
          Polynomial.C κ7 * ((1280 : K[X]) * p2 * f) +
          Polynomial.C κ7 * ((2560 : K[X]) * p1 * g) -
          Polynomial.C κ3 * ((215040 : K[X]) * p2 * f ^ 3) -
          Polynomial.C κ3 * ((552960 : K[X]) * p1 * g * f ^ 2) -
          Polynomial.C κ3 * ((1966080 : K[X]) * p1 ^ 2 * f) +
          Polynomial.C κ3 * ((1966080 : K[X]) * p0 * p2 * f) +
          Polynomial.C κ3 * ((3932160 : K[X]) * p0 * p1 * g) +
        H * ((12902400 : K[X]) * p0 * f ^ 4 -
            (117964800 : K[X]) * p0 ^ 2 * f ^ 2 +
            (838860800 : K[X]) * p0 ^ 3 - Polynomial.C κ11 +
            Polynomial.C κ7 * ((480 : K[X]) * f ^ 2) -
            Polynomial.C κ7 * ((10240 : K[X]) * p0) -
            Polynomial.C κ3 * ((40320 : K[X]) * f ^ 4) +
            Polynomial.C κ3 * ((737280 : K[X]) * p0 * f ^ 2) -
            Polynomial.C κ3 * ((7864320 : K[X]) * p0 ^ 2))))) :
    alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 +
        (320 : K[X]) * g * l *
          alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        H * alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
        H ^ 2 * alignedTwelfthComplementH5Coefficient410 l = 0 := by
  let U : K[X] := (8 : K[X]) * p1
  let V : K[X] := (4 : K[X]) * p2
  have hscaled :
      (3200 : K[X]) * ((143 : K[X]) * g ^ 6 -
            (143 : K[X]) * V * g ^ 4 +
            (33 : K[X]) * V ^ 2 * g ^ 2 - V ^ 3) * f ^ 3 +
        (6400 : K[X]) * U * g *
          ((187 : K[X]) * g ^ 4 - (166 : K[X]) * V * g ^ 2 +
            (27 : K[X]) * V ^ 2) * f ^ 2 +
        (307200 : K[X]) * U ^ 2 * V ^ 2 * f +
        (102400 : K[X]) * U ^ 3 * V * g =
      H * (-(1305600 : K[X]) * U ^ 2 * V * f ^ 2 -
        (358400 : K[X]) * U ^ 3 * g * f +
        (4915200 : K[X]) * p0 * V ^ 2 * f ^ 2 +
        (9830400 : K[X]) * p0 * U * V * g * f -
        (25600 : K[X]) * U ^ 4 +
        (4915200 : K[X]) * p0 * U ^ 2 * V -
        Polynomial.C κ3 * ((15360 : K[X]) * V ^ 2 * f ^ 2) -
        Polynomial.C κ3 * ((30720 : K[X]) * U * V * g * f) -
        Polynomial.C κ3 * ((15360 : K[X]) * U ^ 2 * V) +
      H * (-(1075200 : K[X]) * U ^ 2 * f ^ 3 +
          (17203200 : K[X]) * p0 * V * f ^ 3 +
          (22118400 : K[X]) * p0 * U * g * f ^ 2 +
          (9830400 : K[X]) * p0 * U ^ 2 * f -
          (78643200 : K[X]) * p0 ^ 2 * V * f -
          (78643200 : K[X]) * p0 ^ 2 * U * g +
          Polynomial.C κ7 * ((320 : K[X]) * V * f) +
          Polynomial.C κ7 * ((320 : K[X]) * U * g) -
          Polynomial.C κ3 * ((53760 : K[X]) * V * f ^ 3) -
          Polynomial.C κ3 * ((69120 : K[X]) * U * g * f ^ 2) -
          Polynomial.C κ3 * ((30720 : K[X]) * U ^ 2 * f) +
          Polynomial.C κ3 * ((491520 : K[X]) * p0 * V * f) +
          Polynomial.C κ3 * ((491520 : K[X]) * p0 * U * g) +
        H * ((12902400 : K[X]) * p0 * f ^ 4 -
            (117964800 : K[X]) * p0 ^ 2 * f ^ 2 +
            (838860800 : K[X]) * p0 ^ 3 - Polynomial.C κ11 +
            Polynomial.C κ7 * ((480 : K[X]) * f ^ 2) -
            Polynomial.C κ7 * ((10240 : K[X]) * p0) -
            Polynomial.C κ3 * ((40320 : K[X]) * f ^ 4) +
            Polynomial.C κ3 * ((737280 : K[X]) * p0 * f ^ 2) -
            Polynomial.C κ3 * ((7864320 : K[X]) * p0 ^ 2)))) := by
    dsimp only [U, V]
    linear_combination hblk
  have hU : U = H * l - g * f := by
    dsimp only [U]
    linear_combination hL
  have hV : V = g ^ 2 - H * f := by
    dsimp only [V]
    linear_combination -hgf
  rw [hU, hV] at hscaled
  have hfactored :
      H ^ 3 *
        (alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 +
          (320 : K[X]) * g * l *
            alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
          H * alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
          H ^ 2 * alignedTwelfthComplementH5Coefficient410 l) = 0 := by
    simp only [alignedTwelfthComplementV410,
      alignedEleventhComplementWall410,
      alignedTwelfthComplementH4Coefficient410,
      alignedTwelfthComplementH5Coefficient410]
    linear_combination hscaled
  exact (mul_eq_zero.mp hfactored).resolve_left (pow_ne_zero 3 hH)

/-- Combining M11 and M12 at a root of `H` removes both complement
branches and forces the same `V`-polynomial to vanish. -/
theorem alignedNonsquareTwelfth_complementRootV_410
    (H p0 g f l : K[X]) (κ3 κ7 κ11 x : K)
    (h11 :
      (64 : K[X]) * l *
          alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        (10240 : K[X]) * H * f * l ^ 3 = 0)
    (h12 :
      alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 +
          (320 : K[X]) * g * l *
            alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
          H * alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
          H ^ 2 * alignedTwelfthComplementH5Coefficient410 l = 0)
    (hx : H.eval x = 0) :
    (alignedTwelfthComplementV410 p0 f κ3 κ7 κ11).eval x = 0 := by
  have hprod := alignedNonsquareEleventh_complementRootProduct_410
    H p0 g f l κ3 κ7 x h11 hx
  have hev := congrArg (fun w : K[X] => w.eval x) h12
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hx] at hev
  norm_num at hev
  linear_combination hev - 320 * g.eval x * hprod

/-- The same-witness combination at both simple roots globalizes to the
exact quadratic divisibility `H ∣ V`. -/
theorem alignedNonsquareTwelfth_complementVDivisor_410
    [IsAlgClosed K]
    (H p0 g f l : K[X]) (κ3 κ7 κ11 : K)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : K, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (h11 :
      (64 : K[X]) * l *
          alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        (10240 : K[X]) * H * f * l ^ 3 = 0)
    (h12 :
      alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 +
          (320 : K[X]) * g * l *
            alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
          H * alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
          H ^ 2 * alignedTwelfthComplementH5Coefficient410 l = 0) :
    H ∣ alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 := by
  apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
  intro x hx
  exact alignedNonsquareTwelfth_complementRootV_410
    H p0 g f l κ3 κ7 κ11 x h11 h12 hx

section Source410

variable [IsAlgClosed K]

/-- Narrow normalized-source interface for the exact same-witness factored
rows.  It uses the source only for the quadratic degree and simple-root
facts; constructing these two rows from the large raw chamber packet is kept
as a separate mechanical assembly boundary. -/
theorem normalized410ScaleTwo_alignedNonsquare_complementTwelfth_of_rows
    {P Q : MvPolynomial (Fin 2) K} {H p0 g f l : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (κ3 κ7 κ11 : K)
    (h11 :
      (64 : K[X]) * l *
          alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        (10240 : K[X]) * H * f * l ^ 3 = 0)
    (h12 :
      alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 +
          (320 : K[X]) * g * l *
            alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
          H * alignedTwelfthComplementH4Coefficient410 p0 g f l κ3 +
          H ^ 2 * alignedTwelfthComplementH5Coefficient410 l = 0) :
    H ∣ alignedTwelfthComplementV410 p0 f κ3 κ7 κ11 := by
  have hsimple : ∀ x : K, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx =>
      nonsquare_natDegree_two_derivative_ne_zero hsource.2.1 hnsq hx
  exact alignedNonsquareTwelfth_complementVDivisor_410
    H p0 g f l κ3 κ7 κ11 hsource.2.1 hsimple h11 h12

end Source410

#print axioms alignedNonsquareTwelfth_complementSolved_410
#print axioms alignedNonsquareTwelfth_complementRootV_410
#print axioms alignedNonsquareTwelfth_complementVDivisor_410
#print axioms normalized410ScaleTwo_alignedNonsquare_complementTwelfth_of_rows

end Max11DegreeRoutes
