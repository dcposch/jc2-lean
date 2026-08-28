import CoprimeDegreeRoute

/-! # The standard-endpoint route for the even gcd-two residue

Guccione--Guccione--Valqui prove that the normalized right endpoint of a
standard polynomial `(a,b)`-pair has coordinate gcd strictly greater than
two.  After a large triangular source shear and a swap of the source
variables, a gcd-two partial-degree pair with common leading scale `H > 2`
has normalized right endpoint `(2,H)`.  This module isolates the exact
published endpoint statement used by that argument and checks all of the
large-shear and arithmetic bookkeeping around it.

The remaining exceptional scales are literally `H = 0` and `H = 2`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- The outer-variable polynomial used by the triangular source shear in
the canonical bivariate presentation. -/
def bivariateSourceShearSubstitute {K : Type*} [CommRing K] (L : ℕ) :
    K[X][Y] := Polynomial.X + Polynomial.C (Polynomial.X ^ L)

/-- In the canonical bivariate presentation, the source shear is ordinary
polynomial composition in the outer `y` variable by `y + x^L`. -/
theorem bivariateEquiv_planeSourceShearHom {K : Type*} [CommRing K]
    (L : ℕ) (P : MvPolynomial (Fin 2) K) :
    (Polynomial.Bivariate.equivMvPolynomial K).symm
        (planeSourceShearHom L P) =
      ((Polynomial.Bivariate.equivMvPolynomial K).symm P).comp
        (bivariateSourceShearSubstitute L) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [planeSourceShearHom, Polynomial.Bivariate.equivMvPolynomial_symm_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ, Polynomial.add_comp]
  | mul_X P i hP =>
      fin_cases i <;>
        simp [planeSourceShearHom_X_zero, planeSourceShearHom_X_one,
          bivariateSourceShearSubstitute,
          Polynomial.Bivariate.equivMvPolynomial_symm_X_0,
          Polynomial.Bivariate.equivMvPolynomial_symm_X_1, hP]

/-- A triangular source shear preserves partial degree in `y`. -/
theorem degreeOf_one_planeSourceShear {K : Type*} [Field K]
    (L : ℕ) (P : MvPolynomial (Fin 2) K) :
    degreeOf 1 (planeSourceShear K L P) = degreeOf 1 P := by
  calc
    degreeOf 1 (planeSourceShear K L P) =
        ((Polynomial.Bivariate.equivMvPolynomial K).symm
          (planeSourceShear K L P)).natDegree :=
      (natDegree_bivariate_eq_degreeOf_y _).symm
    _ = (((Polynomial.Bivariate.equivMvPolynomial K).symm P).comp
          (bivariateSourceShearSubstitute L)).natDegree := by
      rw [planeSourceShear_apply, bivariateEquiv_planeSourceShearHom]
    _ = ((Polynomial.Bivariate.equivMvPolynomial K).symm P).natDegree := by
      rw [Polynomial.natDegree_comp]
      rw [show (bivariateSourceShearSubstitute (K := K) L).natDegree = 1 by
        simpa [bivariateSourceShearSubstitute] using
          Polynomial.natDegree_X_add_C (Polynomial.X ^ L), Nat.mul_one]
    _ = degreeOf 1 P := natDegree_bivariate_eq_degreeOf_y P

/-- A triangular source shear preserves the leading `y` coefficient. -/
theorem bivariate_topCoeff_planeSourceShear {K : Type*} [Field K]
    (L m : ℕ) (P : MvPolynomial (Fin 2) K)
    (hP : degreeOf 1 P = m) :
    ((Polynomial.Bivariate.equivMvPolynomial K).symm
        (planeSourceShear K L P)).coeff m =
      ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m := by
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let r : K[X][Y] := bivariateSourceShearSubstitute L
  have hpdegree : p.natDegree = m := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hrdegree : r.natDegree = 1 := by
    simpa [r, bivariateSourceShearSubstitute] using
      Polynomial.natDegree_X_add_C (Polynomial.X ^ L)
  have hcompdegree : (p.comp r).natDegree = m := by
    rw [Polynomial.natDegree_comp, hpdegree, hrdegree, Nat.mul_one]
  calc
    ((Polynomial.Bivariate.equivMvPolynomial K).symm
        (planeSourceShear K L P)).coeff m = (p.comp r).coeff m := by
      rw [planeSourceShear_apply, bivariateEquiv_planeSourceShearHom]
    _ = (p.comp r).leadingCoeff := by
      rw [Polynomial.leadingCoeff, hcompdegree]
    _ = p.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by omega)]
      rw [show r.leadingCoeff = 1 by
        simpa [r, bivariateSourceShearSubstitute] using
          Polynomial.leadingCoeff_X_add_C (Polynomial.X ^ L), one_pow, mul_one]
    _ = p.coeff m := by rw [Polynomial.leadingCoeff, hpdegree]

/-- The numerical conclusion of the standard-pair endpoint obstruction.

The hypotheses say that total degree and partial `y` degree have the same
reduced ratio `a:b`, while the leading-coefficient `x`-degrees give normalized
endpoint `(u,v)`.  Swapping the source variables turns this into the right
endpoint used by the standard-pair theorem.  The
conditions `1 < a`, `1 < b`, `a.Coprime b`, and `u < v` are exactly the
standard-pair range.  The published theorem says that the two coordinates of
that normalized endpoint have gcd strictly greater than two.

This definition is an interface to that classical geometric theorem, not a
new assertion that its Newton-polygon proof has already been formalized. -/
def PlaneKellerStandardEndpointGCDObstruction
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (a b S u v : ℕ),
    1 < a → 1 < b → a.Coprime b →
    IsPlaneKellerPair P Q →
    degreeOf 1 P = a * u → degreeOf 1 Q = b * u →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (a * u)).natDegree =
      a * v →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (b * u)).natDegree =
      b * v →
    P.totalDegree = a * S → Q.totalDegree = b * S →
    u < v → 2 < Nat.gcd u v

/-- Generation-form compatibility interface for the same endpoint theorem.
If the normalized endpoint has coordinate gcd at most two, the numerical
obstruction makes the source data inconsistent. -/
def PlaneKellerStandardEndpointGCDRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (a b S u v : ℕ),
    1 < a → 1 < b → a.Coprime b →
    IsPlaneKellerPair P Q →
    degreeOf 1 P = a * u → degreeOf 1 Q = b * u →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (a * u)).natDegree =
      a * v →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (b * u)).natDegree =
      b * v →
    P.totalDegree = a * S → Q.totalDegree = b * S →
    u < v → Nat.gcd u v ≤ 2 →
    PlanePairGenerates P Q

/-- The exact numerical GGV endpoint obstruction supplies the older
generation-form compatibility interface. -/
theorem planeKellerStandardEndpointGCDRoute_of_obstruction
    {K : Type*} [Field K]
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K)) :
    PlaneKellerStandardEndpointGCDRoute (K := K) := by
  intro P Q a b S u v ha hb hab hKeller hPdegree hQdegree
    hAdegree hBdegree hPtotal hQtotal huv hgcd
  have hgcdLarge := hendpoint P Q a b S u v ha hb hab hKeller
    hPdegree hQdegree hAdegree hBdegree hPtotal hQtotal huv
  omega

/-- One literal value of the common leading-degree scale at a fixed partial-
degree pair. -/
def PlaneKellerLeadingScaleAtDegrees
    {K : Type*} [Field K] (m n H : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K),
    degreeOf 1 P = m → degreeOf 1 Q = n →
    IsPlaneKellerPair P Q →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m).natDegree =
      (m / 2) * H →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff n).natDegree =
      (n / 2) * H →
    PlanePairGenerates P Q

/-- The two literal common leading scales not covered by the strict
standard-endpoint inequality. -/
def PlaneKellerLowEvenLeadingScalesAtDegrees
    {K : Type*} [Field K] (m n : ℕ) : Prop :=
  PlaneKellerLeadingScaleAtDegrees (K := K) m n 0 ∧
    PlaneKellerLeadingScaleAtDegrees (K := K) m n 2

/-- The standard-endpoint theorem closes every gcd-two source with even
common leading scale strictly above two. -/
theorem planeKellerLeadingScaleAtDegrees_of_gcd_two_of_two_lt_scale
    {K : Type*} [Field K] [CharZero K]
    (m n H : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hgcd : Nat.gcd m n = 2)
    (hma : 1 < m / 2) (hnb : 1 < n / 2)
    (hHeven : 2 ∣ H) (hHlarge : 2 < H)
    (hendpoint : PlaneKellerStandardEndpointGCDRoute (K := K)) :
    PlaneKellerLeadingScaleAtDegrees (K := K) m n H := by
  intro P Q hP hQ hKeller hAdegree' hBdegree'
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  let A := p.coeff m
  let B := q.coeff n
  let a := m / 2
  let b := n / 2
  have hpdegree : p.natDegree = m := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hqdegree : q.natDegree = n := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp : p ≠ 0 := by
    intro hpzero
    rw [hpzero, Polynomial.natDegree_zero] at hpdegree
    omega
  have hq : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Polynomial.natDegree_zero] at hqdegree
    omega
  have hA : A ≠ 0 := by
    dsimp only [A]
    rw [← hpdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hB : B ≠ 0 := by
    dsimp only [B]
    rw [← hqdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have h2m : 2 ∣ m := hgcd ▸ Nat.gcd_dvd_left m n
  have h2n : 2 ∣ n := hgcd ▸ Nat.gcd_dvd_right m n
  have hmEq : m = a * 2 := by
    exact (Nat.div_mul_cancel h2m).symm
  have hnEq : n = b * 2 := by
    exact (Nat.div_mul_cancel h2n).symm
  have hgcdpos : 0 < Nat.gcd m n := by rw [hgcd]; norm_num
  have habcop : a.Coprime b := by
    simpa only [a, b, hgcd] using Nat.coprime_div_gcd_div_gcd hgcdpos
  have hAdegree : A.natDegree = a * H := by
    simpa only [A, p, a] using hAdegree'
  have hBdegree : B.natDegree = b * H := by
    simpa only [B, q, b] using hBdegree'
  obtain ⟨L, hlarge, _hprime⟩ :=
    exists_large_prime_eq_add H (max P.totalDegree Q.totalDegree)
  have hPlarge : P.totalDegree < L :=
    (Nat.le_max_left P.totalDegree Q.totalDegree).trans_lt hlarge
  have hQlarge : Q.totalDegree < L :=
    (Nat.le_max_right P.totalDegree Q.totalDegree).trans_lt hlarge
  have hPexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    P A m A.natDegree L hmpos hP rfl hA rfl hPlarge
  have hQexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    Q B n B.natDegree L hnpos hQ rfl hB rfl hQlarge
  have hPtotal : (planeSourceShear K L P).totalDegree =
      a * (H + 2 * L) := by
    rw [planeSourceShear_apply, hPexact, hAdegree, hmEq]
    ring
  have hQtotal : (planeSourceShear K L Q).totalDegree =
      b * (H + 2 * L) := by
    rw [planeSourceShear_apply, hQexact, hBdegree, hnEq]
    ring
  have hendpointGCD : Nat.gcd 2 H ≤ 2 := by
    rw [Nat.gcd_eq_left_iff_dvd.mpr hHeven]
  have hPdegreeRoute :
      degreeOf 1 (planeSourceShear K L P) = a * 2 := by
    rw [degreeOf_one_planeSourceShear]
    exact hP.trans hmEq
  have hQdegreeRoute :
      degreeOf 1 (planeSourceShear K L Q) = b * 2 := by
    rw [degreeOf_one_planeSourceShear]
    exact hQ.trans hnEq
  have hAdegreeRoute :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm
        (planeSourceShear K L P)).coeff
        (a * 2)).natDegree = a * H := by
    rw [← hmEq]
    rw [bivariate_topCoeff_planeSourceShear L m P hP]
    simpa only [a] using hAdegree'
  have hBdegreeRoute :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm
        (planeSourceShear K L Q)).coeff
        (b * 2)).natDegree = b * H := by
    rw [← hnEq]
    rw [bivariate_topCoeff_planeSourceShear L n Q hQ]
    simpa only [b] using hBdegree'
  have hgenerates := hendpoint
    (planeSourceShear K L P) (planeSourceShear K L Q)
    a b (H + 2 * L) 2 H
    (by simpa only [a] using hma)
    (by simpa only [b] using hnb) habcop
    (IsPlaneKellerPair.sourceShear hKeller L)
    hPdegreeRoute hQdegreeRoute hAdegreeRoute hBdegreeRoute
    hPtotal hQtotal hHlarge hendpointGCD
  exact (planePairGenerates_sourceShear_iff L P Q).mp hgenerates

/-- At a fixed gcd-two pair with reduced factors bigger than one, the
standard-endpoint theorem reduces the entire even-scale residue to the two
literal scales `0` and `2`. -/
theorem planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_zero_two
    {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hgcd : Nat.gcd m n = 2)
    (hma : 1 < m / 2) (hnb : 1 < n / 2)
    (hendpoint : PlaneKellerStandardEndpointGCDRoute (K := K))
    (hzero : PlaneKellerLeadingScaleAtDegrees (K := K) m n 0)
    (htwo : PlaneKellerLeadingScaleAtDegrees (K := K) m n 2) :
    PlaneKellerEvenLeadingScaleAtDegrees (K := K) m n := by
  intro P Q H hP hQ hKeller hAdegree hBdegree hHeven
  by_cases hH0 : H = 0
  · subst H
    exact hzero P Q hP hQ hKeller hAdegree hBdegree
  by_cases hH2 : H = 2
  · subst H
    exact htwo P Q hP hQ hKeller hAdegree hBdegree
  have hHlarge : 2 < H := by
    obtain ⟨t, ht⟩ := hHeven
    omega
  exact planeKellerLeadingScaleAtDegrees_of_gcd_two_of_two_lt_scale
    m n H hmpos hnpos hgcd hma hnb hHeven hHlarge hendpoint
    P Q hP hQ hKeller hAdegree hBdegree

/-- Bundled version of the exact `0`/`2` split. -/
theorem planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
    {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hgcd : Nat.gcd m n = 2)
    (hma : 1 < m / 2) (hnb : 1 < n / 2)
    (hendpoint : PlaneKellerStandardEndpointGCDRoute (K := K))
    (hlow : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) m n) :
    PlaneKellerEvenLeadingScaleAtDegrees (K := K) m n :=
  planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_zero_two
    m n hmpos hnpos hgcd hma hnb hendpoint hlow.1 hlow.2

/-- Source-facing bundled version whose classical premise is exactly the
numerical endpoint conclusion stated in the literature. -/
theorem planeKellerEvenLeadingScaleAtDegrees_of_standardEndpointObstruction_and_lowScales
    {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hgcd : Nat.gcd m n = 2)
    (hma : 1 < m / 2) (hnb : 1 < n / 2)
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (hlow : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) m n) :
    PlaneKellerEvenLeadingScaleAtDegrees (K := K) m n :=
  planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
    m n hmpos hnpos hgcd hma hnb
    (planeKellerStandardEndpointGCDRoute_of_obstruction hendpoint) hlow

#print axioms planeKellerStandardEndpointGCDRoute_of_obstruction
#print axioms planeKellerLeadingScaleAtDegrees_of_gcd_two_of_two_lt_scale
#print axioms planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_zero_two
#print axioms planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
#print axioms planeKellerEvenLeadingScaleAtDegrees_of_standardEndpointObstruction_and_lowScales

end Max11DegreeRoutes
