import HistoryDegree
import TotalDegreeRoutes

/-! # Coprime partial degrees from the prime total-degree theorem

The top-coefficient row of the Keller equation forces the two leading
`x`-degrees to have the same ratio as the two positive partial `y`-degrees.
For coprime partial degrees this gives a common integral scale.  A sufficiently
large triangular source shear then makes the total-degree gcd prime, reducing
the pair to `PlaneKellerPrimeTotalDegreeGCDRoute`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- The weighted Wronskian relation already forces proportional numerical
degrees; no extraction of a common polynomial core is needed. -/
theorem natDegree_proportional_of_weightedWronskian {K : Type*}
    [Field K] [CharZero K] {a b : K[X]} {m n : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hmpos : 0 < m) (hnpos : 0 < n)
    (hweighted :
      Polynomial.C (n : K) * b * a.derivative =
        Polynomial.C (m : K) * a * b.derivative) :
    n * a.natDegree = m * b.natDegree := by
  have hampow : a ^ n = a ^ (n - 1) * a := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hnpos, pow_succ]
    rw [Nat.pred_eq_sub_one]
  have hbmpow : b ^ m = b ^ (m - 1) * b := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hmpos, pow_succ]
    rw [Nat.pred_eq_sub_one]
  have hW : Polynomial.wronskian (a ^ n) (b ^ m) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow, hampow, hbmpow]
    calc
      (a ^ (n - 1) * a) *
            (Polynomial.C (m : K) * b ^ (m - 1) * b.derivative) -
          (Polynomial.C (n : K) * a ^ (n - 1) * a.derivative) *
            (b ^ (m - 1) * b) =
          a ^ (n - 1) * b ^ (m - 1) *
            (Polynomial.C (m : K) * a * b.derivative -
              Polynomial.C (n : K) * b * a.derivative) := by ring
      _ = 0 := by rw [hweighted, sub_self, mul_zero]
  obtain ⟨c, hpowers⟩ :=
    eq_C_mul_of_wronskian_eq_zero (pow_ne_zero m hb) hW
  have hc : c ≠ 0 := by
    intro hczero
    apply pow_ne_zero n ha
    rw [hpowers, hczero, Polynomial.C_0, zero_mul]
  calc
    n * a.natDegree = (a ^ n).natDegree :=
      (Polynomial.natDegree_pow a n).symm
    _ = (Polynomial.C c * b ^ m).natDegree := by rw [hpowers]
    _ = (b ^ m).natDegree := Polynomial.natDegree_C_mul hc
    _ = m * b.natDegree := Polynomial.natDegree_pow b m

/-- Numerical proportionality for the top `y`-coefficients of any positive-
degree plane Keller pair. -/
theorem planeKellerLeadingCoefficient_natDegrees_proportional
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {m n : ℕ}
    (hP : degreeOf 1 P = m) (hQ : degreeOf 1 Q = n)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hKeller : IsPlaneKellerPair P Q) :
    n * (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m).natDegree =
      m * (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff n).natDegree := by
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
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
  have hptop : p.coeff m ≠ 0 := by
    rw [← hpdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hqtop : q.coeff n ≠ 0 := by
    rw [← hqdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact natDegree_proportional_of_weightedWronskian hptop hqtop hmpos hnpos
    (leadingCoefficient_weightedWronskian hpdegree hqdegree hmpos hnpos hjac)

/-- Coprime positive factors in an equality `n*u = m*v` leave a common
integral scale. -/
theorem exists_commonScale_of_coprime_mul_eq_mul
    {m n u v : ℕ} (hcop : m.Coprime n)
    (hmpos : 0 < m) (hnpos : 0 < n) (h : n * u = m * v) :
    ∃ H, u = m * H ∧ v = n * H := by
  have hmdiv : m ∣ u :=
    hcop.dvd_of_dvd_mul_left ⟨v, h⟩
  have hndiv : n ∣ v :=
    hcop.symm.dvd_of_dvd_mul_left ⟨u, h.symm⟩
  obtain ⟨H, hu⟩ := hmdiv
  obtain ⟨G, hv⟩ := hndiv
  have hHG : H = G := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hmpos hnpos)
    simpa [hu, hv, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  subst G
  exact ⟨H, hu, hv⟩

/-- There is an arbitrarily large shift making `H + L` prime. -/
theorem exists_large_prime_eq_add (H B : ℕ) :
    ∃ L, B < L ∧ (H + L).Prime := by
  obtain ⟨p, hpbound, hpprime⟩ := Nat.exists_infinite_primes (H + B + 1)
  refine ⟨p - H, ?_, ?_⟩
  · omega
  · have hHle : H ≤ p := by omega
    rwa [Nat.add_sub_of_le hHle]

/-- Every positive coprime partial-degree pair follows from the classical
prime-total-degree-gcd theorem via a checked large source shear. -/
theorem planeKellerAutomorphicAtDegrees_of_coprime_and_primeTotalDegreeGCD
    {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hcop : m.Coprime n)
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    PlaneKellerAutomorphicAtDegrees (K := K) m n := by
  intro P Q hP hQ hKeller
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  let A := p.coeff m
  let B := q.coeff n
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
  have hproportional : n * A.natDegree = m * B.natDegree := by
    simpa only [A, B, p, q] using
      planeKellerLeadingCoefficient_natDegrees_proportional
        hP hQ hmpos hnpos hKeller
  obtain ⟨H, hAdegree, hBdegree⟩ :=
    exists_commonScale_of_coprime_mul_eq_mul hcop hmpos hnpos hproportional
  obtain ⟨L, hlarge, hscalePrime⟩ :=
    exists_large_prime_eq_add H (max P.totalDegree Q.totalDegree)
  have hPlarge : P.totalDegree < L :=
    (Nat.le_max_left P.totalDegree Q.totalDegree).trans_lt hlarge
  have hQlarge : Q.totalDegree < L :=
    (Nat.le_max_right P.totalDegree Q.totalDegree).trans_lt hlarge
  have hPexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    P A m A.natDegree L hmpos hP rfl hA rfl hPlarge
  have hQexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    Q B n B.natDegree L hnpos hQ rfl hB rfl hQlarge
  have hPtotal : (planeSourceShear K L P).totalDegree = m * (H + L) := by
    rw [planeSourceShear_apply, hPexact, hAdegree]
    ring
  have hQtotal : (planeSourceShear K L Q).totalDegree = n * (H + L) := by
    rw [planeSourceShear_apply, hQexact, hBdegree]
    ring
  have hgcd : Nat.gcd (planeSourceShear K L P).totalDegree
      (planeSourceShear K L Q).totalDegree = H + L := by
    rw [hPtotal, hQtotal, Nat.gcd_mul_right]
    simpa only [Nat.Coprime, one_mul] using
      congrArg (fun t => t * (H + L)) hcop
  have hgenerates := hprime (planeSourceShear K L P)
    (planeSourceShear K L Q) (IsPlaneKellerPair.sourceShear hKeller L)
    (by rwa [hgcd])
  exact (planePairGenerates_sourceShear_iff L P Q).mp hgenerates

/-- For partial-degree gcd two, the same proportionality has reduced
coprime factors `m/2` and `n/2`. -/
theorem exists_commonScale_of_gcd_eq_two_mul_eq_mul
    {m n u v : ℕ} (hmpos : 0 < m) (hnpos : 0 < n)
    (hgcd : Nat.gcd m n = 2) (h : n * u = m * v) :
    ∃ H, u = (m / 2) * H ∧ v = (n / 2) * H := by
  have h2m : 2 ∣ m := hgcd ▸ Nat.gcd_dvd_left m n
  have h2n : 2 ∣ n := hgcd ▸ Nat.gcd_dvd_right m n
  have hmfac : m / 2 * 2 = m := Nat.div_mul_cancel h2m
  have hnfac : n / 2 * 2 = n := Nat.div_mul_cancel h2n
  have hscaled : (n / 2) * u = (m / 2) * v := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    calc
      2 * ((n / 2) * u) = (n / 2 * 2) * u := by ring
      _ = n * u := by rw [hnfac]
      _ = m * v := h
      _ = (m / 2 * 2) * v := by rw [hmfac]
      _ = 2 * ((m / 2) * v) := by ring
  have hgcdpos : 0 < Nat.gcd m n := by rw [hgcd]; norm_num
  have hcop : (m / 2).Coprime (n / 2) := by
    simpa only [hgcd] using Nat.coprime_div_gcd_div_gcd hgcdpos
  have hmhalfpos : 0 < m / 2 := by omega
  have hnhalfpos : 0 < n / 2 := by omega
  exact exists_commonScale_of_coprime_mul_eq_mul hcop hmhalfpos hnhalfpos hscaled

/-- The exact unresolved subcase after the source-shear reduction at
partial-degree gcd two: the common leading-degree scale is even. -/
def PlaneKellerEvenLeadingScaleGCDTwoRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (m n H : ℕ),
    degreeOf 1 P = m → degreeOf 1 Q = n →
    0 < m → 0 < n → Nat.gcd m n = 2 →
    IsPlaneKellerPair P Q →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m).natDegree =
      (m / 2) * H →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff n).natDegree =
      (n / 2) * H →
    2 ∣ H → PlanePairGenerates P Q

/-- The same even-scale residue localized to one fixed partial-degree pair. -/
def PlaneKellerEvenLeadingScaleAtDegrees
    {K : Type*} [Field K] (m n : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H : ℕ),
    degreeOf 1 P = m → degreeOf 1 Q = n →
    IsPlaneKellerPair P Q →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m).natDegree =
      (m / 2) * H →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff n).natDegree =
      (n / 2) * H →
    2 ∣ H → PlanePairGenerates P Q

/-- Dirichlet supplies an arbitrarily large shear exponent making `H+2L`
prime whenever the common leading-degree scale `H` is odd. -/
theorem exists_large_prime_eq_add_two_mul (H B : ℕ)
    (hodd : ¬ 2 ∣ H) :
    ∃ L, B < L ∧ (H + 2 * L).Prime := by
  have hcop : H.Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm
  obtain ⟨p, hpbound, hpprime, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (H + 2 * B)
      (q := 2) (a := H) (by norm_num) hcop
  have hHp : H ≤ p := by omega
  obtain ⟨L, hpEq⟩ :=
    (Nat.modEq_iff_exists_eq_add hHp).mp hpmod.symm
  refine ⟨L, ?_, ?_⟩
  · omega
  · rwa [← hpEq]

/-- At one positive partial-degree gcd-two pair, the prime theorem discharges
every odd common-scale source.  Only its localized even-scale interface
remains. -/
theorem planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScaleAtDegrees
    {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hgcd : Nat.gcd m n = 2)
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (heven : PlaneKellerEvenLeadingScaleAtDegrees (K := K) m n) :
    PlaneKellerAutomorphicAtDegrees (K := K) m n := by
  intro P Q hP hQ hKeller
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
  have hproportional : n * A.natDegree = m * B.natDegree := by
    simpa only [A, B, p, q] using
      planeKellerLeadingCoefficient_natDegrees_proportional
        hP hQ hmpos hnpos hKeller
  obtain ⟨H, hAdegree', hBdegree'⟩ :=
    exists_commonScale_of_gcd_eq_two_mul_eq_mul hmpos hnpos hgcd hproportional
  have hAdegree : A.natDegree = a * H := by simpa only [a] using hAdegree'
  have hBdegree : B.natDegree = b * H := by simpa only [b] using hBdegree'
  by_cases hHeven : 2 ∣ H
  · exact heven P Q H hP hQ hKeller
      (by simpa only [a] using hAdegree)
      (by simpa only [b] using hBdegree) hHeven
  · obtain ⟨L, hlarge, hscalePrime⟩ :=
      exists_large_prime_eq_add_two_mul H (max P.totalDegree Q.totalDegree) hHeven
    have hPlarge : P.totalDegree < L :=
      (Nat.le_max_left P.totalDegree Q.totalDegree).trans_lt hlarge
    have hQlarge : Q.totalDegree < L :=
      (Nat.le_max_right P.totalDegree Q.totalDegree).trans_lt hlarge
    have h2m : 2 ∣ m := hgcd ▸ Nat.gcd_dvd_left m n
    have h2n : 2 ∣ n := hgcd ▸ Nat.gcd_dvd_right m n
    have hmEq : m = 2 * a := by
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel h2m).symm
    have hnEq : n = 2 * b := by
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel h2n).symm
    have hgcdpos : 0 < Nat.gcd m n := by rw [hgcd]; norm_num
    have habcop : a.Coprime b := by
      simpa only [a, b, hgcd] using Nat.coprime_div_gcd_div_gcd hgcdpos
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
    have hgcdTotal : Nat.gcd (planeSourceShear K L P).totalDegree
        (planeSourceShear K L Q).totalDegree = H + 2 * L := by
      rw [hPtotal, hQtotal, Nat.gcd_mul_right]
      simpa only [Nat.Coprime, one_mul] using
        congrArg (fun t => t * (H + 2 * L)) habcop
    have hgenerates := hprime (planeSourceShear K L P)
      (planeSourceShear K L Q) (IsPlaneKellerPair.sourceShear hKeller L)
      (by rwa [hgcdTotal])
    exact (planePairGenerates_sourceShear_iff L P Q).mp hgenerates

/-- Uniform form of the preceding localized gcd-two reduction. -/
theorem planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScale
    {K : Type*} [Field K] [CharZero K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (heven : PlaneKellerEvenLeadingScaleGCDTwoRoute (K := K)) :
    ∀ m n, Nat.gcd m n = 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n := by
  intro m n hgcd
  by_cases hmzero : m = 0
  · subst m
    exact Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero n
  by_cases hnzero : n = 0
  · subst n
    exact (Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero m).swap
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
  have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
  apply planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScaleAtDegrees
    m n hmpos hnpos hgcd hprime
  intro P Q H hP hQ hKeller hAdegree hBdegree hHeven
  exact heven P Q m n H hP hQ hmpos hnpos hgcd hKeller
    hAdegree hBdegree hHeven

/-- The strong arbitrary-pair twice-prime total-degree interface closes the
remaining even-scale gcd-two case by factoring `H = 2H'` and choosing
`H' + L` prime.  This is an adapter, not a proof that the strong interface is
available in the literature. -/
theorem planeKellerEvenLeadingScaleGCDTwoRoute_of_twicePrimeTotalDegreeGCD
    {K : Type*} [Field K] [CharZero K]
    (htwice : PlaneKellerTwicePrimeTotalDegreeGCDRoute (K := K)) :
    PlaneKellerEvenLeadingScaleGCDTwoRoute (K := K) := by
  intro P Q m n H hP hQ hmpos hnpos hgcd hKeller hAdegree' hBdegree' hHeven
  obtain ⟨H', hHEq⟩ := hHeven
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
  have hAdegree : A.natDegree = a * H := by
    simpa only [A, p, a] using hAdegree'
  have hBdegree : B.natDegree = b * H := by
    simpa only [B, q, b] using hBdegree'
  obtain ⟨L, hlarge, hscalePrime⟩ :=
    exists_large_prime_eq_add H' (max P.totalDegree Q.totalDegree)
  have hPlarge : P.totalDegree < L :=
    (Nat.le_max_left P.totalDegree Q.totalDegree).trans_lt hlarge
  have hQlarge : Q.totalDegree < L :=
    (Nat.le_max_right P.totalDegree Q.totalDegree).trans_lt hlarge
  have h2m : 2 ∣ m := hgcd ▸ Nat.gcd_dvd_left m n
  have h2n : 2 ∣ n := hgcd ▸ Nat.gcd_dvd_right m n
  have hmEq : m = 2 * a := by
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel h2m).symm
  have hnEq : n = 2 * b := by
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel h2n).symm
  have hPexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    P A m A.natDegree L hmpos hP rfl hA rfl hPlarge
  have hQexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    Q B n B.natDegree L hnpos hQ rfl hB rfl hQlarge
  have hPtotal : (planeSourceShear K L P).totalDegree =
      m * (H' + L) := by
    rw [planeSourceShear_apply, hPexact, hAdegree, hHEq, hmEq]
    ring
  have hQtotal : (planeSourceShear K L Q).totalDegree =
      n * (H' + L) := by
    rw [planeSourceShear_apply, hQexact, hBdegree, hHEq, hnEq]
    ring
  have hgcdTotal : Nat.gcd (planeSourceShear K L P).totalDegree
      (planeSourceShear K L Q).totalDegree = 2 * (H' + L) := by
    rw [hPtotal, hQtotal, Nat.gcd_mul_right, hgcd]
  have hgenerates := htwice (planeSourceShear K L P)
    (planeSourceShear K L Q) (H' + L)
    (IsPlaneKellerPair.sourceShear hKeller L) hscalePrime hgcdTotal
  exact (planePairGenerates_sourceShear_iff L P Q).mp hgenerates

/-- The classical gcd-at-most-two hypothesis can therefore be narrowed to
the exact gcd-two residue: zero degrees are elementary and gcd one is the
coprime source-shear theorem above. -/
theorem planeKellerAutomorphicAtDegrees_of_gcd_le_two
    {K : Type*} [Field K] [CharZero K]
    (hresidual : ∀ m n, Nat.gcd m n = 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n := by
  intro m n hgcdle
  by_cases hmzero : m = 0
  · subst m
    exact Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero n
  by_cases hnzero : n = 0
  · subst n
    exact (Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero m).swap
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
  have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
  by_cases hgcdone : Nat.gcd m n = 1
  · exact planeKellerAutomorphicAtDegrees_of_coprime_and_primeTotalDegreeGCD
      m n hmpos hnpos (Nat.coprime_iff_gcd_eq_one.mpr hgcdone) hprime
  · have hgcdpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hmpos
    have hgcdtwo : Nat.gcd m n = 2 := by omega
    exact hresidual m n hgcdtwo

end Max11DegreeRoutes
