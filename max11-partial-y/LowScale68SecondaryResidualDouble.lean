import LowScale68SecondaryResidualExtraction

/-! # The `(6,8)` residual double face

This module extracts the four equations at residual gap `2g` from the
literal polynomial invariants and one-form rows.  The resulting tied face
specializes to either strict endpoint when one residual coefficient vanishes.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualDouble68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 4000000 in
/-- The two literal invariants and the last two literal one-form rows supply
the complete tied residual double face in `3g<n`. -/
theorem polynomialSecondaryResidualDoubleFace68
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowOne :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowOnePolynomial68
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D0 E0) C0 D0 E0 = 0)
    (hrowZero :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0) :
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowOnePolynomial68
    (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
    (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
      A B C0 D0 E0) C0 D0 E0 = 0 at hrowOne
  change (lowerRowZeroPolynomial68
    (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
      A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0 at hrowZero
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have hfour :
      -(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0 := by
    have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble
      l beta gamma delta epsilon zeta A B c d e n g hg hsmall
      hA hB hc hd he] at hz
    have hindex : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hthree :
      -(A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
    have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble
      l beta gamma delta epsilon zeta A B c d e n g hg hsmall
      hA hB hc hd he] at hz
    have hindex : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowOnePolynomial68_coeff_double A B c d e n g
      hg hsmall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_residualDouble
        l alpha beta gamma delta epsilon zeta eta A B c D0 e n g
        hg hsmall hA hB hc hD he), add_zero, coeff_zero] at hone
  have hone0 := (mul_eq_zero.mp hone).resolve_left (by norm_num)
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    coeff_add,
    show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
        secondaryResidualRowZeroPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowZeroPolynomial68_coeff_double A B c d e n g
      hg hsmall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_residualDouble
        l alpha beta gamma delta epsilon zeta eta A B c D0 e n g
        hg hsmall hA hB hc hD he), add_zero] at hrowZero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfactor : (8 / 27 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 := (mul_eq_zero.mp hrowZero).resolve_left hfactor
  exact ⟨hfour, by linear_combination hthree,
    by linear_combination hzero0, by linear_combination hone0⟩

/-- Vanishing of the constant residual coefficient specializes the tied
double face to the strict `D` endpoint. -/
theorem secondaryResidualDAtDoubleFace68_of_tied
    (N G a b c d e : k) (hb : b ≠ 0) (hc : c ≠ 0) (he : e = 0)
    (hface : SecondaryResidualTiedDoubleFace68 N G a b c d e) :
    SecondaryResidualDAtDoubleFace68 a b c d := by
  constructor
  · simpa only [he, mul_zero, add_zero] using hface.four
  · have h := hface.three
    rw [he] at h
    have hprod : -b * (a * d + b * c) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_left (neg_ne_zero.mpr hb)
  · have h := hface.zero
    rw [he] at h
    have hprod : c * (-a * d + b * c) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_left hc

/-- Vanishing of the translated `D` residual coefficient specializes the
tied face to the strict `E` endpoint. -/
theorem secondaryResidualEAtDoubleFace68_of_tied
    (N G a b c d e : k) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d = 0)
    (hface : SecondaryResidualTiedDoubleFace68 N G a b c d e) :
    SecondaryResidualEAtDoubleFace68 b c e := by
  constructor
  · have h := hface.four
    rw [hd] at h
    have hprod : b * (-b ^ 2 + 9 * e) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_left hb
  · have h := hface.three
    rw [hd] at h
    have hprod : c * (-b ^ 2 + 3 * e) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_left hc

set_option maxHeartbeats 5000000 in
/-- The canonical expanded lower system supplies the complete residual
double face whenever both residual directions have gap at least `2g`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDouble68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g < n)
    (hdouble :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ 5 * n - 2 * g ∧ ee.natDegree ≤ 6 * n - 2 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change 3 * g < n at hsmall
  change d.natDegree ≤ 5 * n - 2 * g ∧
    ee.natDegree ≤ 6 * n - 2 * g at hdouble
  change SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
    (ee.coeff (6 * n - 2 * g))
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have h := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using h
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have h := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using h
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowZeroPolynomial68_expand, hsys.rowZero, expand_C]
    norm_num
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 3 * g - 1) = 0 := by
    rw [h0e]
    apply coeff_eq_zero_of_natDegree_lt
    have hdegree :
        (C terminal * (60 * (X ^ 59 : k[X]))).natDegree ≤ 59 := by
      compute_degree
    have hnlarge : 5 ≤ n := by
      dsimp only [n, weightedRadius68] at hn ⊢
      omega
    exact hdegree.trans_lt (by omega)
  have h1cubic := h1e
  rw [hCrec, hDrec, hErec] at h1cubic
  have h0cubic := h0target
  rw [hCrec, hDrec, hErec] at h0cubic
  exact polynomialSecondaryResidualDoubleFace68
    l alpha beta gamma delta epsilon zeta eta i4 i3 Ae Be ce d ee n g
    hg hsmall hA hB hc hdouble.1 hdouble.2 ha hi4c hi3c h1cubic h0cubic

/-- Every residual double face is impossible in `3g<n`: vanishing of either
endpoint coefficient gives a strict endpoint, while two nonzero coefficients
give the tied endpoint. -/
theorem secondaryResidualDoubleFace68_impossible
    (n g : ℕ) (a b c d e : k)
    (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0) (hsmall : 3 * g < n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hb : b ≠ 0 := by
    rcases hsupport with hb | hc
    · exact hb
    · intro hb0
      have hd0 : d = 0 := by
        have h := hface.four
        rw [hb0] at h
        have hcd : c * d = 0 := by linear_combination (1 / 9 : k) * h
        exact (mul_eq_zero.mp hcd).resolve_left hc
      have he0 : e = 0 := by
        have h := hface.three
        rw [hb0] at h
        have hce : c * e = 0 := by linear_combination (1 / 3 : k) * h
        exact (mul_eq_zero.mp hce).resolve_left hc
      have hone := hface.one
      rw [hb0, hd0, he0] at hone
      have hcoeff : (3 * (g : k) - 12 * (n : k)) ≠ 0 := by
        intro hz
        have hcast : (3 * g : k) = (12 * n : ℕ) := by
          push_cast
          linear_combination hz
        have hnat : 3 * g = 12 * n := by exact_mod_cast hcast
        omega
      have hc3 : c ^ 3 = 0 := by
        have hprod : (3 * (g : k) - 12 * (n : k)) * c ^ 3 = 0 := by
          linear_combination hone
        exact (mul_eq_zero.mp hprod).resolve_left hcoeff
      exact (pow_ne_zero 3 hc) hc3
  have hc : c ≠ 0 := by
    rcases hsupport with hb' | hc
    · intro hc0
      have hd0 : d = 0 := by
        have h := hface.three
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habd : a * b * d = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habd).resolve_left hab
      have he0 : e = 0 := by
        have h := hface.zero
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habe : a * b * e = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habe).resolve_left hab
      have h := hface.four
      rw [hc0, hd0, he0] at h
      have hb3 : b ^ 3 = 0 := by linear_combination -h
      exact (pow_ne_zero 3 hb') hb3
    · exact hc
  by_cases hd : d = 0
  · exact secondaryResidualEAtDoubleFace68_impossible b c e hb hc
      (secondaryResidualEAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc hd hface)
  by_cases he : e = 0
  · exact secondaryResidualDAtDoubleFace68_impossible a b c d hb hc
      (secondaryResidualDAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc he hface)
  exact secondaryResidualTiedDoubleFace68_impossible_of_three_mul_gap_lt_radius
    n g a b c d e ha hb hc hsmall hface

end SecondaryResidualDouble68

#print axioms polynomialSecondaryResidualDoubleFace68
#print axioms secondaryResidualDAtDoubleFace68_of_tied
#print axioms secondaryResidualEAtDoubleFace68_of_tied
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDouble68
#print axioms secondaryResidualDoubleFace68_impossible

end Max11DegreeRoutes
