import LowScale68SecondaryLaterDeepThreeRadiusDoubleRowOne

/-! # Row-zero closure of the exact residual double wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusDoubleRowZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 4000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_double_of_threeRadius
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g)) -
          A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow3 : (derivative A * d * e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  push_cast
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroPolynomial68_degree_lt_double_of_threeRadius_beta
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 3 * g - 1 := by
  rw [cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta']
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hgt : n < g := by omega
  have hgle : g ≤ 2 * n := by omega
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
      hA hB hc hD he'
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 13 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 13 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (13 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative E).natDegree < 13 * n - 3 * g - 1 :=
    hbound (2 * n) (6 * n) (by omega) (by omega) Ur E hUr hE
  have h2 : (Uc * derivative Er).natDegree < 13 * n - 3 * g - 1 :=
    hbound (5 * n - g) (6 * n - g) (by omega) (by omega) Uc Er hUc hEr
  have h3 : (D * derivative Vr).natDegree < 13 * n - 3 * g - 1 :=
    hbound (5 * n - g) (6 * n - g) (by omega) (by omega) D Vr hD hVr
  change (Ur * derivative E + Uc * derivative Er -
      D * derivative Vr).natDegree < _
  exact deepGap_natDegree_sub_lt (deepGap_natDegree_add_lt h1 h2) h3

def ThreeRadiusResidualDoubleRowZeroScalar68
    (a b c d e : k) : k :=
  -a * b * e - a * c * d + b * c ^ 2

theorem threeRadiusResidualDouble_scalarSystem_impossible68
    (a b c d e : k) (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0)
    (hface : ThreeRadiusResidualDoubleInvariantFace68 a b c d e)
    (hrowOne : ThreeRadiusResidualDoubleRowOneScalar68 a b c d e = 0)
    (hrowZero : ThreeRadiusResidualDoubleRowZeroScalar68 a b c d e = 0) : False := by
  simp only [ThreeRadiusResidualDoubleRowOneScalar68] at hrowOne
  simp only [ThreeRadiusResidualDoubleRowZeroScalar68] at hrowZero
  have hc5 : c ^ 5 = 0 := by
    linear_combination
      (1 / 12 * a ^ 2 * b * c + 1 / 12 * a ^ 3 * d) * hface.four +
      (-1 / 12 * a ^ 2 * b ^ 2 + 59 / 60 * a * c ^ 2 -
        11 / 20 * a ^ 2 * e) * hface.three +
      (-1 / 15 * c ^ 2 + 1 / 20 * a * e) * hrowOne +
      (5 / 4 * a * b * c + 3 / 4 * a ^ 2 * d) * hrowZero
  have hc : c = 0 := eq_zero_of_pow_eq_zero hc5
  have hbd : b * d = 0 := by
    have hf := hface.three
    rw [hc] at hf
    have habd : a * (b * d) = 0 := by
      linear_combination -hf
    exact (mul_eq_zero.mp habd).resolve_left ha
  have hbe : b * e = 0 := by
    have hz := hrowZero
    rw [hc] at hz
    have habe : a * (b * e) = 0 := by
      linear_combination -hz
    exact (mul_eq_zero.mp habe).resolve_left ha
  have hb3 : b ^ 3 = 0 := by
    have hf := hface.four
    rw [hc] at hf
    linear_combination -hf + 9 * hbe
  have hb : b = 0 := eq_zero_of_pow_eq_zero hb3
  exact hsupport.elim (fun hbne => hbne hb) (fun hcne => hcne hc)

set_option maxHeartbeats 12000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusDouble_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g = 3 * n)
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
      let h := secondaryResidualGap68 n d ee
      2 * g ≤ h) : False := by
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
  let h := secondaryResidualGap68 n d ee
  change 2 * g = 3 * n at hwall
  change 2 * g ≤ h at hdouble
  have packet :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusDoubleRowOnePacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
  change h = 2 * g ∧
      (d.coeff (5 * n - 2 * g) ≠ 0 ∨ ee.coeff (6 * n - 2 * g) ≠ 0) ∧
      ThreeRadiusResidualDoubleInvariantFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) ∧
      ThreeRadiusResidualDoubleRowOneScalar68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) = 0 at packet
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusNonzeroResidualSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧ _
    at selector
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have hg : 0 < g := secondary.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := secondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := secondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - 2 * g := by
    simpa only [packet.1] using selector.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - 2 * g := by
    simpa only [packet.1] using selector.2.2.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  have hD : Dtr.natDegree ≤ 5 * n - g := by
    simp only [Dtr]
    compute_degree
    omega
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have hidx : 59 < 13 * n - 3 * g - 1 := by omega
  rw [hCrec, hDrec, hErec, selector.1, selector.2.1] at h0e
  have hcoeff := expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
    terminal
    (integratedUPolynomial68 0 alpha 0 gamma delta zeta Ae Be
      ((1 / 3 : k) • Ae ^ 2 + ce) Dtr
      ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
    (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta Ae Be
      ((1 / 3 : k) • Ae ^ 2 + ce) Dtr
      ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
    Dtr ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee)
    (13 * n - 3 * g - 1) h0e hidx
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha 0 gamma delta epsilon zeta eta Ae Be ce Dtr ee
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add,
    show cubicHomogeneousRowZeroPolynomial68 Ae Be ce Dtr ee =
        secondaryResidualRowZeroPolynomial68 Ae Be ce d ee by
      simpa only [Dtr] using
        cubicHomogeneousRowZeroPolynomial68_residualCoordinates Ae Be ce d ee,
    secondaryResidualRowZeroPolynomial68_coeff_double_of_threeRadius
      Ae Be ce d ee n g hn hg hwall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_double_of_threeRadius_beta
        alpha gamma delta epsilon zeta eta Ae Be ce Dtr ee n g
        hn hg hwall hA hB hc hD he), add_zero] at hcoeff
  have hfactor : (8 / 27 : k) * (n : k) * Ae.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))) ha
  have hrowZeroRaw := (mul_eq_zero.mp hcoeff).resolve_left hfactor
  have hrowZero : ThreeRadiusResidualDoubleRowZeroScalar68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) = 0 := by
    dsimp only [ThreeRadiusResidualDoubleRowZeroScalar68]
    linear_combination hrowZeroRaw
  exact threeRadiusResidualDouble_scalarSystem_impossible68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
    (ee.coeff (6 * n - 2 * g)) ha selector.2.2.2.2.2.1
    packet.2.2.1 packet.2.2.2 hrowZero

#print axioms secondaryResidualRowZeroPolynomial68_coeff_double_of_threeRadius
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_double_of_threeRadius_beta
#print axioms threeRadiusResidualDouble_scalarSystem_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusDouble_impossible68

end LaterDeepThreeRadiusDoubleRowZero68

end Max11DegreeRoutes
