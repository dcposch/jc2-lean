import Sol68LaterDeepLowerOpenDoubleBelowFiveEndgameScratch

/-! # The residual double packet on `3g = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallSelector68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

structure LaterDeepLowerOpenDoubleFiveWallScalarPacket68
    (N a b c d e delta : k) : Prop where
  four : (8 / 27 : k) * (-b ^ 3 + 9 * b * e + 9 * c * d) +
    (1 / 4 : k) * delta * a ^ 2 = 0
  three : -a * b * d - b ^ 2 * c + 3 * c * e = 0
  rowOne : -5 * a ^ 2 * b * d + 2 * a * b ^ 2 * c +
    15 * a * c * e - 7 * c ^ 3 = 0
  rowZero : (8 / 27 : k) * N * a *
      (-a * b * e - a * c * d + b * c ^ 2) +
    (1 / 9 : k) * N * delta * a ^ 4 = 0

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaLowPolynomial68_degree_le_fourRadius_of_doubleFiveWall
    (gamma delta epsilon eta : k) (A B c D : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadVAlphaLowPolynomial68 0 gamma delta epsilon eta
      A B c D).natDegree ≤ 4 * n - g := by
  simp only [cubicLoadVAlphaLowPolynomial68, zero_mul, mul_zero, zero_smul,
    smul_zero, add_zero, zero_add]
  compute_degree
  omega

set_option maxHeartbeats 9000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_double_of_laterDeepLowerOpen_fiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest 0 alpha 0 gamma delta
      epsilon zeta eta A B c D e rfl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Vlow := cubicLoadVAlphaLowPolynomial68 0 gamma delta epsilon eta
    A B c D
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hgt : n < g := by omega
  have hgle : g ≤ 2 * n := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
      hA hB hc hD he
  have hVlow : Vlow.natDegree ≤ 4 * n - g :=
    cubicLoadVAlphaLowPolynomial68_degree_le_fourRadius_of_doubleFiveWall
      gamma delta epsilon eta A B c D n g hn hwall hA hB hc
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
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
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 3 * g - 1 :=
    hbound (2 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (2 * n) (6 * n - g) (by omega) (by omega)
      ((2 / 3 * gamma : k) • A) Er ((natDegree_smul_le _ A).trans hA) hEr
  have h4 : ((C epsilon : k[X]) * derivative E).natDegree <
      12 * n - 3 * g - 1 :=
    hbound 0 (6 * n) (by omega) (by omega) _ E heps hE
  have h5 : (C0c * derivative Vlow).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n) (4 * n - g) (by omega) (by omega)
      C0c Vlow hC0c hVlow
  have h6 : (c * derivative Vr).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega) c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 3 * g - 1 :=
    hbound (5 * n - g) (2 * n) (by omega) (by omega) D Ur hD hUr
  simp only [cubicLoadRowOneDeepGapRestPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  change (Ur * derivative D +
      (2 : k) • ((alpha • c) * derivative Er) +
      (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
      (2 : k) • ((C epsilon : k[X]) * derivative E) -
      (2 : k) • (C0c * derivative Vlow) -
      (2 : k) • (c * derivative Vr) -
      D * derivative Ur).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1
              (deepGap_natDegree_smul_lt68 (2 : k) h2))
              (deepGap_natDegree_smul_lt68 (2 : k) h3))
            (deepGap_natDegree_smul_lt68 (2 : k) h4))
          (deepGap_natDegree_smul_lt68 (2 : k) h5))
        (deepGap_natDegree_smul_lt68 (2 : k) h6)) h7

theorem polynomialLaterDeepLowerOpenDoubleFiveWallInvariantFace68
    (gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (8 / 27 : k) *
          (-(B.coeff (3 * n - g) ^ 3) +
            9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
            9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) +
        (1 / 4 : k) * delta * A.coeff (2 * n) ^ 2 = 0 ∧
      -(A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (4 * n)) hi4
    have hres :=
      secondaryResidualInvariantFourPolynomial68_coeff_double_of_laterDeepLowerOpen
        B c d e n g hn hg hopen hB hc hd he
    have htarget : 9 * n - 3 * g = 4 * n := by omega
    rw [htarget] at hres
    have hload :=
      secondaryLoadInvariantFourPolynomial68_coeff_fourRadius_of_laterDeepLowerOpen
        gamma delta epsilon zeta A B c d e n g (2 * g) hn hopen
        (by omega) hA hB hc hd he
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralFourPolynomial68_residualCoordinates,
      hres, hload] at hz
    have hi : 4 * n ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    exact hz
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralThreePolynomial68_residualCoordinates,
      secondaryResidualInvariantThreePolynomial68_coeff_double_of_laterDeepLowerOpen
        A B c d e n g hn hg hopen hA hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_laterDeepLowerOpen
          gamma delta epsilon zeta A B c ((1 / 3 : k) • (A * B) + d) e
          n g hn hg hopen hA hB hc (by compute_degree; omega) he),
      add_zero] at hz
    have hi : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hz'

theorem laterDeepLowerOpenDoubleFiveWall_strictOvershoot_inconsistent68
    (N a b c delta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hsupport : b ≠ 0 ∨ c ≠ 0)
    (hfour : (8 / 27 : k) * (-b ^ 3) + (1 / 4 : k) * delta * a ^ 2 = 0)
    (hthree : -(b ^ 2 * c) = 0)
    (hrowOne : 2 * a * b ^ 2 * c - 7 * c ^ 3 = 0)
    (hrowZero : (8 / 27 : k) * N * a * (b * c ^ 2) +
      (1 / 9 : k) * N * delta * a ^ 4 = 0) : False := by
  have hc : c = 0 := by
    by_contra hc0
    have hb2 : b ^ 2 = 0 := by
      have hp : b ^ 2 * c = 0 := by linear_combination -hthree
      exact (mul_eq_zero.mp hp).resolve_right hc0
    have hb : b = 0 := eq_zero_of_pow_eq_zero hb2
    simp only [hb, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
      mul_zero, zero_add] at hrowOne
    have hc3 : c ^ 3 = 0 := by
      have hp : (-7 : k) * c ^ 3 = 0 := by linear_combination hrowOne
      exact (mul_eq_zero.mp hp).resolve_left (by norm_num)
    exact hc0 (eq_zero_of_pow_eq_zero hc3)
  have hb : b ≠ 0 := by
    rcases hsupport with hb | hcne
    · exact hb
    · exact False.elim (hcne hc)
  have hdelta : delta = 0 := by
    simp only [hc, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
      zero_mul, zero_add] at hrowZero
    have hfactor : (1 / 9 : k) * N * a ^ 4 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hN) (pow_ne_zero 4 ha)
    exact (mul_eq_zero.mp (by
      have : ((1 / 9 : k) * N * a ^ 4) * delta = 0 := by
        linear_combination hrowZero
      exact this)).resolve_left hfactor
  simp only [hdelta, zero_mul, mul_zero, add_zero] at hfour
  have hb3 : b ^ 3 = 0 := by
    have hp : (8 / 27 : k) * (-b ^ 3) = 0 := by exact hfour
    have := (mul_eq_zero.mp hp).resolve_left (by norm_num)
    linear_combination -this
  exact hb (eq_zero_of_pow_eq_zero hb3)

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
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
      2 * g ≤ h)
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
      3 * g = 5 * n) :
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
    h = 2 * g ∧
      (d.coeff (5 * n - 2 * g) ≠ 0 ∨ ee.coeff (6 * n - 2 * g) ≠ 0) ∧
      LaterDeepLowerOpenDoubleFiveWallScalarPacket68
        (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) delta := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change h = 2 * g ∧
      (d.coeff (5 * n - 2 * g) ≠ 0 ∨ ee.coeff (6 * n - 2 * g) ≠ 0) ∧
      LaterDeepLowerOpenDoubleFiveWallScalarPacket68
        (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) delta
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
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
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := bounds.1.trans (by omega)
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := bounds.2.trans (by omega)
  have support : Be.coeff (3 * n - g) ≠ 0 ∨
      ce.coeff (4 * n - g) ≠ 0 := by
    rcases secondary.2.2.2.2.2 with hb | hc | hD | he
    · exact Or.inl hb
    · exact Or.inr hc
    · left
      intro hb0
      have hab : Ae.coeff (2 * n) * Be.coeff (3 * n - g) = 0 := by
        rw [hb0, mul_zero]
      rw [drops.2.2.2.1] at hab
      exact hD ((mul_eq_zero.mp hab).resolve_left (by norm_num))
    · exact False.elim (he drops.2.2.1)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hD : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1] at hi4e
    exact hi4e
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1] at hi3e
    exact hi3e
  have hface := polynomialLaterDeepLowerOpenDoubleFiveWallInvariantFace68
    gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g hn hg hopen hwall
    hA secondary.2.1 secondary.2.2.1 hd2 he2 hi4c hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  rw [hCrec, hDrec, hErec] at h1e
  have hrowOnePoly := polynomialSecondaryResidualRowOne68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h1e
  rw [drops.1, drops.2.1] at hrowOnePoly
  have hloadOne :=
    cubicLoadRowOnePolynomial68_degree_lt_double_of_laterDeepLowerOpen_fiveWall
      alpha gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg hopen hwall
      hA secondary.2.1 secondary.2.2.1 hD (he2.trans (by omega))
  have hcoeffOne := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOnePoly
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hloadOne, add_zero,
    secondaryResidualRowOnePolynomial68_coeff_double_of_laterDeepLowerOpen
      Ae Be ce d ee n g hn hg hopen hA secondary.2.1 secondary.2.2.1
      hd2 he2] at hcoeffOne
  have hrowOne : -5 * Ae.coeff (2 * n) ^ 2 * Be.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) +
      2 * Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 *
        ce.coeff (4 * n - g) +
      15 * Ae.coeff (2 * n) * ce.coeff (4 * n - g) *
        ee.coeff (6 * n - 2 * g) -
      7 * ce.coeff (4 * n - g) ^ 3 = 0 := by
    have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hraw := (mul_eq_zero.mp hcoeffOne).resolve_left (by norm_num)
    have hcast : (3 : k) * (g : k) = 5 * (n : k) := by exact_mod_cast hwall
    have hfac : (n : k) *
        (-5 * Ae.coeff (2 * n) ^ 2 * Be.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g) +
          2 * Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 *
            ce.coeff (4 * n - g) +
          15 * Ae.coeff (2 * n) * ce.coeff (4 * n - g) *
            ee.coeff (6 * n - 2 * g) -
          7 * ce.coeff (4 * n - g) ^ 3) = 0 := by
      linear_combination hraw -
        (Ae.coeff (2 * n) ^ 2 * Be.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g) -
          3 * Ae.coeff (2 * n) * ce.coeff (4 * n - g) *
            ee.coeff (6 * n - 2 * g) +
          ce.coeff (4 * n - g) ^ 3) * hcast
    exact (mul_eq_zero.mp hfac).resolve_left hN
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 : secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa using hsplit0.symm.trans h0e
  have hidx : 8 * n - 1 ≠ 59 := by omega
  have hterm : (C terminal * (60 * (X ^ 59 : k[X]))).coeff
      (8 * n - 1) = 0 := by simp [coeff_C_mul, coeff_X_pow, hidx]
  have hrow0 := congrArg (fun p : k[X] => p.coeff (8 * n - 1)) hsum0
  rw [drops.1, drops.2.1, coeff_add, hterm] at hrow0
  have hres := secondaryResidualRowZeroPolynomial68_coeff_double_of_laterDeepLowerOpen
    Ae Be ce d ee n g hn hg hopen hA secondary.2.1 secondary.2.2.1 hd2 he2
  have htarget : 13 * n - 3 * g - 1 = 8 * n - 1 := by omega
  rw [htarget] at hres
  have hload := cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_coincidentFive
    alpha gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hwall
      hA secondary.2.1 secondary.2.2.1 hD (he2.trans (by omega))
  rw [hres, hload] at hrow0
  have hrowZero : (8 / 27 : k) * (n : k) * Ae.coeff (2 * n) *
        (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            ee.coeff (6 * n - 2 * g)) -
          Ae.coeff (2 * n) * ce.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) +
          Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2) +
      (1 / 9 : k) * (n : k) * delta * Ae.coeff (2 * n) ^ 4 = 0 := by
    push_cast at hrow0
    linear_combination hrow0
  have scalarPacket : LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) delta :=
    ⟨hface.1, (by linear_combination hface.2), hrowOne,
      (by linear_combination hrowZero)⟩
  by_cases heq : h = 2 * g
  · have notboth : ¬ (d = 0 ∧ ee = 0) := by
      rintro ⟨hd0, he0⟩
      have hhzero := heq
      simp only [h, secondaryResidualGap68, polynomialGap68, hd0, he0,
        if_pos, Nat.min_eq_left (by omega : 5 * n + 1 ≤ 6 * n + 1)]
        at hhzero
      omega
    have attained := secondaryResidualGap68_boundary_attained
      n d ee hdbase hebase notboth
    change d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 at attained
    rw [heq] at attained
    exact ⟨heq, attained, scalarPacket⟩
  · have hstrict : 2 * g < h := lt_of_le_of_ne hdouble (Ne.symm heq)
    have hd0 : d.coeff (5 * n - 2 * g) = 0 :=
      coeff_eq_zero_of_natDegree_lt (bounds.1.trans_lt (by omega))
    have he0 : ee.coeff (6 * n - 2 * g) = 0 :=
      coeff_eq_zero_of_natDegree_lt (bounds.2.trans_lt (by omega))
    exact False.elim (laterDeepLowerOpenDoubleFiveWall_strictOvershoot_inconsistent68
      (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) delta (Nat.cast_ne_zero.mpr hn.ne') ha support
      (by simpa only [hd0, he0, mul_zero, zero_mul, add_zero] using scalarPacket.four)
      (by
        have ht := scalarPacket.three
        simp only [hd0, he0, mul_zero, zero_mul] at ht
        linear_combination ht)
      (by
        have ht := scalarPacket.rowOne
        simp only [hd0, he0, mul_zero, zero_mul] at ht
        linear_combination ht)
      (by
        have ht := scalarPacket.rowZero
        simp only [hd0, he0, mul_zero, zero_mul] at ht
        linear_combination ht))

#print axioms cubicLoadRowOnePolynomial68_degree_lt_double_of_laterDeepLowerOpen_fiveWall
#print axioms polynomialLaterDeepLowerOpenDoubleFiveWallInvariantFace68
#print axioms laterDeepLowerOpenDoubleFiveWall_strictOvershoot_inconsistent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68

end LaterDeepLowerOpenDoubleFiveWallSelector68

end Max11DegreeRoutes
