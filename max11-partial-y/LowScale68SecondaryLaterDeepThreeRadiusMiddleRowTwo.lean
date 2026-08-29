import LowScale68SecondaryLaterDeepLowerParentAfterThreeRadius

/-! # Row two on the attained middle packet at `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusMiddleRowTwo68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 2000000 in
/-- After `l=beta=0`, the I4 load is still bounded by `4n` on the
three-radius wall.  This is the endpoint replacement for the strict
first-deep estimate. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_le_fourRadius_of_threeRadius
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree ≤ 4 * n := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- The incidence polynomial therefore has degree at most `4n` at the
three-radius endpoint. -/
theorem residualIncidenceQ68_degree_le_fourRadius_of_threeRadius
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hQeq := residualIncidenceQ68_eq_I4load_of_l_eq_zero
    0 gamma delta epsilon zeta i4 A B c d e hi4
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_le_fourRadius_of_threeRadius
      gamma delta epsilon zeta A B c D e n g hn hwall hA hB hc hD he
  rw [hQeq]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
/-- All row-two loads lie below the cubic index `11n-3g-1` on
`2g=3n`, once `l=beta=0`. -/
theorem cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_threeRadius_beta
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 11 * n - 3 * g - 1 := by
  rw [cubicLoadRowTwoPolynomial68_eq_deepGapRest_of_beta']
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hgt : n < g := by omega
  have hgle : g ≤ 2 * n := by omega
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Tr := cubicLoadTAlphaRestPolynomial68 alpha 0 gamma epsilon A B c
  let Sc := cubicLoadSAlphaCorePolynomial68 alpha B
  let Sr := (C delta : k[X])
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  let U := Uc + Ur
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hTr0 : Tr.natDegree ≤ max (4 * n - g) (2 * n) :=
    cubicLoadTAlphaRestPolynomial68_degree_le_of_laterDeepLower
      alpha 0 gamma epsilon A B c n g hwindow hA hB hc
  have hTr : Tr.natDegree ≤ 4 * n - g :=
    hTr0.trans (by rw [max_eq_left (by omega)])
  have hSc : Sc.natDegree ≤ 3 * n - g := by
    simp only [Sc, cubicLoadSAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha B).trans hB
  have hSr : Sr.natDegree ≤ 0 := by simp [Sr, natDegree_C]
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
      hA hB hc hD he
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hU : U.natDegree ≤ 5 * n - g :=
    (natDegree_add_le Uc Ur).trans
      (max_le hUc (hUr.trans (by omega)))
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
      (hu : u + v - 1 < 11 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 11 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (11 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative C0).natDegree < 11 * n - 3 * g - 1 :=
    hbound (2 * n) (4 * n) (by omega) (by omega) Ur C0 hUr hC0
  have h2 : (Uc * derivative c).natDegree < 11 * n - 3 * g - 1 :=
    hbound (5 * n - g) (4 * n - g) (by omega) (by omega) Uc c hUc hc
  have h3 : (Tr * derivative D).natDegree < 11 * n - 3 * g - 1 :=
    hbound (4 * n - g) (5 * n - g) (by omega) (by omega) Tr D hTr hD
  have h4 : (Sr * derivative E).natDegree < 11 * n - 3 * g - 1 :=
    hbound 0 (6 * n) (by omega) (by omega) Sr E hSr hE
  have h5 : (Sc * derivative Er).natDegree < 11 * n - 3 * g - 1 :=
    hbound (3 * n - g) (6 * n - g) (by omega) (by omega) Sc Er hSc hEr
  have h6 : (B * derivative Vr).natDegree < 11 * n - 3 * g - 1 :=
    hbound (3 * n - g) (6 * n - g) (by omega) (by omega) B Vr hB hVr
  have h7 : (c * derivative U).natDegree < 11 * n - 3 * g - 1 :=
    hbound (4 * n - g) (5 * n - g) (by omega) (by omega) c U hc hU
  have h8 : (C0c * derivative Ur).natDegree < 11 * n - 3 * g - 1 :=
    hbound (4 * n) (2 * n) (by omega) (by omega) C0c Ur hC0c hUr
  have h9 : (D * derivative Tr).natDegree < 11 * n - 3 * g - 1 :=
    hbound (5 * n - g) (4 * n - g) (by omega) (by omega) D Tr hD hTr
  have h3s := deepGap_natDegree_smul_lt68 (2 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (3 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (3 : k) h5
  have h6s := deepGap_natDegree_smul_lt68 (3 : k) h6
  have h7s := deepGap_natDegree_smul_lt68 (2 : k) h7
  have h8s := deepGap_natDegree_smul_lt68 (2 : k) h8
  change (Ur * derivative C0 + Uc * derivative c +
      (2 : k) • (Tr * derivative D) +
      (3 : k) • (Sr * derivative E) +
      (3 : k) • (Sc * derivative Er) -
      (3 : k) • (B * derivative Vr) -
      (2 : k) • (c * derivative U) -
      (2 : k) • (C0c * derivative Ur) -
      D * derivative Tr).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_sub_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_add_lt
                (deepGap_natDegree_add_lt h1 h2) h3s) h4s) h5s) h6s) h7s) h8s) h9

set_option maxHeartbeats 2000000 in
/-- The cubic `B,c` part of residual row two has its usual degree on the
three-radius wall. -/
theorem residualRowTwoInner_BcCore_degree_le68_of_threeRadius
    (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (A * B ^ 2 * derivative B).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative A * B ^ 3).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative (B * c ^ 2)).natDegree ≤ 11 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (by omega)
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hAB2 := natDegree_mul_le_of_le hA hB2
  have hAB2d := natDegree_mul_le_of_le hAB2 hdB
  have hA3 := natDegree_mul_le_of_le hdA hB3
  have hBc2 := natDegree_mul_le_of_le hB hc2
  have hdBc2 := natDegree_derivative_le (B * c ^ 2)
  exact ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 8000000 in
/-- On `2h<3g`, the exact row-two coefficient is the nonzero `d*e` face.
This proof uses no strict first-deep hypothesis. -/
theorem residualRowTwo_coeff_leftChamber_of_threeRadius
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : 2 * g = 3 * n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  change Q.natDegree ≤ 4 * n at hQ
  have hidxQ : 6 * n - 1 < idx := by
    dsimp [idx]
    omega
  have hidx_cubic : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hAQ : (A * derivative Q).natDegree < idx := by
    have hqder : (derivative Q).natDegree ≤ 4 * n - 1 :=
      (natDegree_derivative_le Q).trans (by omega)
    have hmul := natDegree_mul_le_of_le hA hqder
    have hi : 2 * n + (4 * n - 1) = 6 * n - 1 := by omega
    rw [hi] at hmul
    exact hmul.trans_lt hidxQ
  have hAQ' : (derivative A * Q).natDegree < idx := by
    have hader : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have hmul := natDegree_mul_le_of_le hader hQ
    have hi : (2 * n - 1) + 4 * n = 6 * n - 1 := by omega
    rw [hi] at hmul
    exact hmul.trans_lt hidxQ
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_threeRadius
    A B c n g hn hg hwall hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidx_cubic
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidx_cubic
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidx_cubic
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2d := natDegree_mul_le_of_le hB2 hd
  have hBd : (derivative (B ^ 2 * d)).natDegree ≤
      11 * n - 2 * g - h - 1 := by
    have hder := natDegree_derivative_le (B ^ 2 * d)
    omega
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdebound
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hinner : inner.coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0AB, h0A3, h0Bd, h0Bc, hde']
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

theorem residualRowTwo_leftChamber_ne_zero_of_threeRadius
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : 2 * g = 3 * n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber_of_threeRadius A B c d e n g h
    hn hg hgh hh hwall hleft hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

set_option maxHeartbeats 12000000 in
/-- The attained middle packet on `2g=3n` cannot lie on the left side
`2h<3g`.  Its exact remaining selector is the balanced wall or the strict
right chamber, with all four leading residual directions nonzero. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleRowTwoSelector68
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
    (hmiddle :
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
      h < 2 * g) :
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
    (2 * h = 3 * g ∨ 3 * g < 2 * h) ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 ∧
      SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (ee.coeff (6 * n - h)) := by
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
  change h < 2 * g at hmiddle
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusNonzeroResidualSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧ _
    at selector
  rcases selector.2.2.2.2.2.2.2 with hmid | hdouble
  · have hface := hmid.2
    have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have secondary :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
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
    have hd : d.natDegree ≤ 5 * n - h := selector.2.2.2.1
    have he : ee.natDegree ≤ 6 * n - h := selector.2.2.2.2.1
    have hclass := secondaryResidualBetweenFace68_classify_of_support
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) ha selector.2.2.2.2.2.1
      selector.2.2.2.2.2.2.1 hface
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    obtain ⟨i4, hi4⟩ := hsys.firstFour
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    have hi4c := hi4e
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, selector.1, selector.2.1] at hi4c
    have hQ := residualIncidenceQ68_degree_le_fourRadius_of_threeRadius
      gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hwall hA hB hc
      (hd.trans (by omega)) (he.trans (by omega)) hi4c
    have hrowTwoe : lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Be Ce De Ee = 0 := by
      dsimp only [Ae, Be, Ce, De, Ee]
      rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
        ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
        lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
    have hrowTwo : secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
      have hr := hrowTwoe
      rw [hCrec, hDrec, hErec] at hr
      exact polynomialSecondaryResidualRowTwo68
        l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hr
    rw [selector.1, selector.2.1] at hrowTwo
    have hD : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
      compute_degree
      omega
    have hload :=
      cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_threeRadius_beta
        alpha gamma delta epsilon zeta eta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg hwall
        hA hB hc hD (he.trans (by omega))
    have hge : 3 * g ≤ 2 * h := by
      by_contra hnot
      have hleft : 2 * h < 3 * g := Nat.lt_of_not_ge hnot
      have hload' :
          (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
            Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
              11 * n - 2 * h - 1 := hload.trans (by omega)
      have hcoeff := congrArg
        (fun p : k[X] => p.coeff (11 * n - 2 * h - 1)) hrowTwo
      rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload', add_zero]
        at hcoeff
      exact residualRowTwo_leftChamber_ne_zero_of_threeRadius
        Ae Be ce d ee n g h hn hg selector.2.2.1 hmiddle hwall hleft
        hA hB hc hd he hQ hclass.2.2.1 hclass.2.2.2.1 hcoeff
    have hsplit : 2 * h = 3 * g ∨ 3 * g < 2 * h := by
      rcases eq_or_lt_of_le hge with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr hlt
    exact ⟨hsplit, hclass.1, hclass.2.1, hclass.2.2.1,
      hclass.2.2.2.1, hclass.2.2.2.2, hface⟩
  · exact False.elim ((not_lt_of_ge hdouble.1) hmiddle)

#print axioms secondaryLoadInvariantFourPolynomial68_degree_le_fourRadius_of_threeRadius
#print axioms residualIncidenceQ68_degree_le_fourRadius_of_threeRadius
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_threeRadius_beta
#print axioms residualRowTwo_coeff_leftChamber_of_threeRadius
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleRowTwoSelector68

end LaterDeepThreeRadiusMiddleRowTwo68

end Max11DegreeRoutes
