import LowScale68SecondaryLaterDeepThreeRadiusResidualEntry

/-! # Elimination of the mixed load on the later-deep wall `2g = 5n`

At the right endpoint of the later-deep lower window, the `delta` load ties
the first secondary face.  Its exact row-two and row-zero coefficients force
`delta = 0`.  The ordinary five-face classification then makes both
translated odd defects drop strictly and starts a residual gap beyond `g`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusWallElimination68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Exact tied `delta` load in row two -/

theorem cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_laterDeepFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).coeff (6 * n - 1) =
      (2 / 3 : k) * (n : k) * delta * A.coeff (2 * n) ^ 3 := by
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
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
  have hgt : n < g := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hTr : Tr.natDegree ≤ 2 * n := by
    simp only [Tr, cubicLoadTAlphaRestPolynomial68]
    compute_degree
    omega
  have hSc : Sc.natDegree ≤ 3 * n - g := by
    simp only [Sc, cubicLoadSAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha B).trans hB
  have hSr : Sr.natDegree ≤ 0 := by simp [Sr, natDegree_C]
  have hVr : Vr.natDegree ≤ 4 * n :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn
      (by omega : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) (by omega)
      hA hB hc hD he
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
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
  have hE : E.natDegree ≤ 6 * n := by
    exact (natDegree_add_le Ec Er).trans
      (max_le hEc (hEr.trans (by omega)))
  have hU : U.natDegree ≤ 5 * n - g := by
    exact (natDegree_add_le Uc Ur).trans
      (max_le hUc (hUr.trans (by omega)))
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hA2i : 2 * (2 * n) = 4 * n := by omega
  rw [hA2i] at hA2
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hclt : c.natDegree < 4 * n := hc.trans_lt (by omega)
  have hC0top : C0.coeff (4 * n) =
      (1 / 3 : k) * A.coeff (2 * n) ^ 2 := by
    simp only [C0, C0c, coeff_add, coeff_smul, smul_eq_mul, hA2,
      coeff_eq_zero_of_natDegree_lt hclt, add_zero]
  have hC0ctop : C0c.coeff (4 * n) =
      (1 / 3 : k) * A.coeff (2 * n) ^ 2 := by
    simp only [C0c, coeff_smul, smul_eq_mul, hA2]
  have hErlt : Er.natDegree < 6 * n := hEr.trans_lt (by omega)
  have hEtop : E.coeff (6 * n) =
      (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, Ec, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hErlt, add_zero]
  have hUrTop : Ur.coeff (2 * n) =
      (1 / 2 * delta : k) * A.coeff (2 * n) := by
    simp only [Ur, cubicLoadUAlphaRestPolynomial68, zero_mul, zero_smul,
      smul_zero, zero_add, coeff_add, coeff_smul, smul_eq_mul]
    have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
    have hconst : (C zeta : k[X]).coeff (2 * n) = 0 := by
      simp [coeff_C, show 2 * n ≠ 0 by omega]
    rw [coeff_eq_zero_of_natDegree_lt hBlt, hconst]
    ring
  have hSrTop : Sr.coeff 0 = delta := by simp [Sr]
  have h1 : (Ur * derivative C0).coeff (6 * n - 1) =
      Ur.coeff (2 * n) * C0.coeff (4 * n) * ((4 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Ur C0 (2 * n) (4 * n)
      (by omega) hUr hC0
    have hi : 2 * n + 4 * n - 1 = 6 * n - 1 := by omega
    rwa [hi] at h
  have h2deg : (Uc * derivative c).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have h3deg : ((2 : k) • (Tr * derivative D)).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have h4 : ((3 : k) • (Sr * derivative E)).coeff (6 * n - 1) =
      (3 : k) * Sr.coeff 0 * E.coeff (6 * n) * ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Sr E 0 (6 * n)
      (by omega) hSr hE
    have hi : 0 + 6 * n - 1 = 6 * n - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h5deg : ((3 : k) • (Sc * derivative Er)).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have h6deg : ((3 : k) • (B * derivative Vr)).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have h7deg : ((2 : k) • (c * derivative U)).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have h8 : ((2 : k) • (C0c * derivative Ur)).coeff (6 * n - 1) =
      (2 : k) * C0c.coeff (4 * n) * Ur.coeff (2 * n) *
        ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 C0c Ur (4 * n) (2 * n)
      (by omega) hC0c hUr
    have hi : 4 * n + 2 * n - 1 = 6 * n - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h9deg : (D * derivative Tr).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  rw [cubicLoadRowTwoPolynomial68_eq_deepGapRest_of_beta']
  change (Ur * derivative C0 + Uc * derivative c +
      (2 : k) • (Tr * derivative D) + (3 : k) • (Sr * derivative E) +
      (3 : k) • (Sc * derivative Er) - (3 : k) • (B * derivative Vr) -
      (2 : k) • (c * derivative U) - (2 : k) • (C0c * derivative Ur) -
      D * derivative Tr).coeff (6 * n - 1) = _
  simp only [coeff_add, coeff_sub, h1,
    coeff_eq_zero_of_natDegree_lt h2deg,
    coeff_eq_zero_of_natDegree_lt h3deg, h4,
    coeff_eq_zero_of_natDegree_lt h5deg,
    coeff_eq_zero_of_natDegree_lt h6deg,
    coeff_eq_zero_of_natDegree_lt h7deg, h8,
    coeff_eq_zero_of_natDegree_lt h9deg, add_zero, zero_add, sub_zero]
  rw [hUrTop, hC0top, hSrTop, hEtop, hC0ctop]
  push_cast
  ring

theorem integratedLowerRowTwoPolynomial68_sixRadius_of_laterDeepFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha 0 delta A B
        ((1 / 3 : k) • A ^ 2 + c) D)
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (6 * n - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) +
      (2 / 3 : k) * (n : k) * delta * A.coeff (2 * n) ^ 3 := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hidx : 11 * n - 2 * g - 1 = 6 * n - 1 := by omega
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha 0 gamma delta epsilon zeta eta A B c D e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split, coeff_add]
  rw [← hidx,
    cubicHomogeneousRowTwoPolynomial68_secondaryCoeff_of_laterDeepLower
      A B c D e n g hn hg hwindow hA hB hc hD he, hidx]
  rw [cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_laterDeepFiveWall
      alpha gamma delta epsilon zeta eta A B c D e n g hn hg hwall
      hA hB hc hD he]

/-! ## Exact tied `delta` load in the terminal row -/

theorem cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_laterDeepFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).coeff (8 * n - 1) =
      (1 / 9 : k) * (n : k) * delta * A.coeff (2 * n) ^ 4 := by
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  have hgt : n < g := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hVr : Vr.natDegree ≤ 4 * n :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn
      (by omega : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) (by omega)
      hA hB hc hD he
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E, Ec, Er]
    compute_degree
    omega
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := he.trans_lt (by omega)
  have hEtop : E.coeff (6 * n) =
      (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, Ec, Er, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hUrTop : Ur.coeff (2 * n) =
      (1 / 2 * delta : k) * A.coeff (2 * n) := by
    simp only [Ur, cubicLoadUAlphaRestPolynomial68, zero_mul, zero_smul,
      smul_zero, zero_add, coeff_add, coeff_smul, smul_eq_mul]
    have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
    have hconst : (C zeta : k[X]).coeff (2 * n) = 0 := by
      simp [coeff_C, show 2 * n ≠ 0 by omega]
    rw [coeff_eq_zero_of_natDegree_lt hBlt, hconst]
    ring
  have h1 : (Ur * derivative E).coeff (8 * n - 1) =
      Ur.coeff (2 * n) * E.coeff (6 * n) * ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Ur E (2 * n) (6 * n)
      (by omega) hUr hE
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    rwa [hi] at h
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have h2deg : (Uc * derivative Er).natDegree < 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 Uc Er
      (5 * n - g) (6 * n - g) hUc (by omega) hEr
    have hi : (5 * n - g) + (6 * n - g) - 1 = 6 * n - 1 := by omega
    rw [hi] at h
    exact h.trans_lt (by omega)
  have h3deg : (D * derivative Vr).natDegree < 8 * n - 1 := by
    compute_degree
    omega
  rw [cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta']
  change (Ur * derivative E +
      Uc * derivative Er -
      D * derivative Vr).coeff (8 * n - 1) = _
  simp only [coeff_add, coeff_sub, h1,
    coeff_eq_zero_of_natDegree_lt h2deg,
    coeff_eq_zero_of_natDegree_lt h3deg, add_zero, sub_zero]
  rw [hUrTop, hEtop]
  push_cast
  ring

theorem integratedLowerRowZeroPolynomial68_eightRadius_of_laterDeepFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (8 * n - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) +
      (1 / 9 : k) * (n : k) * delta * A.coeff (2 * n) ^ 4 := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hidx : 13 * n - 2 * g - 1 = 8 * n - 1 := by omega
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha 0 gamma delta epsilon zeta eta A B c D e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add]
  rw [← hidx,
    cubicHomogeneousRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower
      A B c D e n g hn hg hwindow hA hB hc hD he, hidx]
  rw [cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_laterDeepFiveWall
      alpha gamma delta epsilon zeta eta A B c D e n g hn hwall
      hA hB hc hD he]

/-! ## Scalar elimination and source-level residual entry -/

theorem laterDeepFiveRadiusWall_delta_zero68
    (N G a b c d e delta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hwall : 2 * G = 5 * N)
    (hfour :
      (-8 / 9 : k) * firstSecondaryFour68 a b c d e +
        (1 / 4 * delta : k) * a ^ 2 = 0)
    (htwo :
      (8 / 27 : k) * firstSecondaryTwo68 N G a b c d e +
        (2 / 3 : k) * N * delta * a ^ 3 = 0)
    (hzero :
      firstSecondaryZero68 a b c d e +
        (9 / 8 : k) * delta * a ^ 3 = 0) :
    delta = 0 := by
  have hG : G = (5 / 2 : k) * N := by
    linear_combination (1 / 2 : k) * hwall
  rw [hG] at htwo
  have htwoFactor :
      N * ((8 / 27 : k) *
          firstSecondaryTwo68 1 (5 / 2 : k) a b c d e +
        (2 / 3 : k) * delta * a ^ 3) = 0 := by
    convert htwo using 1 <;> simp only [firstSecondaryTwo68] <;> ring
  have htwoInner :
      (8 / 27 : k) *
          firstSecondaryTwo68 1 (5 / 2 : k) a b c d e +
        (2 / 3 : k) * delta * a ^ 3 = 0 :=
    (mul_eq_zero.mp htwoFactor).resolve_left hN
  have hproduct : delta * a ^ 3 = 0 := by
    simp only [firstSecondaryFour68, firstSecondaryTwo68,
      firstSecondaryZero68] at hfour htwoInner hzero
    linear_combination
      (12 / 35 : k) * a * hfour +
      (12 / 35 : k) * htwoInner +
      (64 / 105 : k) * hzero
  exact (mul_eq_zero.mp hproduct).resolve_right (pow_ne_zero 3 ha)

set_option maxHeartbeats 18000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualEntry68
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
      2 * g = 5 * n) :
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
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧
      ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < secondaryResidualGap68 n d ee := by
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
  change 2 * g = 5 * n at hwall
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hsplit :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerResidualSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  obtain ⟨hl, hthree, hone, hcases⟩ := hsplit
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  rcases hcases with hwall3 | hopen | hwall5
  · have hwall3eq := hwall3.1
    change 2 * g = 3 * n at hwall3eq
    have hn := data.hn
    omega
  · change 3 * n < 2 * g ∧ 2 * g < 5 * n ∧ _ at hopen
    have hopenlt := hopen.2.1
    omega
  · have hbeta : beta = 0 := hwall5.2.1
    have hfour := hwall5.2.2
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have h2e : lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Be Ce De Ee = 0 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_lowerRowTwoPolynomial68_of_system
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
    have h0e : lowerRowZeroPolynomial68
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) De Ee =
        C terminal * (60 * (X ^ 59 : k[X])) := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_lowerRowZeroPolynomial68_of_system
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
    rw [hl, hbeta, hCrec, hErec] at h2e h0e
    have htwoCoeff := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) h2e
    rw [integratedLowerRowTwoPolynomial68_sixRadius_of_laterDeepFiveWall
        alpha gamma delta epsilon zeta eta Ae Be ce De ee n g
        data.hn data.hg hwall data.hA data.hB data.hc data.hD data.he]
      at htwoCoeff
    simp only [coeff_zero] at htwoCoeff
    have hnEight : 8 ≤ n := by
      have hnTen : 10 ≤ n := by
        simpa only [n] using weightedRadius68_ge_ten A B C0 D E data.hn
      omega
    have hindex : 59 < 8 * n - 1 := by omega
    have hzeroCoeff :=
      expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt terminal
        (integratedUPolynomial68 0 alpha 0 gamma delta zeta Ae Be
          ((1 / 3 : k) • Ae ^ 2 + ce) De
          ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
        (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta Ae Be
          ((1 / 3 : k) • Ae ^ 2 + ce) De
          ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
        De ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee)
        (8 * n - 1) h0e hindex
    rw [integratedLowerRowZeroPolynomial68_eightRadius_of_laterDeepFiveWall
        alpha gamma delta epsilon zeta eta Ae Be ce De ee n g
        data.hn data.hg hwall data.hA data.hB data.hc data.hD data.he]
      at hzeroCoeff
    have hnCast : (n : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt data.hn)
    have hwallCast : (2 : k) * (g : k) = 5 * (n : k) := by
      exact_mod_cast hwall
    have hzeroScalar : firstSecondaryZero68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) +
          (9 / 8 : k) * delta * Ae.coeff (2 * n) ^ 3 = 0 := by
      have hfactor : (n : k) * Ae.coeff (2 * n) *
          ((8 / 81 : k) * firstSecondaryZero68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (1 / 9 : k) * delta * Ae.coeff (2 * n) ^ 3) = 0 := by
        convert hzeroCoeff using 1
        ring
      have hna : (n : k) * Ae.coeff (2 * n) ≠ 0 :=
        mul_ne_zero hnCast data.ha
      have hinner := (mul_eq_zero.mp hfactor).resolve_left hna
      linear_combination (81 / 8 : k) * hinner
    have hdelta := laterDeepFiveRadiusWall_delta_zero68
      (n : k) (g : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
      (ee.coeff (6 * n - g)) delta hnCast data.ha hwallCast
      hfour htwoCoeff hzeroScalar
    have hfour0 : firstSecondaryFour68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 := by
      rw [hdelta] at hfour
      norm_num at hfour ⊢
      exact hfour
    have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 := by
      rw [hdelta] at htwoCoeff
      norm_num at htwoCoeff ⊢
      exact htwoCoeff
    have hzero0 : firstSecondaryZero68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 := by
      rw [hdelta] at hzeroScalar
      simpa using hzeroScalar
    have hgapCast : (g : k) - 6 * (n : k) ≠ 0 :=
      laterDeepLower_gap_ne_six_radius n g data.hn hwindow
    have hface : FirstSecondaryFace68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) :=
      ⟨hfour0, hthree, htwo0, hone, hzero0⟩
    have hclass := firstSecondaryFace68_classify
      (n : k) (g : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
      (ee.coeff (6 * n - g)) data.ha hgapCast hface
    have hd : d.natDegree < 5 * n - g :=
      secondaryDDefectPolynomial68_degree_lt_of_laterDeepLower
        Ae Be De n g data.hn hwindow data.hA data.hB data.hD hclass.2
    have he : ee.natDegree < 6 * n - g :=
      natDegree_lt_of_le_of_coeff_eq_zero68 ee (6 * n - g)
        (laterDeepLower_index_pos_six n g data.hn hwindow) data.he hclass.1
    exact ⟨hl, hbeta, hdelta, hclass.1, hclass.2, hd, he,
      secondaryResidualGap68_gt_of_strictDrops n g d ee hd he⟩

#print axioms cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_laterDeepFiveWall
#print axioms integratedLowerRowTwoPolynomial68_sixRadius_of_laterDeepFiveWall
#print axioms cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_laterDeepFiveWall
#print axioms integratedLowerRowZeroPolynomial68_eightRadius_of_laterDeepFiveWall
#print axioms laterDeepFiveRadiusWall_delta_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualEntry68

end LaterDeepFiveRadiusWallElimination68

end Max11DegreeRoutes
