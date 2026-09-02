import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedTerminalRowTwoClosureSourceScratch

/-! # Row-two closure of the nondegenerate double-five tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 10000000 in
theorem secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (6 * n - 1) =
      (8 / 27 : k) * (n : k) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
          9 * A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g) +
          9 * A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) -
          18 * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have hp := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using hp
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using hp
  have h1 := coeff_mul_mul_derivative_at_bounds68 A B e
    (2 * n) (3 * n - g) (6 * n - 2 * g) (by omega) hA hB he
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) - 1 =
      6 * n - 1 := by omega
  rw [hi1] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 A e B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA he hB
  have hi2 : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative B * e).coeff (6 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_derivative_at_bounds68 A c d
    (2 * n) (4 * n - g) (5 * n - 2 * g) (by omega) hA hc hd
  have hi3 : 2 * n + (4 * n - g) + (5 * n - 2 * g) - 1 =
      6 * n - 1 := by omega
  rw [hi3] at h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A d c
    (2 * n) (5 * n - 2 * g) (4 * n - g) (by omega) hA hd hc
  have hi4 : 2 * n + (5 * n - 2 * g) + (4 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi4] at h4
  have h4' : (A * derivative c * d).coeff (6 * n - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h4
  have h5 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hi5 : (9 * n - 3 * g) + 2 * n - 1 = 6 * n - 1 := by omega
  rw [hi5, hB3] at h5
  have h5' : (derivative A * B ^ 3).coeff (6 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 B e A
    (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega) hB he hA
  have hi6 : (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi6] at h6
  have h6' : (derivative A * B * e).coeff (6 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have h7 := coeff_mul_mul_derivative_at_bounds68 c d A
    (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega) hc hd hA
  have hi7 : (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi7] at h7
  have h7' : (derivative A * c * d).coeff (6 * n - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h7
  have h10 := coeff_mul_mul_derivative_at_bounds68 B c c
    (3 * n - g) (4 * n - g) (4 * n - g) (by omega) hB hc hc
  have hi10 : (3 * n - g) + (4 * n - g) + (4 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi10] at h10
  have h11 := coeff_mul_derivative_at_bounds68 (c ^ 2) B
    (8 * n - 2 * g) (3 * n - g) (by omega) hc2deg hB
  have hi11 : (8 * n - 2 * g) + (3 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi11, hc2] at h11
  have h11' : (derivative B * c ^ 2).coeff (6 * n - 1) =
      B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h11
  have hlow1 : (B ^ 2 * derivative d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow2 : (B * derivative B * d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow3 : (d * derivative e).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow4 : (derivative d * e).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  simp only [secondaryResidualRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3, h4', h5', h6', h7', h10, h11',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4, smul_eq_mul]
  have hcast2 : (((2 * n : ℕ) : k)) = 2 * (n : k) := by push_cast; rfl
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - 2 * g : ℕ) : k)) =
      5 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  rw [hcast2, hcast3, hcast4, hcast5, hcast6]
  have hw : (3 : k) * (g : k) = 5 * (n : k) := by exact_mod_cast hwall
  linear_combination
    (-8 / 9 : k) *
      (A.coeff (2 * n) * B.coeff (3 * n - g) *
          e.coeff (6 * n - 2 * g) +
        A.coeff (2 * n) * c.coeff (4 * n - g) *
          d.coeff (5 * n - 2 * g) -
        B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) * hw

theorem laterDeepLowerOpenDoubleFiveWall_nondegenerate_rowTwo_inconsistent68
    (N a b c d e delta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hc : c ≠ 0) (hdisc : a * b ^ 2 = c ^ 2)
    (packet : LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      N a b c d e delta)
    (hrowTwo : (8 / 27 : k) * N *
        (a * b ^ 3 + 9 * a * b * e + 9 * a * c * d - 18 * b * c ^ 2) +
      (2 / 3 : k) * N * delta * a ^ 3 = 0) : False := by
  have hb : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hdisc
    exact hc (eq_zero_of_pow_eq_zero hdisc.symm)
  have hcd : a * c * d + a * b ^ 3 - 3 * a * b * e = 0 := by
    have hp : b * (a * c * d + a * b ^ 3 - 3 * a * b * e) = 0 := by
      linear_combination
        -c * packet.three + b ^ 2 * hdisc - 3 * e * hdisc
    exact (mul_eq_zero.mp hp).resolve_left hb
  have hfour : (16 / 27 : k) * b * (-5 * b ^ 2 + 18 * e) +
      (1 / 4 : k) * delta * a ^ 2 = 0 := by
    have hp : a * ((16 / 27 : k) * b * (-5 * b ^ 2 + 18 * e) +
        (1 / 4 : k) * delta * a ^ 2) = 0 := by
      linear_combination a * packet.four - (8 / 3 : k) * hcd
    exact (mul_eq_zero.mp hp).resolve_left ha
  have htwo : (16 / 27 : k) * N * a * b * (-13 * b ^ 2 + 18 * e) +
      (2 / 3 : k) * N * delta * a ^ 3 = 0 := by
    linear_combination
      hrowTwo - (8 / 3 : k) * N * hcd -
        (16 / 3 : k) * N * b * hdisc
  have heprod : N * a * b * (b ^ 2 - 90 * e) = 0 := by
    linear_combination
      (81 / 16 : k) * (htwo - (8 / 3 : k) * N * a * hfour)
  have hNab : N * a * b ≠ 0 := mul_ne_zero (mul_ne_zero hN ha) hb
  have heq : e = (1 / 90 : k) * b ^ 2 := by
    have ht := (mul_eq_zero.mp heprod).resolve_left hNab
    linear_combination (-1 / 90 : k) * ht
  have hdelta : delta * a ^ 2 = (512 / 45 : k) * b ^ 3 := by
    rw [heq] at hfour
    linear_combination 4 * hfour
  have hzero : (8 / 27 : k) * N * a *
        (2 * a * b ^ 3 - 4 * a * b * e) +
      (1 / 9 : k) * N * delta * a ^ 4 = 0 := by
    linear_combination
      packet.rowZero + (8 / 27 : k) * N * a * hcd +
        (8 / 27 : k) * N * a * b * hdisc
  rw [heq] at hzero
  have hbad : (448 / 243 : k) * N * a ^ 2 * b ^ 3 = 0 := by
    linear_combination hzero - (1 / 9 : k) * N * a ^ 2 * hdelta
  have hbadne : (448 / 243 : k) * N * a ^ 2 * b ^ 3 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hN) (pow_ne_zero 2 ha))
      (pow_ne_zero 3 hb)
  exact hbadne hbad

set_option maxHeartbeats 12000000 in
theorem cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
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
  have hTr : Tr.natDegree ≤ 4 * n - g := by
    simp only [Tr, cubicLoadTAlphaRestPolynomial68]
    compute_degree
    omega
  have hSc : Sc.natDegree ≤ 3 * n - g := by
    simp only [Sc, cubicLoadSAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha B).trans hB
  have hSr : Sr.natDegree ≤ 0 := by simp [Sr, natDegree_C]
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn
      (by omega : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) (by omega)
      hA hB hc hD (he.trans (by omega))
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
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans
      (max_le hEc (hEr.trans (by omega)))
  have hU : U.natDegree ≤ 5 * n - g :=
    (natDegree_add_le Uc Ur).trans
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
    have ht := coeff_mul_derivative_at_bounds68 Ur C0 (2 * n) (4 * n)
      (by omega) hUr hC0
    have hi : 2 * n + 4 * n - 1 = 6 * n - 1 := by omega
    rwa [hi] at ht
  have h2deg : (Uc * derivative c).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have h3deg : ((2 : k) • (Tr * derivative D)).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have h4 : ((3 : k) • (Sr * derivative E)).coeff (6 * n - 1) =
      (3 : k) * Sr.coeff 0 * E.coeff (6 * n) * ((6 * n : ℕ) : k) := by
    have ht := coeff_mul_derivative_at_bounds68 Sr E 0 (6 * n)
      (by omega) hSr hE
    have hi : 0 + 6 * n - 1 = 6 * n - 1 := by omega
    rw [hi] at ht
    rw [coeff_smul, smul_eq_mul, ht]
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
    have ht := coeff_mul_derivative_at_bounds68 C0c Ur (4 * n) (2 * n)
      (by omega) hC0c hUr
    have hi : 4 * n + 2 * n - 1 = 6 * n - 1 := by omega
    rw [hi] at ht
    rw [coeff_smul, smul_eq_mul, ht]
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

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallNondegenerate_inconsistent68
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
      3 * g = 5 * n)
    (hnondegenerate :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ce.coeff (4 * n - g) ≠ 0) : False := by
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
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  let a := Ae.coeff (2 * n)
  let b := Be.coeff (3 * n - g)
  let c := ce.coeff (4 * n - g)
  let de := d.coeff (5 * n - 2 * g)
  let e := ee.coeff (6 * n - 2 * g)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change c ≠ 0 at hnondegenerate
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ (de ≠ 0 ∨ e ≠ 0) ∧
      LaterDeepLowerOpenDoubleFiveWallScalarPacket68
        (n : k) a b c de e delta at selector
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _
    at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have ha : a ≠ 0 := by
    dsimp only [a]
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
    have ht := bounds.1
    change d.natDegree ≤ 5 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have hDtr : Dtr.natDegree ≤ 5 * n - g := by
    simp only [Dtr]
    compute_degree
    omega
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at h2e
  have hrowPoly := polynomialSecondaryResidualRowTwo68
    0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee h2e
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) hrowPoly
  rw [coeff_add, coeff_zero,
    secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
      Ae Be ce d ee n g hn hwall hA secondary.2.1 secondary.2.2.1 hd2 he2,
    cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
      alpha gamma delta epsilon zeta eta Ae Be ce Dtr ee n g hn hwall
      hA secondary.2.1 secondary.2.2.1 hDtr he2] at hcoeff
  have hrowTwo : (8 / 27 : k) * (n : k) *
        (a * b ^ 3 + 9 * a * b * e + 9 * a * c * de - 18 * b * c ^ 2) +
      (2 / 3 : k) * (n : k) * delta * a ^ 3 = 0 := by
    simpa only [a, b, c, de, e] using hcoeff
  have refined := laterDeepLowerOpenDoubleFiveWallScalarPacket68_refine
    (n : k) a b c de e delta ha (Or.inr hnondegenerate)
    selector.2.1 selector.2.2
  have hdisc : a * b ^ 2 = c ^ 2 := by
    rcases refined with hdeg | hnon
    · exact False.elim (hnondegenerate hdeg.1)
    · exact hnon.2
  exact laterDeepLowerOpenDoubleFiveWall_nondegenerate_rowTwo_inconsistent68
    (n : k) a b c de e delta (Nat.cast_ne_zero.mpr hn.ne') ha
    hnondegenerate hdisc selector.2.2 hrowTwo

#print axioms secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
#print axioms cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
#print axioms laterDeepLowerOpenDoubleFiveWall_nondegenerate_rowTwo_inconsistent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallNondegenerate_inconsistent68

end LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68

end Max11DegreeRoutes
