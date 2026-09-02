import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedTerminalLoadedSourceScratch

/-! # Row-two closure of the rigid loaded aligned terminal -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedTerminalRowTwoClosureSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 8000000 in
theorem secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - 2 * g)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (6 * n - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        B.coeff (3 * n - g) *
          (B.coeff (3 * n - g) ^ 2 +
            9 * e.coeff (6 * n - 2 * g)) := by
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have hp := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
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
  have hlow1 : (A * c * derivative d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow2 : (A * derivative c * d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative A * c * d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow4 : (B ^ 2 * derivative d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow5 : (B * derivative B * d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow6 : (B * c * derivative c).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow7 : (derivative B * c ^ 2).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow8 : (d * derivative e).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow9 : (derivative d * e).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  simp only [secondaryResidualRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h5', h6',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9, smul_eq_mul]
  have hcast2 : (((2 * n : ℕ) : k)) = 2 * (n : k) := by push_cast; rfl
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  rw [hcast2, hcast3, hcast6]
  have hw : (3 : k) * (g : k) = 5 * (n : k) := by exact_mod_cast hwall
  linear_combination
    (-8 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) *
      e.coeff (6 * n - 2 * g) * hw

set_option maxHeartbeats 12000000 in
theorem cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - 2 * g)
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
      A B c n g hgt hA hB (hc.trans (by omega))
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
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn
      (by omega : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) (by omega)
      hA hB (hc.trans (by omega)) hD (he.trans (by omega))
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
    have hclt' : c.natDegree < 2 * n := hc.trans_lt (by omega)
    have hconst : (C zeta : k[X]).coeff (2 * n) = 0 := by
      simp [coeff_C, show 2 * n ≠ 0 by omega]
    rw [coeff_eq_zero_of_natDegree_lt hBlt,
      coeff_eq_zero_of_natDegree_lt hclt', hconst]
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

theorem laterDeepLowerOpenDoubleFiveWall_terminal_rowTwo_inconsistent68
    (N a b e delta : k) (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (he : e = (4 / 45 : k) * b ^ 2)
    (hdelta : delta * a ^ 2 = (32 / 135 : k) * b ^ 3)
    (hrowTwo : (8 / 27 : k) * N * a * b * (b ^ 2 + 9 * e) +
      (2 / 3 : k) * N * delta * a ^ 3 = 0) : False := by
  have hprod : (56 / 81 : k) * N * a * b ^ 3 = 0 := by
    have ht := hrowTwo
    rw [he] at ht
    linear_combination ht - (2 / 3 : k) * N * a * hdelta
  have hfac : (56 / 81 : k) * N * a * b ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hN) ha)
      (pow_ne_zero 3 hb)
  exact hfac hprod

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAligned_inconsistent68
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
    (hdegenerate :
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
      ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
        d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0)
    (hcAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 4 * n - g)
    (hdAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 5 * n - 2 * g) : False := by
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
  let e := ee.coeff (6 * n - 2 * g)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change 60 ∣ 4 * n - g at hcAlign
  change 60 ∣ 5 * n - 2 * g at hdAlign
  have rigid :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedTerminalLoadedPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hcAlign)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdAlign)
  change 5 * n - 2 * g = g ∧ ce.natDegree ≤ 4 * n - 2 * g ∧
      d.natDegree ≤ 0 ∧ _ ∧ _ ∧
      e = (4 / 45 : k) * b ^ 2 ∧
      delta * a ^ 2 = (32 / 135 : k) * b ^ 3 ∧ delta ≠ 0 ∧ _ ∧ _
    at rigid
  rcases rigid with
    ⟨hterminalEq, hc, hd, hi3, hrowOne, heq, hdelta, hdeltane, hc₁, hd₀⟩
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
  have hb : b ≠ 0 := by
    dsimp only [b]
    exact hdegenerate.2.1
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
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ at selector
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
    secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
      Ae Be ce d ee n g hn hwall hA secondary.2.1 hc hd he2,
    cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
      alpha gamma delta epsilon zeta eta Ae Be ce Dtr ee n g hn hwall
      hA secondary.2.1 hc hDtr he2] at hcoeff
  have hrowTwo : (8 / 27 : k) * (n : k) * a * b * (b ^ 2 + 9 * e) +
      (2 / 3 : k) * (n : k) * delta * a ^ 3 = 0 := by
    simpa only [a, b, e] using hcoeff
  exact laterDeepLowerOpenDoubleFiveWall_terminal_rowTwo_inconsistent68
    (n : k) a b e delta (Nat.cast_ne_zero.mpr hn.ne') ha hb
    heq hdelta hrowTwo

#print axioms secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
#print axioms cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
#print axioms laterDeepLowerOpenDoubleFiveWall_terminal_rowTwo_inconsistent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAligned_inconsistent68

end LaterDeepLowerOpenDoubleFiveWallAlignedTerminalRowTwoClosureSource68

end Max11DegreeRoutes
