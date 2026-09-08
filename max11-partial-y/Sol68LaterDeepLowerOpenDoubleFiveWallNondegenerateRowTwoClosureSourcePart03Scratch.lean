import Sol68LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSourcePart02Scratch

/-! # Row-two closure of the nondegenerate double-five tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68

variable {k : Type*} [Field k] [CharZero k]

private theorem leaf68_natDegree_mulDeriv_lt {p q : k[X]} {u v bound : ℕ}
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) (h : u + (v - 1) < bound) :
    (p * derivative q).natDegree < bound :=
  natDegree_mul_le.trans_lt
    (lt_of_le_of_lt
      (Nat.add_le_add hp ((natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1))) h)

private theorem leaf68_natDegree_smul_lt (r : k) {p : k[X]} {bound : ℕ}
    (h : p.natDegree < bound) : (r • p).natDegree < bound :=
  (natDegree_smul_le r p).trans_lt h

private theorem leaf68_natDegree_add_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p + q).natDegree < bound :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem leaf68_natDegree_sub_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p - q).natDegree < bound :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)


set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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
  have h2deg : (Uc * derivative c).natDegree < 6 * n - 1 :=
    leaf68_natDegree_mulDeriv_lt hUc hc (by omega)
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
  have h9deg : (D * derivative Tr).natDegree < 6 * n - 1 :=
    leaf68_natDegree_mulDeriv_lt hD hTr (by omega)
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

end LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68
end Max11DegreeRoutes
