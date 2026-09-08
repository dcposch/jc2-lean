import LowScale68SecondaryExtractionPart09Scratch

/-! # Extracting the first `(6,8)` secondary face

This module connects the abstract scalar face classified in
`LowScale68SecondaryFace` to the literal polynomial lower system.  The four
transverse coordinates have different secondary degree bounds, so the usual
single weighted-boundary lemmas are first replaced by arbitrary-bound
coefficient rules.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryExtraction68

variable {k : Type*} [Field k] [CharZero k]

private theorem extraction_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans_lt ((hidx ▸ hsum).trans_lt huv)

private theorem extraction_natDegree_smul_lt68 (r : k) {p : k[X]} {m : ℕ}
    (hp : p.natDegree < m) : (r • p).natDegree < m :=
  (natDegree_smul_le r p).trans_lt hp

private theorem extraction_natDegree_add_lt68 {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p + q).natDegree < m :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem extraction_natDegree_sub_lt68 {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p - q).natDegree < m :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 11 * n - 2 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he
  have hSl : Sl.natDegree ≤ 4 * n := by simpa only [Sl] using hloads.1
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 6 * n := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlC : (Ul * derivative C0).natDegree < 11 * n - 2 * g - 1 :=
    extraction_natDegree_mul_derivative_lt68 Ul C0 (6 * n) (4 * n) _
      (by omega) hUl hC0 (by omega)
  have hTlD : (Tl * derivative D).natDegree < 11 * n - 2 * g - 1 :=
    extraction_natDegree_mul_derivative_lt68 Tl D (5 * n - g) (5 * n - g) _
      (by omega) hTl hD (by omega)
  have hSlE : (Sl * derivative E).natDegree < 11 * n - 2 * g - 1 :=
    extraction_natDegree_mul_derivative_lt68 Sl E (4 * n) (6 * n) _
      (by omega) hSl hE (by omega)
  have hBVl : (B * derivative Vl).natDegree < 11 * n - 2 * g - 1 :=
    extraction_natDegree_mul_derivative_lt68 B Vl (3 * n - g) (7 * n - g) _
      (by omega) hB hVl (by omega)
  have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 2 * g - 1 :=
    extraction_natDegree_mul_derivative_lt68 C0 Ul (4 * n) (6 * n) _
      (by omega) hC0 hUl (by omega)
  have hDTl : (D * derivative Tl).natDegree < 11 * n - 2 * g - 1 :=
    extraction_natDegree_mul_derivative_lt68 D Tl (5 * n - g) (5 * n - g) _
      (by omega) hD hTl (by omega)
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
  exact extraction_natDegree_sub_lt68
    (extraction_natDegree_sub_lt68
      (extraction_natDegree_sub_lt68
        (extraction_natDegree_add_lt68
          (extraction_natDegree_add_lt68 hUlC
            (extraction_natDegree_smul_lt68 (2 : k) hTlD))
          (extraction_natDegree_smul_lt68 (3 : k) hSlE))
        (extraction_natDegree_smul_lt68 (3 : k) hBVl))
      (extraction_natDegree_smul_lt68 (2 : k) hC0Ul))
    hDTl

end SecondaryExtraction68
end Max11DegreeRoutes
