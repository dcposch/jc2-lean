import LowScale68SecondaryExtractionPart05Scratch

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

set_option maxHeartbeats 2000000 in
/-- In the first chamber `2g<n`, the first invariant contributes exactly the
first abstract secondary-face equation. -/
theorem cubicFirstIntegralFourPolynomial68_secondaryCoeff
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 9 * n - 2 * g) :
      p.coeff (9 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hABC : (A * B * c).coeff (9 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n)
      (3 * n - g) (4 * n - g) hA hB hc
    have hi : 2 * n + (3 * n - g) + (4 * n - g) =
        9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (9 * n - 2 * g) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
    have hi : (3 * n - g) + (6 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hDc : (D * c).coeff (9 * n - 2 * g) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hi : (5 * n - g) + (4 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB3 : (B ^ 3).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hAz : A.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hBz : B.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hA2 : (A ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hcz : c.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hDz : D.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hAB : (A * B).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hez : e.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hAc : (A * c).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hB2 : (B ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA3 : (A ^ 3).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA4 : (A ^ 4).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2c : (A ^ 2 * c).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hAB2 : (A * B ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hAe : (A * e).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hBD : (B * D).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hc2 : (c ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralFourPolynomial68, coeff_add, coeff_sub,
    coeff_smul, hABC, hBe, hDc, hB3, hAz, hBz, hA2, hcz, hDz,
    hAB, hez, hAc, hB2, hA3, hA4, hA2c, hAB2, hAe, hBD, hc2,
    smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryFour68]
  ring

end SecondaryExtraction68
end Max11DegreeRoutes
