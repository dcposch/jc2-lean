import LowScale68SecondaryExtraction

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
section SolLoadBound
variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 3000000 in
/-- After translating `D=A*B/3+d`, every constant-load contribution to the
first one-form lies strictly below the next `3g` residual face. -/
theorem solCubicLoadRowTwoPolynomial68_degree_lt_cubicFace
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        11 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have hsmall' : 2 * g < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall' hA hB hc hD he'
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
  have hUlC : (Ul * derivative C0).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hTlD : (Tl * derivative D).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hSlE : (Sl * derivative E).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hBVl : (B * derivative Vl).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hDTl : (D * derivative Tl).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
  compute_degree
  omega

/-- Exact load contribution to the first one-form after `D=A*B/3+d`.
The coefficients are the factored CAS expansion; `alpha` and `eta` are
absent because they cancel. -/
def cubicLoadRowTwoTranslatedPolynomial68
    (l beta gamma delta epsilon zeta : k)

end SolLoadBound
#print axioms solCubicLoadRowTwoPolynomial68_degree_lt_cubicFace
end Max11DegreeRoutes

