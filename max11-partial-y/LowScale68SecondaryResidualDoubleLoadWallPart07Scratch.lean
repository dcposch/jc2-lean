import LowScale68SecondaryResidualDoubleLoadWallPart06Scratch

/-! # Mixed residual double face on the `(6,8)` wall `n = 3g`, `h = 2g`

On `n = 3g` the residual double face `9n-3g` collides with the Jacobian
load `l A^4` at degree `8n`.  Row two and row zero likewise meet the cores
`l A^5` and `l A^6` at `10n-1` and `12n-1`.  I3 and row one remain
load-free.  The five leading scalars force `l = b = c = 0`; residual
support `b ≠ 0 ∨ c ≠ 0` therefore excludes the wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Abstract mixed numerators -/

/-! ## Scalar identities -/

/-! ## Wall index arithmetic -/

/-! ## I4 load core versus remainder -/

/-! ## Term-by-term remainder degree bounds on `3g = n`

Cores, rest polynomials, Jacobian splits, and
`cubicLoadRowTwo/ZeroPolynomial68_eq_lCore_add_rest` are the tracked
definitions in `LowScale68SecondaryFirstLoadWallRemainder`.  Only the
wall-specific degree comparisons `3g = n` are restated here. -/

private theorem natDegree_mul_derivative_le_add_sub68
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

private theorem natDegree_mul_derivative_lt_of_add_sub68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (natDegree_mul_derivative_le_add_sub68 p q u v hv hp hq).trans_lt huv

private theorem natDegree_smul_lt68 (r : k) {p : k[X]} {n : ℕ}
    (hp : p.natDegree < n) : (r • p).natDegree < n :=
  (natDegree_smul_le r p).trans_lt hp

private theorem natDegree_add_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem natDegree_sub_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoRestPolynomial68_degree_lt_wall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowTwoRestPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 10 * n - 1 := by
  let Ulc := cubicLoadUCorePolynomial68 l A
  let Ulr := cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
    A B c D e
  let Ul := Ulc + Ulr
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Slc := cubicLoadSCorePolynomial68 l A
  let Slr := cubicLoadSRestPolynomial68 l alpha beta delta A B c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := cubicERestPolynomial68 A c e
  let E := Ec + Er
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg htwo hA hB hc hD he'
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_wall
      l alpha beta gamma delta zeta A B c D e n g
      hg hwall hA hB hc hD he
  have hUl : Ul.natDegree ≤ 6 * n :=
    (natDegree_add_le Ulc Ulr).trans (max_le hUlc (hUlr.trans (by omega)))
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0, C0c]
    compute_degree
    omega
  have hSlc : Slc.natDegree ≤ 4 * n :=
    cubicLoadSCorePolynomial68_degree_le l A n hA
  have hSlr : Slr.natDegree ≤ 4 * n - g :=
    cubicLoadSRestPolynomial68_degree_le_wall
      l alpha beta delta A B c n g hg hwall hA hB hc
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_wall A c e n g
      hg hwall hA hc he
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative c).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulc c (6 * n) (4 * n - g)
      (10 * n - 1) (by omega) hUlc hc (by omega)
  have h2 : (Ulr * derivative C0).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulr C0 (6 * n - g) (4 * n)
      (10 * n - 1) (by omega) hUlr hC0 (by omega)
  have h3 : (Tl * derivative D).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Tl D (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hTl hD (by omega)
  have h4 : (Slc * derivative Er).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Slc Er (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hSlc hEr (by omega)
  have h5 : (Slr * derivative E).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Slr E (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hSlr hE (by omega)
  have h6 : (B * derivative Vl).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 B Vl (3 * n - g) (7 * n - g)
      (10 * n - 1) (by omega) hB hVl (by omega)
  have h7 : (C0c * derivative Ulr).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 C0c Ulr (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hC0c hUlr (by omega)
  have h8 : (c * derivative Ul).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 c Ul (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hc hUl (by omega)
  have h9 : (D * derivative Tl).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 D Tl (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hD hTl (by omega)
  have h3s := natDegree_smul_lt68 (2 : k) h3
  have h4s := natDegree_smul_lt68 (3 : k) h4
  have h5s := natDegree_smul_lt68 (3 : k) h5
  have h6s := natDegree_smul_lt68 (3 : k) h6
  have h7s := natDegree_smul_lt68 (2 : k) h7
  have h8s := natDegree_smul_lt68 (2 : k) h8
  have s1 := natDegree_add_lt68 h1 h2
  have s2 := natDegree_add_lt68 s1 h3s
  have s3 := natDegree_add_lt68 s2 h4s
  have s4 := natDegree_add_lt68 s3 h5s
  have s5 := natDegree_sub_lt68 s4 h6s
  have s6 := natDegree_sub_lt68 s5 h7s
  have s7 := natDegree_sub_lt68 s6 h8s
  have s8 := natDegree_sub_lt68 s7 h9
  change (Ulc * derivative c + Ulr * derivative C0 +
      (2 : k) • (Tl * derivative D) +
      (3 : k) • (Slc * derivative Er) +
      (3 : k) • (Slr * derivative E) -
      (3 : k) • (B * derivative Vl) -
      (2 : k) • (C0c * derivative Ulr) -
      (2 : k) • (c * derivative Ul) -
      D * derivative Tl).natDegree < _
  exact s8

end Max11DegreeRoutes
