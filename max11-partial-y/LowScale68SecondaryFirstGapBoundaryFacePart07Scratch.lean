import LowScale68SecondaryFirstGapBoundaryFacePart06Scratch

/-! # Residual faces on the first-gap boundary `2g = n`

The tracked classifier
`maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68`
already gives `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`2g = n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle invariants throughout `g < h < 2g`.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, while the
heaviest residual row-one load is `alpha A^3` against `C0'` at `10n-1`.
Both sit strictly below every displayed residual index on this wall, so
the next exact face is the ordinary middle pair rather than a new mixed
scalar system.  Closing the wall still needs the residual double / row-two
selector and the balanced row-one cubic scalar, supplied by
`LowScale68SecondaryFirstGapBoundary`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FirstGapBoundaryEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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


/-! ## Residual degree drops after the classified wall -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on the wall -/

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstLoadWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        11 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 0 alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he'
  have hSl : Sl.natDegree ≤ 3 * n - g := by simpa only [Sl] using hloads.1
  have hTl : Tl.natDegree ≤ 4 * n := by simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlC : (Ul * derivative C0).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hUl hC0 (by omega)
  have hTlD : (Tl * derivative D).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hTl hD (by omega)
  have hSlE : (Sl * derivative E).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hSl hE (by omega)
  have hBVl : (B * derivative Vl).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hB hVl (by omega)
  have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hC0 hUl (by omega)
  have hDTl : (D * derivative Tl).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hD hTl (by omega)
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
  exact leaf68_natDegree_sub_lt
        (leaf68_natDegree_sub_lt
          (leaf68_natDegree_sub_lt
            (leaf68_natDegree_add_lt
              (leaf68_natDegree_add_lt
                hUlC
                (leaf68_natDegree_smul_lt (2 : k)
                  hTlD))
              (leaf68_natDegree_smul_lt (3 : k)
                hSlE))
            (leaf68_natDegree_smul_lt (3 : k)
              hBVl))
          (leaf68_natDegree_smul_lt (2 : k)
            hC0Ul))
        hDTl

end FirstGapBoundaryEndgame68
end Max11DegreeRoutes
