import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroAllocationReductionScratch

/-! # Consuming the retained `H ∣ b₂ψ` split in R5, R6 and R8a

The AllocationReduction packet left a flat twenty-leaf inventory for
the `H ∣ r` lower-zero tree.  Exactly three of the `d/k`-allocation
leaves still carry the retained divisibility `H ∣ b₂ψ` next to their
core relations `b₂ψ = -6·Hᵉ·(w₂·d)`:

* **R5**, the exact `(3,1)` allocation `d₂ = H³d₇ ∧ k₁ = Hk₂ ∧
  d₇k₂ = m` with square-cored `b₂ψ = -6H²(w₂d₇)`;
* **R6**, the exact balanced `(2,2)` allocation `d₂ = H²d₅ ∧
  k₁ = H²k₃ ∧ d₅k₃ = m` with linear-cored `b₂ψ = -6H(w₂d₅)`;
* **R8a**, the first mixed transverse residual `d₂ = H²d₅ ∧ k₁ = Hk₂ ∧
  d₅k₂ = Hm` with linear-cored `b₂ψ = -6H(w₂d₅)` and its pinned
  root-pair orientation.

Here that retained split — and nothing else — is consumed.  At each of
the two simple core roots the core relation gives the order-zero face
`b₂ψ = 0`, so the two-root transfer resolves each of the three leaves
into the exclusive three-limb refinement

* **`H ∣ b₂` limb**: `b₂ = Hb₃` globally, the core de-cores by one `H`
  (`b₃ψ = -6H(w₂d₇)` on R5, fully de-cored `b₃ψ = -6(w₂d₅)` on R6 and
  R8a), with the descended order-zero root faces; on R8a the retained
  witness `d₅(y) = 0` further pins `b₃(y)ψ(y) = 0` with its exclusive
  factor split.
* **`H ∣ ψ` limb**: `ψ = Hψ₂` globally, so `φ₁ = H²ψ` descends to
  `φ₁ = H³ψ₂` with `H³ ∣ φ₁`, the core de-cores symmetrically, and on
  R8a the witness `d₅(y) = 0` pins `b₂(y)ψ₂(y) = 0` with its split.
* **transverse limb**: neither factor dies at both roots, so the
  per-root split orients exactly one `b₂`-dead and one `ψ`-dead root.
  On R5 and R6 the two orientations are *merged* into one canonical
  leaf by renaming the root pair (the remaining leaf data is
  root-symmetric); on R8a the pair `x, y` is already pinned by the
  `d/k` orientation (`k₂(x) = 0` versus `k₂(y) ≠ 0`), so both
  orientations remain, each with its reduced first-order tie.

In addition every refined leaf gains the branch-independent
first-differentiated face of its core relation at the roots
(`b₂'ψ + b₂ψ' = -6H'(w₂d₅)` for the linear cores, `= 0` for the square
core of R5); in the R5 transverse limb these reduce to the exact unit
pins `b₂'(x) = 0` and `ψ'(y) = 0`.  Only order-zero evaluations, the
one retained first-differentiated face of the core product, the
two-root transfer and exact cancellation by the nonzero `H` are used:
no new Taylor or coefficient row is opened, no `x`-degree bound is
invoked, and no leaf closes (every limb is witnessed).  The overlap
regime where `b₂` and `ψ` are both globally divisible is routed into
the `H ∣ b₂` limb, so the three limbs stay a genuine merge-free cover.

All seventeen other leaves, the root-pair witnesses, the `d/k`
allocation orientations, the `Q₃` quotient rows, the `T₃/U₁` ties and
every unit pin are transported verbatim and opaquely.  The residual is
the literal twenty-leaf disjunction below, with R5, R6 and R8a refined
in place; the next unused splits are the one-`H`-deep descents
`H ∣ b₃ψ` / `H ∣ b₂ψ₂` retained inside the R5 limbs and the untouched
transverse divisibilities `H ∣ d₃'k₂'` (R10), `H ∣ d₃'k₁'` and
`H ∣ d₃''k₁''` (R12). -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RDivisorLowerZeroBPsiSplitAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Resolve a product face vanishing at both simple roots of a
degree-two core into the two global divisibilities or an exact
transverse orientation on the given root pair. -/
theorem rDivisorBPsiSplit_resolve_68
    (H b2 psi : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (x y : k) (hxy : x ≠ y) (hx : H.eval x = 0) (hy : H.eval y = 0)
    (hpx : b2.eval x * psi.eval x = 0)
    (hpy : b2.eval y * psi.eval y = 0) :
    H ∣ b2 ∨ H ∣ psi ∨
      ((b2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
          b2.eval y ≠ 0 ∧ psi.eval y = 0) ∨
        (b2.eval x ≠ 0 ∧ psi.eval x = 0 ∧
          b2.eval y = 0 ∧ psi.eval y ≠ 0)) := by
  by_cases hbx : b2.eval x = 0
  · by_cases hby : b2.eval y = 0
    · exact Or.inl (rDivisorSeventh_dvd_of_two_root_evals_68 H b2 hdeg
        hsimple x y hxy hx hy hbx hby)
    · have hpy0 : psi.eval y = 0 :=
        (mul_eq_zero.mp hpy).resolve_left hby
      by_cases hpsix : psi.eval x = 0
      · exact Or.inr (Or.inl
          (rDivisorSeventh_dvd_of_two_root_evals_68 H psi hdeg
            hsimple x y hxy hx hy hpsix hpy0))
      · exact Or.inr (Or.inr (Or.inl ⟨hbx, hpsix, hby, hpy0⟩))
  · have hpx0 : psi.eval x = 0 :=
      (mul_eq_zero.mp hpx).resolve_left hbx
    by_cases hby : b2.eval y = 0
    · by_cases hpsiy : psi.eval y = 0
      · exact Or.inr (Or.inl
          (rDivisorSeventh_dvd_of_two_root_evals_68 H psi hdeg
            hsimple x y hxy hx hy hpx0 hpsiy))
      · exact Or.inr (Or.inr (Or.inr ⟨hbx, hpx0, hby, hpsiy⟩))
    · have hpy0 : psi.eval y = 0 :=
        (mul_eq_zero.mp hpy).resolve_left hby
      exact Or.inr (Or.inl
        (rDivisorSeventh_dvd_of_two_root_evals_68 H psi hdeg
          hsimple x y hxy hx hy hpx0 hpy0))

/-- Order-zero and first-differentiated faces of a linear-cored
`b₂ψ = -6H(w·d)` relation at a core root. -/
theorem rDivisorBPsiLinearCore_faces_68 (H b2 psi w d : k[X]) (a : k)
    (ha : H.eval a = 0)
    (hbpsi : b2 * psi = -(6 : k[X]) * (H * (w * d))) :
    b2.eval a * psi.eval a = 0 ∧
      b2.derivative.eval a * psi.eval a +
        b2.eval a * psi.derivative.eval a =
        -(6 : k) * (H.derivative.eval a * (w.eval a * d.eval a)) := by
  have hshape : b2 * psi = H * (-(6 : k[X]) * (w * d)) := by
    rw [hbpsi]; ring
  constructor
  · have h := congrArg (fun P : k[X] => P.eval a) hbpsi
    simp only [eval_mul, eval_neg, eval_ofNat] at h
    linear_combination h - 6 * (w.eval a * d.eval a) * ha
  · have h := linearCore_first_face_68 H b2 psi
      (-(6 : k[X]) * (w * d)) a ha hshape
    simp only [eval_mul, eval_neg, eval_ofNat] at h
    linear_combination h

/-- Order-zero and first-differentiated faces of a square-cored
`b₂ψ = -6H²(w·d)` relation at a core root: both vanish. -/
theorem rDivisorBPsiSquareCore_faces_68 (H b2 psi w d : k[X]) (a : k)
    (ha : H.eval a = 0)
    (hbpsi : b2 * psi = -(6 : k[X]) * (H ^ 2 * (w * d))) :
    b2.eval a * psi.eval a = 0 ∧
      b2.derivative.eval a * psi.eval a +
        b2.eval a * psi.derivative.eval a = 0 := by
  have hshape : b2 * psi = H * (-(6 : k[X]) * (H * (w * d))) := by
    rw [hbpsi]; ring
  constructor
  · have h := congrArg (fun P : k[X] => P.eval a) hbpsi
    simp only [eval_mul, eval_neg, eval_ofNat, eval_pow] at h
    linear_combination h - 6 * (H.eval a * (w.eval a * d.eval a)) * ha
  · have h := linearCore_first_face_68 H b2 psi
      (-(6 : k[X]) * (H * (w * d))) a ha hshape
    simp only [eval_mul, eval_neg, eval_ofNat] at h
    linear_combination
      h - 6 * (H.derivative.eval a * (w.eval a * d.eval a)) * ha

end RDivisorLowerZeroBPsiSplitAlgebra68

section RDivisorLowerZeroBPsiSplitSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Consumption of the retained `H ∣ b₂ψ` split inside the residuals
R5, R6 and R8a of the allocated `H ∣ r` lower-zero tree: each of the
three leaves is refined in place by the exclusive three-limb cover
`H ∣ b₂` (core de-cored by one `H`) / `H ∣ ψ` (with `φ₁ = H³ψ₂`) /
transverse orientation, together with the branch-independent
order-zero and first-differentiated faces of its core relation.  The
two transverse orientations of R5 and R6 merge under the canonical
root renaming; on R8a both orientations stay pinned against the
retained `d/k` witnesses, and the `d₅(y) = 0` witness adds the exact
factor split of the de-cored product at `y`.  Every other leaf,
root-pair witness, allocation orientation, quotient row and unit pin
is transported verbatim; no leaf closes. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorLowerZeroBPsiSplitReductionPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X Yd phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      ((∃ s t1 y1 A1 c2 e3 psi m : k[X],
          r = H * s ∧
          t = H * t1 ∧
          (3 : k[X]) * t1 = H * s ^ 2 + X ∧
          p.coeff 4 = H ^ 2 * t1 ∧
          p.coeff 3 = H * y1 ∧
          (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd ∧
          H ∣ t ∧ H ^ 2 ∣ p.coeff 4 ∧ H ∣ p.coeff 3 ∧
          A1 = t1 - C (5 / 12 : k) * H * s ^ 2 ∧
          cubicANumerator68 t r = H * A1 ∧
          c2 = C (1 / 3 : k) * A1 ^ 2 + C (9 / 4 : k) * w2 -
            C (3 / 2 * S.gamma : k) ∧
          cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r = H ^ 2 * c2 ∧
          e3 = p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
              C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
              C (1 / 216 : k) * H * y1 * s ^ 3 +
              C (1 / 1296 : k) * H ^ 2 * t1 * s ^ 4 -
              C (5 / 46656 : k) * H ^ 3 * s ^ 6 ∧
          cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r = H ^ 3 * e3 ∧
          terminalEDerivativeNumerator68 H
              (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
                (p.coeff 3) t r) = H ^ 4 * e3.derivative ∧
          psi = rDivisorLowerZeroPhiQuotient68 H A1 b2 c2 e3
            S.gamma S.epsilon ∧
          phi1 = H ^ 2 * psi ∧
          H ^ 2 ∣ phi1 ∧ H ∣ phi1 ∧
          w2 * d2 = -(C (1 / 6 : k)) * (H * b2 * psi) ∧
          H ∣ w2 * d2 ∧
          terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * b2)
            (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) (H * d2)
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r)
            S.alpha S.gamma S.epsilon S.eta = 0 ∧
          terminalLowerZeroCleared68 H (H * A1) (H * b2) (H ^ 2 * c2)
            (H * d2) (H ^ 3 * e3) S.alpha S.gamma S.epsilon S.eta =
            H ^ 4 * rDivisorLowerZeroQuotient68 H A1 b2 c2 d2 e3
              S.alpha S.gamma S.epsilon S.eta ∧
          rDivisorLowerZeroQuotient68 H A1 b2 c2 d2 e3
            S.alpha S.gamma S.epsilon S.eta = 0 ∧
          H ∣ d2 * psi ∧
          (∀ a : k, H.eval a = 0 →
            (w2 * d2).eval a = 0 ∧ (d2 * psi).eval a = 0 ∧
              d2.eval a * k1.eval a = 0) ∧
          m = H * b2 * w2 * e3.derivative - C j ∧
          d2 * k1 = H ^ 4 * m ∧
          H ^ 4 ∣ d2 * k1 ∧
          (∀ a : k, H.eval a = 0 → m.eval a = -j ∧ m.eval a ≠ 0) ∧
          d2 ≠ 0 ∧ k1 ≠ 0 ∧
          ((∃ d3 d4 b3 : k[X],
              d2 = H * d3 ∧ d3 = H * d4 ∧ d2 = H ^ 2 * d4 ∧
              b2 = H * b3 ∧ H ∣ b2 ∧
              b3 * psi = -(6 : k[X]) * (w2 * d4) ∧
              d4 * k1 = H ^ 2 * m ∧ d4 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                b2.eval a = 0 ∧
                b3.eval a * psi.eval a =
                  -(6 : k) * (w2.eval a * d4.eval a) ∧
                d4.eval a * k1.eval a = 0 ∧
                c2.eval a * (b2.eval a * w2.eval a) = 0 ∧
                d4.derivative.eval a * k1.eval a +
                  d4.eval a * k1.derivative.eval a = 0 ∧
                d4.derivative.derivative.eval a * k1.eval a +
                  2 * (d4.derivative.eval a * k1.derivative.eval a) +
                  d4.eval a * k1.derivative.derivative.eval a =
                  -(2 * j) * H.derivative.eval a ^ 2 ∧
                b2.derivative.eval a * psi.eval a +
                  b2.eval a * psi.derivative.eval a =
                  -(6 : k) *
                    (H.derivative.eval a *
                      (w2.eval a * d4.eval a)))) ∨
            (∃ psi2 d3 D : k[X],
              psi = H * psi2 ∧ H ∣ psi ∧
              phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              d2 = H * d3 ∧ d3 = H * D ∧ d2 = H ^ 2 * D ∧
              b2 * psi2 = -(6 : k[X]) * (w2 * D) ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              D * k1 = H ^ 2 * m ∧ D ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧ d3.eval a = 0 ∧
                b2.eval a * psi2.eval a =
                  -(6 : k) * (w2.eval a * D.eval a) ∧
                D.eval a * k1.eval a = 0 ∧
                c2.eval a *
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval a = 0) ∧
              ((∀ a : k, H.eval a = 0 →
                  D.derivative.eval a * k1.eval a +
                    D.eval a * k1.derivative.eval a = 0 ∧
                  D.derivative.derivative.eval a * k1.eval a +
                    2 * (D.derivative.eval a * k1.derivative.eval a) +
                    D.eval a * k1.derivative.derivative.eval a =
                    -(2 * j) * H.derivative.eval a ^ 2 ∧
                  b2.derivative.eval a * psi.eval a +
                    b2.eval a * psi.derivative.eval a =
                    -(6 : k) *
                      (H.derivative.eval a *
                        (w2.eval a * D.eval a))) ∨
                (∀ a : k, H.eval a = 0 →
                  d3.derivative.eval a * k1.eval a +
                    d3.eval a * k1.derivative.eval a = 0 ∧
                  d3.derivative.derivative.eval a * k1.eval a +
                    2 * (d3.derivative.eval a *
                      k1.derivative.eval a) +
                    d3.eval a * k1.derivative.derivative.eval a = 0 ∧
                  w2.derivative.eval a * d3.eval a +
                    w2.eval a * d3.derivative.eval a =
                    -(1 / 6 : k) *
                      (H.derivative.eval a *
                        (b2.eval a * psi2.eval a))))) ∨
            (∃ psi2 w3 w4 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧ w3 = H * w4 ∧ w2 = H ^ 2 * w4 ∧
              w4 * d2 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧ w2.eval a = 0 ∧ w3.eval a = 0 ∧
                w2.derivative.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0 ∧
                d2.eval a * k1.eval a = 0)) ∨
            (∃ psi2 w3 d3 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧ d2 = H * d3 ∧ d3 ≠ 0 ∧
              w3 * d3 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
              d3 * k1 = H ^ 3 * m ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧ w2.eval a = 0 ∧ d2.eval a = 0 ∧
                d3.eval a * k1.eval a = 0 ∧
                (rDivisorLowerZeroTThree68 H A1 b2 c2 e3
                    S.alpha S.gamma S.epsilon).eval a * d3.eval a =
                  c2.eval a *
                    (rDivisorDTwoUOne68 A1 b2 c2 d3
                      S.alpha S.gamma).eval a ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0) ∧
              ((∀ a : k, H.eval a = 0 →
                  w2.derivative.eval a =
                    H.derivative.eval a * w3.eval a ∧
                  w3.derivative.eval a * d2.eval a +
                    w3.eval a * d2.derivative.eval a =
                    -(1 / 6 : k) *
                      (H.derivative.eval a *
                        (b2.eval a * psi2.eval a)) ∧
                  d2.derivative.eval a * k1.eval a +
                    d2.eval a * k1.derivative.eval a = 0) ∨
                (∀ a : k, H.eval a = 0 →
                  d3.derivative.eval a * k1.eval a +
                    d3.eval a * k1.derivative.eval a = 0 ∧
                  d3.derivative.derivative.eval a * k1.eval a +
                    2 * (d3.derivative.eval a *
                      k1.derivative.eval a) +
                    d3.eval a * k1.derivative.derivative.eval a = 0 ∧
                  w2.derivative.eval a * d3.eval a +
                    w2.eval a * d3.derivative.eval a =
                    -(1 / 6 : k) *
                      (H.derivative.eval a *
                        (b2.eval a * psi2.eval a))))) ∨
            (∃ d3 k2 d5 d7 : k[X],
              d2 = H * d3 ∧ d3 = H * d5 ∧ d5 = H * d7 ∧
              d2 = H ^ 3 * d7 ∧ k1 = H * k2 ∧
              d7 * k2 = m ∧
              d7 * k2 + C j = H * b2 * w2 * e3.derivative ∧
              b2 * psi = -(6 : k[X]) * (H ^ 2 * (w2 * d7)) ∧
              H ∣ b2 * psi ∧ d7 ≠ 0 ∧ k2 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                d7.eval a * k2.eval a = -j ∧
                d7.eval a ≠ 0 ∧ k2.eval a ≠ 0 ∧
                d3.derivative.eval a = 0 ∧
                d3.derivative.derivative.eval a * k2.eval a =
                  -(2 * j) * H.derivative.eval a ^ 2 ∧
                d3.derivative.derivative.eval a ≠ 0) ∧
              (∀ a : k, H.eval a = 0 →
                b2.eval a * psi.eval a = 0 ∧
                b2.derivative.eval a * psi.eval a +
                  b2.eval a * psi.derivative.eval a = 0) ∧
              ((∃ b3 : k[X],
                  b2 = H * b3 ∧ H ∣ b2 ∧
                  b3 * psi = -(6 : k[X]) * (H * (w2 * d7)) ∧
                  H ∣ b3 * psi ∧
                  (∀ a : k, H.eval a = 0 →
                    b2.eval a = 0 ∧
                    b3.eval a * psi.eval a = 0)) ∨
                (∃ psi2 : k[X],
                  psi = H * psi2 ∧ H ∣ psi ∧
                  phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
                  b2 * psi2 = -(6 : k[X]) * (H * (w2 * d7)) ∧
                  H ∣ b2 * psi2 ∧
                  (∀ a : k, H.eval a = 0 →
                    psi.eval a = 0 ∧
                    b2.eval a * psi2.eval a = 0)) ∨
                (∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                  b2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
                  b2.eval y ≠ 0 ∧ psi.eval y = 0 ∧
                  b2.derivative.eval x = 0 ∧
                  psi.derivative.eval y = 0))) ∨
            (∃ d3 k2 d5 k3 : k[X],
              d2 = H * d3 ∧ d3 = H * d5 ∧ d2 = H ^ 2 * d5 ∧
              k1 = H * k2 ∧ k2 = H * k3 ∧ k1 = H ^ 2 * k3 ∧
              d5 * k3 = m ∧
              d5 * k3 + C j = H * b2 * w2 * e3.derivative ∧
              b2 * psi = -(6 : k[X]) * (H * (w2 * d5)) ∧
              H ∣ b2 * psi ∧ d5 ≠ 0 ∧ k3 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                d5.eval a * k3.eval a = -j ∧
                d5.eval a ≠ 0 ∧ k3.eval a ≠ 0 ∧
                d3.derivative.eval a * k2.derivative.eval a =
                  -j * H.derivative.eval a ^ 2 ∧
                d3.derivative.eval a ≠ 0 ∧
                k2.derivative.eval a ≠ 0) ∧
              (∀ a : k, H.eval a = 0 →
                b2.eval a * psi.eval a = 0 ∧
                b2.derivative.eval a * psi.eval a +
                  b2.eval a * psi.derivative.eval a =
                  -(6 : k) *
                    (H.derivative.eval a *
                      (w2.eval a * d5.eval a))) ∧
              ((∃ b3 : k[X],
                  b2 = H * b3 ∧ H ∣ b2 ∧
                  b3 * psi = -(6 : k[X]) * (w2 * d5) ∧
                  (∀ a : k, H.eval a = 0 →
                    b2.eval a = 0 ∧
                    b3.eval a * psi.eval a =
                      -(6 : k) * (w2.eval a * d5.eval a))) ∨
                (∃ psi2 : k[X],
                  psi = H * psi2 ∧ H ∣ psi ∧
                  phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
                  b2 * psi2 = -(6 : k[X]) * (w2 * d5) ∧
                  (∀ a : k, H.eval a = 0 →
                    psi.eval a = 0 ∧
                    b2.eval a * psi2.eval a =
                      -(6 : k) * (w2.eval a * d5.eval a))) ∨
                (∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                  b2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
                  b2.eval y ≠ 0 ∧ psi.eval y = 0 ∧
                  b2.derivative.eval x * psi.eval x =
                    -(6 : k) *
                      (H.derivative.eval x *
                        (w2.eval x * d5.eval x)) ∧
                  b2.eval y * psi.derivative.eval y =
                    -(6 : k) *
                      (H.derivative.eval y *
                        (w2.eval y * d5.eval y))))) ∨
            (∃ d3 k2 k3 k4 : k[X],
              d2 = H * d3 ∧ k1 = H * k2 ∧ k2 = H * k3 ∧
              k3 = H * k4 ∧ k1 = H ^ 3 * k4 ∧
              d3 * k4 = m ∧
              d3 * k4 + C j = H * b2 * w2 * e3.derivative ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 ≠ 0 ∧ k4 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                d3.eval a * k4.eval a = -j ∧
                d3.eval a ≠ 0 ∧ k4.eval a ≠ 0 ∧
                k2.derivative.eval a = 0 ∧
                d3.eval a * k2.derivative.derivative.eval a =
                  -(2 * j) * H.derivative.eval a ^ 2 ∧
                k2.derivative.derivative.eval a ≠ 0)) ∨
            (∃ d3 k2 d5 : k[X],
              d2 = H * d3 ∧ d3 = H * d5 ∧ d2 = H ^ 2 * d5 ∧
              k1 = H * k2 ∧
              d5 * k2 = H * m ∧
              b2 * psi = -(6 : k[X]) * (H * (w2 * d5)) ∧
              H ∣ b2 * psi ∧ d5 ≠ 0 ∧ k2 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                b2.eval a * psi.eval a = 0 ∧
                b2.derivative.eval a * psi.eval a +
                  b2.eval a * psi.derivative.eval a =
                  -(6 : k) *
                    (H.derivative.eval a *
                      (w2.eval a * d5.eval a))) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                k2.eval x = 0 ∧
                d3.derivative.eval x * k2.derivative.eval x =
                  -j * H.derivative.eval x ^ 2 ∧
                d3.derivative.eval x ≠ 0 ∧
                k2.derivative.eval x ≠ 0 ∧
                k2.eval y ≠ 0 ∧ d5.eval y = 0 ∧
                d3.derivative.eval y = 0 ∧
                d3.derivative.derivative.eval y * k2.eval y =
                  -(2 * j) * H.derivative.eval y ^ 2 ∧
                d3.derivative.derivative.eval y ≠ 0 ∧
                ((∃ b3 : k[X],
                    b2 = H * b3 ∧ H ∣ b2 ∧
                    b3 * psi = -(6 : k[X]) * (w2 * d5) ∧
                    b3.eval y * psi.eval y = 0 ∧
                    (b3.eval y = 0 ∨ psi.eval y = 0) ∧
                    (∀ a : k, H.eval a = 0 →
                      b2.eval a = 0 ∧
                      b3.eval a * psi.eval a =
                        -(6 : k) * (w2.eval a * d5.eval a))) ∨
                  (∃ psi2 : k[X],
                    psi = H * psi2 ∧ H ∣ psi ∧
                    phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
                    b2 * psi2 = -(6 : k[X]) * (w2 * d5) ∧
                    b2.eval y * psi2.eval y = 0 ∧
                    (b2.eval y = 0 ∨ psi2.eval y = 0) ∧
                    (∀ a : k, H.eval a = 0 →
                      psi.eval a = 0 ∧
                      b2.eval a * psi2.eval a =
                        -(6 : k) * (w2.eval a * d5.eval a))) ∨
                  ((b2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
                      b2.eval y ≠ 0 ∧ psi.eval y = 0 ∧
                      b2.derivative.eval x * psi.eval x =
                        -(6 : k) *
                          (H.derivative.eval x *
                            (w2.eval x * d5.eval x)) ∧
                      b2.eval y * psi.derivative.eval y =
                        -(6 : k) *
                          (H.derivative.eval y *
                            (w2.eval y * d5.eval y))) ∨
                    (b2.eval x ≠ 0 ∧ psi.eval x = 0 ∧
                      b2.eval y = 0 ∧ psi.eval y ≠ 0 ∧
                      b2.eval x * psi.derivative.eval x =
                        -(6 : k) *
                          (H.derivative.eval x *
                            (w2.eval x * d5.eval x)) ∧
                      b2.derivative.eval y * psi.eval y =
                        -(6 : k) *
                          (H.derivative.eval y *
                            (w2.eval y * d5.eval y)))))) ∨
            (∃ d3 k2 k3 : k[X],
              d2 = H * d3 ∧ k1 = H * k2 ∧ k2 = H * k3 ∧
              k1 = H ^ 2 * k3 ∧
              d3 * k3 = H * m ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 ≠ 0 ∧ k3 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                d3.eval x = 0 ∧
                d3.derivative.eval x * k2.derivative.eval x =
                  -j * H.derivative.eval x ^ 2 ∧
                d3.derivative.eval x ≠ 0 ∧
                k2.derivative.eval x ≠ 0 ∧
                d3.eval y ≠ 0 ∧ k3.eval y = 0 ∧
                k2.derivative.eval y = 0 ∧
                d3.eval y * k2.derivative.derivative.eval y =
                  -(2 * j) * H.derivative.eval y ^ 2 ∧
                k2.derivative.derivative.eval y ≠ 0) ∨
            (∃ d3 k2 : k[X],
              d2 = H * d3 ∧ k1 = H * k2 ∧ d3 * k2 = H ^ 2 * m ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 ≠ 0 ∧ k2 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                d3.eval x = 0 ∧ k2.eval x ≠ 0 ∧
                d3.eval y ≠ 0 ∧ k2.eval y = 0 ∧
                d3.derivative.eval x = 0 ∧
                d3.derivative.derivative.eval x * k2.eval x =
                  -(2 * j) * H.derivative.eval x ^ 2 ∧
                d3.derivative.derivative.eval x ≠ 0 ∧
                k2.derivative.eval y = 0 ∧
                d3.eval y * k2.derivative.derivative.eval y =
                  -(2 * j) * H.derivative.eval y ^ 2 ∧
                k2.derivative.derivative.eval y ≠ 0 ∧
                H ∣ d3.derivative * k2.derivative) ∨
            (∃ d3 d4 : k[X],
              d2 = H * d3 ∧ d3 = H * d4 ∧ d2 = H ^ 2 * d4 ∧
              b2 * psi = -(6 : k[X]) * (H * (w2 * d4)) ∧
              H ∣ b2 * psi ∧
              d4 * k1 = H ^ 2 * m ∧ d4 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                b2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
                b2.eval y ≠ 0 ∧ psi.eval y = 0 ∧
                b2.derivative.eval x * psi.eval x =
                  -(6 : k) *
                    (H.derivative.eval x *
                      (w2.eval x * d4.eval x)) ∧
                b2.eval y * psi.derivative.eval y =
                  -(6 : k) *
                    (H.derivative.eval y *
                      (w2.eval y * d4.eval y)) ∧
                (c2.eval y = 0 ∨ w2.eval y = 0)) ∨
            (∃ d3 : k[X],
              d2 = H * d3 ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 * k1 = H ^ 3 * m ∧ d3 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
                d3.eval a = 0 ∧ k1.eval a ≠ 0 ∧
                d3.eval b ≠ 0 ∧ k1.eval b = 0 ∧
                d3.derivative.eval a = 0 ∧
                d3.derivative.derivative.eval a = 0 ∧
                b2.eval a * psi.eval a = 0 ∧
                k1.derivative.eval b = 0 ∧
                k1.derivative.derivative.eval b = 0 ∧
                d3.derivative.derivative.derivative.eval a *
                    k1.eval a =
                  -(6 * j) * H.derivative.eval a ^ 3 ∧
                d3.derivative.derivative.derivative.eval a ≠ 0 ∧
                d3.eval b *
                    k1.derivative.derivative.derivative.eval b =
                  -(6 * j) * H.derivative.eval b ^ 3 ∧
                k1.derivative.derivative.derivative.eval b ≠ 0 ∧
                H ∣ d3.derivative * k1.derivative ∧
                H ∣ d3.derivative.derivative *
                  k1.derivative.derivative ∧
                (b2.eval a = 0 ∨ psi.eval a = 0) ∧
                (c2.eval a = 0 ∨
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval a = 0) ∧
                b2.eval b * psi.eval b =
                  -(6 : k) * (w2.eval b * d3.eval b)) ∨
            (∃ psi2 w3 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧
              w3 * d2 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                w2.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w3.eval x = 0 ∧ d2.eval x ≠ 0 ∧
                w3.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                w3.derivative.eval x * d2.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                w2.derivative.eval y ≠ 0 ∧
                w3.eval y * d2.derivative.eval y =
                  -(1 / 6 : k) *
                    (H.derivative.eval y *
                      (b2.eval y * psi2.eval y)) ∧
                d2.derivative.eval y = 0 ∧
                b2.eval y * psi2.eval y = 0 ∧
                (b2.eval y = 0 ∨ psi2.eval y = 0)) ∨
            (∃ psi2 w3 k2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧
              w3 * d2 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                w2.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0) ∧
              k1 = H * k2 ∧ k2 ≠ 0 ∧ d2 * k2 = H ^ 3 * m ∧
              (∀ a : k, H.eval a = 0 →
                d2.eval a * k2.eval a = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w3.eval x = 0 ∧ d2.eval x ≠ 0 ∧ k2.eval x = 0 ∧
                w3.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                d2.derivative.eval y ≠ 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.eval y = 0 ∧
                w2.derivative.eval y ≠ 0 ∧
                w3.derivative.eval x * d2.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                w3.eval y * d2.derivative.eval y =
                  -(1 / 6 : k) *
                    (H.derivative.eval y *
                      (b2.eval y * psi2.eval y))) ∨
            (∃ psi2 d3 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              d2 = H * d3 ∧ d3 ≠ 0 ∧
              w2 * d3 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              d3 * k1 = H ^ 3 * m ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d3.eval x ≠ 0 ∧
                w2.eval y ≠ 0 ∧ d3.eval y = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                w2.derivative.eval x * d3.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                (c2.eval y = 0 ∨
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval y = 0) ∧
                d3.derivative.eval y = 0 ∧
                b2.eval y * psi2.eval y = 0 ∧
                (b2.eval y = 0 ∨ psi2.eval y = 0) ∧
                d3.derivative.derivative.eval y * k1.eval y = 0) ∨
            (∃ psi2 d3 k2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              d2 = H * d3 ∧ k1 = H * k2 ∧ d3 * k2 = H ^ 2 * m ∧
              w2 * d3 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              d3 ≠ 0 ∧ k2 ≠ 0 ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                d3.eval a * k2.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d3.eval x ≠ 0 ∧ k2.eval x = 0 ∧
                w2.eval y ≠ 0 ∧ d3.eval y = 0 ∧
                d3.derivative.eval y ≠ 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                k1.eval y = 0 ∧ k1.derivative.eval y = 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                w2.derivative.eval x * d3.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                (c2.eval y = 0 ∨
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval y = 0)) ∨
            (∃ psi2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d2.eval x ≠ 0 ∧
                w2.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                k1.derivative.derivative.derivative.eval x = 0 ∧
                d2.eval x *
                    k1.derivative.derivative.derivative.derivative.eval
                      x =
                  -(24 * j) * H.derivative.eval x ^ 4 ∧
                k1.derivative.derivative.derivative.derivative.eval
                    x ≠ 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                d2.derivative.eval y = 0 ∧
                d2.derivative.derivative.eval y = 0 ∧
                b2.eval y * psi2.eval y = 0 ∧
                (b2.eval y = 0 ∨ psi2.eval y = 0) ∧
                d2.derivative.derivative.derivative.eval y *
                  k1.eval y = 0 ∧
                (d2.derivative.derivative.derivative.eval y = 0 ∨
                  k1.eval y = 0) ∧
                H ∣ w2 * d2.derivative ∧
                H ∣ k1 * d2.derivative) ∨
            (∃ psi2 k2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              k1 = H * k2 ∧ k2 ≠ 0 ∧ d2 * k2 = H ^ 3 * m ∧
              (∀ a : k, H.eval a = 0 →
                d2.eval a * k2.eval a = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d2.eval x ≠ 0 ∧ k2.eval x = 0 ∧
                w2.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                d2.derivative.eval y = 0 ∧
                d2.derivative.derivative.eval y ≠ 0 ∧
                b2.eval y ≠ 0 ∧ psi2.eval y ≠ 0 ∧
                k1.eval y = 0 ∧ k1.derivative.eval y = 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                k1.derivative.derivative.derivative.eval x = 0 ∧
                d2.eval x *
                    k1.derivative.derivative.derivative.derivative.eval
                      x =
                  -(24 * j) * H.derivative.eval x ^ 4 ∧
                k1.derivative.derivative.derivative.derivative.eval
                    x ≠ 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                w2.eval y * d2.derivative.derivative.eval y =
                  -(1 / 3 : k) * (H.derivative.eval y ^ 2 *
                    (b2.eval y * psi2.eval y)) ∧
                H ∣ w2 * d2.derivative ∧
                H ∣ k1 * d2.derivative) ∨
            (∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
              d2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
              d2.eval y ≠ 0 ∧ psi.eval y = 0 ∧
              d2.derivative.eval x = 0 ∧ b2.eval x = 0 ∧
              w2.eval y = 0 ∧ k1.eval y = 0 ∧
              w2.derivative.eval y = 0 ∧ k1.derivative.eval y = 0 ∧
              k1.derivative.derivative.eval y = 0 ∧
              k1.derivative.derivative.derivative.eval y = 0 ∧
              (4 / 3 : k) * e3.eval y -
                  (4 / 81 : k) * A1.eval y ^ 3 +
                  2 / 3 * S.gamma * A1.eval y + S.epsilon = 0 ∧
              d2.eval y *
                  k1.derivative.derivative.derivative.derivative.eval
                    y =
                -(24 * j) * H.derivative.eval y ^ 4 ∧
              k1.derivative.derivative.derivative.derivative.eval
                  y ≠ 0 ∧
              w2.derivative.derivative.eval y * d2.eval y =
                -(1 / 3 : k) * (H.derivative.eval y * b2.eval y *
                  psi.derivative.eval y) ∧
              d2.derivative.derivative.eval x * k1.eval x = 0 ∧
              (d2.derivative.derivative.eval x = 0 ∨
                k1.eval x = 0) ∧
              d2.derivative.derivative.derivative.eval x *
                  k1.eval x +
                3 * (d2.derivative.derivative.eval x *
                  k1.derivative.eval x) = 0 ∧
              H ∣ d2 * k1.derivative ∧ H ∣ d2 * w2.derivative) ∨
            (∃ k2 : k[X],
              k1 = H * k2 ∧ k2 ≠ 0 ∧ d2 * k2 = H ^ 3 * m ∧
              (∀ a : k, H.eval a = 0 →
                d2.eval a * k2.eval a = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                d2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
                d2.eval y ≠ 0 ∧ psi.eval y = 0 ∧ k2.eval y = 0 ∧
                d2.derivative.eval x ≠ 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                w2.eval y = 0 ∧ k1.eval y = 0 ∧
                w2.derivative.eval y = 0 ∧
                k1.derivative.eval y = 0 ∧
                k1.derivative.derivative.eval y = 0 ∧
                k1.derivative.derivative.derivative.eval y = 0 ∧
                (4 / 3 : k) * e3.eval y -
                    (4 / 81 : k) * A1.eval y ^ 3 +
                    2 / 3 * S.gamma * A1.eval y + S.epsilon = 0 ∧
                d2.eval y *
                    k1.derivative.derivative.derivative.derivative.eval
                      y =
                  -(24 * j) * H.derivative.eval y ^ 4 ∧
                k1.derivative.derivative.derivative.derivative.eval
                    y ≠ 0 ∧
                w2.derivative.derivative.eval y * d2.eval y =
                  -(1 / 3 : k) * (H.derivative.eval y * b2.eval y *
                    psi.derivative.eval y) ∧
                H ∣ d2 * k1.derivative ∧
                H ∣ d2 * w2.derivative))) ∨
        H ∣ phi1 ∨
        (let A0 := cubicANumerator68 t r
         let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
         let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
           (p.coeff 3) t r
         let eDot := terminalEDerivativeNumerator68 H E0
         ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
           r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
           r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
           b2.eval a = 0 ∧
           b2.derivative.eval a * phi1.eval a +
             6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
           (d2.eval a = 0 ∨ k1.eval a = 0) ∧
           H.derivative.eval a * b2.eval a * w2.eval a * eDot.eval a -
             (d2.derivative.eval a * k1.eval a +
               d2.eval a * k1.derivative.eval a) = 0 ∧
           b2.eval b * phi1.derivative.eval b +
             6 * H.derivative.eval b * w2.eval b * d2.eval b = 0 ∧
           H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b -
             (d2.derivative.eval b * k1.eval b +
               d2.eval b * k1.derivative.eval b) = 0 ∧
           (d2.eval b = 0 ∨ k1.eval b = 0))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hbranch⟩ :=
    S.terminalAfterLowerOneRDivisorLowerZeroAllocationReductionPacket
      (H := H) hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow, ?_⟩
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  obtain ⟨u, v, huv, hu, hv⟩ :=
    rDivisorReduction_root_pair_exists_68 H hdeg hsimple
  rcases hbranch with hmain | hphiDvd | htrans
  · left
    obtain ⟨s, t1, y1, A1, c2, e3, psi, m, hs, ht1c, ht1sc, hp4sc,
        hy1c, hy1sc, hdvdt, hdvdp4, hdvdp3, hA1def, hAf, hc2def, hCf,
        he3def, hEf, heDot, hpsidef, hphi2, hphidvd2, hphidvd1, hwd,
        hwddvd, hlowerB, hrowfact, hQ0, hdpsi, hfaces, hmdef, hdk,
        hdkdvd, hval, hd2ne, hk1ne, hsplit3⟩ := hmain
    refine ⟨s, t1, y1, A1, c2, e3, psi, m, hs, ht1c, ht1sc, hp4sc,
      hy1c, hy1sc, hdvdt, hdvdp4, hdvdp3, hA1def, hAf, hc2def, hCf,
      he3def, hEf, heDot, hpsidef, hphi2, hphidvd2, hphidvd1, hwd,
      hwddvd, hlowerB, hrowfact, hQ0, hdpsi, hfaces, hmdef, hdk,
      hdkdvd, hval, hd2ne, hk1ne, ?_⟩
    rcases hsplit3 with hL1 | hL2 | hL3 | hL4 | hL5 | hL6 | hL7 | hL8 |
      hL9 | hL10 | hL11 | hL12 | hL13 | hL14 | hL15 | hL16 | hL17 |
      hL18 | hL19 | hL20
    · -- R1: transported verbatim.
      exact Or.inl hL1
    · -- R2: transported verbatim.
      iterate 1 right
      left
      exact hL2
    · -- R3: transported verbatim.
      iterate 2 right
      left
      exact hL3
    · -- R4: transported verbatim.
      iterate 3 right
      left
      exact hL4
    · -- R5: consume the retained `H ∣ b₂ψ` split of the square-cored
      -- exact `(3,1)` allocation.
      obtain ⟨d3, k2, d5, d7, hd3, hd5c, hd7c, hd2d7, hk2, hd7k2,
          hsrc, hbpsi, hbpsidvd, hd7ne, hk2ne, hQ3, hfaces5⟩ := hL5
      have hfaces0 : ∀ a : k, H.eval a = 0 →
          b2.eval a * psi.eval a = 0 ∧
            b2.derivative.eval a * psi.eval a +
              b2.eval a * psi.derivative.eval a = 0 :=
        fun a ha =>
          rDivisorBPsiSquareCore_faces_68 H b2 psi w2 d7 a ha hbpsi
      iterate 4 right
      left
      refine ⟨d3, k2, d5, d7, hd3, hd5c, hd7c, hd2d7, hk2, hd7k2,
        hsrc, hbpsi, hbpsidvd, hd7ne, hk2ne, hQ3, hfaces5,
        hfaces0, ?_⟩
      rcases rDivisorBPsiSplit_resolve_68 H b2 psi hdeg hsimple u v
          huv hu hv (hfaces0 u hu).1 (hfaces0 v hv).1 with
        hdvdb | hdvdpsi | horient
      · -- `H ∣ b₂` limb: de-core one `H`.
        obtain ⟨b3, hb3⟩ := hdvdb
        have hb3psi : b3 * psi = -(6 : k[X]) * (H * (w2 * d7)) := by
          apply mul_left_cancel₀ hH
          have h' := hbpsi
          rw [hb3] at h'
          linear_combination h'
        left
        refine ⟨b3, hb3, ⟨b3, hb3⟩, hb3psi,
          ⟨-(6 : k[X]) * (w2 * d7), by rw [hb3psi]; ring⟩, ?_⟩
        intro a ha
        refine ⟨by rw [hb3, eval_mul, ha, zero_mul], ?_⟩
        have h := congrArg (fun P : k[X] => P.eval a) hb3psi
        simp only [eval_mul, eval_neg, eval_ofNat] at h
        linear_combination h - 6 * (w2.eval a * d7.eval a) * ha
      · -- `H ∣ ψ` limb: `φ₁` descends to `H³ψ₂`.
        obtain ⟨psi2, hpsi2⟩ := hdvdpsi
        have hb2psi2 : b2 * psi2 =
            -(6 : k[X]) * (H * (w2 * d7)) := by
          apply mul_left_cancel₀ hH
          have h' := hbpsi
          rw [hpsi2] at h'
          linear_combination h'
        have hphi3 : phi1 = H ^ 3 * psi2 := by
          rw [hphi2, hpsi2]; ring
        right; left
        refine ⟨psi2, hpsi2, ⟨psi2, hpsi2⟩, hphi3, ⟨psi2, hphi3⟩,
          hb2psi2,
          ⟨-(6 : k[X]) * (w2 * d7), by rw [hb2psi2]; ring⟩, ?_⟩
        intro a ha
        refine ⟨by rw [hpsi2, eval_mul, ha, zero_mul], ?_⟩
        have h := congrArg (fun P : k[X] => P.eval a) hb2psi2
        simp only [eval_mul, eval_neg, eval_ofNat] at h
        linear_combination h - 6 * (w2.eval a * d7.eval a) * ha
      · -- Transverse limb: both orientations merge canonically and
        -- the square core forces the exact unit pins.
        right; right
        rcases horient with ⟨hbu0, hpune, hbvne, hpv0⟩ |
          ⟨hbune, hpu0, hbv0, hpvne⟩
        · have hbdu : b2.derivative.eval u = 0 := by
            have h := (hfaces0 u hu).2
            rw [hbu0, zero_mul, add_zero] at h
            exact (mul_eq_zero.mp h).resolve_right hpune
          have hpdv : psi.derivative.eval v = 0 := by
            have h := (hfaces0 v hv).2
            rw [hpv0, mul_zero, zero_add] at h
            exact (mul_eq_zero.mp h).resolve_left hbvne
          exact ⟨u, v, huv, hu, hv, hbu0, hpune, hbvne, hpv0,
            hbdu, hpdv⟩
        · have hbdv : b2.derivative.eval v = 0 := by
            have h := (hfaces0 v hv).2
            rw [hbv0, zero_mul, add_zero] at h
            exact (mul_eq_zero.mp h).resolve_right hpvne
          have hpdu : psi.derivative.eval u = 0 := by
            have h := (hfaces0 u hu).2
            rw [hpu0, mul_zero, zero_add] at h
            exact (mul_eq_zero.mp h).resolve_left hbune
          exact ⟨v, u, huv.symm, hv, hu, hbv0, hpvne, hbune, hpu0,
            hbdv, hpdu⟩
    · -- R6: consume the retained `H ∣ b₂ψ` split of the balanced
      -- exact `(2,2)` allocation; the core de-cores completely.
      obtain ⟨d3, k2, d5, k3, hd3, hd5c, hd2d5, hk2, hk3c, hk1k3,
          hd5k3, hsrc, hbpsi, hbpsidvd, hd5ne, hk3ne, hQ3,
          hfaces6⟩ := hL6
      have hfaces0 : ∀ a : k, H.eval a = 0 →
          b2.eval a * psi.eval a = 0 ∧
            b2.derivative.eval a * psi.eval a +
              b2.eval a * psi.derivative.eval a =
              -(6 : k) *
                (H.derivative.eval a *
                  (w2.eval a * d5.eval a)) :=
        fun a ha =>
          rDivisorBPsiLinearCore_faces_68 H b2 psi w2 d5 a ha hbpsi
      iterate 5 right
      left
      refine ⟨d3, k2, d5, k3, hd3, hd5c, hd2d5, hk2, hk3c, hk1k3,
        hd5k3, hsrc, hbpsi, hbpsidvd, hd5ne, hk3ne, hQ3, hfaces6,
        hfaces0, ?_⟩
      rcases rDivisorBPsiSplit_resolve_68 H b2 psi hdeg hsimple u v
          huv hu hv (hfaces0 u hu).1 (hfaces0 v hv).1 with
        hdvdb | hdvdpsi | horient
      · -- `H ∣ b₂` limb: fully de-cored `b₃ψ = -6(w₂d₅)`.
        obtain ⟨b3, hb3⟩ := hdvdb
        have hb3psi : b3 * psi = -(6 : k[X]) * (w2 * d5) := by
          apply mul_left_cancel₀ hH
          have h' := hbpsi
          rw [hb3] at h'
          linear_combination h'
        left
        refine ⟨b3, hb3, ⟨b3, hb3⟩, hb3psi, ?_⟩
        intro a ha
        refine ⟨by rw [hb3, eval_mul, ha, zero_mul], ?_⟩
        have h := congrArg (fun P : k[X] => P.eval a) hb3psi
        simp only [eval_mul, eval_neg, eval_ofNat] at h
        linear_combination h
      · -- `H ∣ ψ` limb: fully de-cored `b₂ψ₂ = -6(w₂d₅)`.
        obtain ⟨psi2, hpsi2⟩ := hdvdpsi
        have hb2psi2 : b2 * psi2 = -(6 : k[X]) * (w2 * d5) := by
          apply mul_left_cancel₀ hH
          have h' := hbpsi
          rw [hpsi2] at h'
          linear_combination h'
        have hphi3 : phi1 = H ^ 3 * psi2 := by
          rw [hphi2, hpsi2]; ring
        right; left
        refine ⟨psi2, hpsi2, ⟨psi2, hpsi2⟩, hphi3, ⟨psi2, hphi3⟩,
          hb2psi2, ?_⟩
        intro a ha
        refine ⟨by rw [hpsi2, eval_mul, ha, zero_mul], ?_⟩
        have h := congrArg (fun P : k[X] => P.eval a) hb2psi2
        simp only [eval_mul, eval_neg, eval_ofNat] at h
        linear_combination h
      · -- Transverse limb with reduced first-order ties, both
        -- orientations merged by the canonical renaming.
        right; right
        rcases horient with ⟨hbu0, hpune, hbvne, hpv0⟩ |
          ⟨hbune, hpu0, hbv0, hpvne⟩
        · have htx : b2.derivative.eval u * psi.eval u =
              -(6 : k) *
                (H.derivative.eval u *
                  (w2.eval u * d5.eval u)) := by
            have h := (hfaces0 u hu).2
            rw [hbu0, zero_mul, add_zero] at h
            exact h
          have hty : b2.eval v * psi.derivative.eval v =
              -(6 : k) *
                (H.derivative.eval v *
                  (w2.eval v * d5.eval v)) := by
            have h := (hfaces0 v hv).2
            rw [hpv0, mul_zero, zero_add] at h
            exact h
          exact ⟨u, v, huv, hu, hv, hbu0, hpune, hbvne, hpv0,
            htx, hty⟩
        · have htx : b2.derivative.eval v * psi.eval v =
              -(6 : k) *
                (H.derivative.eval v *
                  (w2.eval v * d5.eval v)) := by
            have h := (hfaces0 v hv).2
            rw [hbv0, zero_mul, add_zero] at h
            exact h
          have hty : b2.eval u * psi.derivative.eval u =
              -(6 : k) *
                (H.derivative.eval u *
                  (w2.eval u * d5.eval u)) := by
            have h := (hfaces0 u hu).2
            rw [hpu0, mul_zero, zero_add] at h
            exact h
          exact ⟨v, u, huv.symm, hv, hu, hbv0, hpvne, hbune, hpu0,
            htx, hty⟩
    · -- R7: transported verbatim.
      iterate 6 right
      left
      exact hL7
    · -- R8a: consume the retained `H ∣ b₂ψ` split against the pinned
      -- `d/k` root-pair orientation.
      obtain ⟨d3, k2, d5, hd3, hd5c, hd2d5, hk2, hd5k2, hbpsi,
          hbpsidvd, hd5ne, hk2ne, hQ3, x, y, hxy, hx, hy, hk2x,
          hpinx, hd3dx, hk2dx, hk2y, hd5y, hd3dy, hpiny,
          hd3ddy⟩ := hL8
      have hfaces0 : ∀ a : k, H.eval a = 0 →
          b2.eval a * psi.eval a = 0 ∧
            b2.derivative.eval a * psi.eval a +
              b2.eval a * psi.derivative.eval a =
              -(6 : k) *
                (H.derivative.eval a *
                  (w2.eval a * d5.eval a)) :=
        fun a ha =>
          rDivisorBPsiLinearCore_faces_68 H b2 psi w2 d5 a ha hbpsi
      iterate 7 right
      left
      refine ⟨d3, k2, d5, hd3, hd5c, hd2d5, hk2, hd5k2, hbpsi,
        hbpsidvd, hd5ne, hk2ne, hQ3, hfaces0, x, y, hxy, hx, hy,
        hk2x, hpinx, hd3dx, hk2dx, hk2y, hd5y, hd3dy, hpiny,
        hd3ddy, ?_⟩
      rcases rDivisorBPsiSplit_resolve_68 H b2 psi hdeg hsimple x y
          hxy hx hy (hfaces0 x hx).1 (hfaces0 y hy).1 with
        hdvdb | hdvdpsi | horient
      · -- `H ∣ b₂` limb with the `d₅(y) = 0` factor split.
        obtain ⟨b3, hb3⟩ := hdvdb
        have hb3psi : b3 * psi = -(6 : k[X]) * (w2 * d5) := by
          apply mul_left_cancel₀ hH
          have h' := hbpsi
          rw [hb3] at h'
          linear_combination h'
        have hfaceb : ∀ a : k, H.eval a = 0 →
            b2.eval a = 0 ∧
              b3.eval a * psi.eval a =
                -(6 : k) * (w2.eval a * d5.eval a) := by
          intro a ha
          refine ⟨by rw [hb3, eval_mul, ha, zero_mul], ?_⟩
          have h := congrArg (fun P : k[X] => P.eval a) hb3psi
          simp only [eval_mul, eval_neg, eval_ofNat] at h
          linear_combination h
        have hb3y : b3.eval y * psi.eval y = 0 := by
          have h := (hfaceb y hy).2
          rw [hd5y, mul_zero, mul_zero] at h
          exact h
        exact Or.inl ⟨b3, hb3, ⟨b3, hb3⟩, hb3psi, hb3y,
          mul_eq_zero.mp hb3y, hfaceb⟩
      · -- `H ∣ ψ` limb with the `d₅(y) = 0` factor split.
        obtain ⟨psi2, hpsi2⟩ := hdvdpsi
        have hb2psi2 : b2 * psi2 = -(6 : k[X]) * (w2 * d5) := by
          apply mul_left_cancel₀ hH
          have h' := hbpsi
          rw [hpsi2] at h'
          linear_combination h'
        have hphi3 : phi1 = H ^ 3 * psi2 := by
          rw [hphi2, hpsi2]; ring
        have hfacep : ∀ a : k, H.eval a = 0 →
            psi.eval a = 0 ∧
              b2.eval a * psi2.eval a =
                -(6 : k) * (w2.eval a * d5.eval a) := by
          intro a ha
          refine ⟨by rw [hpsi2, eval_mul, ha, zero_mul], ?_⟩
          have h := congrArg (fun P : k[X] => P.eval a) hb2psi2
          simp only [eval_mul, eval_neg, eval_ofNat] at h
          linear_combination h
        have hb2y2 : b2.eval y * psi2.eval y = 0 := by
          have h := (hfacep y hy).2
          rw [hd5y, mul_zero, mul_zero] at h
          exact h
        exact Or.inr (Or.inl ⟨psi2, hpsi2, ⟨psi2, hpsi2⟩, hphi3,
          ⟨psi2, hphi3⟩, hb2psi2, hb2y2, mul_eq_zero.mp hb2y2,
          hfacep⟩)
      · -- Transverse limb: both orientations stay pinned against the
        -- retained `d/k` witnesses.
        refine Or.inr (Or.inr ?_)
        rcases horient with ⟨hbx0, hpxne, hbyne, hpy0⟩ |
          ⟨hbxne, hpx0, hby0, hpyne⟩
        · left
          refine ⟨hbx0, hpxne, hbyne, hpy0, ?_, ?_⟩
          · have h := (hfaces0 x hx).2
            rw [hbx0, zero_mul, add_zero] at h
            exact h
          · have h := (hfaces0 y hy).2
            rw [hpy0, mul_zero, zero_add] at h
            exact h
        · right
          refine ⟨hbxne, hpx0, hby0, hpyne, ?_, ?_⟩
          · have h := (hfaces0 x hx).2
            rw [hpx0, mul_zero, zero_add] at h
            exact h
          · have h := (hfaces0 y hy).2
            rw [hby0, zero_mul, add_zero] at h
            exact h
    · -- R8b: transported verbatim.
      iterate 8 right
      left
      exact hL9
    · -- R10: transported verbatim.
      iterate 9 right
      left
      exact hL10
    · -- R11: transported verbatim.
      iterate 10 right
      left
      exact hL11
    · -- R12: transported verbatim.
      iterate 11 right
      left
      exact hL12
    · -- R13: transported verbatim.
      iterate 12 right
      left
      exact hL13
    · -- R14: transported verbatim.
      iterate 13 right
      left
      exact hL14
    · -- R15: transported verbatim.
      iterate 14 right
      left
      exact hL15
    · -- R16: transported verbatim.
      iterate 15 right
      left
      exact hL16
    · -- R17: transported verbatim.
      iterate 16 right
      left
      exact hL17
    · -- R18: transported verbatim.
      iterate 17 right
      left
      exact hL18
    · -- R19: transported verbatim.
      iterate 18 right
      left
      exact hL19
    · -- R20: transported verbatim.
      iterate 19 right
      exact hL20
  · exact Or.inr (Or.inl hphiDvd)
  · exact Or.inr (Or.inr htrans)

end RDivisorLowerZeroBPsiSplitSource68

end Max11DegreeRoutes
