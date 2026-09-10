import Fable68ScaleTwoRefinedIIIConjugateAllocationReductionScratch

/-! # Order-two `j`-loaded rung of the `D₁(c) = 0` deep-II family

This file continues the exact verified conjugate allocation-reduction
packet and attacks only the order-two `D₁(c) = 0` deep-II family — the
third leaf of the reduced `D`-child inventory, carrying the row
`H·U·e − D₁·K = Cj·H²` with the conjugate kernel unit `K(c) ≠ 0` and the
deep kernel root `K(a) = 0` — through the exact next unused rung
identified by the predecessor: the order-two `j`-loaded rung of the
cancelled `H²`-row.  The order-zero and order-one evaluations of the row
at both simple core roots are `j`-free (`K(a) = 0` and `D₁(c) = 0` cancel
the loaded terms), so order two is where `j` first enters.

The attack is purely exact:

* the row cancels one core power outright,
  `D₁·K = H·(U·e − Cj·H)`, and the cancelled row is retained globally;
* the transverse product cancels once as well, `b·w₁ = H·U`, with the
  order-one faces `b'(x)w₁(x) + b(x)w₁'(x) = H'(x)U(x)` at both core
  roots backwiring the root values of `U` to the source `b₂`/`w₂` jets;
* the order-one rungs of the cancelled row are `j`-free and reduce
  exactly under `K(a) = 0` resp. `D₁(c) = 0`:
  `D₁(a)·K'(a) = H'(a)·U(a)e(a)` and `D₁'(c)·K(c) = H'(c)·U(c)e(c)`;
* the order-two rungs are the first `j`-loaded faces of the family:
  `2D₁'(a)K'(a) + D₁(a)K''(a)
     = H''(a)·U(a)e(a) + 2H'(a)·(U'e + Ue')(a) − 2jH'(a)²` and
  `D₁''(c)K(c) + 2D₁'(c)K'(c)
     = H''(c)·U(c)e(c) + 2H'(c)·(U'e + Ue')(c) − 2jH'(c)²`;
* the retained units `K(c) ≠ 0` and `H'(c) ≠ 0` force the exact conjugate
  multiplicity dichotomy `D₁'(c) = 0 ↔ U(c)·e(c) = 0`: the conjugate
  root of the loaded determinant `D = H·D₁` deepens to order three
  exactly when the row value `U(c)e(c)` dies there.

No closure is claimed: the family survives as the smallest exact
residual, the old leaf conjoined with the rung packet.  The coordinate
child (the `H ∣ r` R-divisor cascade exit) and the kernel children (the
common child, the deep conjugate-II child, and the entire `K`-child
reduced inventory with its core-one merge family and `S1`–`S7` faces)
are preserved verbatim, as are the other four `D`-child leaves.

Next unused row for this family: the order-three rung of the `H²`-row —
the order-two rung of the cancelled row, `j`-loaded through `6jH'H''`,
first loading the jets `U''`, `e''`, `D₁'''`, `K'''`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

section RefinedIIIConjugateOrderTwoJRungAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The deep-II row `H·U·e − D₁·K = Cj·H²` cancels one core power
exactly: `D₁·K = H·(U·e − Cj·H)`. -/
theorem conjugateDeepII_cancelled_row_68 (H U e D1 K : k[X]) (j : k)
    (hrow : H * U * e - D1 * K = C j * H ^ 2) :
    D1 * K = H * (U * e - C j * H) := by
  linear_combination -hrow

/-- Order-one rung of the cancelled row at a core root (`j`-free):
`D₁'(x)K(x) + D₁(x)K'(x) = H'(x)·U(x)e(x)`. -/
theorem conjugateDeepII_first_rung_68 (H U e D1 K : k[X]) (j : k) (x : k)
    (hcancel : D1 * K = H * (U * e - C j * H)) (hx : H.eval x = 0) :
    D1.derivative.eval x * K.eval x + D1.eval x * K.derivative.eval x =
      H.derivative.eval x * (U.eval x * e.eval x) := by
  have h1 := congrArg (fun P : k[X] => P.derivative.eval x) hcancel
  simp only [derivative_mul, derivative_sub, derivative_C, zero_mul,
    mul_zero, zero_add, add_zero, sub_zero, eval_add, eval_sub, eval_mul,
    eval_C, hx] at h1
  linear_combination h1

/-- Order-two rung of the cancelled row at a core root — the first
`j`-loaded face of the deep-II family:
`D₁''K + 2D₁'K' + D₁K'' = H''·Ue + 2H'·(U'e + Ue') − 2jH'²`
evaluated at the root. -/
theorem conjugateDeepII_second_rung_68 (H U e D1 K : k[X]) (j : k) (x : k)
    (hcancel : D1 * K = H * (U * e - C j * H)) (hx : H.eval x = 0) :
    D1.derivative.derivative.eval x * K.eval x +
        2 * (D1.derivative.eval x * K.derivative.eval x) +
        D1.eval x * K.derivative.derivative.eval x =
      H.derivative.derivative.eval x * (U.eval x * e.eval x) +
        2 * H.derivative.eval x *
          (U.derivative.eval x * e.eval x +
            U.eval x * e.derivative.eval x) -
        2 * j * H.derivative.eval x ^ 2 := by
  have h2 := congrArg (fun P : k[X] => P.derivative.derivative.eval x)
    hcancel
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_C,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, eval_add, eval_sub,
    eval_mul, eval_C, hx] at h2
  linear_combination h2

/-- Order-one face of the once-cancelled transverse product `b·w₁ = H·U`
at a core root: `b'(x)w₁(x) + b(x)w₁'(x) = H'(x)U(x)`. -/
theorem conjugateDeepII_product_face_68 (H b w1 U : k[X]) (x : k)
    (hbw1 : b * w1 = H * U) (hx : H.eval x = 0) :
    b.derivative.eval x * w1.eval x + b.eval x * w1.derivative.eval x =
      H.derivative.eval x * U.eval x := by
  have h1 := congrArg (fun P : k[X] => P.derivative.eval x) hbw1
  simp only [derivative_mul, eval_add, eval_mul, hx, zero_mul, mul_zero,
    add_zero] at h1
  linear_combination h1

/-- Conjugate multiplicity dichotomy: with the kernel unit `K(c) ≠ 0` and
the simple-root unit `H'(c) ≠ 0`, the divided determinant `D₁` carries an
at-least-double conjugate root exactly when the row value `U(c)·e(c)`
dies. -/
theorem conjugateDeepII_multiplicity_dichotomy_68
    (H U e D1 K : k[X]) (j : k) (c : k)
    (hcancel : D1 * K = H * (U * e - C j * H)) (hc : H.eval c = 0)
    (hD1c : D1.eval c = 0) (hKc : K.eval c ≠ 0)
    (hHc : H.derivative.eval c ≠ 0) :
    D1.derivative.eval c = 0 ↔ U.eval c * e.eval c = 0 := by
  have h1 := conjugateDeepII_first_rung_68 H U e D1 K j c hcancel hc
  rw [hD1c, zero_mul, add_zero] at h1
  constructor
  · intro h0
    rw [h0, zero_mul] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hHc
  · intro h0
    rw [h0, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hKc

/-- Exact order-two rung packet of the `D₁(c) = 0` deep-II family: the
cancelled row, the once-cancelled transverse product with its two
order-one faces, the two `j`-free order-one rungs (reduced by the deep
kernel root `K(a) = 0` resp. the conjugate determinant root
`D₁(c) = 0`), the two `j`-loaded order-two rungs, and the conjugate
multiplicity dichotomy forced by the retained units. -/
def terminalConjugateDeepIIOrderTwoJRung68
    (H b w1 U e D1 K : k[X]) (j a c : k) : Prop :=
  D1 * K = H * (U * e - C j * H) ∧
  b * w1 = H * U ∧
  b.derivative.eval a * w1.eval a + b.eval a * w1.derivative.eval a =
    H.derivative.eval a * U.eval a ∧
  b.derivative.eval c * w1.eval c + b.eval c * w1.derivative.eval c =
    H.derivative.eval c * U.eval c ∧
  D1.eval a * K.derivative.eval a =
    H.derivative.eval a * (U.eval a * e.eval a) ∧
  D1.derivative.eval c * K.eval c =
    H.derivative.eval c * (U.eval c * e.eval c) ∧
  2 * (D1.derivative.eval a * K.derivative.eval a) +
      D1.eval a * K.derivative.derivative.eval a =
    H.derivative.derivative.eval a * (U.eval a * e.eval a) +
      2 * H.derivative.eval a *
        (U.derivative.eval a * e.eval a +
          U.eval a * e.derivative.eval a) -
      2 * j * H.derivative.eval a ^ 2 ∧
  D1.derivative.derivative.eval c * K.eval c +
      2 * (D1.derivative.eval c * K.derivative.eval c) =
    H.derivative.derivative.eval c * (U.eval c * e.eval c) +
      2 * H.derivative.eval c *
        (U.derivative.eval c * e.eval c +
          U.eval c * e.derivative.eval c) -
      2 * j * H.derivative.eval c ^ 2 ∧
  (D1.derivative.eval c = 0 ↔ U.eval c * e.eval c = 0)

/-- The order-two `j`-loaded rung of the cancelled `H²`-row, consumed on
the `D₁(c) = 0` deep-II family: the family data alone produces the full
rung packet at both simple core roots. -/
theorem terminalRefinedIII_conjugateDeepII_orderTwo_jRung_68
    (H b w w1 U e D1 K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0)
    (hKa : K.eval a = 0) (hD1c : D1.eval c = 0) (hKc : K.eval c ≠ 0)
    (hw1 : w = H * w1) (hbw : b * w = H ^ 2 * U)
    (hrow : H * U * e - D1 * K = C j * H ^ 2) :
    terminalConjugateDeepIIOrderTwoJRung68 H b w1 U e D1 K j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hcancel := conjugateDeepII_cancelled_row_68 H U e D1 K j hrow
  have hbw1 : b * w1 = H * U := by
    apply mul_left_cancel₀ hH
    linear_combination hbw - b * hw1
  have h1a := conjugateDeepII_first_rung_68 H U e D1 K j a hcancel ha
  rw [hKa, mul_zero, zero_add] at h1a
  have h1c := conjugateDeepII_first_rung_68 H U e D1 K j c hcancel hc
  rw [hD1c, zero_mul, add_zero] at h1c
  have h2a := conjugateDeepII_second_rung_68 H U e D1 K j a hcancel ha
  rw [hKa, mul_zero, zero_add] at h2a
  have h2c := conjugateDeepII_second_rung_68 H U e D1 K j c hcancel hc
  rw [hD1c, zero_mul, add_zero] at h2c
  exact ⟨hcancel, hbw1,
    conjugateDeepII_product_face_68 H b w1 U a hbw1 ha,
    conjugateDeepII_product_face_68 H b w1 U c hbw1 hc,
    h1a, h1c, h2a, h2c,
    conjugateDeepII_multiplicity_dichotomy_68 H U e D1 K j c hcancel hc
      hD1c hKc (hsimple c hc)⟩

end RefinedIIIConjugateOrderTwoJRungAlgebra68

section RefinedIIIConjugateOrderTwoJRungReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Reduced inventory of the `D`-child allocation with the order-two
`j`-loaded rung consumed on the `D₁(c) = 0` deep-II leaf.  The coordinate
exit, the core-one `D∧K` family, the two apex-mixed coordinate leaves and
every provenance record are preserved verbatim; only the deep-II leaf
gains the exact rung packet. -/
def terminalRefinedIIIConjugateDAllocationJRungReduced68
    (H t r X0 A b D w phi e K D1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  H ∣ r ∨
  (∃ K2 U : k[X],
      K = H * K2 ∧ b * w = H ^ 2 * U ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      U * e - D1 * K2 = C j * H ∧
      terminalConjugateDTransverseProvenance68
        H r b D w phi e K D1 w1 phi1 j a c) ∨
  (∃ U : k[X],
      D1.eval c = 0 ∧ K.eval c ≠ 0 ∧
      b * w = H ^ 2 * U ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      H * U * e - D1 * K = C j * H ^ 2 ∧
      terminalConjugateDeepIIOrderTwoJRung68 H b w1 U e D1 K j a c ∧
      terminalConjugateDTransverseProvenance68
        H r b D w phi e K D1 w1 phi1 j a c) ∨
  (∃ V : k[X],
      A * b = H * V ∧
      r ^ 2 * b = H * (4 * X0 * b - 12 * V) ∧
      ((b.eval a = 0 ∧ D1.eval a * K.eval a = 0 ∧ b.eval c ≠ 0 ∧
         w1.eval c ≠ 0 ∧ A.eval c = 0 ∧ r.eval c = 0 ∧ t.eval c = 0 ∧
         phi1.eval c = 0) ∨
       (b.eval c = 0 ∧ D1.eval c * K.eval c = 0 ∧ b.eval a ≠ 0 ∧
         w1.eval a ≠ 0 ∧ A.eval a = 0 ∧ r.eval a = 0 ∧ t.eval a = 0 ∧
         phi1.eval a = 0 ∧ e.eval a = 0))) ∨
  (∃ phi2 V : k[X],
      phi1 = H * phi2 ∧ phi = H ^ 2 * phi2 ∧
      b * phi2 + 6 * w1 * D1 = 0 ∧
      A * w1 = H * V ∧
      r ^ 2 * w1 = H * (4 * X0 * w1 - 12 * V) ∧
      b.eval a ≠ 0 ∧ b.eval c ≠ 0 ∧
      ((w1.eval a = 0 ∧ phi2.eval a = 0 ∧ w1.eval c ≠ 0 ∧ A.eval c = 0 ∧
         r.eval c = 0 ∧ t.eval c = 0 ∧ r.eval a ≠ 0 ∧
         terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
           (6 * j * H.derivative.eval a ^ 3)) ∨
       (w1.eval c = 0 ∧ phi2.eval c = 0 ∧ w1.eval a ≠ 0 ∧ A.eval a = 0 ∧
         r.eval a = 0 ∧ t.eval a = 0 ∧ e.eval a = 0 ∧ r.eval c ≠ 0 ∧
         terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K c
           (6 * j * H.derivative.eval c ^ 3))))

/-- The reduced `D`-child inventory upgrades leaf-by-leaf: four leaves
pass through verbatim, and the `D₁(c) = 0` deep-II leaf consumes the
order-two `j`-loaded rung of its cancelled `H²`-row. -/
theorem terminalRefinedIII_conjugateD_allocation_jRung_reduction_68
    (H t r X0 A b D w phi e K D1 w1 phi1 : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0)
    (hKa : K.eval a = 0) (hw1 : w = H * w1)
    (hred : terminalRefinedIIIConjugateDAllocationReduced68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateDAllocationJRungReduced68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c := by
  rcases hred with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨U, hD1c, hKc, hbw, hI4, hrowU, hprov⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨U, hD1c, hKc, hbw, hI4, hrowU,
      terminalRefinedIII_conjugateDeepII_orderTwo_jRung_68
        H b w w1 U e D1 K j a c hdeg hsimple ha hc hKa hD1c hKc hw1
        hbw hrowU, hprov⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The conjugate global split with the order-two `j`-loaded rung
consumed on the `D`-child deep-II leaf.  The common child, the deep
conjugate-II child, and the full `K`-child branch (allocation and reduced
inventory) are preserved verbatim from the allocation-reduction split. -/
def terminalRefinedIIIConjugateOrderTwoJRungSplit68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k) : Prop :=
  (∃ G : k[X],
      phi + 2 * A * w = H * G ∧
      H * b * G - 2 * w * (A * b - 3 * D) = 0) ∨
  (∃ D1 BW : k[X],
      D = H * D1 ∧ b * w = H * BW ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      BW * e - D1 * K = C j * H ^ 2) ∨
  ((∃ w1 phi1 D1 : k[X],
      w = H * w1 ∧ phi = H * phi1 ∧ D = H * D1 ∧
      b * phi1 + 6 * H * w1 * D1 = 0 ∧
      b * w1 * e - D1 * K = C j * H ^ 2 ∧
      (∀ x : k, H.eval x = 0 →
        terminalRefinedIIIConjugateDQuotientSplit68 (A.eval x)
          (H.derivative.eval x) (b.eval x) (b.derivative.eval x)
          (w1.eval x) (phi1.eval x) (phi1.derivative.eval x)
          (D1.eval x) (K.eval x) (e.eval x)) ∧
      (∃ P : k[X], A ^ 2 * b * w1 = H * P) ∧
      terminalRefinedIIIConjugateDQuotientAllocation68
        H A b w phi e K D1 w1 phi1 j a c ∧
      terminalRefinedIIIConjugateDAllocationJRungReduced68
        H t r X0 A b D w phi e K D1 w1 phi1 j a c) ∨
   (∃ w1 phi1 K1 : k[X],
      w = H * w1 ∧ phi = H * phi1 ∧ K = H * K1 ∧
      b * phi1 + 6 * w1 * D = 0 ∧
      b * w1 * e - D * K1 = C j * H ^ 2 ∧
      (∀ x : k, H.eval x = 0 →
        terminalRefinedIIIConjugateKQuotientSplit68 (A.eval x) (b.eval x)
          (w1.eval x) (D.eval x) (phi1.eval x)) ∧
      (∃ P : k[X], (A * b - 3 * D) * (phi1 + 2 * A * w1) = H * P) ∧
      (b.eval a = 0 ∨
        (phi1.eval a = 0 ∧ (A.eval a = 0 ∨ w1.eval a = 0))) ∧
      terminalRefinedIIIConjugateKQuotientAllocation68
        H A b D w phi e K1 w1 phi1 j a c ∧
      terminalRefinedIIIConjugateKAllocationReduced68
        H t r X0 A b D w phi e K K1 w1 phi1 j a c))

/-- The allocation-reduction split upgrades: only the `D`-child reduced
inventory changes, consuming the order-two `j`-loaded rung on its
deep-II leaf. -/
theorem terminalRefinedIII_conjugate_orderTwo_jRung_split_upgrade_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hKa : K.eval a = 0)
    (hsplit : terminalRefinedIIIConjugateAllocationReductionSplit68
      H t r X0 A b D w phi e K j a c) :
    terminalRefinedIIIConjugateOrderTwoJRungSplit68
      H t r X0 A b D w phi e K j a c := by
  rcases hsplit with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4, hrowL, hforall, hP,
      halloc, hred⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4,
      hrowL, hforall, hP, halloc,
      terminalRefinedIII_conjugateD_allocation_jRung_reduction_68
        H t r X0 A b D w phi e K D1 w1 phi1 j a c hdeg hsimple ha hc
        hKa hw1 hred⟩))
  · exact Or.inr (Or.inr (Or.inr h))

end RefinedIIIConjugateOrderTwoJRungReduction68

section RefinedIIIConjugateOrderTwoJRungSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: the coordinate rows carry the exact R-divisor
cascade behind any `H ∣ r` exit, and at every deep component-III root the
conjugate matching persists with the order-two `j`-loaded rung consumed
on the `D`-child deep-II leaf; the common, conjugate-II, and `K`-child
kernel children are preserved verbatim. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateOrderTwoJRungPacket
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
      (H ∣ r →
        ∃ s t1 y1 : k[X],
          r = H * s ∧ t = H * t1 ∧
          (3 : k[X]) * t1 = H * s ^ 2 + X ∧
          H ∣ t ∧ H ^ 2 ∣ p.coeff 4 ∧ H ∣ p.coeff 3 ∧
          p.coeff 4 = H ^ 2 * t1 ∧ p.coeff 3 = H * y1 ∧
          (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd) ∧
      (H ∣ phi1 →
        ∃ phi2 k2 : k[X], phi1 = H * phi2 ∧ k1 = H * k2 ∧
          b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∧
          (let A0 := cubicANumerator68 t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           ∀ a : k, H.eval a = 0 → w2.eval a = 0 →
             phi2.eval a = 0 → d2.eval a = 0 → k2.eval a = 0 →
             ∃ c : k, c ≠ a ∧ H.eval c = 0 ∧
               terminalRefinedIIIConjugateMatching68
                 H A0 b2 d2 w2 phi2 eDot k2 j c ∧
               terminalRefinedIIIConjugateOrderTwoJRungSplit68
                 H t r X A0 b2 d2 w2 phi2 eDot k2 j a c)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hcascade,
    hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorConjugateAllocationReductionPacket
      (H := H) hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hcascade, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hroots ⊢
  intro a ha hwa hphia hDa hKa
  obtain ⟨c, hca, hc, hmatch, hsplit⟩ := hroots a ha hwa hphia hDa hKa
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  exact ⟨c, hca, hc, hmatch,
    terminalRefinedIII_conjugate_orderTwo_jRung_split_upgrade_68
      H t r X _ b2 d2 w2 phi2 _ k2 j a c hdeg hsimple ha hc hKa hsplit⟩

end RefinedIIIConjugateOrderTwoJRungSource68

end Max11DegreeRoutes
