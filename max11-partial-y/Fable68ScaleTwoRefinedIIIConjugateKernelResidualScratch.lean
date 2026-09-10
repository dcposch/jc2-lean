import Fable68ScaleTwoRefinedIIIConjugateAllocationReductionScratch

/-! # The `S7` kernel residual of the conjugate `K`-child allocation

This file isolates and attacks the single `S7` kernel leaf of the reduced
conjugate `K`-child inventory — `K = H·K₁`, `K₁(c) = 0`, `b·w₁ = H·U`,
`D·K₁ = H·(U·e - C j·H)` with the unit gates
`phi₁(a) + 2A(a)w₁(a) ≠ 0`, `A(c)b(c) - 3D(c) ≠ 0` and the kills
`b(a) = 0`, `w₁(c) = 0`, `phi₁(c) = 0` — using only already-verified
consumers and no new Taylor or loaded coefficient row.

The attacking consumer is the loaded-degeneracy trichotomy of the
lower-third classification at the conjugate root `c`, retained through the
conjugate matching but never consumed on this leaf.  On `S7` the
determinant unit `A(c)·b(c) - 3·D(c) ≠ 0` kills its common and
component-II branches outright, forcing the component-III branch, whose
final sub-disjunction splits the leaf exactly:

* `D(c) = 0`: the row root globalizes (`D(a) = 0` at the deep root), so
  `D = H·D₁` and the retained kernel row drops to the core-one shape
  `U·e - D₁·K₁ = C j·H`.  The unit `A(c)b(c) ≠ 0` splits off `A(c) ≠ 0`
  and `b(c) ≠ 0`, the apex unit forces the coordinate unit `r(c) ≠ 0`,
  and the refined-III residual applies at `c` — the leaf MERGES verbatim
  into the existing core-one `D∧K` family with the first
  `terminalConjugateKMergeProvenance68` leaf.  `S7` loses this half to the
  already-tracked family; no new residual shape appears.
* `D(c) ≠ 0`: the trichotomy's `d`-branch is unreachable, so its
  `k`-branch face is forced — the FIRST `j`-loaded face ever seen by the
  `S7` leaf.  Both `w = H·w₁` and `K = H·K₁` carry double zeros at `c`
  (`w₁(c) = K₁(c) = 0`), so the middle-zero triple and right-zero pair
  reduce exactly through the product jets, leaving the loaded kernel face
  `6H'(c)·(b'w₁'e + bw₁'e' - D'K₁')(c) + 3H''(c)·(bw₁'e - DK₁')(c)
    + 3H'(c)·(bw₁''e - DK₁'')(c) = 6j·H'(c)³`
  with the new unit `D(c) ≠ 0` retained.

No global divisibility, determinant, or coordinate contradiction exists on
either half: the retained global data (`F·G = H·P` with the crosswise
kills `F(a) = 0`, `G(c) = 0`, the cross identity `b·G = 2w₁·F`, the
per-root quotient splits and the apex pins) is exactly consistent with the
kernel branch, and the sympy-confirmed witness `b = 0`, `w₁ = 0`,
`phi₁ = X - c`, `D = (X - a)²`, `K₁ = -C j·(X - c)²`, `U = 0`, `e` free
satisfies every retained conjunct including the loaded kernel face
(`6j·D(c)·H'(c) = 6j·H'(c)³` since `D(c) = H'(c)²`).  The kernel branch is
therefore the smallest honest source-facing residual of the leaf.

Exact next unused rows for the kernel branch (deliberately not opened —
they are new tower rungs): the order-2 (first `j`-loaded) coefficient of
the divided terminal row `b·w₁·e - D·K₁ = C j·H²` at `c` — subtracting
`3H'(c)` times that rung from the kernel face would leave the clean
`H''`-tie `3H''(c)·(b(c)w₁'(c)e(c) - D(c)K₁'(c)) = 0` with `H''` a
nonzero constant — and, equivalently, the order-1 rungs of the retained
products `b·w₁ = H·U` and `D·K₁ = H·(U·e - C j·H)` at `c` (first loading
`U(c)`, `K₁'(c)`).
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

section RefinedIIIConjugateKernelResidualAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- At a core root `c` where the quotient also vanishes, the right-zero
pair face of a once-divided cofactor reduces exactly through the product
jets: `K = H·K₁` with `H(c) = 0`, `K₁(c) = 0` has a double zero at `c`,
and the surviving second and third jets are `2H'K₁'` and
`3H''K₁' + 3H'K₁''`. -/
theorem conjugateKernel_pair_reduction_68 (H d K1 : k[X]) (c : k)
    (hc : H.eval c = 0) (hK1c : K1.eval c = 0) :
    terminalThirdPairRightZeroAt68 d (H * K1) c =
      6 * H.derivative.eval c * d.derivative.eval c *
          K1.derivative.eval c +
        3 * H.derivative.derivative.eval c * d.eval c *
          K1.derivative.eval c +
        3 * H.derivative.eval c * d.eval c *
          K1.derivative.derivative.eval c := by
  simp only [terminalThirdPairRightZeroAt68, derivative_mul, derivative_add,
    eval_add, eval_mul, hc, hK1c, zero_mul, mul_zero, zero_add, add_zero]
  ring

/-- The same exact reduction for the middle-zero triple face: `w = H·w₁`
with `H(c) = 0`, `w₁(c) = 0` has a double zero at `c`, and the loaded
triple collapses onto the four surviving quotient jets. -/
theorem conjugateKernel_triple_reduction_68 (H b w1 e : k[X]) (c : k)
    (hc : H.eval c = 0) (hw1c : w1.eval c = 0) :
    terminalThirdTripleMiddleZeroAt68 b (H * w1) e c =
      6 * H.derivative.eval c * b.derivative.eval c *
          w1.derivative.eval c * e.eval c +
        3 * H.derivative.derivative.eval c * b.eval c *
          w1.derivative.eval c * e.eval c +
        3 * H.derivative.eval c * b.eval c *
          w1.derivative.derivative.eval c * e.eval c +
        6 * H.derivative.eval c * b.eval c * w1.derivative.eval c *
          e.derivative.eval c := by
  simp only [terminalThirdTripleMiddleZeroAt68, derivative_mul,
    derivative_add, eval_add, eval_mul, hc, hw1c, zero_mul, mul_zero,
    zero_add, add_zero]
  ring

/-- The refined `S7` kernel residual: the original leaf data sharpened by
the conjugate row unit `D(c) ≠ 0` and the first `j`-loaded kernel face at
`c`, fully reduced through the quotient double zeros. -/
def terminalRefinedIIIConjugateS7KernelRefined68
    (H A b D e K1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  phi1.eval a + 2 * A.eval a * w1.eval a ≠ 0 ∧
  A.eval c * b.eval c - 3 * D.eval c ≠ 0 ∧
  b.eval a = 0 ∧ w1.eval c = 0 ∧ phi1.eval c = 0 ∧
  K1.eval c = 0 ∧ D.eval c ≠ 0 ∧
  (∃ U : k[X], b * w1 = H * U ∧ D * K1 = H * (U * e - C j * H)) ∧
  6 * H.derivative.eval c *
      (b.derivative.eval c * w1.derivative.eval c * e.eval c +
        b.eval c * w1.derivative.eval c * e.derivative.eval c -
        D.derivative.eval c * K1.derivative.eval c) +
    3 * H.derivative.derivative.eval c *
      (b.eval c * w1.derivative.eval c * e.eval c -
        D.eval c * K1.derivative.eval c) +
    3 * H.derivative.eval c *
      (b.eval c * w1.derivative.derivative.eval c * e.eval c -
        D.eval c * K1.derivative.derivative.eval c) =
    6 * j * H.derivative.eval c ^ 3

end RefinedIIIConjugateKernelResidualAlgebra68

section RefinedIIIConjugateKernelResidual68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The `S7` kernel leaf splits exclusively through the loaded-degeneracy
trichotomy at the conjugate root: either `D(c) = 0` and the leaf merges
verbatim into the core-one `D∧K` family with the first merge-provenance
leaf, or `D(c) ≠ 0` and the trichotomy's `k`-branch face is forced,
yielding the refined kernel residual. -/
theorem terminalRefinedIII_conjugateS7_kernel_refinement_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hDa : D.eval a = 0)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (w1 phi1 K1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1) (hK1 : K = H * K1)
    (hI4q : b * phi1 + 6 * w1 * D = 0)
    (hres : ∀ x : k, H.eval x = 0 → D.eval x = 0 → b.eval x ≠ 0 →
      terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K x
        (6 * j * H.derivative.eval x ^ 3))
    (hdegen : terminalPhiDivisorLoadedDegeneracy68 (A.eval c)
      (H.derivative.eval c) (6 * j * (H.derivative.eval c) ^ 3)
      b D w phi e K c)
    (hGa : phi1.eval a + 2 * A.eval a * w1.eval a ≠ 0)
    (hFc : A.eval c * b.eval c - 3 * D.eval c ≠ 0)
    (hba : b.eval a = 0) (hwc : w1.eval c = 0) (hphic : phi1.eval c = 0)
    (hKc : K1.eval c = 0)
    (U : k[X]) (hU : b * w1 = H * U)
    (hrowK : D * K1 = H * (U * e - C j * H)) :
    (∃ D1 U2 : k[X],
        D = H * D1 ∧ b * w = H ^ 2 * U2 ∧
        b * phi + 6 * H * w * D1 = 0 ∧
        U2 * e - D1 * K1 = C j * H ∧
        terminalConjugateKMergeProvenance68
          H r A b D w phi e K w1 phi1 j a c) ∨
      terminalRefinedIIIConjugateS7KernelRefined68
        H A b D e K1 w1 phi1 j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  by_cases hDc : D.eval c = 0
  · -- merge into the core-one family
    left
    have hAb : A.eval c * b.eval c ≠ 0 := by
      intro h0
      exact hFc (by linear_combination h0 - 3 * hDc)
    have hAc : A.eval c ≠ 0 := left_ne_zero_of_mul hAb
    have hbc : b.eval c ≠ 0 := right_ne_zero_of_mul hAb
    have hrc : r.eval c ≠ 0 :=
      conjugateApex_unit_root_68 H t r X0 A c hA hX hc hAc
    obtain ⟨D1, hD1⟩ := dvd_of_two_simple_root_evals_68 H D
      hdeg hsimple a c hac ha hc hDa hDc
    refine ⟨D1, U, hD1, ?_, ?_, ?_,
      Or.inl ⟨hba, hbc, hwc, hphic, hAc, hrc, hGa, hres c hc hDc hbc⟩⟩
    · linear_combination b * hw1 + H * hU
    · linear_combination b * hphi1 + 6 * H * D1 * hw1 + H * hI4q -
        6 * H * w1 * hD1
    · apply mul_left_cancel₀ hH
      linear_combination K1 * hD1 - hrowK
  · -- the kernel branch: the trichotomy is forced into its component-III
    -- `k`-branch and delivers the loaded kernel face
    right
    rcases hdegen with hcommon | hleft | hmiddle
    · exact absurd hcommon.1 hFc
    · exact absurd hleft.1 hFc
    obtain ⟨-, -, -, hsub⟩ := hmiddle
    have hfaceR : terminalThirdTripleMiddleZeroAt68 b w e c -
        terminalThirdPairRightZeroAt68 D K c =
        6 * j * (H.derivative.eval c) ^ 3 := by
      rcases hsub with ⟨hD0, -⟩ | ⟨-, hface⟩
      · exact absurd hD0 hDc
      · exact hface
    rw [hw1, hK1, conjugateKernel_triple_reduction_68 H b w1 e c hc hwc,
      conjugateKernel_pair_reduction_68 H D K1 c hc hKc] at hfaceR
    refine ⟨hGa, hFc, hba, hwc, hphic, hKc, hDc, ⟨U, hU, hrowK⟩, ?_⟩
    linear_combination hfaceR

/-- The reduced `K`-child inventory with the `S7` kernel leaf refined: the
first six leaves are retained verbatim, and the kernel leaf carries the
conjugate row unit and the loaded kernel face. -/
def terminalRefinedIIIConjugateKKernelReduced68
    (H t r X0 A b D w phi e K K1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  (∃ G1 F1 : k[X],
      phi1 + 2 * A * w1 = H * G1 ∧
      phi + 2 * A * w = H ^ 2 * G1 ∧
      A * b - 3 * D = H * F1 ∧
      b * G1 = 2 * w1 * F1 ∧
      (b.eval a = 0 ∨ (A.eval a = 0 ∧ r.eval a = 0))) ∨
  (∃ G1 : k[X],
      phi1 + 2 * A * w1 = H * G1 ∧
      phi + 2 * A * w = H ^ 2 * G1 ∧
      2 * w1 * (A * b - 3 * D) = H * (b * G1) ∧
      A.eval a * b.eval a - 3 * D.eval a = 0 ∧
      (b.eval a = 0 ∨ (A.eval a = 0 ∧ r.eval a = 0)) ∧
      A.eval c * b.eval c - 3 * D.eval c ≠ 0 ∧
      w1.eval c = 0 ∧ phi1.eval c = 0) ∨
  (∃ G1 : k[X],
      phi1 + 2 * A * w1 = H * G1 ∧
      phi + 2 * A * w = H ^ 2 * G1 ∧
      2 * w1 * (A * b - 3 * D) = H * (b * G1) ∧
      A.eval c * b.eval c - 3 * D.eval c = 0 ∧
      A.eval a * b.eval a - 3 * D.eval a ≠ 0 ∧
      w1.eval a = 0 ∧ phi1.eval a = 0 ∧
      b.eval a ≠ 0 ∧ A.eval a ≠ 0 ∧ r.eval a ≠ 0 ∧
      terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
        (6 * j * H.derivative.eval a ^ 3)) ∨
  (∃ D1 U : k[X],
      D = H * D1 ∧ b * w = H ^ 2 * U ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      U * e - D1 * K1 = C j * H ∧
      terminalConjugateKMergeProvenance68
        H r A b D w phi e K w1 phi1 j a c) ∨
  (∃ w2 G1 : k[X],
      w1 = H * w2 ∧ w = H ^ 2 * w2 ∧
      phi1 + 2 * A * w1 = H * G1 ∧
      phi1 = H * (G1 - 2 * A * w2) ∧
      phi = H ^ 2 * (G1 - 2 * A * w2) ∧
      b * (G1 - 2 * A * w2) + 6 * w2 * D = 0 ∧
      H * (b * w2) * e - D * K1 = C j * H ^ 2 ∧
      D.eval c ≠ 0 ∧ K1.eval c = 0 ∧
      A.eval a * b.eval a - 3 * D.eval a ≠ 0 ∧
      A.eval c * b.eval c - 3 * D.eval c ≠ 0 ∧
      b.eval a ≠ 0 ∧ A.eval a ≠ 0 ∧ r.eval a ≠ 0 ∧
      terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
        (6 * j * H.derivative.eval a ^ 3)) ∨
  (∃ F1 : k[X],
      A * b - 3 * D = H * F1 ∧
      b * (phi1 + 2 * A * w1) = H * (2 * w1 * F1) ∧
      (b.eval a = 0 ∨ (A.eval a = 0 ∧ r.eval a = 0))) ∨
  terminalRefinedIIIConjugateS7KernelRefined68
    H A b D e K1 w1 phi1 j a c

/-- Consuming the loaded-degeneracy trichotomy at the conjugate root
refines the reduced `K`-child inventory: the `S7` kernel leaf either
merges into the existing core-one family (fourth leaf) or sharpens to the
refined kernel residual; every other leaf passes through verbatim. -/
theorem terminalRefinedIII_conjugateK_kernel_reduction_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hDa : D.eval a = 0)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (w1 phi1 K1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1) (hK1 : K = H * K1)
    (hI4q : b * phi1 + 6 * w1 * D = 0)
    (hres : ∀ x : k, H.eval x = 0 → D.eval x = 0 → b.eval x ≠ 0 →
      terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K x
        (6 * j * H.derivative.eval x ^ 3))
    (hdegen : terminalPhiDivisorLoadedDegeneracy68 (A.eval c)
      (H.derivative.eval c) (6 * j * (H.derivative.eval c) ^ 3)
      b D w phi e K c)
    (hreduced : terminalRefinedIIIConjugateKAllocationReduced68
      H t r X0 A b D w phi e K K1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateKKernelReduced68
      H t r X0 A b D w phi e K K1 w1 phi1 j a c := by
  rcases hreduced with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · obtain ⟨hGa, hFc, hba, hwc, hphic, hKc, U, hU, hrowK⟩ := h
    rcases terminalRefinedIII_conjugateS7_kernel_refinement_68
        H t r X0 A b D w phi e K j a c hdeg hsimple ha hc hac hDa hA hX
        w1 phi1 K1 hw1 hphi1 hK1 hI4q hres hdegen hGa hFc hba hwc hphic
        hKc U hU hrowK with hmerge | hkernel
    · exact Or.inr (Or.inr (Or.inr (Or.inl hmerge)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hkernel)))))

/-- The conjugate global split with the `K`-child additionally carrying
the kernel-refined inventory.  The common and component-II children, the
`D`-child, the divided identities, the per-root quotient splits, the
product divisibilities, the deep-root left-zero selector and both
allocation layers are retained verbatim from the allocation-reduction
split. -/
def terminalRefinedIIIConjugateKernelResidualSplit68
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
      terminalRefinedIIIConjugateDAllocationReduced68
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
        H t r X0 A b D w phi e K K1 w1 phi1 j a c ∧
      terminalRefinedIIIConjugateKKernelReduced68
        H t r X0 A b D w phi e K K1 w1 phi1 j a c))

end RefinedIIIConjugateKernelResidual68

section RefinedIIIConjugateKernelResidualSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: the coordinate rows carry the exact R-divisor
cascade behind any `H ∣ r` exit, and at every deep component-III root the
conjugate matching persists with the `K`-child carrying the kernel-refined
inventory on top of both allocation layers. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateKernelResidualPacket
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
               terminalRefinedIIIConjugateKernelResidualSplit68
                 H t r X A0 b2 d2 w2 phi2 eDot k2 j a c)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorRefinedIIIPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_, ?_⟩
  · intro hr
    exact conjugateCoordinate_cascade_of_dvd_68 H r t X Yd
      (p.coeff 3) (p.coeff 4) ht hX hY hr
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hroots ⊢
  intro a ha hwa hphia hDa hKa
  let A0 := cubicANumerator68 t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hclass : ∀ x : k, H.eval x = 0 →
      terminalPhiDivisorLowerThirdClassification68 (A0.eval x)
        (H.derivative.eval x) (6 * j * (H.derivative.eval x) ^ 3)
        b2 d2 w2 phi2 eDot k2 x := fun x hx => (hroots x hx).1
  obtain ⟨c, hca, hc, hmatch⟩ := terminalRefinedIII_conjugate_matching_68
    H A0 b2 d2 w2 phi2 eDot k2 j a hdeg hsimple ha hwa hphia hDa hKa hclass
  have hglobal := terminalRefinedIII_conjugate_global_split_68
    H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      hwa hphia hDa hKa hI4 hrow hmatch
  refine ⟨c, hca, hc, hmatch, ?_⟩
  rcases hglobal with hcommon | hII | hD | hK
  · exact Or.inl hcommon
  · exact Or.inr (Or.inl hII)
  · obtain ⟨w1, phi1x, D1, hw1, hphi1x, hD1, hI4L, hrowL⟩ := hD
    obtain ⟨hforall, P, hP⟩ := terminalRefinedIII_conjugateD_global_quotient_68
      H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      w1 phi1x D1 hw1 hphi1x hD1 hI4L hrowL hclass
    have halloc := terminalRefinedIII_conjugateD_quotient_allocation_68
      H A0 b2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm hKa
      w1 phi1x D1 hw1 hphi1x hI4L hrowL hforall
    have hres : ∀ x : k, H.eval x = 0 → b2.eval x ≠ 0 →
        terminalPhiDivisorRefinedIIIResidual68 r b2 d2 w2 phi2 eDot k2 x
          (6 * j * H.derivative.eval x ^ 3) := by
      intro x hx hbx
      have hwx : w2.eval x = 0 := by rw [hw1]; simp [eval_mul, hx]
      have hphix : phi2.eval x = 0 := by rw [hphi1x]; simp [eval_mul, hx]
      have hDx : d2.eval x = 0 := by rw [hD1]; simp [eval_mul, hx]
      exact (hroots x hx).2 hwx hphix hDx hbx
    have hreduced := terminalRefinedIII_conjugateD_allocation_reduction_68
      H t r X A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      hKa rfl hX w1 phi1x D1 hw1 hphi1x hD1 hI4L hrowL hres halloc
    exact Or.inr (Or.inr (Or.inl
      ⟨w1, phi1x, D1, hw1, hphi1x, hD1, hI4L, hrowL, hforall,
        ⟨P, hP⟩, halloc, hreduced⟩))
  · obtain ⟨w1, phi1x, K1, hw1, hphi1x, hK1, hI4L, hrowL⟩ := hK
    obtain ⟨hforall, hFG, hleftA⟩ :=
      terminalRefinedIII_conjugateK_global_quotient_68
        H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm hDa
        w1 phi1x hw1 hphi1x hI4L hclass
    have halloc := terminalRefinedIII_conjugateK_quotient_allocation_68
      H A0 b2 d2 w2 phi2 eDot j a c hdeg hsimple ha hc hca.symm hDa
      w1 phi1x K1 hw1 hphi1x hI4L hrowL hforall
    have hres : ∀ x : k, H.eval x = 0 → d2.eval x = 0 → b2.eval x ≠ 0 →
        terminalPhiDivisorRefinedIIIResidual68 r b2 d2 w2 phi2 eDot k2 x
          (6 * j * H.derivative.eval x ^ 3) := by
      intro x hx hDx hbx
      have hwx : w2.eval x = 0 := by rw [hw1]; simp [eval_mul, hx]
      have hphix : phi2.eval x = 0 := by rw [hphi1x]; simp [eval_mul, hx]
      exact (hroots x hx).2 hwx hphix hDx hbx
    have hreduced := terminalRefinedIII_conjugateK_allocation_reduction_68
      H t r X A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      hDa rfl hX w1 phi1x K1 hw1 hphi1x hK1 hI4L hrowL hres halloc
    have hkernel := terminalRefinedIII_conjugateK_kernel_reduction_68
      H t r X A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      hDa rfl hX w1 phi1x K1 hw1 hphi1x hK1 hI4L hres (hclass c hc).1
      hreduced
    exact Or.inr (Or.inr (Or.inr
      ⟨w1, phi1x, K1, hw1, hphi1x, hK1, hI4L, hrowL, hforall, hFG,
        hleftA, halloc, hreduced, hkernel⟩))

end RefinedIIIConjugateKernelResidualSource68

end Max11DegreeRoutes
