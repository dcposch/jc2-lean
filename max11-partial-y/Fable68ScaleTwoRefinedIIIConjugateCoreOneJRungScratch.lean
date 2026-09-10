import Fable68ScaleTwoRefinedIIIConjugateAllocationReductionScratch

/-! # Order-one `j`-rung of the merged core-one `D∧K` family

The allocation-reduction packet merges six `D`/`K` allocation leaves
(`D1`, `D2`, `D4`, the dead-conjugate-`D` branch of `K3`, `K4` and the
double `w₁`-kill face of `K1`) into a single core-one family whose row

  `U·ė - D₁·K₂ = C j · H`

sits one core power below every previously opened row, with
`D = H·D₁`, `K = H·K₂`, `w = H·w₁`, `phi = H·phi₁`, `b·w = H²·U` and the
once-cancelled `I₄` `b·phi + 6·H·w·D₁ = 0`.  Its order-zero evaluation at
a core root is the value tie `U(x)·ė(x) = D₁(x)·K₂(x)` already implicit in
the allocation (it is the order-one rung of the spent `H²`-row).  The next
unused row identified by the predecessor is the *order-one* rung of the
core-one row itself: differentiating once and evaluating at a simple core
root `x` loads the unit `j·H'(x)`,

  `U'(x)·ė(x) + U(x)·ė'(x) - D₁'(x)·K₂(x) - D₁(x)·K₂'(x) = j·H'(x) ≠ 0`.

This file opens exactly that rung — no other Taylor row, no degree bound,
no root identification — at *both* simple core roots, on both the
`D`-child and the `K`-child copies of the family, and records:

* the value tie `U(x)·ė(x) = D₁(x)·K₂(x)` and the exhaustive
  seven-child zero/nonzero split of the rung on the value quadruple
  `(U(x), ė(x), D₁(x), K₂(x))`:
  - all four values are units (the rung and the tie are retained whole);
  - `U(x) = 0`, `ė(x) ≠ 0` with `D₁(x) = 0` (rung `U'·ė - D₁'·K₂ = jH'`)
    or `K₂(x) = 0`, `D₁(x) ≠ 0` (rung `U'·ė - D₁·K₂' = jH'`);
  - `ė(x) = 0`, `U(x) ≠ 0` with `D₁(x) = 0` (rung `U·ė' - D₁'·K₂ = jH'`)
    or `K₂(x) = 0`, `D₁(x) ≠ 0` (rung `U·ė' - D₁·K₂' = jH'`);
  - the double kill `U(x) = ė(x) = 0` forces an exact `j`-loaded unit
    pin: `D₁(x) = 0` gives `D₁'(x)·K₂(x) = -j·H'(x)` with
    `D₁'(x) ≠ 0 ∧ K₂(x) ≠ 0`, else `K₂(x) = 0` with `D₁(x) ≠ 0` and
    `D₁(x)·K₂'(x) = -j·H'(x)`, `K₂'(x) ≠ 0`;
* the genuine closure: the total-kill child
  `U(x) = ė(x) = D₁(x) = K₂(x) = 0` is *eliminated outright* at every
  core root (`0 = j·H'(x)` against `j ≠ 0` and the simple-root unit) —
  `terminalConjugateCoreOneFamilyJRunged68_no_total_kill`;
* the once-cancelled transverse tie
  `b'(x)·w₁(x) + b(x)·w₁'(x) = H'(x)·U(x)` from the family's own product
  `b·w₁ = H·U` (obtained by one exact unit division from `b·w = H²·U`),
  wiring the rung's `U`-column back to the `b`/`w₁` jets that the
  three-fold provenances constrain.

Both three-fold provenance records are preserved verbatim
(`terminalConjugateDTransverseProvenance68` on the `D`-child sources
`D1`/`D2`/`D4`, `terminalConjugateKMergeProvenance68` on the `K`-child
sources `K3`-dead-`D`/`K4`/`K1`-`w₁`), as are all non-core-one leaves of
both reduced allocations, the quotient splits, the product
divisibilities, the conjugate matching and the `H ∣ r` cascade exit.

Exact residual (no closure overclaim): the family is not eliminated —
per core root the seven-child split above remains, each child carrying
its exact rung identity; the rung constrains only the first jets of
`U`, `ė`, `D₁`, `K₂` at the two roots.  Next unused row for this family:
the order-two rung of the same core-one row (RHS `j·H''(x)` with
`H'' = 2·lead(H)` a nonzero constant, first loading `U''`, `ė''`,
`D₁''`, `K₂''`); the order-two rung of the cancelled `H²`-row on the
`D₁(c) = 0` deep-II family remains untouched, as identified by the
predecessor.
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

section CoreOneJRungValue68

variable {k : Type*} [Field k] [CharZero k]

/-- Exhaustive zero/nonzero children of the order-one `j`-rung
`up·ev + u·ep - dp·k2 - d·k2p = load` at one core root, against the value
tie `u·ev = d·k2` and the nonzero load.  The total-kill child
`u = ev = d = k2 = 0` is impossible and does not appear; both double-kill
children carry exact `j`-loaded unit pins. -/
def terminalCoreOneJRungSplit68 (u up ev ep d dp k2 k2p load : k) : Prop :=
  (u ≠ 0 ∧ ev ≠ 0 ∧ d ≠ 0 ∧ k2 ≠ 0 ∧ u * ev = d * k2 ∧
    up * ev + u * ep - dp * k2 - d * k2p = load) ∨
  (u = 0 ∧ ev ≠ 0 ∧ d = 0 ∧ up * ev - dp * k2 = load) ∨
  (u = 0 ∧ ev ≠ 0 ∧ d ≠ 0 ∧ k2 = 0 ∧ up * ev - d * k2p = load) ∨
  (ev = 0 ∧ u ≠ 0 ∧ d = 0 ∧ u * ep - dp * k2 = load) ∨
  (ev = 0 ∧ u ≠ 0 ∧ d ≠ 0 ∧ k2 = 0 ∧ u * ep - d * k2p = load) ∨
  (u = 0 ∧ ev = 0 ∧ d = 0 ∧ k2 ≠ 0 ∧ dp ≠ 0 ∧ dp * k2 = -load) ∨
  (u = 0 ∧ ev = 0 ∧ k2 = 0 ∧ d ≠ 0 ∧ k2p ≠ 0 ∧ d * k2p = -load)

/-- The value tie and the loaded order-one rung produce the exhaustive
seven-child split. -/
theorem terminalCoreOne_jRung_split_68 (u up ev ep d dp k2 k2p load : k)
    (hload : load ≠ 0)
    (hval : u * ev = d * k2)
    (hrung : up * ev + u * ep - dp * k2 - d * k2p = load) :
    terminalCoreOneJRungSplit68 u up ev ep d dp k2 k2p load := by
  rcases eq_or_ne u 0 with hu | hu
  · rcases eq_or_ne ev 0 with he | he
    · -- both left value factors die: the rung pins the right pair
      rcases eq_or_ne d 0 with hd | hd
      · have hpin : dp * k2 = -load := by
          linear_combination -hrung + up * he + ep * hu - k2p * hd
        have hk2 : k2 ≠ 0 := by
          intro h0
          exact hload (by linear_combination hpin - dp * h0)
        have hdp : dp ≠ 0 := by
          intro h0
          exact hload (by linear_combination hpin - k2 * h0)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hu, he, hd, hk2, hdp, hpin⟩)))))
      · have hk2 : k2 = 0 := by
          have hdk : d * k2 = 0 := by linear_combination -hval + ev * hu
          exact (mul_eq_zero.mp hdk).resolve_left hd
        have hpin : d * k2p = -load := by
          linear_combination -hrung + up * he + ep * hu - dp * hk2
        have hk2p : k2p ≠ 0 := by
          intro h0
          exact hload (by linear_combination hpin - d * h0)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hu, he, hk2, hd, hk2p, hpin⟩)))))
    · -- `u` dies, `ev` survives
      have hdk : d * k2 = 0 := by linear_combination -hval + ev * hu
      rcases eq_or_ne d 0 with hd | hd
      · exact Or.inr (Or.inl ⟨hu, he, hd,
          by linear_combination hrung - ep * hu + k2p * hd⟩)
      · have hk2 : k2 = 0 := (mul_eq_zero.mp hdk).resolve_left hd
        exact Or.inr (Or.inr (Or.inl ⟨hu, he, hd, hk2,
          by linear_combination hrung - ep * hu + dp * hk2⟩))
  · rcases eq_or_ne ev 0 with he | he
    · -- `ev` dies, `u` survives
      have hdk : d * k2 = 0 := by linear_combination -hval + u * he
      rcases eq_or_ne d 0 with hd | hd
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hu, hd,
          by linear_combination hrung - up * he + k2p * hd⟩)))
      · have hk2 : k2 = 0 := (mul_eq_zero.mp hdk).resolve_left hd
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hu, hd, hk2,
          by linear_combination hrung - up * he + dp * hk2⟩))))
    · -- all four value factors are units
      have hue : u * ev ≠ 0 := mul_ne_zero hu he
      have hd : d ≠ 0 := by
        intro h0
        exact hue (by rw [hval, h0, zero_mul])
      have hk2 : k2 ≠ 0 := by
        intro h0
        exact hue (by rw [hval, h0, mul_zero])
      exact Or.inl ⟨hu, he, hd, hk2, hval, hrung⟩

/-- Closure of the total-kill child: every rung child keeps at least one
of the four core-one values alive. -/
theorem terminalCoreOneJRungSplit68_not_total_kill
    {u up ev ep d dp k2 k2p load : k}
    (h : terminalCoreOneJRungSplit68 u up ev ep d dp k2 k2p load) :
    ¬(u = 0 ∧ ev = 0 ∧ d = 0 ∧ k2 = 0) := by
  rintro ⟨hu, he, hd, hk⟩
  rcases h with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ |
    ⟨-, h1, -⟩ | ⟨-, -, -, h1, -⟩ | ⟨-, -, -, h1, -⟩
  · exact h1 hu
  · exact h1 he
  · exact h1 he
  · exact h1 hu
  · exact h1 hu
  · exact h1 hk
  · exact h1 hd

end CoreOneJRungValue68

section CoreOneJRungFamily68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The merged six-source core-one `D∧K` family, with its order-one
`j`-rung opened at every core root.  The eight global identities and the
three-fold provenance of the originating child are retained verbatim; at
every core root the family carries the dead transverse value
`b(x)·w₁(x) = 0`, the once-cancelled transverse tie
`b'(x)·w₁(x) + b(x)·w₁'(x) = H'(x)·U(x)`, and the exhaustive rung split
on `(U, ė, D₁, K₂)` with load `j·H'(x)`. -/
def terminalConjugateCoreOneFamilyJRunged68
    (H r A b D w phi e K D1 K2 U w1 phi1 : k[X]) (j a c : k) : Prop :=
  D = H * D1 ∧ K = H * K2 ∧ w = H * w1 ∧ phi = H * phi1 ∧
  b * w = H ^ 2 * U ∧ b * w1 = H * U ∧
  b * phi + 6 * H * w * D1 = 0 ∧
  U * e - D1 * K2 = C j * H ∧
  (terminalConjugateDTransverseProvenance68
      H r b D w phi e K D1 w1 phi1 j a c ∨
    terminalConjugateKMergeProvenance68
      H r A b D w phi e K w1 phi1 j a c) ∧
  ∀ x : k, H.eval x = 0 →
    (b.eval x * w1.eval x = 0 ∧
      b.derivative.eval x * w1.eval x + b.eval x * w1.derivative.eval x =
        H.derivative.eval x * U.eval x ∧
      terminalCoreOneJRungSplit68 (U.eval x) (U.derivative.eval x)
        (e.eval x) (e.derivative.eval x)
        (D1.eval x) (D1.derivative.eval x)
        (K2.eval x) (K2.derivative.eval x)
        (j * H.derivative.eval x))

/-- Constructor: the eight global identities of the merged family open
their order-one `j`-rung at every core root. -/
theorem terminalConjugateCoreOneFamily_jRunged_of_data_68
    (H r A b D w phi e K D1 K2 U w1 phi1 : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (hj : j ≠ 0)
    (hD1 : D = H * D1) (hK2 : K = H * K2)
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1)
    (hbw : b * w = H ^ 2 * U)
    (hI4 : b * phi + 6 * H * w * D1 = 0)
    (hrow : U * e - D1 * K2 = C j * H)
    (hprov :
      terminalConjugateDTransverseProvenance68
        H r b D w phi e K D1 w1 phi1 j a c ∨
      terminalConjugateKMergeProvenance68
        H r A b D w phi e K w1 phi1 j a c) :
    terminalConjugateCoreOneFamilyJRunged68
      H r A b D w phi e K D1 K2 U w1 phi1 j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hbw1 : b * w1 = H * U := by
    apply mul_left_cancel₀ hH
    linear_combination hbw - b * hw1
  refine ⟨hD1, hK2, hw1, hphi1, hbw, hbw1, hI4, hrow, hprov, ?_⟩
  intro x hx
  have hload : j * H.derivative.eval x ≠ 0 :=
    mul_ne_zero hj (hsimple x hx)
  have hval : U.eval x * e.eval x = D1.eval x * K2.eval x := by
    have h := congrArg (fun P : k[X] => P.eval x) hrow
    simp only [eval_sub, eval_mul, eval_C, hx, mul_zero] at h
    linear_combination h
  have hrung : U.derivative.eval x * e.eval x +
      U.eval x * e.derivative.eval x -
      D1.derivative.eval x * K2.eval x -
      D1.eval x * K2.derivative.eval x = j * H.derivative.eval x := by
    have h := congrArg (fun P : k[X] => P.derivative.eval x) hrow
    simp only [derivative_sub, derivative_mul, derivative_C, zero_mul,
      zero_add, eval_sub, eval_add, eval_mul, eval_C] at h
    linear_combination h
  have hbwx : b.eval x * w1.eval x = 0 := by
    have h := congrArg (fun P : k[X] => P.eval x) hbw1
    simp only [eval_mul, hx, zero_mul] at h
    exact h
  have htie : b.derivative.eval x * w1.eval x +
      b.eval x * w1.derivative.eval x =
      H.derivative.eval x * U.eval x := by
    have h := congrArg (fun P : k[X] => P.derivative.eval x) hbw1
    simp only [derivative_mul, eval_add, eval_mul, hx, zero_mul,
      add_zero] at h
    linear_combination h
  exact ⟨hbwx, htie, terminalCoreOne_jRung_split_68 _ _ _ _ _ _ _ _ _
    hload hval hrung⟩

/-- Genuine closure: at no core root of the merged family can the four
core-one values `U`, `ė`, `D₁`, `K₂` all die — the order-one rung is
`j`-loaded there. -/
theorem terminalConjugateCoreOneFamilyJRunged68_no_total_kill
    (H r A b D w phi e K D1 K2 U w1 phi1 : k[X]) (j a c : k) (x : k)
    (hfam : terminalConjugateCoreOneFamilyJRunged68
      H r A b D w phi e K D1 K2 U w1 phi1 j a c)
    (hx : H.eval x = 0) :
    ¬(U.eval x = 0 ∧ e.eval x = 0 ∧ D1.eval x = 0 ∧ K2.eval x = 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hrung⟩ := hfam
  exact terminalCoreOneJRungSplit68_not_total_kill ((hrung x hx).2.2)

/-- The `D`-child reduced allocation with the core-one leaf upgraded to
the `j`-runged merged family; the `H ∣ r` exit, the `D₁(c) = 0` residual
family and both apex-mixed coordinate leaves are retained verbatim. -/
def terminalRefinedIIIConjugateDAllocationJRunged68
    (H t r X0 A b D w phi e K D1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  H ∣ r ∨
  (∃ K2 U : k[X],
      terminalConjugateCoreOneFamilyJRunged68
        H r A b D w phi e K D1 K2 U w1 phi1 j a c) ∨
  (∃ U : k[X],
      D1.eval c = 0 ∧ K.eval c ≠ 0 ∧
      b * w = H ^ 2 * U ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      H * U * e - D1 * K = C j * H ^ 2 ∧
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

/-- The `K`-child reduced allocation with the core-one merge leaf `S4`
upgraded to the `j`-runged merged family; `S1`–`S3`, `S5`–`S7` are
retained verbatim. -/
def terminalRefinedIIIConjugateKAllocationJRunged68
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
      terminalConjugateCoreOneFamilyJRunged68
        H r A b D w phi e K D1 K1 U w1 phi1 j a c) ∨
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
  (phi1.eval a + 2 * A.eval a * w1.eval a ≠ 0 ∧
    A.eval c * b.eval c - 3 * D.eval c ≠ 0 ∧
    b.eval a = 0 ∧ w1.eval c = 0 ∧ phi1.eval c = 0 ∧
    K1.eval c = 0 ∧
    ∃ U : k[X], b * w1 = H * U ∧ D * K1 = H * (U * e - C j * H))

/-- The `D`-child reduced allocation upgrades: its core-one leaf opens
the order-one `j`-rung, all other leaves pass through verbatim. -/
theorem terminalRefinedIII_conjugateD_allocation_jRung_68
    (H t r X0 A b D w phi e K D1 w1 phi1 : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (hj : j ≠ 0)
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1) (hD1 : D = H * D1)
    (hreduced : terminalRefinedIIIConjugateDAllocationReduced68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateDAllocationJRunged68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c := by
  rcases hreduced with hr | ⟨K2, U, hK2, hbw, hI4, hrow, hprov⟩ |
    hleaf | hleaf | hleaf
  · exact Or.inl hr
  · exact Or.inr (Or.inl ⟨K2, U,
      terminalConjugateCoreOneFamily_jRunged_of_data_68 H r A b D w phi e
        K D1 K2 U w1 phi1 j a c hdeg hsimple hj hD1 hK2 hw1 hphi1 hbw hI4
        hrow (Or.inl hprov)⟩)
  · exact Or.inr (Or.inr (Or.inl hleaf))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hleaf)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hleaf)))

/-- The `K`-child reduced allocation upgrades: its core-one merge leaf
opens the order-one `j`-rung, all other leaves pass through verbatim. -/
theorem terminalRefinedIII_conjugateK_allocation_jRung_68
    (H t r X0 A b D w phi e K K1 w1 phi1 : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (hj : j ≠ 0)
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1) (hK1 : K = H * K1)
    (hreduced : terminalRefinedIIIConjugateKAllocationReduced68
      H t r X0 A b D w phi e K K1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateKAllocationJRunged68
      H t r X0 A b D w phi e K K1 w1 phi1 j a c := by
  rcases hreduced with hleaf | hleaf | hleaf |
    ⟨D1, U, hD1, hbw, hI4, hrow, hprov⟩ | hleaf | hleaf | hleaf
  · exact Or.inl hleaf
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr (Or.inl hleaf))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨D1, U,
      terminalConjugateCoreOneFamily_jRunged_of_data_68 H r A b D w phi e
        K D1 K1 U w1 phi1 j a c hdeg hsimple hj hD1 hK1 hw1 hphi1 hbw hI4
        hrow (Or.inr hprov)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hleaf))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hleaf)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hleaf)))))

/-- The conjugate global split with both component-III children carrying
their allocations and the `j`-runged reduced inventories.  The common and
component-II children, the divided identities, the per-root quotient
splits, the product divisibilities and the deep-root left-zero selector
are retained verbatim from the allocation-reduction split. -/
def terminalRefinedIIIConjugateCoreOneJRungSplit68
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
      terminalRefinedIIIConjugateDAllocationJRunged68
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
      terminalRefinedIIIConjugateKAllocationJRunged68
        H t r X0 A b D w phi e K K1 w1 phi1 j a c))

/-- The allocation-reduction split upgrades to the `j`-runged split:
only the two core-one leaves change, everything else passes through
verbatim. -/
theorem terminalRefinedIII_conjugate_coreOne_jRung_split_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (hj : j ≠ 0)
    (hsplit : terminalRefinedIIIConjugateAllocationReductionSplit68
      H t r X0 A b D w phi e K j a c) :
    terminalRefinedIIIConjugateCoreOneJRungSplit68
      H t r X0 A b D w phi e K j a c := by
  rcases hsplit with hcommon | hII | hD | hK
  · exact Or.inl hcommon
  · exact Or.inr (Or.inl hII)
  · obtain ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4, hrow, hforall, hP,
      halloc, hreduced⟩ := hD
    exact Or.inr (Or.inr (Or.inl ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4,
      hrow, hforall, hP, halloc,
      terminalRefinedIII_conjugateD_allocation_jRung_68 H t r X0 A b D w
        phi e K D1 w1 phi1 j a c hdeg hsimple hj hw1 hphi1 hD1 hreduced⟩))
  · obtain ⟨w1, phi1, K1, hw1, hphi1, hK1, hI4, hrow, hforall, hFG,
      hleftA, halloc, hreduced⟩ := hK
    exact Or.inr (Or.inr (Or.inr ⟨w1, phi1, K1, hw1, hphi1, hK1, hI4,
      hrow, hforall, hFG, hleftA, halloc,
      terminalRefinedIII_conjugateK_allocation_jRung_68 H t r X0 A b D w
        phi e K K1 w1 phi1 j a c hdeg hsimple hj hw1 hphi1 hK1 hreduced⟩))

end CoreOneJRungFamily68

section CoreOneJRungSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: the coordinate rows carry the exact R-divisor
cascade behind any `H ∣ r` exit, and at every deep component-III root the
conjugate matching persists with both component-III children carrying
their allocations and the `j`-runged reduced inventories — in particular
the merged six-source core-one family returns with its order-one
`j`-rung opened at both simple core roots. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateCoreOneJRungPacket
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
               terminalRefinedIIIConjugateCoreOneJRungSplit68
                 H t r X A0 b2 d2 w2 phi2 eDot k2 j a c)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hcasc, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorConjugateAllocationReductionPacket
      (H := H) hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hcasc, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hroots ⊢
  intro a ha hwa hphia hDa hKa
  obtain ⟨c, hca, hc, hmatch, hsplit⟩ := hroots a ha hwa hphia hDa hKa
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  exact ⟨c, hca, hc, hmatch,
    terminalRefinedIII_conjugate_coreOne_jRung_split_68 H t r X
      (cubicANumerator68 t r) b2 d2 w2 phi2
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r))
      k2 j a c hdeg hsimple hj hsplit⟩

end CoreOneJRungSource68

end Max11DegreeRoutes
