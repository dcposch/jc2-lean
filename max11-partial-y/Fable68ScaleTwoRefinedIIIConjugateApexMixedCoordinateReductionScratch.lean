import Fable68ScaleTwoRefinedIIIConjugateAllocationReductionScratch

/-! # Reduction of the two apex-mixed `D`-child leaves (`D5`, `D6`)

This file continues the exact verified conjugate allocation-reduction
packet and attacks only the two apex-mixed coordinate leaves of the
reduced `D`-child inventory — leaf (4), the `b`/apex mixed coordinate
leaf descending from `D5`, and leaf (5), the `w₁`/apex jet-residual leaf
descending from `D6` — without opening any later Taylor or loaded
coefficient row.  Every move recycles data already inside the packet:
the proved apex identity `12·A = 4·H·X₀ − r²`, the converted coordinate
products `r²·b = H·(4X₀b − 12V)` / `r²·w₁ = H·(4X₀w₁ − 12V)`, the
conjugate matching with its per-root classification, the retained
terminal row `b·w₁·e − D₁·K = Cj·H²`, the deep kernel root `K(a) = 0`,
the retained refined-III residuals, and the same-witness two-root
`H`-divisor transfer.

Exact gains on leaf (4) (`D5`):

* both cases resolve the coordinate dichotomy at the `b`-kill root: the
  killed side already carries `r = 0` from the apex kill, so either `r`
  also dies at the `b`-kill root and the leaf exits into `H ∣ r` — the
  verified R-divisor coordinate cascade, exactly as `D2`/`D3`/`D6`
  already exit — or the coordinate unit is pinned there, `r ≠ 0`, and
  the apex identity forces the apex and `p₄`-quotient units
  `A = −(1/12)r² ≠ 0`, `3t = r² ≠ 0`;
* case A (`b(a) = 0`) gains the three-way kernel split at the
  transverse-unit root `c`: the row value ties
  `b(c)w₁(c)·e(c) = D₁(c)K(c)` with `b(c)w₁(c) ≠ 0`, so either
  `K(c) = 0` joins the deep root `K(a) = 0` and globalizes to
  `K = H·K₂` with the row dropping one core power in the mixed grouping
  `(b·w₁)·e = H·(D₁·K₂ + Cj·H)` and the derivative-numerator kill
  `e(c) = 0`, or the kernel survives and the row value allocates
  exactly: `D₁(c) = 0 ∧ e(c) = 0`, or all of `D₁(c)`, `e(c)` are units;
* case B (`b(c) = 0`) splits its retained dead product
  `D₁(c)·K(c) = 0`: `K(c) = 0` globalizes to `K = H·K₂` with the same
  dropped row, else the conjugate determinant kill `D₁(c) = 0` is
  pinned against the kernel unit.

Exact gains on leaf (5) (`D6`):

* the apex identity pins the apex and `p₄`-quotient units at the
  surviving root (case A′ gains `A(a) ≠ 0`, `t(a) ≠ 0`; case B′ gains
  `A(c) ≠ 0`, `t(c) ≠ 0`);
* the retained refined-III residual at the coordinate-unit root has a
  dead `r`-branch, and its jet packet transports through the same
  witnesses `w = H·w₁`, `phi = H·phi₁ = H²·phi₂`, `D = H·D₁` into the
  exact quotient-level packet at the `w₁`-kill root: the divided fourth
  jet `b·phi₂' + 6·w₁'·D₁ = 0` and the first `j`-loaded quotient load
  equation with right-hand side `6j·H'³`, using `H''' = 0` for the
  degree-two core — no residual jet survives at the source level only;
* case A′ gains the kernel split at `c` enriched by the divided `I₄`:
  on the `K(c) ≠ 0 ∧ D₁(c) = 0` branch the quotient value
  `b(c)·phi₂(c) = −6w₁(c)D₁(c) = 0` kills `phi₂(c)`, which joins the
  deep kill `phi₂(a) = 0` and cascades the `phi`-face cube-deep,
  `phi₂ = H·phi₃`, `phi = H³·phi₃`, with the exactly cancelled `I₄`
  `6·w₁·D₁ + H·b·phi₃ = 0`; on the all-units branch `phi₂(c) ≠ 0`;
* case B′ derives the dead product `D₁(c)·K(c) = 0` from the row at the
  `w₁`-kill root and splits it as in `D5` case B.

Exact mismatches — why no existing family consumes these leaves:

* the core-one `D∧K` family and the `D₁(c) = 0` deep-II family both
  need `b·w = H²·U`, i.e. `H ∣ b·w₁`; on every apex-mixed configuration
  `b·w₁` keeps a unit at one core root (`b(c)w₁(c) ≠ 0` on `D5`-A and
  `D6`-A′, `b(a)w₁(a) ≠ 0` on `D5`-B and `D6`-B′), so the kernel
  globalization drops the row only in the mixed grouping
  `(b·w₁)·e = H·(D₁K₂ + CjH)` and the leaves stay outside both
  families;
* the refined-III residual consumer needs `b ≠ 0` at the probed root
  and is trivial wherever the apex kill sits (`r = 0` there), so `D5`
  retains no jet data at all and `D6`'s packets live only at the
  coordinate-unit roots;
* the `phi`-cascade fires only on `D6`-A′: it needs the `phi₂`-level
  witness with the deep kill `phi₂(a) = 0`; on `D5` the `I₄` shape
  `b·phi₁ + 6H·w₁·D₁ = 0` is core-loaded and evaluates trivially at
  both roots.

No closure is claimed: both leaves survive as strictly smaller exact
residuals, the old pins conjoined verbatim with the new packets.  The
coordinate child, the core-one `D∧K` family, the deep-II family with
its provenance, and the entire `K`-child reduced inventory are
preserved verbatim, as are the conjugate matching, both allocations,
the per-root quotient splits and the product divisibilities.

Next unused rows for these two leaves: the order-one `j`-rung of the
dropped kernel rows `b·w₁·e = H·(D₁·K₂ + Cj·H)` on the `K = H·K₂`
branches, and the order-one faces of the retained apex products
`A·b = H·V` / `A·w₁ = H·V` backwiring the quotient `V`.
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

section RefinedIIIConjugateApexMixedAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The degree-two core has vanishing third derivative. -/
theorem natDegreeTwo_thirdDerivative_zero_68 (H : k[X])
    (hdeg : H.natDegree = 2) :
    H.derivative.derivative.derivative = 0 := by
  have h1 := natDegree_derivative_le (p := H)
  have h2 := natDegree_derivative_le (p := H.derivative)
  rw [hdeg] at h1
  rw [eq_C_of_natDegree_le_zero
    (p := H.derivative.derivative) (by omega), derivative_C]

/-- First-derivative value of an exact core multiple at a core root. -/
theorem conjugateCoreFirstJet_68 (H P Q : k[X]) (x : k)
    (hP : P = H * Q) (hx : H.eval x = 0) :
    P.derivative.eval x = H.derivative.eval x * Q.eval x := by
  subst hP
  simp [derivative_mul, hx]

/-- Second-derivative value of an exact core multiple at a core root. -/
theorem conjugateCoreSecondJet_68 (H P Q : k[X]) (x : k)
    (hP : P = H * Q) (hx : H.eval x = 0) :
    P.derivative.derivative.eval x =
      H.derivative.derivative.eval x * Q.eval x +
        2 * (H.derivative.eval x * Q.derivative.eval x) := by
  subst hP
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, hx,
    zero_mul, mul_zero, add_zero, zero_add]
  ring

/-- Third-derivative value of an exact core multiple at a core root. -/
theorem conjugateCoreThirdJet_68 (H P Q : k[X]) (x : k)
    (hP : P = H * Q) (hx : H.eval x = 0) :
    P.derivative.derivative.derivative.eval x =
      H.derivative.derivative.derivative.eval x * Q.eval x +
        3 * (H.derivative.derivative.eval x * Q.derivative.eval x) +
        3 * (H.derivative.eval x * Q.derivative.derivative.eval x) := by
  subst hP
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, hx,
    zero_mul, mul_zero, add_zero, zero_add]
  ring

/-- A coordinate unit at a core root is an apex unit (converse direction
of the proved apex kill). -/
theorem conjugateCoordinateUnit_apex_68 (H t r X0 A : k[X]) (x : k)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hx : H.eval x = 0) (hr : r.eval x ≠ 0) :
    A.eval x ≠ 0 :=
  fun hA0 => hr (conjugateApex_zero_root_68 H t r X0 A x hA hX hx hA0)

/-- A coordinate unit at a core root keeps the divided `p₄`-coefficient
a unit as well: `3t(x) = r(x)² ≠ 0`. -/
theorem conjugateCoordinate_t_unit_root_68 (H t r X0 : k[X]) (x : k)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hx : H.eval x = 0) (hr : r.eval x ≠ 0) :
    t.eval x ≠ 0 := by
  intro ht0
  apply hr
  have hxe := congrArg (fun P : k[X] => P.eval x) hX
  simp only [eval_sub, eval_mul, eval_pow, eval_ofNat, hx, zero_mul] at hxe
  have hsq : r.eval x ^ 2 = 0 := by linear_combination 3 * ht0 - hxe
  exact sq_eq_zero_iff.mp hsq

/-- Quotient-level translation of the retained refined-III jet packet at
a `w₁`-kill root carrying the coordinate unit: the divided fourth jet and
the first `j`-loaded load equation, entirely in the quotient witnesses. -/
def terminalConjugateApexMixedJetPacket68
    (H b w1 phi2 e D1 K : k[X]) (j x : k) : Prop :=
  b.eval x * phi2.derivative.eval x +
      6 * (w1.derivative.eval x * D1.eval x) = 0 ∧
  6 * H.derivative.eval x *
      (b.derivative.eval x * w1.derivative.eval x * e.eval x) +
    3 * H.derivative.derivative.eval x *
      (b.eval x * w1.derivative.eval x * e.eval x) +
    3 * H.derivative.eval x *
      (b.eval x * w1.derivative.derivative.eval x * e.eval x) +
    6 * H.derivative.eval x *
      (b.eval x * w1.derivative.eval x * e.derivative.eval x) -
    (3 * H.derivative.derivative.eval x *
        (D1.derivative.eval x * K.eval x) +
      3 * H.derivative.eval x *
        (D1.derivative.derivative.eval x * K.eval x) +
      3 * H.derivative.derivative.eval x *
        (D1.eval x * K.derivative.eval x) +
      6 * H.derivative.eval x *
        (D1.derivative.eval x * K.derivative.eval x) +
      3 * H.derivative.eval x *
        (D1.eval x * K.derivative.derivative.eval x)) =
    6 * j * H.derivative.eval x ^ 3

/-- The retained refined-III residual at a `w₁`-kill root with the
coordinate unit has a dead `r`-branch, and its jet packet transports
through the same witnesses `w = H·w₁`, `phi = H·phi₁ = H²·phi₂`,
`D = H·D₁` into the exact quotient-level packet; `H''' = 0` for the
degree-two core removes the only untransported term. -/
theorem terminalConjugateApexMixed_jetPacket_68
    (H r b w phi e D K w1 phi1 phi2 D1 : k[X]) (j x : k)
    (hdeg : H.natDegree = 2)
    (hx : H.eval x = 0) (hsx : H.derivative.eval x ≠ 0)
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1)
    (hphi12 : phi1 = H * phi2) (hD1 : D = H * D1)
    (hw1x : w1.eval x = 0) (hphi2x : phi2.eval x = 0)
    (hrx : r.eval x ≠ 0)
    (hres : terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K x
      (6 * j * H.derivative.eval x ^ 3)) :
    terminalConjugateApexMixedJetPacket68 H b w1 phi2 e D1 K j x := by
  rcases hres with hr0 | ⟨hwp, hpp, hppp, hjet, hload⟩
  · exact absurd hr0 hrx
  dsimp only [terminalThirdTripleMiddleDoubleZeroAt68,
    terminalThirdPairLeftZeroAt68] at hload
  -- transported jets of `w = H·w₁` at the `w₁`-kill root
  have hw2raw := conjugateCoreSecondJet_68 H w w1 x hw1 hx
  have hw2c : w.derivative.derivative.eval x =
      2 * (H.derivative.eval x * w1.derivative.eval x) := by
    linear_combination hw2raw + H.derivative.derivative.eval x * hw1x
  have hw3raw := conjugateCoreThirdJet_68 H w w1 x hw1 hx
  have hw3c : w.derivative.derivative.derivative.eval x =
      3 * (H.derivative.derivative.eval x * w1.derivative.eval x) +
        3 * (H.derivative.eval x * w1.derivative.derivative.eval x) := by
    linear_combination hw3raw +
      H.derivative.derivative.derivative.eval x * hw1x
  -- transported jets of `phi = H·phi₁ = H²·phi₂`
  have hp1x : phi1.eval x = 0 := by
    rw [hphi12, eval_mul, hx, zero_mul]
  have hp1d := conjugateCoreFirstJet_68 H phi1 phi2 x hphi12 hx
  have hp1dd := conjugateCoreSecondJet_68 H phi1 phi2 x hphi12 hx
  have hp3raw := conjugateCoreThirdJet_68 H phi phi1 x hphi1 hx
  have hp3c : phi.derivative.derivative.derivative.eval x =
      6 * (H.derivative.eval x ^ 2 * phi2.derivative.eval x) := by
    linear_combination hp3raw +
      H.derivative.derivative.derivative.eval x * hp1x +
      3 * H.derivative.derivative.eval x * hp1d +
      3 * H.derivative.eval x * hp1dd +
      6 * (H.derivative.eval x * H.derivative.derivative.eval x) * hphi2x
  -- transported jets of `D = H·D₁` (`H''' = 0` for the degree-two core)
  have hd1 := conjugateCoreFirstJet_68 H D D1 x hD1 hx
  have hd2 := conjugateCoreSecondJet_68 H D D1 x hD1 hx
  have hd3raw := conjugateCoreThirdJet_68 H D D1 x hD1 hx
  have hH3x : H.derivative.derivative.derivative.eval x = 0 := by
    rw [natDegreeTwo_thirdDerivative_zero_68 H hdeg, eval_zero]
  have hd3c : D.derivative.derivative.derivative.eval x =
      3 * (H.derivative.derivative.eval x * D1.derivative.eval x) +
        3 * (H.derivative.eval x * D1.derivative.derivative.eval x) := by
    linear_combination hd3raw + D1.eval x * hH3x
  refine ⟨?_, ?_⟩
  · -- the divided fourth jet
    have hkey : 6 * H.derivative.eval x ^ 2 *
        (b.eval x * phi2.derivative.eval x +
          6 * (w1.derivative.eval x * D1.eval x)) = 0 := by
      linear_combination hjet - b.eval x * hp3c -
        18 * D.derivative.eval x * hw2c -
        36 * H.derivative.eval x * w1.derivative.eval x * hd1
    exact (mul_eq_zero.mp hkey).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hsx))
  · -- the first `j`-loaded quotient load equation
    linear_combination hload -
      3 * b.derivative.eval x * e.eval x * hw2c -
      3 * b.eval x * e.derivative.eval x * hw2c -
      b.eval x * e.eval x * hw3c +
      K.eval x * hd3c +
      3 * K.derivative.eval x * hd2 +
      3 * K.derivative.derivative.eval x * hd1

end RefinedIIIConjugateApexMixedAlgebra68

section RefinedIIIConjugateApexMixedKernel68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Kernel split at the transverse-unit root of an apex-mixed leaf: the
row value ties `b(c)w₁(c)·e(c) = D₁(c)K(c)` against the retained units,
so either the kernel gains both core roots (globalizing to `K = H·K₂`
with the row dropping one core power in the mixed grouping and the
derivative-numerator kill `e(c) = 0`), or the kernel survives and the
row value allocates `D₁(c)`/`e(c)` exactly. -/
def terminalConjugateApexMixedKernelSplit68
    (H b w1 e D1 K : k[X]) (j c : k) : Prop :=
  (∃ K2 : k[X],
      K = H * K2 ∧ b * w1 * e = H * (D1 * K2 + C j * H) ∧
      e.eval c = 0) ∨
  (K.eval c ≠ 0 ∧ D1.eval c = 0 ∧ e.eval c = 0) ∨
  (K.eval c ≠ 0 ∧ D1.eval c ≠ 0 ∧ e.eval c ≠ 0)

theorem terminalConjugateApexMixed_kernel_split_68
    (H b w1 e D1 K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hKa : K.eval a = 0)
    (hbc : b.eval c ≠ 0) (hwc : w1.eval c ≠ 0)
    (hrowq : b * w1 * e - D1 * K = C j * H ^ 2) :
    terminalConjugateApexMixedKernelSplit68 H b w1 e D1 K j c := by
  have hrowc : b.eval c * w1.eval c * e.eval c =
      D1.eval c * K.eval c := by
    have hev := congrArg (fun P : k[X] => P.eval c) hrowq
    simp only [eval_sub, eval_mul, eval_pow, eval_C, hc] at hev
    linear_combination hev
  by_cases hKc : K.eval c = 0
  · left
    obtain ⟨K2, hK2⟩ := dvd_of_two_simple_root_evals_68 H K
      hdeg hsimple a c hac ha hc hKa hKc
    refine ⟨K2, hK2, by linear_combination hrowq + D1 * hK2, ?_⟩
    have h0 : b.eval c * w1.eval c * e.eval c = 0 := by
      rw [hrowc, hKc, mul_zero]
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hbc hwc)
  · by_cases hD1c : D1.eval c = 0
    · refine Or.inr (Or.inl ⟨hKc, hD1c, ?_⟩)
      have h0 : b.eval c * w1.eval c * e.eval c = 0 := by
        rw [hrowc, hD1c, zero_mul]
      exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hbc hwc)
    · refine Or.inr (Or.inr ⟨hKc, hD1c, ?_⟩)
      intro he0
      have h0 : D1.eval c * K.eval c = 0 := by
        rw [← hrowc, he0, mul_zero]
      exact hD1c ((mul_eq_zero.mp h0).resolve_right hKc)

/-- Kernel split of a dead conjugate row product `D₁(c)·K(c) = 0`: the
kernel joins the deep root and globalizes with the dropped row, or the
conjugate determinant kill is pinned against the kernel unit. -/
def terminalConjugateApexMixedKernelDrop68
    (H b w1 e D1 K : k[X]) (j c : k) : Prop :=
  (∃ K2 : k[X],
      K = H * K2 ∧ b * w1 * e = H * (D1 * K2 + C j * H)) ∨
  (K.eval c ≠ 0 ∧ D1.eval c = 0)

theorem terminalConjugateApexMixed_kernel_drop_68
    (H b w1 e D1 K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hKa : K.eval a = 0)
    (hDK : D1.eval c * K.eval c = 0)
    (hrowq : b * w1 * e - D1 * K = C j * H ^ 2) :
    terminalConjugateApexMixedKernelDrop68 H b w1 e D1 K j c := by
  by_cases hKc : K.eval c = 0
  · left
    obtain ⟨K2, hK2⟩ := dvd_of_two_simple_root_evals_68 H K
      hdeg hsimple a c hac ha hc hKa hKc
    exact ⟨K2, hK2, by linear_combination hrowq + D1 * hK2⟩
  · exact Or.inr ⟨hKc, (mul_eq_zero.mp hDK).resolve_right hKc⟩

/-- Kernel split at the transverse-unit root of the `D6` case-A′ leaf,
enriched by the divided `I₄`: on the `K(c) ≠ 0 ∧ D₁(c) = 0` branch the
quotient value kills `phi₂(c)`, which joins the deep kill `phi₂(a) = 0`
and cascades the `phi`-face cube-deep with the exactly cancelled `I₄`;
on the all-units branch `phi₂(c)` is a unit. -/
def terminalConjugateApexMixedPhiCascade68
    (H b w1 phi phi1 phi2 e D1 K : k[X]) (j c : k) : Prop :=
  (∃ K2 : k[X],
      K = H * K2 ∧ b * w1 * e = H * (D1 * K2 + C j * H) ∧
      e.eval c = 0) ∨
  (K.eval c ≠ 0 ∧ D1.eval c = 0 ∧ e.eval c = 0 ∧ phi2.eval c = 0 ∧
    ∃ phi3 : k[X],
      phi2 = H * phi3 ∧ phi1 = H ^ 2 * phi3 ∧ phi = H ^ 3 * phi3 ∧
      6 * (w1 * D1) + H * (b * phi3) = 0) ∨
  (K.eval c ≠ 0 ∧ D1.eval c ≠ 0 ∧ e.eval c ≠ 0 ∧ phi2.eval c ≠ 0)

theorem terminalConjugateApexMixed_phi_cascade_68
    (H b w1 phi phi1 phi2 e D1 K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hKa : K.eval a = 0)
    (hbc : b.eval c ≠ 0) (hwc : w1.eval c ≠ 0)
    (hphi2a : phi2.eval a = 0)
    (hphi12 : phi1 = H * phi2) (hphiq : phi = H ^ 2 * phi2)
    (hI4p : b * phi2 + 6 * w1 * D1 = 0)
    (hrowq : b * w1 * e - D1 * K = C j * H ^ 2) :
    terminalConjugateApexMixedPhiCascade68
      H b w1 phi phi1 phi2 e D1 K j c := by
  have hrowc : b.eval c * w1.eval c * e.eval c =
      D1.eval c * K.eval c := by
    have hev := congrArg (fun P : k[X] => P.eval c) hrowq
    simp only [eval_sub, eval_mul, eval_pow, eval_C, hc] at hev
    linear_combination hev
  have hI4c : b.eval c * phi2.eval c +
      6 * (w1.eval c * D1.eval c) = 0 := by
    have hev := congrArg (fun P : k[X] => P.eval c) hI4p
    simp only [eval_add, eval_mul, eval_ofNat, eval_zero] at hev
    linear_combination hev
  by_cases hKc : K.eval c = 0
  · left
    obtain ⟨K2, hK2⟩ := dvd_of_two_simple_root_evals_68 H K
      hdeg hsimple a c hac ha hc hKa hKc
    refine ⟨K2, hK2, by linear_combination hrowq + D1 * hK2, ?_⟩
    have h0 : b.eval c * w1.eval c * e.eval c = 0 := by
      rw [hrowc, hKc, mul_zero]
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hbc hwc)
  · by_cases hD1c : D1.eval c = 0
    · have he0 : e.eval c = 0 := by
        have h0 : b.eval c * w1.eval c * e.eval c = 0 := by
          rw [hrowc, hD1c, zero_mul]
        exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hbc hwc)
      have hphi2c : phi2.eval c = 0 := by
        have hb0 : b.eval c * phi2.eval c = 0 := by
          linear_combination hI4c - 6 * w1.eval c * hD1c
        exact (mul_eq_zero.mp hb0).resolve_left hbc
      obtain ⟨phi3, hphi3⟩ := dvd_of_two_simple_root_evals_68 H phi2
        hdeg hsimple a c hac ha hc hphi2a hphi2c
      exact Or.inr (Or.inl ⟨hKc, hD1c, he0, hphi2c, phi3, hphi3,
        by linear_combination hphi12 + H * hphi3,
        by linear_combination hphiq + H ^ 2 * hphi3,
        by linear_combination hI4p - b * hphi3⟩)
    · refine Or.inr (Or.inr ⟨hKc, hD1c, ?_, ?_⟩)
      · intro he0
        have h0 : D1.eval c * K.eval c = 0 := by
          rw [← hrowc, he0, mul_zero]
        exact hD1c ((mul_eq_zero.mp h0).resolve_right hKc)
      · intro hp0
        have h6 : (6 : k) * (w1.eval c * D1.eval c) = 0 := by
          linear_combination hI4c - b.eval c * hp0
        rcases mul_eq_zero.mp ((mul_eq_zero.mp h6).resolve_left
            (by norm_num : (6 : k) ≠ 0)) with h | h
        · exact hwc h
        · exact hD1c h

end RefinedIIIConjugateApexMixedKernel68

section RefinedIIIConjugateApexMixedReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Reduced inventory of the `D`-child allocation with both apex-mixed
leaves consumed.  The coordinate exit, the core-one `D∧K` family, the
deep-II family and every provenance record are preserved verbatim; leaf
(4) resolves its coordinate dichotomy (exiting into `H ∣ r` when the
`b`-kill root also kills `r`) and gains the kernel splits, and leaf (5)
gains the coordinate/apex units, the quotient-level jet packets, the
`phi`-cascade kernel split at the conjugate root of case A′ and the
dead-product kernel split of case B′. -/
def terminalRefinedIIIConjugateDAllocationApexMixedReduced68
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
      terminalConjugateDTransverseProvenance68
        H r b D w phi e K D1 w1 phi1 j a c) ∨
  (∃ V : k[X],
      A * b = H * V ∧
      r ^ 2 * b = H * (4 * X0 * b - 12 * V) ∧
      ((b.eval a = 0 ∧ D1.eval a * K.eval a = 0 ∧ b.eval c ≠ 0 ∧
         w1.eval c ≠ 0 ∧ A.eval c = 0 ∧ r.eval c = 0 ∧ t.eval c = 0 ∧
         phi1.eval c = 0 ∧
         r.eval a ≠ 0 ∧ A.eval a ≠ 0 ∧ t.eval a ≠ 0 ∧
         terminalConjugateApexMixedKernelSplit68 H b w1 e D1 K j c) ∨
       (b.eval c = 0 ∧ D1.eval c * K.eval c = 0 ∧ b.eval a ≠ 0 ∧
         w1.eval a ≠ 0 ∧ A.eval a = 0 ∧ r.eval a = 0 ∧ t.eval a = 0 ∧
         phi1.eval a = 0 ∧ e.eval a = 0 ∧
         r.eval c ≠ 0 ∧ A.eval c ≠ 0 ∧ t.eval c ≠ 0 ∧
         terminalConjugateApexMixedKernelDrop68 H b w1 e D1 K j c))) ∨
  (∃ phi2 V : k[X],
      phi1 = H * phi2 ∧ phi = H ^ 2 * phi2 ∧
      b * phi2 + 6 * w1 * D1 = 0 ∧
      A * w1 = H * V ∧
      r ^ 2 * w1 = H * (4 * X0 * w1 - 12 * V) ∧
      b.eval a ≠ 0 ∧ b.eval c ≠ 0 ∧
      ((w1.eval a = 0 ∧ phi2.eval a = 0 ∧ w1.eval c ≠ 0 ∧ A.eval c = 0 ∧
         r.eval c = 0 ∧ t.eval c = 0 ∧ r.eval a ≠ 0 ∧
         A.eval a ≠ 0 ∧ t.eval a ≠ 0 ∧
         terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
           (6 * j * H.derivative.eval a ^ 3) ∧
         terminalConjugateApexMixedJetPacket68 H b w1 phi2 e D1 K j a ∧
         terminalConjugateApexMixedPhiCascade68
           H b w1 phi phi1 phi2 e D1 K j c) ∨
       (w1.eval c = 0 ∧ phi2.eval c = 0 ∧ w1.eval a ≠ 0 ∧ A.eval a = 0 ∧
         r.eval a = 0 ∧ t.eval a = 0 ∧ e.eval a = 0 ∧ r.eval c ≠ 0 ∧
         A.eval c ≠ 0 ∧ t.eval c ≠ 0 ∧
         terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K c
           (6 * j * H.derivative.eval c ^ 3) ∧
         terminalConjugateApexMixedJetPacket68 H b w1 phi2 e D1 K j c ∧
         terminalConjugateApexMixedKernelDrop68 H b w1 e D1 K j c)))

/-- The reduced `D`-child inventory upgrades leaf-by-leaf: the first
three leaves pass through verbatim, and the two apex-mixed leaves
consume their coordinate dichotomies, kernel splits, jet packets and the
`phi`-cascade. -/
theorem terminalRefinedIII_conjugateD_apexMixed_reduction_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hKa : K.eval a = 0)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (w1 phi1 D1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1) (hD1 : D = H * D1)
    (hrowq : b * w1 * e - D1 * K = C j * H ^ 2)
    (hred : terminalRefinedIIIConjugateDAllocationReduced68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateDAllocationApexMixedReduced68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c := by
  rcases hred with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · -- leaf (4): the `b`/apex mixed coordinate leaf
    obtain ⟨V, hV, hprod, hcase⟩ := h
    rcases hcase with ⟨hba, hDKa, hbc, hwc, hAc, hrc, htc, hphic⟩ |
      ⟨hbc, hDKc, hba, hwa, hAa, hra, hta, hphia, hea⟩
    · by_cases hra : r.eval a = 0
      · exact Or.inl (dvd_of_two_simple_root_evals_68 H r hdeg hsimple
          a c hac ha hc hra hrc)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨V, hV, hprod, Or.inl
          ⟨hba, hDKa, hbc, hwc, hAc, hrc, htc, hphic, hra,
            conjugateCoordinateUnit_apex_68 H t r X0 A a hA hX ha hra,
            conjugateCoordinate_t_unit_root_68 H t r X0 a hX ha hra,
            terminalConjugateApexMixed_kernel_split_68 H b w1 e D1 K
              j a c hdeg hsimple ha hc hac hKa hbc hwc hrowq⟩⟩)))
    · by_cases hrcu : r.eval c = 0
      · exact Or.inl (dvd_of_two_simple_root_evals_68 H r hdeg hsimple
          a c hac ha hc hra hrcu)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨V, hV, hprod, Or.inr
          ⟨hbc, hDKc, hba, hwa, hAa, hra, hta, hphia, hea, hrcu,
            conjugateCoordinateUnit_apex_68 H t r X0 A c hA hX hc hrcu,
            conjugateCoordinate_t_unit_root_68 H t r X0 c hX hc hrcu,
            terminalConjugateApexMixed_kernel_drop_68 H b w1 e D1 K
              j a c hdeg hsimple ha hc hac hKa hDKc hrowq⟩⟩)))
  · -- leaf (5): the `w₁`/apex jet-residual leaf
    obtain ⟨phi2, V, hphi12, hphiq, hI4p, hV, hprod, hbau, hbcu,
      hcase⟩ := h
    rcases hcase with ⟨hw1a, hphi2a, hwcu, hAc, hrc, htc, hrau, hresa⟩ |
      ⟨hw1c, hphi2c, hwau, hAa, hra, hta, hea, hrcu, hresc⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨phi2, V, hphi12, hphiq,
        hI4p, hV, hprod, hbau, hbcu, Or.inl
        ⟨hw1a, hphi2a, hwcu, hAc, hrc, htc, hrau,
          conjugateCoordinateUnit_apex_68 H t r X0 A a hA hX ha hrau,
          conjugateCoordinate_t_unit_root_68 H t r X0 a hX ha hrau,
          hresa,
          terminalConjugateApexMixed_jetPacket_68 H r b w phi e D K
            w1 phi1 phi2 D1 j a hdeg ha (hsimple a ha) hw1 hphi1
            hphi12 hD1 hw1a hphi2a hrau hresa,
          terminalConjugateApexMixed_phi_cascade_68 H b w1 phi phi1
            phi2 e D1 K j a c hdeg hsimple ha hc hac hKa hbcu hwcu
            hphi2a hphi12 hphiq hI4p hrowq⟩⟩)))
    · have hDKc : D1.eval c * K.eval c = 0 := by
        have hev := congrArg (fun P : k[X] => P.eval c) hrowq
        simp only [eval_sub, eval_mul, eval_pow, eval_C, hc] at hev
        linear_combination -hev + b.eval c * e.eval c * hw1c
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨phi2, V, hphi12, hphiq,
        hI4p, hV, hprod, hbau, hbcu, Or.inr
        ⟨hw1c, hphi2c, hwau, hAa, hra, hta, hea, hrcu,
          conjugateCoordinateUnit_apex_68 H t r X0 A c hA hX hc hrcu,
          conjugateCoordinate_t_unit_root_68 H t r X0 c hX hc hrcu,
          hresc,
          terminalConjugateApexMixed_jetPacket_68 H r b w phi e D K
            w1 phi1 phi2 D1 j c hdeg hc (hsimple c hc) hw1 hphi1
            hphi12 hD1 hw1c hphi2c hrcu hresc,
          terminalConjugateApexMixed_kernel_drop_68 H b w1 e D1 K
            j a c hdeg hsimple ha hc hac hKa hDKc hrowq⟩⟩)))

/-- The conjugate global split with both apex-mixed `D`-child leaves
reduced.  The common child, the deep conjugate-II child, and the full
`K`-child branch (allocation and reduced inventory) are preserved
verbatim from the allocation-reduction split. -/
def terminalRefinedIIIConjugateApexMixedCoordinateSplit68
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
      terminalRefinedIIIConjugateDAllocationApexMixedReduced68
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
inventory changes, consuming the coordinate dichotomies, kernel splits,
jet packets and `phi`-cascade on its two apex-mixed leaves. -/
theorem terminalRefinedIII_conjugate_apexMixed_split_upgrade_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hKa : K.eval a = 0)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hsplit : terminalRefinedIIIConjugateAllocationReductionSplit68
      H t r X0 A b D w phi e K j a c) :
    terminalRefinedIIIConjugateApexMixedCoordinateSplit68
      H t r X0 A b D w phi e K j a c := by
  rcases hsplit with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4, hrowL, hforall, hP,
      halloc, hred⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4,
      hrowL, hforall, hP, halloc,
      terminalRefinedIII_conjugateD_apexMixed_reduction_68
        H t r X0 A b D w phi e K j a c hdeg hsimple ha hc hac hKa
        hA hX w1 phi1 D1 hw1 hphi1 hD1 hrowL hred⟩))
  · exact Or.inr (Or.inr (Or.inr h))

end RefinedIIIConjugateApexMixedReduction68

section RefinedIIIConjugateApexMixedSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: the coordinate rows carry the exact R-divisor
cascade behind any `H ∣ r` exit (now also fed by the rerouted leaf-(4)
configurations), and at every deep component-III root the conjugate
matching persists with both apex-mixed `D`-child leaves reduced; the
common, conjugate-II, and `K`-child kernel children are preserved
verbatim. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateApexMixedCoordinatePacket
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
               terminalRefinedIIIConjugateApexMixedCoordinateSplit68
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
    terminalRefinedIII_conjugate_apexMixed_split_upgrade_68
      H t r X _ b2 d2 w2 phi2 _ k2 j a c hdeg hsimple ha hc hca.symm
      hKa rfl hX hsplit⟩

end RefinedIIIConjugateApexMixedSource68

end Max11DegreeRoutes
