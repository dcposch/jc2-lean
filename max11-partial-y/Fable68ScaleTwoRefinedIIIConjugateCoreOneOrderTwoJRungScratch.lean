import Fable68ScaleTwoRefinedIIIConjugateCoreOneJRungScratch

/-! # Order-two `H''`-rung of the merged core-one `D∧K` family

The order-one `j`-rung packet left the merged six-source core-one family
`U·ė - D₁·K₂ = Cj·H` with the exhaustive seven-child zero/nonzero split
of its first rung at both simple core roots, and identified as the next
unused row for this family the *order-two* rung of the same core-one
row.  This file consumes exactly that rung — no other Taylor row, no
degree bound, no root identification.  Differentiating the row twice
gives globally

  `U''·ė + 2U'·ė' + U·ė'' - D₁''·K₂ - 2D₁'·K₂' - D₁·K₂'' = j·H''`,

and since the core `H` has degree two over characteristic zero its
second derivative is the constant unit `H'' = C (2·lead H)` — so at a
core root `x` the rung is `j`-loaded through `j·H''(x) ≠ 0`, first
loading the second jets `U''`, `ė''`, `D₁''`, `K₂''`.

All seven first-rung chambers are preserved verbatim; each gains its
exactly reduced second rung (the value factors dead in that chamber are
deleted, nothing else is touched):

* all four values units: the full second rung is retained whole;
* `U(x) = 0`, `D₁(x) = 0`: `U''ė + 2U'ė' - D₁''K₂ - 2D₁'K₂' = jH''`;
* `U(x) = 0`, `K₂(x) = 0`: `U''ė + 2U'ė' - 2D₁'K₂' - D₁K₂'' = jH''`;
* `ė(x) = 0`, `D₁(x) = 0`: `2U'ė' + Uė'' - D₁''K₂ - 2D₁'K₂' = jH''`;
* `ė(x) = 0`, `K₂(x) = 0`: `2U'ė' + Uė'' - 2D₁'K₂' - D₁K₂'' = jH''`;
* double kill `U(x) = ė(x) = 0` with `D₁(x) = 0` (unit pin
  `D₁'K₂ = -jH'` retained): `2U'ė' - D₁''K₂ - 2D₁'K₂' = jH''`;
* double kill with `K₂(x) = 0` (unit pin `D₁K₂' = -jH'` retained):
  `2U'ė' - 2D₁'K₂' - D₁K₂'' = jH''`.

The strongest honest closure at this order, beyond the reduced rungs
themselves, is the *total jet kill*: in every chamber the reduced second
rung is a sum of terms each carrying at least one first- or second-jet
factor of the quadruple, so with the `H''`-unit the eight jets
`U'`, `U''`, `ė'`, `ė''`, `D₁'`, `D₁''`, `K₂'`, `K₂''` cannot all die at
a core root — `terminalConjugateCoreOneFamilyOrderTwoJRunged68_no_total_jet_kill`.
The order-one closure (no total kill of the four values) is carried
through unchanged.  No further closure is claimed: the algebra is
satisfiable and the family survives.

Both three-fold provenance records are preserved verbatim
(`terminalConjugateDTransverseProvenance68` on the `D`-child sources
`D1`/`D2`/`D4`, `terminalConjugateKMergeProvenance68` on the `K`-child
sources `K3`-dead-`D`/`K4`/`K1`-`w₁`), as are the once-cancelled
transverse product `b·w₁ = H·U` with its order-one root faces, all
non-core-one leaves of both reduced allocations, the quotient splits,
the product divisibilities, the conjugate matching and the `H ∣ r`
cascade exit.

Exact residual (no closure overclaim): per core root the seven-child
split remains, each child now carrying its first *and* second rung
identities; the rung constrains only the first and second jets of `U`,
`ė`, `D₁`, `K₂` at the two roots.  The `j`-loaded ladder of the
core-one row is exhausted here: `H''' = 0` for the degree-two core, so
the order-three rung of this row is `j`-free
(`U'''ė + 3U''ė' + 3U'ė'' + Uė''' - D₁'''K₂ - 3D₁''K₂' - 3D₁'K₂''
- D₁K₂''' = 0` at every point) and is the next unused row of this
family.  The previously identified sibling rows remain untouched: the
order-three rung (`6jH'H''`) of the `D₁(c) = 0` deep-II family, the
kernel-leaf divided-row order-two rung at `c`, and the join of the
three sibling splits on the common parent.
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

section CoreOneOrderTwoJRungValue68

variable {k : Type*} [Field k] [CharZero k]

/-- Over characteristic zero a degree-two core has a globally nonzero
second derivative: `H''` is the constant `C (2·lead H)`.  This is the
unit that loads the order-two rung of the core-one row. -/
theorem natDegree_two_second_derivative_eval_ne_zero_68
    {H : k[X]} (hdeg : H.natDegree = 2) (x : k) :
    H.derivative.derivative.eval x ≠ 0 := by
  have hd1 : H.derivative.natDegree = 1 := by
    simp [natDegree_derivative, hdeg]
  have hne : H.derivative.derivative ≠ 0 :=
    derivative_ne_zero.mpr (by simp [hd1])
  have hd2 : H.derivative.derivative.natDegree = 0 := by
    simp [natDegree_derivative, hd1]
  have hC := eq_C_of_natDegree_eq_zero hd2
  intro h0
  rw [hC, eval_C] at h0
  exact hne (by rw [hC, h0, C_0])

/-- Exhaustive order-two refinement of the seven first-rung chambers at
one core root: each chamber keeps its order-one data verbatim (values,
value tie, first rung or `j`-loaded unit pin) and gains its exactly
reduced second rung `upp·ev + 2·up·ep + u·epp - dpp·k2 - 2·dp·k2p -
d·k2pp = load2` with the chamber's dead value factors deleted. -/
def terminalCoreOneOrderTwoJRungSplit68
    (u up upp ev ep epp d dp dpp k2 k2p k2pp load load2 : k) : Prop :=
  (u ≠ 0 ∧ ev ≠ 0 ∧ d ≠ 0 ∧ k2 ≠ 0 ∧ u * ev = d * k2 ∧
    up * ev + u * ep - dp * k2 - d * k2p = load ∧
    upp * ev + 2 * (up * ep) + u * epp - dpp * k2 - 2 * (dp * k2p) -
      d * k2pp = load2) ∨
  (u = 0 ∧ ev ≠ 0 ∧ d = 0 ∧ up * ev - dp * k2 = load ∧
    upp * ev + 2 * (up * ep) - dpp * k2 - 2 * (dp * k2p) = load2) ∨
  (u = 0 ∧ ev ≠ 0 ∧ d ≠ 0 ∧ k2 = 0 ∧ up * ev - d * k2p = load ∧
    upp * ev + 2 * (up * ep) - 2 * (dp * k2p) - d * k2pp = load2) ∨
  (ev = 0 ∧ u ≠ 0 ∧ d = 0 ∧ u * ep - dp * k2 = load ∧
    2 * (up * ep) + u * epp - dpp * k2 - 2 * (dp * k2p) = load2) ∨
  (ev = 0 ∧ u ≠ 0 ∧ d ≠ 0 ∧ k2 = 0 ∧ u * ep - d * k2p = load ∧
    2 * (up * ep) + u * epp - 2 * (dp * k2p) - d * k2pp = load2) ∨
  (u = 0 ∧ ev = 0 ∧ d = 0 ∧ k2 ≠ 0 ∧ dp ≠ 0 ∧ dp * k2 = -load ∧
    2 * (up * ep) - dpp * k2 - 2 * (dp * k2p) = load2) ∨
  (u = 0 ∧ ev = 0 ∧ k2 = 0 ∧ d ≠ 0 ∧ k2p ≠ 0 ∧ d * k2p = -load ∧
    2 * (up * ep) - 2 * (dp * k2p) - d * k2pp = load2)

/-- The first-rung split and the raw order-two rung refine to the
order-two split: each chamber's second rung reduces exactly under that
chamber's dead values, and nothing else moves. -/
theorem terminalCoreOne_orderTwo_jRung_split_68
    {u up upp ev ep epp d dp dpp k2 k2p k2pp load load2 : k}
    (hfirst : terminalCoreOneJRungSplit68 u up ev ep d dp k2 k2p load)
    (hrung2 : upp * ev + 2 * (up * ep) + u * epp - dpp * k2 -
      2 * (dp * k2p) - d * k2pp = load2) :
    terminalCoreOneOrderTwoJRungSplit68
      u up upp ev ep epp d dp dpp k2 k2p k2pp load load2 := by
  rcases hfirst with ⟨hu, he, hd, hk2, hval, hrung⟩ |
    ⟨hu, he, hd, hrung⟩ | ⟨hu, he, hd, hk2, hrung⟩ |
    ⟨he, hu, hd, hrung⟩ | ⟨he, hu, hd, hk2, hrung⟩ |
    ⟨hu, he, hd, hk2, hdp, hpin⟩ | ⟨hu, he, hk2, hd, hk2p, hpin⟩
  · exact Or.inl ⟨hu, he, hd, hk2, hval, hrung, hrung2⟩
  · exact Or.inr (Or.inl ⟨hu, he, hd, hrung,
      by linear_combination hrung2 - epp * hu + k2pp * hd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hu, he, hd, hk2, hrung,
      by linear_combination hrung2 - epp * hu + dpp * hk2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hu, hd, hrung,
      by linear_combination hrung2 - upp * he + k2pp * hd⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hu, hd, hk2, hrung,
      by linear_combination hrung2 - upp * he + dpp * hk2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hu, he, hd, hk2, hdp, hpin,
        by linear_combination hrung2 - upp * he - epp * hu + k2pp * hd⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hu, he, hk2, hd, hk2p, hpin,
        by linear_combination hrung2 - upp * he - epp * hu + dpp * hk2⟩)))))

/-- The order-one closure is carried through: every order-two chamber
keeps at least one of the four core-one values alive. -/
theorem terminalCoreOneOrderTwoJRungSplit68_not_total_kill
    {u up upp ev ep epp d dp dpp k2 k2p k2pp load load2 : k}
    (h : terminalCoreOneOrderTwoJRungSplit68
      u up upp ev ep epp d dp dpp k2 k2p k2pp load load2) :
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

/-- Genuine order-two closure: every chamber's reduced second rung is a
sum of terms each carrying a first- or second-jet factor, so with the
loaded `H''`-unit the eight jets of the core-one quadruple cannot all
die at a core root. -/
theorem terminalCoreOneOrderTwoJRungSplit68_no_total_jet_kill
    {u up upp ev ep epp d dp dpp k2 k2p k2pp load load2 : k}
    (hload2 : load2 ≠ 0)
    (h : terminalCoreOneOrderTwoJRungSplit68
      u up upp ev ep epp d dp dpp k2 k2p k2pp load load2) :
    ¬(up = 0 ∧ upp = 0 ∧ ep = 0 ∧ epp = 0 ∧ dp = 0 ∧ dpp = 0 ∧
      k2p = 0 ∧ k2pp = 0) := by
  rintro ⟨hup, hupp, hep, hepp, hdp, hdpp, hk2p, hk2pp⟩
  rcases h with ⟨-, -, -, -, -, -, h2⟩ | ⟨-, -, -, -, h2⟩ |
    ⟨-, -, -, -, -, h2⟩ | ⟨-, -, -, -, h2⟩ | ⟨-, -, -, -, -, h2⟩ |
    ⟨-, -, -, -, -, -, h2⟩ | ⟨-, -, -, -, -, -, h2⟩
  · exact hload2 (by linear_combination -h2 + ev * hupp + 2 * ep * hup +
      u * hepp - k2 * hdpp - 2 * k2p * hdp - d * hk2pp)
  · exact hload2 (by linear_combination -h2 + ev * hupp + 2 * ep * hup -
      k2 * hdpp - 2 * k2p * hdp)
  · exact hload2 (by linear_combination -h2 + ev * hupp + 2 * ep * hup -
      2 * k2p * hdp - d * hk2pp)
  · exact hload2 (by linear_combination -h2 + 2 * ep * hup + u * hepp -
      k2 * hdpp - 2 * k2p * hdp)
  · exact hload2 (by linear_combination -h2 + 2 * ep * hup + u * hepp -
      2 * k2p * hdp - d * hk2pp)
  · exact hload2 (by linear_combination -h2 + 2 * ep * hup - k2 * hdpp -
      2 * k2p * hdp)
  · exact hload2 (by linear_combination -h2 + 2 * ep * hup -
      2 * k2p * hdp - d * hk2pp)

end CoreOneOrderTwoJRungValue68

section CoreOneOrderTwoJRungFamily68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The merged six-source core-one `D∧K` family with both the order-one
and the order-two rungs of its row opened at every core root.  The eight
global identities and the three-fold provenance of the originating child
are retained verbatim; at every core root the family carries the dead
transverse value `b(x)·w₁(x) = 0`, the once-cancelled transverse tie
`b'(x)·w₁(x) + b(x)·w₁'(x) = H'(x)·U(x)`, and the exhaustive order-two
rung split on the jets of `(U, ė, D₁, K₂)` with loads `j·H'(x)` and
`j·H''(x)`. -/
def terminalConjugateCoreOneFamilyOrderTwoJRunged68
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
      terminalCoreOneOrderTwoJRungSplit68 (U.eval x)
        (U.derivative.eval x) (U.derivative.derivative.eval x)
        (e.eval x) (e.derivative.eval x)
        (e.derivative.derivative.eval x)
        (D1.eval x) (D1.derivative.eval x)
        (D1.derivative.derivative.eval x)
        (K2.eval x) (K2.derivative.eval x)
        (K2.derivative.derivative.eval x)
        (j * H.derivative.eval x)
        (j * H.derivative.derivative.eval x))

/-- Frontier consumption: the `j`-runged merged family opens the
order-two rung of its row at every core root.  The raw second rung is
the twice-differentiated row (`(Cj·H)'' = Cj·H''` — no root hypothesis
is even needed), and it reduces chamber by chamber through the
first-rung split. -/
theorem terminalConjugateCoreOneFamily_orderTwoJRunged_of_jRunged_68
    (H r A b D w phi e K D1 K2 U w1 phi1 : k[X]) (j a c : k)
    (hfam : terminalConjugateCoreOneFamilyJRunged68
      H r A b D w phi e K D1 K2 U w1 phi1 j a c) :
    terminalConjugateCoreOneFamilyOrderTwoJRunged68
      H r A b D w phi e K D1 K2 U w1 phi1 j a c := by
  obtain ⟨hD1, hK2, hw1, hphi1, hbw, hbw1, hI4, hrow, hprov, hroots⟩ :=
    hfam
  refine ⟨hD1, hK2, hw1, hphi1, hbw, hbw1, hI4, hrow, hprov, ?_⟩
  intro x hx
  obtain ⟨hbwx, htie, hsplit⟩ := hroots x hx
  have hrung2 : U.derivative.derivative.eval x * e.eval x +
      2 * (U.derivative.eval x * e.derivative.eval x) +
      U.eval x * e.derivative.derivative.eval x -
      D1.derivative.derivative.eval x * K2.eval x -
      2 * (D1.derivative.eval x * K2.derivative.eval x) -
      D1.eval x * K2.derivative.derivative.eval x =
      j * H.derivative.derivative.eval x := by
    have h := congrArg (fun P : k[X] => P.derivative.derivative.eval x)
      hrow
    simp only [derivative_sub, derivative_add, derivative_mul,
      derivative_C, zero_mul, mul_zero, zero_add, add_zero, sub_zero,
      eval_add, eval_sub, eval_mul, eval_C] at h
    linear_combination h
  exact ⟨hbwx, htie,
    terminalCoreOne_orderTwo_jRung_split_68 hsplit hrung2⟩

/-- Carried closure: at no core root of the merged family can the four
core-one values `U`, `ė`, `D₁`, `K₂` all die. -/
theorem terminalConjugateCoreOneFamilyOrderTwoJRunged68_no_total_kill
    (H r A b D w phi e K D1 K2 U w1 phi1 : k[X]) (j a c : k) (x : k)
    (hfam : terminalConjugateCoreOneFamilyOrderTwoJRunged68
      H r A b D w phi e K D1 K2 U w1 phi1 j a c)
    (hx : H.eval x = 0) :
    ¬(U.eval x = 0 ∧ e.eval x = 0 ∧ D1.eval x = 0 ∧ K2.eval x = 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hrung⟩ := hfam
  exact terminalCoreOneOrderTwoJRungSplit68_not_total_kill
    ((hrung x hx).2.2)

/-- Genuine order-two closure at family level: with the degree-two core
and `j ≠ 0` the load `j·H''(x)` is a unit, so at no core root can the
eight first- and second-jet coordinates of `U`, `ė`, `D₁`, `K₂` all
die. -/
theorem terminalConjugateCoreOneFamilyOrderTwoJRunged68_no_total_jet_kill
    (H r A b D w phi e K D1 K2 U w1 phi1 : k[X]) (j a c : k) (x : k)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (hfam : terminalConjugateCoreOneFamilyOrderTwoJRunged68
      H r A b D w phi e K D1 K2 U w1 phi1 j a c)
    (hx : H.eval x = 0) :
    ¬(U.derivative.eval x = 0 ∧ U.derivative.derivative.eval x = 0 ∧
      e.derivative.eval x = 0 ∧ e.derivative.derivative.eval x = 0 ∧
      D1.derivative.eval x = 0 ∧ D1.derivative.derivative.eval x = 0 ∧
      K2.derivative.eval x = 0 ∧
      K2.derivative.derivative.eval x = 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hrung⟩ := hfam
  exact terminalCoreOneOrderTwoJRungSplit68_no_total_jet_kill
    (mul_ne_zero hj (natDegree_two_second_derivative_eval_ne_zero_68
      hdeg x))
    ((hrung x hx).2.2)

/-- The `D`-child reduced allocation with the core-one leaf upgraded to
the order-two-runged merged family; the `H ∣ r` exit, the `D₁(c) = 0`
residual family and both apex-mixed coordinate leaves are retained
verbatim. -/
def terminalRefinedIIIConjugateDAllocationOrderTwoJRunged68
    (H t r X0 A b D w phi e K D1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  H ∣ r ∨
  (∃ K2 U : k[X],
      terminalConjugateCoreOneFamilyOrderTwoJRunged68
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
upgraded to the order-two-runged merged family; `S1`–`S3`, `S5`–`S7`
are retained verbatim. -/
def terminalRefinedIIIConjugateKAllocationOrderTwoJRunged68
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
      terminalConjugateCoreOneFamilyOrderTwoJRunged68
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

/-- The `D`-child `j`-runged allocation upgrades: its core-one leaf
opens the order-two rung, all other leaves pass through verbatim. -/
theorem terminalRefinedIII_conjugateD_allocation_orderTwoJRung_68
    (H t r X0 A b D w phi e K D1 w1 phi1 : k[X]) (j a c : k)
    (hrunged : terminalRefinedIIIConjugateDAllocationJRunged68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateDAllocationOrderTwoJRunged68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c := by
  rcases hrunged with hr | ⟨K2, U, hfam⟩ | hleaf | hleaf | hleaf
  · exact Or.inl hr
  · exact Or.inr (Or.inl ⟨K2, U,
      terminalConjugateCoreOneFamily_orderTwoJRunged_of_jRunged_68 H r A
        b D w phi e K D1 K2 U w1 phi1 j a c hfam⟩)
  · exact Or.inr (Or.inr (Or.inl hleaf))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hleaf)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hleaf)))

/-- The `K`-child `j`-runged allocation upgrades: its core-one merge
leaf opens the order-two rung, all other leaves pass through
verbatim. -/
theorem terminalRefinedIII_conjugateK_allocation_orderTwoJRung_68
    (H t r X0 A b D w phi e K K1 w1 phi1 : k[X]) (j a c : k)
    (hrunged : terminalRefinedIIIConjugateKAllocationJRunged68
      H t r X0 A b D w phi e K K1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateKAllocationOrderTwoJRunged68
      H t r X0 A b D w phi e K K1 w1 phi1 j a c := by
  rcases hrunged with hleaf | hleaf | hleaf | ⟨D1, U, hfam⟩ |
    hleaf | hleaf | hleaf
  · exact Or.inl hleaf
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr (Or.inl hleaf))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨D1, U,
      terminalConjugateCoreOneFamily_orderTwoJRunged_of_jRunged_68 H r A
        b D w phi e K D1 K1 U w1 phi1 j a c hfam⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hleaf))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hleaf)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hleaf)))))

/-- The conjugate global split with both component-III children carrying
their allocations and the order-two-runged reduced inventories.  The
common and component-II children, the divided identities, the per-root
quotient splits, the product divisibilities and the deep-root left-zero
selector are retained verbatim from the order-one split. -/
def terminalRefinedIIIConjugateCoreOneOrderTwoJRungSplit68
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
      terminalRefinedIIIConjugateDAllocationOrderTwoJRunged68
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
      terminalRefinedIIIConjugateKAllocationOrderTwoJRunged68
        H t r X0 A b D w phi e K K1 w1 phi1 j a c))

/-- The order-one `j`-rung split upgrades to the order-two split: only
the two core-one leaves change, everything else passes through
verbatim.  No new hypothesis is needed — the raw second rung is a
global identity of the row. -/
theorem terminalRefinedIII_conjugate_coreOne_orderTwo_jRung_split_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hsplit : terminalRefinedIIIConjugateCoreOneJRungSplit68
      H t r X0 A b D w phi e K j a c) :
    terminalRefinedIIIConjugateCoreOneOrderTwoJRungSplit68
      H t r X0 A b D w phi e K j a c := by
  rcases hsplit with hcommon | hII | hD | hK
  · exact Or.inl hcommon
  · exact Or.inr (Or.inl hII)
  · obtain ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4, hrow, hforall, hP,
      halloc, hrunged⟩ := hD
    exact Or.inr (Or.inr (Or.inl ⟨w1, phi1, D1, hw1, hphi1, hD1, hI4,
      hrow, hforall, hP, halloc,
      terminalRefinedIII_conjugateD_allocation_orderTwoJRung_68 H t r X0
        A b D w phi e K D1 w1 phi1 j a c hrunged⟩))
  · obtain ⟨w1, phi1, K1, hw1, hphi1, hK1, hI4, hrow, hforall, hFG,
      hleftA, halloc, hrunged⟩ := hK
    exact Or.inr (Or.inr (Or.inr ⟨w1, phi1, K1, hw1, hphi1, hK1, hI4,
      hrow, hforall, hFG, hleftA, halloc,
      terminalRefinedIII_conjugateK_allocation_orderTwoJRung_68 H t r X0
        A b D w phi e K K1 w1 phi1 j a c hrunged⟩))

end CoreOneOrderTwoJRungFamily68

section CoreOneOrderTwoJRungSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: the coordinate rows carry the exact R-divisor
cascade behind any `H ∣ r` exit, and at every deep component-III root
the conjugate matching persists with both component-III children
carrying their allocations and the order-two-runged reduced inventories
— in particular the merged six-source core-one family returns with both
the order-one and the order-two rungs of its row opened at both simple
core roots. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateCoreOneOrderTwoJRungPacket
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
               terminalRefinedIIIConjugateCoreOneOrderTwoJRungSplit68
                 H t r X A0 b2 d2 w2 phi2 eDot k2 j a c)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hcasc, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorConjugateCoreOneJRungPacket
      (H := H) hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hcasc, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hroots ⊢
  intro a ha hwa hphia hDa hKa
  obtain ⟨c, hca, hc, hmatch, hsplit⟩ := hroots a ha hwa hphia hDa hKa
  exact ⟨c, hca, hc, hmatch,
    terminalRefinedIII_conjugate_coreOne_orderTwo_jRung_split_68 H t r X
      (cubicANumerator68 t r) b2 d2 w2 phi2
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r))
      k2 j a c hsplit⟩

end CoreOneOrderTwoJRungSource68

end Max11DegreeRoutes
