import Fable68ScaleTwoRefinedIIIConjugateGlobalQuotientAllocationScratch
import Fable68ScaleTwoAlignedNonsquareRDivisorScratch

/-! # Reduction of the conjugate `D`/`K` quotient-product root allocations

This file continues the exact verified allocation packet without opening any
later Taylor or loaded coefficient row.  Two already-verified sources are
recycled: the coordinate identity `3t - r² = H·X₀` pins the apex numerator
globally, `12·A = 4·H·X₀ - r²`, so at every core root
`A(x) = -(1/12)·r(x)²` — apex kills are coordinate kills, apex units are
coordinate units — and the refined-III transverse residual
(`r(x) = 0` or the retained order-two jet packet) is available at every core
root of the two component-III children where the deep `w`, `phi`, `D` all
vanish and `b` survives.

Consumed / rerouted allocation leaves:

* `D3` (apex at both roots): `A = H·A₁` forces `r(a) = r(c) = 0`, hence
  `H ∣ r` — the leaf exits into the verified R-divisor coordinate cascade
  (`rDivisor_coordinate_cascade_68`), reproduced source-side as `t = H·t₁`,
  `p₄ = H²·t₁`, `p₃ = H·y₁` with exact unit divisions.
* `D1`, `D2`, `D4`: the one-deeper terminal row `D₁·K = H·(U·e - C j·H)`
  is evaluated at the conjugate root.  Either `K(c) = 0` globalizes against
  the deep-root value `K(a) = 0` to `K = H·K₂` and the row drops to the
  *same* core-one shape `U·e - D₁·K₂ = C j·H` as the `K`-child merge
  leaves, or `K(c) ≠ 0` pins the order-two conjugate root `D₁(c) = 0` of
  the loaded `D`.  `D2` (both `b`-units) first splits on the two coordinate
  evaluations and exits into `H ∣ r` when both vanish; otherwise both
  refined-III residuals are retained together with the surviving
  coordinate unit.
* `K3` (`D(c) = 0` branch) and `K4` merge verbatim into the same core-one
  family `U·e - D₁·K₁ = C j·H` with `D = H·D₁`, `K = H·K₁`,
  `b·w = H²·U`; the apex unit at the killing root forces the coordinate
  unit `r ≠ 0` there, so the retained refined-III residual has its
  `r`-branch unreachable and reduces to the order-two jet packet.
* `K1`: the cross identity `2w₁(Ab - 3D) = H·b·G₁` evaluated at both
  simple roots allocates the determinant faces.  The both-roots case
  merges with the `K2` leaf (`Ab - 3D = H·F₁` with the exactly cancelled
  cross `b·G₁ = 2w₁·F₁`); the double `w₁`-kill sends `w`, `phi` two core
  powers deep, and the conjugate root of the divided row splits into the
  core-one family (`D(c) = 0`) or the `K₁(c) = 0` order-two kernel
  residual; the two mixed faces keep exact per-root pins.
* `K2` and every deep face `F(a) = 0`: with `D(a) = 0` the determinant
  value factors, `b(a) = 0` or the apex/coordinate kill
  `A(a) = 0 ∧ r(a) = 0`.
* `D5`, `D6`: the apex products globalize as coordinate products
  `r²·b = H·(4X₀·b - 12V)` resp. `r²·w₁ = H·(4X₀·w₁ - 12V)`, with `r`
  and `t` killed at the apex root; on `D6` the surviving-side residual
  either completes `H ∣ r` (cascade exit) or pins the coordinate unit with
  the retained jet packet.

Exact mismatches — leaves NOT consumable by the existing consumers:

* `terminalRefinedIII_conjugateCommon_transverseNext_68` produces its
  productive faces only at a conjugate root off the deep component
  (`w.eval c ≠ 0`); every `D`/`K` allocation leaf carries `w = H·w₁`,
  hence `w.eval c = 0`, and the consumer's only reachable branch is the
  component-III collapse that the allocation already strictly refines.
* The Sol conjugate-II loaded consumers (`IIF...`, `IIExactFaces`,
  coordinate routing) require the double root `B = (X - C c)²·B₂`, the
  cube-order face `A·B - 3D = (X - C c)³·F₃` and the normalized loaded
  coefficient; no allocation leaf provides more than simple vanishing of
  `b` at one root (`D1` gives `H ∣ b` but no root of `b₁`).
* The refined-III transverse residual requires `b ≠ 0` at the probed
  root: it is unavailable at both roots of `D1` (`b = H·b₁`), at the
  `b`-kill roots of `D4`, `D5`, `K3`, `K4`, and at the conjugate root of
  the `K1`/`K2` faces where `b(c)` is unpinned.
* `K3`'s `K₁(c) = 0` branch lacks `D(c) = 0`, so neither the deep
  component-II merge nor the residual consumer applies; it retains the
  order-two kernel root `K = H·K₁`, `K₁(c) = 0` with the one-deeper row
  `D·K₁ = H·(U·e - C j·H)`.

Literal finite residual inventory (the reduced split below): the
R-divisor cascade exit; the single core-one `D∧K` family
`U·e - D₁·K₂ = C j·H` (next unused row: its order-one `j`-rung); the
order-two `D₁(c) = 0` deep-II family (next: the order-two rung of the
cancelled `H²`-row); the two apex-mixed coordinate leaves from `D5`/`D6`;
the `K1` faces `S1`–`S3`, the double-deep `S5`, the determinant-global
`S6`, and the `S7` kernel residual.
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

section RefinedIIIConjugateAllocationReductionApex68

variable {k : Type*} [Field k] [CharZero k]

/-- The aligned coordinate identity pins the apex numerator globally:
`12·A = 4·H·X₀ - r²`. -/
theorem conjugateApexTwelve_68 (H t r X0 A : k[X])
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0) :
    (12 : k[X]) * A = 4 * (H * X0) - r ^ 2 := by
  have h512 : (12 : k[X]) * C (5 / 12 : k) = 5 := by
    rw [show (12 : k[X]) = C (12 : k) from (C_ofNat 12).symm, ← map_mul,
      show (12 : k) * (5 / 12 : k) = 5 by norm_num]
    exact C_ofNat 5
  rw [hA]
  dsimp only [cubicANumerator68]
  linear_combination 4 * hX - r ^ 2 * h512

/-- At a core root the apex value is `-(1/12)·r(x)²`. -/
theorem conjugateApex_eval_root_68 (H t r X0 A : k[X]) (x : k)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hx : H.eval x = 0) :
    A.eval x = -(1 / 12 : k) * r.eval x ^ 2 := by
  have hxe := congrArg (fun P : k[X] => P.eval x) hX
  simp only [eval_sub, eval_mul, eval_pow, eval_ofNat, hx, zero_mul] at hxe
  rw [hA]
  dsimp only [cubicANumerator68]
  simp only [eval_sub, eval_mul, eval_pow, eval_C]
  linear_combination (1 / 3 : k) * hxe

/-- An apex kill at a core root is a coordinate kill. -/
theorem conjugateApex_zero_root_68 (H t r X0 A : k[X]) (x : k)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hx : H.eval x = 0) (hAx : A.eval x = 0) :
    r.eval x = 0 := by
  have hpin := conjugateApex_eval_root_68 H t r X0 A x hA hX hx
  rw [hAx] at hpin
  have hsq : r.eval x ^ 2 = 0 := by
    linear_combination 12 * hpin
  exact sq_eq_zero_iff.mp hsq

/-- An apex unit at a core root is a coordinate unit. -/
theorem conjugateApex_unit_root_68 (H t r X0 A : k[X]) (x : k)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hx : H.eval x = 0) (hAx : A.eval x ≠ 0) :
    r.eval x ≠ 0 := by
  intro hr0
  apply hAx
  rw [conjugateApex_eval_root_68 H t r X0 A x hA hX hx, hr0]
  ring

/-- A coordinate kill at a core root kills the divided `p₄`-coefficient. -/
theorem conjugateCoordinate_t_root_68 (H t r X0 : k[X]) (x : k)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hx : H.eval x = 0) (hr : r.eval x = 0) :
    t.eval x = 0 := by
  have hxe := congrArg (fun P : k[X] => P.eval x) hX
  simp only [eval_sub, eval_mul, eval_pow, eval_ofNat, hx, zero_mul] at hxe
  linear_combination (1 / 3 : k) * hxe + (1 / 3 : k) * r.eval x * hr

/-- An apex-loaded product divisibility is exactly a coordinate-square
product divisibility: `A·b = H·V` gives `r²·b = H·(4X₀·b - 12V)`. -/
theorem conjugateApex_product_coordinate_68 (H t r X0 A b V : k[X])
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hV : A * b = H * V) :
    r ^ 2 * b = H * (4 * X0 * b - 12 * V) := by
  have h12 := conjugateApexTwelve_68 H t r X0 A hA hX
  linear_combination b * h12 - 12 * hV

/-- Global coordinate divisor entering the verified R-divisor cascade:
both lower coordinate rows split one further core power by exact unit
division. -/
theorem conjugateCoordinate_cascade_of_dvd_68 (H r t X0 Yd p3 p4 : k[X])
    (hp4 : p4 = H * t)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hY : (27 : k[X]) * p3 - r ^ 3 = H * Yd)
    (hr : H ∣ r) :
    ∃ s t1 y1 : k[X],
      r = H * s ∧ t = H * t1 ∧
      (3 : k[X]) * t1 = H * s ^ 2 + X0 ∧
      H ∣ t ∧ H ^ 2 ∣ p4 ∧ H ∣ p3 ∧
      p4 = H ^ 2 * t1 ∧ p3 = H * y1 ∧
      (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd := by
  obtain ⟨s, hs⟩ := hr
  have hcascade := rDivisor_coordinate_cascade_68 H r t X0 Yd p3 p4 s
    hs hp4 hX hY
  exact ⟨s, C (1 / 3 : k) * (H * s ^ 2 + X0),
    C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd),
    hs, hcascade.1, hcascade.2.1, ⟨_, hcascade.1⟩, ⟨_, hcascade.2.2.1⟩,
    ⟨_, hcascade.2.2.2.1⟩, hcascade.2.2.1, hcascade.2.2.2.1,
    hcascade.2.2.2.2⟩

end RefinedIIIConjugateAllocationReductionApex68

section RefinedIIIConjugateAllocationReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Provenance record shared by the two terminal-row families of the
reduced `D`-child: which factor of the transverse product died where,
together with the retained refined-III residuals at the `b`-unit roots
(`D1` kills `b` globally, `D2` keeps both `b`-units with the cube-deep
quotient tie and at least one coordinate unit, `D4` mixes). -/
def terminalConjugateDTransverseProvenance68
    (H r b D w phi e K D1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  (H ∣ b) ∨
  (b.eval a ≠ 0 ∧ b.eval c ≠ 0 ∧
    (∃ w2 phi3 : k[X], w1 = H * w2 ∧ phi1 = H ^ 2 * phi3 ∧
      b * phi3 + 6 * w2 * D1 = 0) ∧
    terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
      (6 * j * H.derivative.eval a ^ 3) ∧
    terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K c
      (6 * j * H.derivative.eval c ^ 3) ∧
    (r.eval a ≠ 0 ∨ r.eval c ≠ 0)) ∨
  ((b.eval a = 0 ∧ b.eval c ≠ 0 ∧ w1.eval c = 0 ∧ phi1.eval c = 0 ∧
     phi1.derivative.eval c = 0 ∧
     terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K c
       (6 * j * H.derivative.eval c ^ 3)) ∨
   (b.eval c = 0 ∧ b.eval a ≠ 0 ∧ w1.eval a = 0 ∧ phi1.eval a = 0 ∧
     phi1.derivative.eval a = 0 ∧
     terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
       (6 * j * H.derivative.eval a ^ 3)))

/-- Reduced inventory of the `D`-child six-leaf allocation.  The apex leaf
exits into `H ∣ r`; the three transverse leaves collapse into the core-one
`D∧K` family or the order-two `D₁(c)`-residual family; the two apex-mixed
leaves convert their apex data into exact coordinate products and pins. -/
def terminalRefinedIIIConjugateDAllocationReduced68
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

/-- The six-leaf `D`-child allocation reduces: apex leaves become
coordinate leaves (`H ∣ r` exits into the R-divisor cascade), the three
transverse leaves split through the conjugate root of the one-deeper
terminal row into the core-one `D∧K` family or the `D₁(c) = 0` residual,
and the refined-III residual is attached at every `b`-unit root. -/
theorem terminalRefinedIII_conjugateD_allocation_reduction_68
    (H t r X0 A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hKa : K.eval a = 0)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (w1 phi1 D1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1) (hD1 : D = H * D1)
    (hI4q : b * phi1 + 6 * H * w1 * D1 = 0)
    (hrowq : b * w1 * e - D1 * K = C j * H ^ 2)
    (hres : ∀ x : k, H.eval x = 0 → b.eval x ≠ 0 →
      terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K x
        (6 * j * H.derivative.eval x ^ 3))
    (halloc : terminalRefinedIIIConjugateDQuotientAllocation68
      H A b w phi e K D1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateDAllocationReduced68
      H t r X0 A b D w phi e K D1 w1 phi1 j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hI4conj : b * phi + 6 * H * w * D1 = 0 := by
    linear_combination b * hphi1 + 6 * H * D1 * hw1 + H * hI4q
  rcases halloc with hleaf | hleaf | hleaf | hleaf | hleaf | hleaf
  · -- `D1`: `b` carries both core roots
    obtain ⟨b1, hb1, hI4b, hrowb⟩ := hleaf
    have hDK : D1.eval c * K.eval c = 0 := by
      have hev := congrArg (fun P : k[X] => P.eval c) hrowb
      simp only [eval_mul, eval_sub, eval_C, hc, zero_mul] at hev
      exact hev
    by_cases hKc : K.eval c = 0
    · right; left
      obtain ⟨K2, hK2⟩ := dvd_of_two_simple_root_evals_68 H K
        hdeg hsimple a c hac ha hc hKa hKc
      refine ⟨K2, b1 * w1, hK2, ?_, hI4conj, ?_, Or.inl ⟨b1, hb1⟩⟩
      · linear_combination w * hb1 + H * b1 * hw1
      · apply mul_left_cancel₀ hH
        linear_combination D1 * hK2 - hrowb
    · right; right; left
      have hD1c : D1.eval c = 0 := (mul_eq_zero.mp hDK).resolve_right hKc
      refine ⟨b1 * w1, hD1c, hKc, ?_, hI4conj, ?_, Or.inl ⟨b1, hb1⟩⟩
      · linear_combination w * hb1 + H * b1 * hw1
      · linear_combination -hrowb
  · -- `D2`: `w1` carries both core roots, `b` a unit at both
    obtain ⟨hba, hbc, w2, phi3, hw2, hphi13, hww2, hphih3, hI4w, hroww⟩ :=
      hleaf
    have hresa := hres a ha hba
    have hresc := hres c hc hbc
    have hkey : (r.eval a ≠ 0 ∨ r.eval c ≠ 0) →
        terminalRefinedIIIConjugateDAllocationReduced68
          H t r X0 A b D w phi e K D1 w1 phi1 j a c := by
      intro hrne
      have hDK : D1.eval c * K.eval c = 0 := by
        have hev := congrArg (fun P : k[X] => P.eval c) hroww
        simp only [eval_mul, eval_sub, eval_C, hc, zero_mul] at hev
        exact hev
      have hprov : terminalConjugateDTransverseProvenance68
          H r b D w phi e K D1 w1 phi1 j a c :=
        Or.inr (Or.inl ⟨hba, hbc, ⟨w2, phi3, hw2, hphi13, hI4w⟩,
          hresa, hresc, hrne⟩)
      by_cases hKc : K.eval c = 0
      · right; left
        obtain ⟨K2, hK2⟩ := dvd_of_two_simple_root_evals_68 H K
          hdeg hsimple a c hac ha hc hKa hKc
        refine ⟨K2, b * w2, hK2, ?_, hI4conj, ?_, hprov⟩
        · linear_combination b * hww2
        · apply mul_left_cancel₀ hH
          linear_combination D1 * hK2 - hroww
      · right; right; left
        have hD1c : D1.eval c = 0 := (mul_eq_zero.mp hDK).resolve_right hKc
        refine ⟨b * w2, hD1c, hKc, ?_, hI4conj, ?_, hprov⟩
        · linear_combination b * hww2
        · linear_combination -hroww
    by_cases hra : r.eval a = 0
    · by_cases hrc : r.eval c = 0
      · exact Or.inl (dvd_of_two_simple_root_evals_68 H r
          hdeg hsimple a c hac ha hc hra hrc)
      · exact hkey (Or.inr hrc)
    · exact hkey (Or.inl hra)
  · -- `D3`: the apex carries both core roots — coordinate exit
    left
    obtain ⟨hba, hbc, hwa, hwc, hea, A1, phi2, hA1, hphi2, hphih2, hI4a⟩ :=
      hleaf
    have hAa : A.eval a = 0 := by rw [hA1]; simp [eval_mul, ha]
    have hAc : A.eval c = 0 := by rw [hA1]; simp [eval_mul, hc]
    have hra := conjugateApex_zero_root_68 H t r X0 A a hA hX ha hAa
    have hrc := conjugateApex_zero_root_68 H t r X0 A c hA hX hc hAc
    exact dvd_of_two_simple_root_evals_68 H r hdeg hsimple a c hac
      ha hc hra hrc
  · -- `D4`: mixed `b`/`w1` allocation
    obtain ⟨hcase, U, hU, hrowU⟩ := hleaf
    have hDK : D1.eval c * K.eval c = 0 := by
      have hev := congrArg (fun P : k[X] => P.eval c) hrowU
      simp only [eval_mul, eval_sub, eval_C, hc, zero_mul] at hev
      exact hev
    have hprov : terminalConjugateDTransverseProvenance68
        H r b D w phi e K D1 w1 phi1 j a c := by
      rcases hcase with ⟨hba, hbc, hwc, hphic, hphipc⟩ |
        ⟨hbc, hba, hwa, hphia, hphipa⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨hba, hbc, hwc, hphic, hphipc, hres c hc hbc⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨hbc, hba, hwa, hphia, hphipa, hres a ha hba⟩))
    by_cases hKc : K.eval c = 0
    · right; left
      obtain ⟨K2, hK2⟩ := dvd_of_two_simple_root_evals_68 H K
        hdeg hsimple a c hac ha hc hKa hKc
      refine ⟨K2, U, hK2, ?_, hI4conj, ?_, hprov⟩
      · linear_combination b * hw1 + H * hU
      · apply mul_left_cancel₀ hH
        linear_combination D1 * hK2 - hrowU
    · right; right; left
      have hD1c : D1.eval c = 0 := (mul_eq_zero.mp hDK).resolve_right hKc
      refine ⟨U, hD1c, hKc, ?_, hI4conj, ?_, hprov⟩
      · linear_combination b * hw1 + H * hU
      · linear_combination -hrowU
  · -- `D5`: mixed `b`/apex allocation — coordinate conversion
    obtain ⟨hcase, V, hV⟩ := hleaf
    right; right; right; left
    refine ⟨V, hV,
      conjugateApex_product_coordinate_68 H t r X0 A b V hA hX hV, ?_⟩
    rcases hcase with ⟨hba, hDKa, hbc, hwc, hAc, hphic⟩ |
      ⟨hbc, hDKc, hba, hwa, hAa, hphia, hea⟩
    · have hrc := conjugateApex_zero_root_68 H t r X0 A c hA hX hc hAc
      exact Or.inl ⟨hba, hDKa, hbc, hwc, hAc, hrc,
        conjugateCoordinate_t_root_68 H t r X0 c hX hc hrc, hphic⟩
    · have hra := conjugateApex_zero_root_68 H t r X0 A a hA hX ha hAa
      exact Or.inr ⟨hbc, hDKc, hba, hwa, hAa, hra,
        conjugateCoordinate_t_root_68 H t r X0 a hX ha hra, hphia, hea⟩
  · -- `D6`: mixed `w1`/apex allocation — coordinate conversion with the
    -- surviving-side residual, or the full `H ∣ r` exit
    obtain ⟨hba, hbc, phi2, V, hphi2, hphih2, hI4p, hV, hcase⟩ := hleaf
    have hproduct := conjugateApex_product_coordinate_68 H t r X0 A w1 V
      hA hX hV
    rcases hcase with ⟨hwa, hphi2a, hwc, hAc⟩ | ⟨hwc, hphi2c, hwa, hAa, hea⟩
    · have hrc := conjugateApex_zero_root_68 H t r X0 A c hA hX hc hAc
      by_cases hra : r.eval a = 0
      · exact Or.inl (dvd_of_two_simple_root_evals_68 H r
          hdeg hsimple a c hac ha hc hra hrc)
      · right; right; right; right
        exact ⟨phi2, V, hphi2, hphih2, hI4p, hV, hproduct, hba, hbc,
          Or.inl ⟨hwa, hphi2a, hwc, hAc, hrc,
            conjugateCoordinate_t_root_68 H t r X0 c hX hc hrc, hra,
            hres a ha hba⟩⟩
    · have hra := conjugateApex_zero_root_68 H t r X0 A a hA hX ha hAa
      by_cases hrc : r.eval c = 0
      · exact Or.inl (dvd_of_two_simple_root_evals_68 H r
          hdeg hsimple a c hac ha hc hra hrc)
      · right; right; right; right
        exact ⟨phi2, V, hphi2, hphih2, hI4p, hV, hproduct, hba, hbc,
          Or.inr ⟨hwc, hphi2c, hwa, hAa, hra,
            conjugateCoordinate_t_root_68 H t r X0 a hX ha hra, hea, hrc,
            hres c hc hbc⟩⟩

/-- Provenance record of the `K`-child core-one merge family: the `b`-kill
leaf (`K3`, `D(c) = 0` branch), the `w1`-kill merge leaf (`K4`), or the
double `w1`-kill of the `G`-face leaf (`K1`), each with the coordinate
unit forced by the apex unit and the retained refined-III residual at the
`b`-unit root. -/
def terminalConjugateKMergeProvenance68
    (H r A b D w phi e K w1 phi1 : k[X]) (j a c : k) : Prop :=
  (b.eval a = 0 ∧ b.eval c ≠ 0 ∧ w1.eval c = 0 ∧ phi1.eval c = 0 ∧
    A.eval c ≠ 0 ∧ r.eval c ≠ 0 ∧
    phi1.eval a + 2 * A.eval a * w1.eval a ≠ 0 ∧
    terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K c
      (6 * j * H.derivative.eval c ^ 3)) ∨
  (b.eval c = 0 ∧ b.eval a ≠ 0 ∧ w1.eval a = 0 ∧ phi1.eval a = 0 ∧
    A.eval a ≠ 0 ∧ r.eval a ≠ 0 ∧
    phi1.eval c + 2 * A.eval c * w1.eval c ≠ 0 ∧
    terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
      (6 * j * H.derivative.eval a ^ 3)) ∨
  (∃ G1 w2 : k[X],
    phi1 + 2 * A * w1 = H * G1 ∧ w1 = H * w2 ∧
    b.eval a ≠ 0 ∧ A.eval a ≠ 0 ∧ r.eval a ≠ 0 ∧
    terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K a
      (6 * j * H.derivative.eval a ^ 3))

/-- Reduced inventory of the `K`-child four-leaf allocation.  The `G`-face
leaf allocates its cross identity across the two simple roots (`S1`–`S3`,
`S5` and the merge family), the merge leaves land in the single core-one
family `S4`, the determinant leaf gains the exact deep factorization, and
the `K₁(c) = 0` kernel branch stays as the `S7` residual. -/
def terminalRefinedIIIConjugateKAllocationReduced68
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
  (phi1.eval a + 2 * A.eval a * w1.eval a ≠ 0 ∧
    A.eval c * b.eval c - 3 * D.eval c ≠ 0 ∧
    b.eval a = 0 ∧ w1.eval c = 0 ∧ phi1.eval c = 0 ∧
    K1.eval c = 0 ∧
    ∃ U : k[X], b * w1 = H * U ∧ D * K1 = H * (U * e - C j * H))

/-- The four-leaf `K`-child allocation reduces: the `G`-face leaf
allocates its retained cross identity across the two simple roots, the
`b`-kill/`w1`-kill merge leaves collapse into the single core-one family,
every deep determinant face factors through the apex into `b(a) = 0` or
the coordinate kill, and apex units force coordinate units that make the
retained refined-III residuals `r`-branch-free. -/
theorem terminalRefinedIII_conjugateK_allocation_reduction_68
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
    (hrowq : b * w1 * e - D * K1 = C j * H ^ 2)
    (hres : ∀ x : k, H.eval x = 0 → D.eval x = 0 → b.eval x ≠ 0 →
      terminalPhiDivisorRefinedIIIResidual68 r b D w phi e K x
        (6 * j * H.derivative.eval x ^ 3))
    (halloc : terminalRefinedIIIConjugateKQuotientAllocation68
      H A b D w phi e K1 w1 phi1 j a c) :
    terminalRefinedIIIConjugateKAllocationReduced68
      H t r X0 A b D w phi e K K1 w1 phi1 j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  rcases halloc with hleaf | hleaf | hleaf | hleaf
  · -- `K1`: the `G`-face carries both core roots — allocate the cross
    obtain ⟨G1, hG1, hGdeep, hcross⟩ := hleaf
    have hcra : 2 * w1.eval a * (A.eval a * b.eval a - 3 * D.eval a) = 0 := by
      have hev := congrArg (fun P : k[X] => P.eval a) hcross
      simp only [eval_mul, eval_sub, eval_ofNat, ha, zero_mul] at hev
      linear_combination hev
    have hcrc : 2 * w1.eval c * (A.eval c * b.eval c - 3 * D.eval c) = 0 := by
      have hev := congrArg (fun P : k[X] => P.eval c) hcross
      simp only [eval_mul, eval_sub, eval_ofNat, hc, zero_mul] at hev
      linear_combination hev
    by_cases hFa : A.eval a * b.eval a - 3 * D.eval a = 0
    · have hpin : b.eval a = 0 ∨ (A.eval a = 0 ∧ r.eval a = 0) := by
        have hAb : A.eval a * b.eval a = 0 := by
          linear_combination hFa + 3 * hDa
        rcases mul_eq_zero.mp hAb with hA0 | hb0
        · exact Or.inr ⟨hA0,
            conjugateApex_zero_root_68 H t r X0 A a hA hX ha hA0⟩
        · exact Or.inl hb0
      by_cases hFc : A.eval c * b.eval c - 3 * D.eval c = 0
      · -- `S1`: the determinant face carries both roots as well
        left
        have hFa' : (A * b - 3 * D).eval a = 0 := by
          simp only [eval_sub, eval_mul, eval_ofNat]
          linear_combination hFa
        have hFc' : (A * b - 3 * D).eval c = 0 := by
          simp only [eval_sub, eval_mul, eval_ofNat]
          linear_combination hFc
        obtain ⟨F1, hF1⟩ := dvd_of_two_simple_root_evals_68 H
          (A * b - 3 * D) hdeg hsimple a c hac ha hc hFa' hFc'
        refine ⟨G1, F1, hG1, hGdeep, hF1, ?_, hpin⟩
        apply mul_left_cancel₀ hH
        linear_combination 2 * w1 * hF1 - hcross
      · -- `S2`: the conjugate root misses the determinant face
        right; left
        have hwc : w1.eval c = 0 := by
          rcases mul_eq_zero.mp hcrc with h2w | hF
          · rcases mul_eq_zero.mp h2w with h2 | hw
            · exact absurd h2 (by norm_num : (2 : k) ≠ 0)
            · exact hw
          · exact absurd hF hFc
        have hphic : phi1.eval c = 0 := by
          have hev := congrArg (fun P : k[X] => P.eval c) hG1
          simp only [eval_add, eval_mul, eval_ofNat, hc, zero_mul] at hev
          linear_combination hev - 2 * A.eval c * hwc
        exact ⟨G1, hG1, hGdeep, hcross, hFa, hpin, hFc, hwc, hphic⟩
    · -- the deep root misses the determinant face
      have hwa : w1.eval a = 0 := by
        rcases mul_eq_zero.mp hcra with h2w | hF
        · rcases mul_eq_zero.mp h2w with h2 | hw
          · exact absurd h2 (by norm_num : (2 : k) ≠ 0)
          · exact hw
        · exact absurd hF hFa
      have hphia : phi1.eval a = 0 := by
        have hev := congrArg (fun P : k[X] => P.eval a) hG1
        simp only [eval_add, eval_mul, eval_ofNat, ha, zero_mul] at hev
        linear_combination hev - 2 * A.eval a * hwa
      have hAb : A.eval a * b.eval a ≠ 0 := by
        intro h0
        exact hFa (by linear_combination h0 - 3 * hDa)
      have hAa : A.eval a ≠ 0 := left_ne_zero_of_mul hAb
      have hba : b.eval a ≠ 0 := right_ne_zero_of_mul hAb
      have hra : r.eval a ≠ 0 :=
        conjugateApex_unit_root_68 H t r X0 A a hA hX ha hAa
      have hresa := hres a ha hDa hba
      by_cases hFc : A.eval c * b.eval c - 3 * D.eval c = 0
      · -- `S3`: the deep transverse jets stay
        right; right; left
        exact ⟨G1, hG1, hGdeep, hcross, hFc, hFa, hwa, hphia, hba, hAa,
          hra, hresa⟩
      · -- the conjugate root also misses: `w1` divides by the core
        have hwc : w1.eval c = 0 := by
          rcases mul_eq_zero.mp hcrc with h2w | hF
          · rcases mul_eq_zero.mp h2w with h2 | hw
            · exact absurd h2 (by norm_num : (2 : k) ≠ 0)
            · exact hw
          · exact absurd hF hFc
        obtain ⟨w2, hw2⟩ := dvd_of_two_simple_root_evals_68 H w1
          hdeg hsimple a c hac ha hc hwa hwc
        have hww2 : w = H ^ 2 * w2 := by
          linear_combination hw1 + H * hw2
        have hphi1G : phi1 = H * (G1 - 2 * A * w2) := by
          linear_combination hG1 - 2 * A * hw2
        have hphiG : phi = H ^ 2 * (G1 - 2 * A * w2) := by
          linear_combination hphi1 + H * hphi1G
        have hI4deep : b * (G1 - 2 * A * w2) + 6 * w2 * D = 0 := by
          apply mul_left_cancel₀ hH
          linear_combination hI4q - b * hphi1G - 6 * D * hw2
        have hDK : D.eval c * K1.eval c = 0 := by
          have hev := congrArg (fun P : k[X] => P.eval c) hrowq
          simp only [eval_sub, eval_mul, eval_pow, eval_C, hc] at hev
          linear_combination -hev + b.eval c * e.eval c * hwc
        by_cases hDc : D.eval c = 0
        · -- `S4` through the double `w1`-kill
          right; right; right; left
          obtain ⟨D1, hD1⟩ := dvd_of_two_simple_root_evals_68 H D
            hdeg hsimple a c hac ha hc hDa hDc
          refine ⟨D1, b * w2, hD1, ?_, ?_, ?_,
            Or.inr (Or.inr ⟨G1, w2, hG1, hw2, hba, hAa, hra, hresa⟩)⟩
          · linear_combination b * hww2
          · linear_combination b * hphi1 + 6 * H * D1 * hw1 + H * hI4q -
              6 * H * w1 * hD1
          · apply mul_left_cancel₀ hH
            linear_combination hrowq - b * e * hw2 + K1 * hD1
        · -- `S5`: the kernel quotient keeps the conjugate row root
          right; right; right; right; left
          have hK1c : K1.eval c = 0 := (mul_eq_zero.mp hDK).resolve_left hDc
          refine ⟨w2, G1, hw2, hww2, hG1, hphi1G, hphiG, hI4deep, ?_,
            hDc, hK1c, hFa, hFc, hba, hAa, hra, hresa⟩
          linear_combination hrowq - b * e * hw2
  · -- `K2`: the determinant face carries both roots
    right; right; right; right; right; left
    obtain ⟨F1, hF1, hcrossF⟩ := hleaf
    refine ⟨F1, hF1, hcrossF, ?_⟩
    have hFa : (A * b - 3 * D).eval a = 0 := by
      rw [hF1]; simp [eval_mul, ha]
    have hAb : A.eval a * b.eval a = 0 := by
      have hFa' : A.eval a * b.eval a - 3 * D.eval a = 0 := by
        simpa only [eval_sub, eval_mul, eval_ofNat] using hFa
      linear_combination hFa' + 3 * hDa
    rcases mul_eq_zero.mp hAb with hA0 | hb0
    · exact Or.inr ⟨hA0,
        conjugateApex_zero_root_68 H t r X0 A a hA hX ha hA0⟩
    · exact Or.inl hb0
  · -- `K3`: the `b`-kill mixed leaf
    obtain ⟨hGa, hFc, hba, hwc, hphic, U, hU, hsub⟩ := hleaf
    rcases hsub with ⟨hDc, hAc, hbc, D1, hD1, hrowD⟩ | ⟨hKc, hrowK⟩
    · -- `S4` through the dead conjugate `D`-root
      right; right; right; left
      have hrc : r.eval c ≠ 0 :=
        conjugateApex_unit_root_68 H t r X0 A c hA hX hc hAc
      refine ⟨D1, U, hD1, ?_, ?_, hrowD,
        Or.inl ⟨hba, hbc, hwc, hphic, hAc, hrc, hGa, hres c hc hDc hbc⟩⟩
      · linear_combination b * hw1 + H * hU
      · linear_combination b * hphi1 + 6 * H * D1 * hw1 + H * hI4q -
          6 * H * w1 * hD1
    · -- `S7`: the kernel residual
      right; right; right; right; right; right
      exact ⟨hGa, hFc, hba, hwc, hphic, hKc, U, hU, hrowK⟩
  · -- `K4`: the `w1`-kill merge leaf
    right; right; right; left
    obtain ⟨hFa, hGc, hAa, hba, hwa, hphia, hbc, hDc, D1, U, hD1, hU,
      hI4D, hrowD⟩ := hleaf
    have hra : r.eval a ≠ 0 :=
      conjugateApex_unit_root_68 H t r X0 A a hA hX ha hAa
    refine ⟨D1, U, hD1, ?_, ?_, hrowD,
      Or.inr (Or.inl ⟨hbc, hba, hwa, hphia, hAa, hra, hGc,
        hres a ha hDa hba⟩)⟩
    · linear_combination b * hw1 + H * hU
    · linear_combination b * hphi1 + 6 * H * D1 * hw1 + H * hI4D

/-- The conjugate global split with both component-III children carrying
the full allocation data and the new reduced inventories.  The common and
component-II children, the divided identities, the per-root quotient
splits, the product divisibilities and the deep-root left-zero selector
are retained verbatim from the allocation split. -/
def terminalRefinedIIIConjugateAllocationReductionSplit68
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
        H t r X0 A b D w phi e K K1 w1 phi1 j a c))

end RefinedIIIConjugateAllocationReduction68

section RefinedIIIConjugateAllocationReductionSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: the coordinate rows carry the exact R-divisor
cascade behind any `H ∣ r` exit, and at every deep component-III root the
conjugate matching persists with both component-III children carrying
their allocations and the new reduced inventories. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateAllocationReductionPacket
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
               terminalRefinedIIIConjugateAllocationReductionSplit68
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
    exact Or.inr (Or.inr (Or.inr
      ⟨w1, phi1x, K1, hw1, hphi1x, hK1, hI4L, hrowL, hforall, hFG,
        hleftA, halloc, hreduced⟩))

end RefinedIIIConjugateAllocationReductionSource68

end Max11DegreeRoutes
