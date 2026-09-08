import LowScale68SecondaryRelaxedFirstFacePart01Scratch

/-! # Relaxed first `(6,8)` secondary face after `l = 0`

The tracked extraction in `LowScale68SecondaryExtraction` and
`LowScale68SecondaryOneForms` uses the chamber `2g < n` because the Jacobian
load `l A^4` and the `l`-pieces of the integrated coefficients sit on or
above the first secondary face once `2g ≥ n`.  In the complementary
large-gap chamber the quartic invariant forces `l = 0`.  With that
hypothesis the same leading coefficients can be re-extracted under the
weaker old-weight cutoff `2g < 3n`, except the second one-form row, whose
`alpha A^2` load meets the face as soon as `g ≥ n`.

Exact chambers, remaining loads otherwise arbitrary:

* invariants `F₄`, `F₃` and one-forms `F₂`, `F₀`: `2g < 3n`
* one-form `F₁`: `g < n` (or `2g < 3n` after the extra vanishing `alpha = 0`)
* full five-face classification `e = 0 ∧ a*b = 3*d`: needs `F₁`
* four-equation classification without `F₁`, under `2g < 3n`:
  `(e = 0 ∧ a*b = 3*d) ∨ (e = 0 ∧ c = 0 ∧ a*b = d) ∨ (b = c = d = 0)`
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RelaxedSecondaryFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Abstract classification under the relaxed radius gap -/

/-- The two invariants and the terminal one-form, without `F₁`, leave three
algebraic families.  The middle family `e = 0`, `c = 0`, `a*b = d` is killed
only by `F₁`. -/
theorem firstSecondaryFourThreeZero68_classify
    (a b c d e : k) (ha : a ≠ 0)
    (hfour : firstSecondaryFour68 a b c d e = 0)
    (hthree : firstSecondaryThree68 a b c d e = 0)
    (hzero : firstSecondaryZero68 a b c d e = 0) :
    (e = 0 ∧ a * b = 3 * d) ∨
      (e = 0 ∧ c = 0 ∧ a * b = d) ∨
      (b = 0 ∧ c = 0 ∧ d = 0) := by
  have heFactor : e * (a * b - 3 * d) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-3 : k) ≠ 0)
    calc
      (-3 : k) * (e * (a * b - 3 * d)) =
          a * firstSecondaryFour68 a b c d e -
            firstSecondaryZero68 a b c d e := by
        simp only [firstSecondaryFour68, firstSecondaryZero68]
        ring
      _ = 0 := by rw [hfour, hzero]; ring
  rcases mul_eq_zero.mp heFactor with he0 | hab3
  · have hcFactor : c * (a * b - 3 * d) = 0 := by
      calc
        c * (a * b - 3 * d) = firstSecondaryFour68 a b c d e := by
          simp only [firstSecondaryFour68, he0, mul_zero, sub_zero]
          ring
        _ = 0 := hfour
    rcases mul_eq_zero.mp hcFactor with hc0 | hab3'
    · have hbd : (a * b - d) * (a * b - 3 * d) = 0 := by
        calc
          (a * b - d) * (a * b - 3 * d) =
              firstSecondaryThree68 a b c d e := by
            simp only [firstSecondaryThree68, he0, hc0, mul_zero, add_zero]
            ring
          _ = 0 := hthree
      rcases mul_eq_zero.mp hbd with habd | hab3''
      · exact Or.inr (Or.inl ⟨he0, hc0, sub_eq_zero.mp habd⟩)
      · exact Or.inl ⟨he0, sub_eq_zero.mp hab3''⟩
    · exact Or.inl ⟨he0, sub_eq_zero.mp hab3'⟩
  · have hab3' : a * b = 3 * d := sub_eq_zero.mp hab3
    by_cases he : e = 0
    · exact Or.inl ⟨he, hab3'⟩
    · have hce : c * e = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (6 : k) ≠ 0)
        calc
          (6 : k) * (c * e) = firstSecondaryThree68 a b c d e -
              (a * b - d) * (a * b - 3 * d) := by
            simp only [firstSecondaryThree68]
            ring
          _ = 0 := by rw [hthree, hab3']; ring
      have hc0 : c = 0 := (mul_eq_zero.mp hce).resolve_right he
      have hde : d * e = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-9 : k) ≠ 0)
        calc
          (-9 : k) * (d * e) = firstSecondaryZero68 a b c d e := by
            simp [firstSecondaryZero68, hc0]
            ring
          _ = 0 := hzero
      have hd0 : d = 0 := (mul_eq_zero.mp hde).resolve_right he
      have hb0 : b = 0 := by
        have hab0 : a * b = 0 := by simpa [hd0] using hab3'
        exact (mul_eq_zero.mp hab0).resolve_left ha
      exact Or.inr (Or.inr ⟨hb0, hc0, hd0⟩)

end RelaxedSecondaryFace68
end Max11DegreeRoutes
