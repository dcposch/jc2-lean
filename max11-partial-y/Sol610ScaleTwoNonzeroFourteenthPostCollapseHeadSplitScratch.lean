import Sol610ScaleTwoNonzeroFourteenthPostCollapseResidualScratch

/-! # First split of the `(6,10)` post-collapse fourth-tail head

The generic eight-term head has no nonconstant factor.  On the exact
`q₄₁(a) = 0` child retained by the preceding `μ` packet, however, it is
`p₃₂(a)` times one five-term cofactor.  This file records only that honest
split; the complementary `q₄₁(a) ≠ 0` wall remains open.
-/

noncomputable section

namespace Max11DegreeRoutes

section PostCollapseHeadSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- Cofactor multiplying `q₄₁` in the generic post-collapse head. -/
def nonzeroFourteenthPostCollapseQ41Cofactor610
    (w1 a42 p32 p21 p1 : F) : F :=
  24 * a42 * p32 ^ 2 - 36 * p1 * p32 - 18 * p21 ^ 2 +
    48 * p21 * p32 * w1 - 28 * p32 ^ 2 * w1 ^ 2

/-- Cofactor multiplying `p₃₂` in the generic post-collapse head. -/
def nonzeroFourteenthPostCollapseP32Cofactor610
    (w1 p32 q53 p21 q3 : F) : F :=
  10 * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3

set_option maxHeartbeats 4000000 in
/-- The sharp bilateral form `q₄₁ L + p₃₂ N` of the otherwise
unfactorable generic eight-term head. -/
theorem nonzeroFourteenthPostCollapseJetHead610_bilateral
    (w1 a42 p32 q53 p21 p1 q41 q3 : F) :
    nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 =
      (117546246144 : F) *
        (q41 * nonzeroFourteenthPostCollapseQ41Cofactor610
            w1 a42 p32 p21 p1 +
          p32 * nonzeroFourteenthPostCollapseP32Cofactor610
            w1 p32 q53 p21 q3) := by
  simp only [nonzeroFourteenthPostCollapseJetHead610,
    nonzeroFourteenthPostCollapseQ41Cofactor610,
    nonzeroFourteenthPostCollapseP32Cofactor610]
  ring

set_option maxHeartbeats 4000000 in
/-- Exact factorization of the post-collapse head on `q₄₁ = 0`. -/
theorem nonzeroFourteenthPostCollapseJetHead610_q41Zero_factor
    (w1 a42 p32 q53 p21 p1 q41 q3 : F) (hq41 : q41 = 0) :
    nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 =
      (117546246144 : F) * p32 *
        (10 * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3) := by
  simp only [nonzeroFourteenthPostCollapseJetHead610, hq41, mul_zero,
    zero_mul, sub_zero, add_zero]
  ring

set_option maxHeartbeats 4000000 in
/-- Honest scalar split of the `q₄₁ = 0` post-collapse head. -/
theorem nonzeroFourteenthPostCollapseJetHead610_q41Zero_split
    (w1 a42 p32 q53 p21 p1 q41 q3 : F)
    (hhead :
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1
        q41 q3 = 0)
    (hq41 : q41 = 0) :
    p32 = 0 ∨
      10 * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3 = 0 := by
  rw [nonzeroFourteenthPostCollapseJetHead610_q41Zero_factor
    w1 a42 p32 q53 p21 p1 q41 q3 hq41] at hhead
  rcases mul_eq_zero.mp hhead with hconstant | hcofactor
  · have hp32 : p32 = 0 :=
      (mul_eq_zero.mp hconstant).resolve_left (by norm_num)
    exact Or.inl hp32
  · exact Or.inr hcofactor

set_option maxHeartbeats 4000000 in
/-- On `p₃₂ = 0`, the same head is the single monomial
`-2115832430592 q₄₁ p₂₁²`. -/
theorem nonzeroFourteenthPostCollapseJetHead610_p32Zero_factor
    (w1 a42 p32 q53 p21 p1 q41 q3 : F) (hp32 : p32 = 0) :
    nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 = -(2115832430592 : F) * q41 * p21 ^ 2 := by
  simp only [nonzeroFourteenthPostCollapseJetHead610, hp32, zero_pow,
    Nat.ofNat_pos, mul_zero, zero_mul, sub_zero, add_zero]
  ring

set_option maxHeartbeats 4000000 in
/-- Honest scalar split of the `p₃₂ = 0` post-collapse head. -/
theorem nonzeroFourteenthPostCollapseJetHead610_p32Zero_split
    (w1 a42 p32 q53 p21 p1 q41 q3 : F)
    (hhead :
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1
        q41 q3 = 0)
    (hp32 : p32 = 0) : q41 = 0 ∨ p21 = 0 := by
  rw [nonzeroFourteenthPostCollapseJetHead610_p32Zero_factor
    w1 a42 p32 q53 p21 p1 q41 q3 hp32] at hhead
  rcases mul_eq_zero.mp hhead with hconstant | hp21sq
  · have hq41 : q41 = 0 :=
      (mul_eq_zero.mp hconstant).resolve_left (by norm_num)
    exact Or.inl hq41
  · exact Or.inr
      ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hp21sq)

end PostCollapseHeadSplit610

#print axioms nonzeroFourteenthPostCollapseJetHead610_bilateral
#print axioms nonzeroFourteenthPostCollapseJetHead610_q41Zero_factor
#print axioms nonzeroFourteenthPostCollapseJetHead610_q41Zero_split
#print axioms nonzeroFourteenthPostCollapseJetHead610_p32Zero_factor
#print axioms nonzeroFourteenthPostCollapseJetHead610_p32Zero_split

end Max11DegreeRoutes
