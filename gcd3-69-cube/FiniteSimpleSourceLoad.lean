import FiniteBoundarySource

/-! # The weight-one load at the remaining simple root

On the singular cubic `s^3 - 3 r^2 s + 2 r^3`, the remaining simple root is
`-2 * r`.  With vanishing transverse residue the leading depressed sextic is
`(4 r^6, -12 r^5, 9 r^4, 4 r^3, -6 r^2)`, and the eighth Faber value there
is the displayed monomial `(130 / 9) * r^8`.  That scalar is the residue of
the weight-one `d`-load.
-/

noncomputable section
open Polynomial

/-- Over a characteristic-zero field, the rational-coefficient eighth Faber
value is ordinary evaluation of the existing eighth Faber polynomial. -/
theorem GCD369CubeFaberEightValueQ_eq_eval
    {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 x : K) :
    GCD369CubeFaberEightValueQ (algebraMap ℚ K)
      a0 a1 a2 a3 a4 x =
      (GCD369CubeFaberEight a0 a1 a2 a3 a4).eval x := by
  simp only [GCD369CubeFaberEightValueQ, GCD369CubeFaberEight,
    Polynomial.eval_add, Polynomial.eval_monomial]
  norm_num
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The eighth Faber value of the leading simple-root sextic is
`(130 / 9) * r ^ 8`. -/
theorem GCD369CubeFaberEightValueQ_simpleRoot
    {k : Type*} [Field k] [CharZero k] (r : k) :
    GCD369CubeFaberEightValueQ (algebraMap ℚ k)
      (4 * r ^ 6) (-12 * r ^ 5) (9 * r ^ 4) (4 * r ^ 3)
      (-6 * r ^ 2) (-2 * r) =
      (130 / 9) * r ^ 8 := by
  simp only [GCD369CubeFaberEightValueQ]
  norm_num
  ring

/-- Equivalent polynomial evaluation of the same simple-root identity. -/
theorem GCD369CubeFaberEight_eval_simpleRoot
    {k : Type*} [Field k] [CharZero k] (r : k) :
    (GCD369CubeFaberEight
      (4 * r ^ 6) (-12 * r ^ 5) (9 * r ^ 4) (4 * r ^ 3)
      (-6 * r ^ 2)).eval (-2 * r) =
      (130 / 9) * r ^ 8 := by
  rw [← GCD369CubeFaberEightValueQ_eq_eval]
  exact GCD369CubeFaberEightValueQ_simpleRoot r

#print axioms GCD369CubeFaberEightValueQ_eq_eval
#print axioms GCD369CubeFaberEightValueQ_simpleRoot
#print axioms GCD369CubeFaberEight_eval_simpleRoot
