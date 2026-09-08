import InfinityC7Assembly
import InfinityC5Before
import InfinityC5Tie
import InfinityC5Middle
import InfinityC5BalancedLate
import InfinityC5Late

/-! # Complete weight-four infinity fan

After `d` and `c7` vanish, the weight-four `c5` load can occur before the
first transverse normal, tie it, lie strictly between it and the intrinsic
cubic term, tie the cubic term, or lie after it.  The preceding modules
close those five cells; this file performs the arithmetic routing.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- On a constant-core infinity branch, the completed `d = c7 = 0` theorem
forces the next Faber parameter `c5` to vanish as well. -/
theorem infinity_c5_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0) :
    S.faberConstantParameters.c5 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  rcases lt_trichotomy (4 * D.faber.scale.p) (2 * T.delta) with
      hbefore | htie | hafter
  · exact S.infinity_c5_eq_zero_strict_before hsdegree T hd0 hc70
      (by simpa only [D] using hbefore)
  · exact S.infinity_c5_eq_zero_at_transverse hsdegree T hd0 hc70
      (by simpa only [D] using htie)
  · rcases lt_trichotomy (4 * D.faber.scale.p) (3 * T.delta) with
        hmiddle | hbalanced | hlate
    · exact S.infinity_c5_eq_zero_singular_middle hsdegree T hd0 hc70
        (by simpa only [D] using hafter)
        (by simpa only [D] using hmiddle)
    · exact (S.infinity_c5_singular_balanced_inconsistent
        hsdegree T hd0 hc70 (by simpa only [D] using hbalanced)).elim
    · exact (S.infinity_c5_singular_late_inconsistent
        hsdegree T hd0 hc70 (by simpa only [D] using hlate)).elim

/-- The first three source loads vanish together on every constant-core
infinity packet. -/
theorem infinity_d_eq_zero_and_c7_eq_zero_and_c5_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale) :
    S.faberConstantParameters.d = 0 ∧
      S.faberConstantParameters.c7 = 0 ∧
      S.faberConstantParameters.c5 = 0 := by
  obtain ⟨hd, hc7⟩ := S.infinity_d_eq_zero_and_c7_eq_zero hsdegree T
  exact ⟨hd, hc7, S.infinity_c5_eq_zero hsdegree T hd hc7⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_c5_eq_zero
#print axioms
  GCD369CubePolynomialSource.infinity_d_eq_zero_and_c7_eq_zero_and_c5_eq_zero
