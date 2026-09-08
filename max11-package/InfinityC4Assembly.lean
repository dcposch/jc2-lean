import InfinityC5Assembly
import InfinityC4Before
import InfinityC4Tie
import InfinityC4Middle
import InfinityC4Balanced
import InfinityC4Late

/-! # Complete weight-five infinity fan

After `d`, `c7`, and `c5` vanish, the weight-five `c4` load has the same
five timing cells relative to the first transverse normal and the intrinsic
cubic term.  The preceding modules close each cell; this file assembles the
global result.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- On a constant-core infinity branch, vanishing through `c5` forces the
next Faber parameter `c4` to vanish. -/
theorem infinity_c4_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0) :
    S.faberConstantParameters.c4 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  rcases lt_trichotomy (5 * D.faber.scale.p) (2 * T.delta) with
      hbefore | htie | hafter
  · exact S.infinity_c4_eq_zero_strict_before hsdegree T hd0 hc70 hc50
      (by simpa only [D] using hbefore)
  · exact S.infinity_c4_eq_zero_at_transverse hsdegree T hd0 hc70 hc50
      (by simpa only [D] using htie)
  · rcases lt_trichotomy (5 * D.faber.scale.p) (3 * T.delta) with
        hmiddle | hbalanced | hlate
    · exact S.infinity_c4_eq_zero_singular_middle hsdegree T hd0 hc70 hc50
        (by simpa only [D] using hafter)
        (by simpa only [D] using hmiddle)
    · exact (S.infinity_c4_singular_balanced_inconsistent
        hsdegree T hd0 hc70 hc50
          (by simpa only [D] using hbalanced)).elim
    · exact (S.infinity_c4_singular_late_inconsistent
        hsdegree T hd0 hc70 hc50 (by simpa only [D] using hlate)).elim

/-- The first four relevant source loads vanish together on every
constant-core infinity packet. -/
theorem infinity_d_eq_zero_and_c7_eq_zero_and_c5_eq_zero_and_c4_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale) :
    S.faberConstantParameters.d = 0 ∧
      S.faberConstantParameters.c7 = 0 ∧
      S.faberConstantParameters.c5 = 0 ∧
      S.faberConstantParameters.c4 = 0 := by
  obtain ⟨hd, hc7, hc5⟩ :=
    S.infinity_d_eq_zero_and_c7_eq_zero_and_c5_eq_zero hsdegree T
  exact ⟨hd, hc7, hc5, S.infinity_c4_eq_zero hsdegree T hd hc7 hc5⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_c4_eq_zero
#print axioms
  GCD369CubePolynomialSource.infinity_d_eq_zero_and_c7_eq_zero_and_c5_eq_zero_and_c4_eq_zero
