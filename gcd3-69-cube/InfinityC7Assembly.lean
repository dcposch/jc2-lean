import InfinityC7Before
import InfinityC7Load
import InfinityC7Middle
import InfinityC7BalancedAssembly
import InfinityC7LateAssembly

/-! # Complete weight-two infinity fan

After the weight-one coefficient has vanished, the relative order of the
weight-two load, the first transverse normal, and the intrinsic cubic term
has five cells.  The preceding modules close each cell; this file performs
the arithmetic routing.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- On a constant-core infinity branch, the completed `d = 0` theorem forces
the next Faber parameter `c7` to vanish as well. -/
theorem infinity_c7_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0) :
    S.faberConstantParameters.c7 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  rcases lt_trichotomy (2 * D.faber.scale.p) (2 * T.delta) with
      hbefore | htie | hafter
  · exact S.infinity_c7_eq_zero_strict_before hsdegree T hd0
      (by simpa only [D] using hbefore)
  · have hpTie : D.faber.scale.p = T.delta := by linarith
    exact S.infinity_c7_eq_zero_at_transverse hsdegree T hd0
      (by simpa only [D] using hpTie)
  · have hdeltaP : T.delta < D.faber.scale.p := by linarith
    rcases lt_trichotomy (2 * D.faber.scale.p) (3 * T.delta) with
        hmiddle | hbalanced | hlate
    · exact S.infinity_c7_eq_zero_singular_middle hsdegree T hd0
        (by simpa only [D] using hdeltaP)
        (by simpa only [D] using hmiddle)
    · exact (S.infinity_c7_singular_balanced_inconsistent
        hsdegree T hd0 (by simpa only [D] using hbalanced)).elim
    · exact (S.infinity_c7_singular_late_inconsistent
        hsdegree T hd0 (by simpa only [D] using hlate)).elim

/-- The first two source loads vanish together on every constant-core
infinity packet. -/
theorem infinity_d_eq_zero_and_c7_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale) :
    S.faberConstantParameters.d = 0 ∧
      S.faberConstantParameters.c7 = 0 := by
  have hd := S.infinity_d_eq_zero hsdegree T
  exact ⟨hd, S.infinity_c7_eq_zero hsdegree T hd⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_c7_eq_zero
#print axioms GCD369CubePolynomialSource.infinity_d_eq_zero_and_c7_eq_zero
