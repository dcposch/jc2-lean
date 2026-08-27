import InfinityC2Assembly
import InfinityC1Before
import InfinityC1Tie
import InfinityC1Middle
import InfinityC1Balanced
import InfinityC1Late

/-! # Complete weight-eight infinity fan

In the canonical `c3 = 0` gauge, the weight-eight `c1` load has the same
five timing cells.  This file assembles them and extends the normalized
load handoff through `c1`.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- With the canonical gauge and all earlier loads zero, the weight-eight
Faber parameter `c1` vanishes. -/
theorem infinity_c1_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (hc20 : S.faberConstantParameters.c2 = 0) :
    S.faberConstantParameters.c1 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  rcases lt_trichotomy (8 * D.faber.scale.p) (2 * T.delta) with
      hbefore | htie | hafter
  · exact S.infinity_c1_eq_zero_strict_before hsdegree T
      hd0 hc70 hc50 hc40 hc30 hc20 (by simpa only [D] using hbefore)
  · exact S.infinity_c1_eq_zero_at_transverse hsdegree T
      hd0 hc70 hc50 hc40 hc30 hc20 (by simpa only [D] using htie)
  · rcases lt_trichotomy (8 * D.faber.scale.p) (3 * T.delta) with
        hmiddle | hbalanced | hlate
    · exact S.infinity_c1_eq_zero_singular_middle hsdegree T
        hd0 hc70 hc50 hc40 hc30 hc20
        (by simpa only [D] using hafter)
        (by simpa only [D] using hmiddle)
    · exact (S.infinity_c1_singular_balanced_inconsistent hsdegree T
        hd0 hc70 hc50 hc40 hc30 hc20
        (by simpa only [D] using hbalanced)).elim
    · exact (S.infinity_c1_singular_late_inconsistent hsdegree T
        hd0 hc70 hc50 hc40 hc30 hc20
        (by simpa only [D] using hlate)).elim

/-- The target-normalized constant-core infinity fan forces every genuine
Faber load through `c1` to vanish. -/
theorem targetNormalized_infinity_loads_through_c1
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      (U.infinityCommonCoefficientData hsdegreeU).TransverseScale) :
    let U := S.targetNormalizedSource
    U.faberConstantParameters.c7 = 0 ∧
      U.faberConstantParameters.c5 = 0 ∧
      U.faberConstantParameters.c4 = 0 ∧
      U.faberConstantParameters.c2 = 0 ∧
      U.faberConstantParameters.c1 = 0 := by
  dsimp only
  let U := S.targetNormalizedSource
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨hc7, hc5, hc4, hc2⟩ :=
    S.targetNormalized_infinity_loads_through_c2 hsdegree T
  have hdS : S.faberConstantParameters.d = 0 :=
    S.infinity_d_eq_zero_of_constantCore hsdegree
  obtain ⟨hUd, _hUc7, _hUc6, _hUc5, _hUc4, hUc3, _hUc2,
      _hUc1, _hUc0⟩ := S.targetNormalizedCanonicalParameters hdS
  have hdU : U.faberConstantParameters.d = 0 := by
    simpa only [U] using hUd
  have hc3 : U.faberConstantParameters.c3 = 0 := by
    simpa only [U] using hUc3
  have hc1 := U.infinity_c1_eq_zero hsdegreeU T
    hdU hc7 hc5 hc4 hc3 hc2
  exact ⟨hc7, hc5, hc4, hc2, hc1⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_c1_eq_zero
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_loads_through_c1
