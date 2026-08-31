import InfinityC4Assembly
import InfinityC2Before
import InfinityC2Tie
import InfinityC2Middle
import InfinityC2Balanced
import InfinityC2Late

/-! # Complete weight-seven infinity fan

In the canonical `c3 = 0` gauge, the weight-seven `c2` load again has five
timing cells relative to the first transverse normal and the intrinsic
cubic term.  This file assembles the cellwise results and packages the
target-normalized handoff through `c2`.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- With the canonical `c3 = 0` gauge and all earlier genuine loads zero,
the weight-seven Faber parameter `c2` vanishes. -/
theorem infinity_c2_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0) :
    S.faberConstantParameters.c2 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  rcases lt_trichotomy (7 * D.faber.scale.p) (2 * T.delta) with
      hbefore | htie | hafter
  · exact S.infinity_c2_eq_zero_strict_before hsdegree T
      hd0 hc70 hc50 hc40 hc30 (by simpa only [D] using hbefore)
  · exact S.infinity_c2_eq_zero_at_transverse hsdegree T
      hd0 hc70 hc50 hc40 hc30 (by simpa only [D] using htie)
  · rcases lt_trichotomy (7 * D.faber.scale.p) (3 * T.delta) with
        hmiddle | hbalanced | hlate
    · exact S.infinity_c2_eq_zero_singular_middle hsdegree T
        hd0 hc70 hc50 hc40 hc30
        (by simpa only [D] using hafter)
        (by simpa only [D] using hmiddle)
    · exact (S.infinity_c2_singular_balanced_inconsistent hsdegree T
        hd0 hc70 hc50 hc40 hc30
        (by simpa only [D] using hbalanced)).elim
    · exact (S.infinity_c2_singular_late_inconsistent hsdegree T
        hd0 hc70 hc50 hc40 hc30 (by simpa only [D] using hlate)).elim

/-- Target normalization supplies `c3 = 0`; consequently the constant-core
infinity fan forces all genuine Faber loads through `c2` to vanish. -/
theorem targetNormalized_infinity_loads_through_c2
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
      U.faberConstantParameters.c2 = 0 := by
  dsimp only
  let U := S.targetNormalizedSource
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  have hdS : S.faberConstantParameters.d = 0 :=
    S.infinity_d_eq_zero_of_constantCore hsdegree
  obtain ⟨hUd, _hUc7, _hUc6, _hUc5, _hUc4, hUc3, _hUc2,
      _hUc1, _hUc0⟩ := S.targetNormalizedCanonicalParameters hdS
  have hdU : U.faberConstantParameters.d = 0 := by
    simpa only [U] using hUd
  have hc7 := U.infinity_c7_eq_zero hsdegreeU T hdU
  have hc5 := U.infinity_c5_eq_zero hsdegreeU T hdU hc7
  have hc4 := U.infinity_c4_eq_zero hsdegreeU T hdU hc7 hc5
  have hc3 : U.faberConstantParameters.c3 = 0 := by
    simpa only [U] using hUc3
  have hc2 := U.infinity_c2_eq_zero hsdegreeU T hdU hc7 hc5 hc4 hc3
  exact ⟨hc7, hc5, hc4, hc2⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_c2_eq_zero
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_loads_through_c2
