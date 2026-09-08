import InfinityRho2Landing
import InfinitySingularTerminalCoeff

/-! # Degree-landing backend for the post-c7 infinity fan

This file turns exact scaled-terminal orders into the global scale equation
and packages the six impossible constant-core degree landings used after
`c7`: `c5`, `c4`, `c2`, `c1`, `rho1`, and `rho2`.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- Constant-core spelling of the global terminal scale equation, using the
canonical infinity coefficient packet rather than exposing its pole witness. -/
theorem infinity_terminal_scale_eq_of_constantCore_order_eq_weight
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (w : ℕ)
    (hfirst :
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          w * D.faber.scale.p) :
    (14 - (w : ℚ)) *
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p = 1 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  have hfirstF :
      let F := S.infinityFaberPoleData hpole
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          w * F.scale.p := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using hfirst
  have hscale := S.infinity_terminal_scale_eq_of_order_eq_weight
    hsdegree hpole w hfirstF
  simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
    using hscale

/-- Generic conversion from a branch-local exact terminal order and an
impossible global scale equation to vanishing of the proposed load. -/
theorem infinity_load_eq_zero_of_terminal_order_eq_weight
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (load : k) (w : ℕ)
    (hfirst : load ≠ 0 →
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          w * D.faber.scale.p)
    (hscale : (14 - (w : ℚ)) *
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p ≠ 1) :
    load = 0 := by
  by_contra hload
  exact hscale
    (S.infinity_terminal_scale_eq_of_constantCore_order_eq_weight
      hsdegree w (hfirst hload))

/-- The weight-four `c5` scale is incompatible with the degree lattice when
the leading weight-two coordinate is nonzero. -/
theorem infinity_c5_scale_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h4 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0) :
    10 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p ≠ 1 := by
  intro hscale
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  have hscaleF : 10 * (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using hscale
  have h4F : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using h4
  exact GCD369CubeConstantPoleDegreeLandingEmpty
    (S.infinityConstantPoleDegreeLanding_of_c5_scale
      hsdegree hpole hscaleF h4F)

/-- The weight-five `c4` scale is incompatible with the degree lattice when
the leading weight-three coordinate is nonzero. -/
theorem infinity_c4_scale_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h3 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading3 ≠ 0) :
    9 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p ≠ 1 := by
  intro hscale
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  have hscaleF : 9 * (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using hscale
  have h3F : (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using h3
  exact GCD369CubeConstantPoleDegreeLandingEmpty
    (S.infinityConstantPoleDegreeLanding_of_c4_scale
      hsdegree hpole hscaleF h3F)

/-- The weight-seven `c2` scale is incompatible with the degree lattice when
the leading weight-two coordinate is nonzero. -/
theorem infinity_c2_scale_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h4 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0) :
    7 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p ≠ 1 := by
  intro hscale
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  have hscaleF : 7 * (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using hscale
  have h4F : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using h4
  exact GCD369CubeConstantPoleDegreeLandingEmpty
    (S.infinityConstantPoleDegreeLanding_of_c2_scale
      hsdegree hpole hscaleF h4F)

/-- The weight-eight `c1` scale is incompatible whenever either leading
common-cubic coordinate is nonzero. -/
theorem infinity_c1_scale_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hcoordinate :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0 ∨
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading3 ≠ 0) :
    6 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p ≠ 1 := by
  intro hscale
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  have hscaleF : 6 * (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using hscale
  have hcoordinateF :
      (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 ∨
      (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using hcoordinate
  exact GCD369CubeConstantPoleDegreeLandingEmpty
    (S.infinityConstantPoleDegreeLanding_of_c1_scale
      hsdegree hpole hscaleF hcoordinateF)

/-- The weight-ten `rho1` scale is incompatible with the degree lattice when
the leading weight-two coordinate is nonzero. -/
theorem infinity_rho1_scale_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h4 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0) :
    4 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p ≠ 1 := by
  intro hscale
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  have hscaleF : 4 * (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using hscale
  have h4F : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, hpole, S.infinityCommonCoefficientData_faber hsdegree]
      using h4
  exact GCD369CubeConstantPoleDegreeLandingEmpty
    (S.infinityConstantPoleDegreeLanding_of_rho1_scale
      hsdegree hpole hscaleF h4F)

/-- At the first-transverse `rho2` timing, the weight-eleven terminal scale
is incompatible with one of the three correction-degree rows. -/
theorem infinity_rho2_scale_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hdelta : 2 * T.delta =
      11 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    3 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p ≠ 1 := by
  intro hscale
  exact GCD369CubeConstantPoleDegreeLandingEmpty
    (S.infinityConstantPoleDegreeLanding_of_rho2_scale
      hsdegree T hscale hdelta)

/-- An exact weight-four terminal order forces the `c5` load to vanish. -/
theorem infinity_c5_eq_zero_of_terminal_order_eq_four
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h4 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0)
    (hfirst : S.faberConstantParameters.c5 ≠ 0 →
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          4 * D.faber.scale.p) :
    S.faberConstantParameters.c5 = 0 := by
  apply S.infinity_load_eq_zero_of_terminal_order_eq_weight
    hsdegree S.faberConstantParameters.c5 4 hfirst
  intro hscale
  apply S.infinity_c5_scale_inconsistent hsdegree h4
  norm_num at hscale ⊢
  exact hscale

/-- An exact weight-five terminal order forces the `c4` load to vanish. -/
theorem infinity_c4_eq_zero_of_terminal_order_eq_five
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h3 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading3 ≠ 0)
    (hfirst : S.faberConstantParameters.c4 ≠ 0 →
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          5 * D.faber.scale.p) :
    S.faberConstantParameters.c4 = 0 := by
  apply S.infinity_load_eq_zero_of_terminal_order_eq_weight
    hsdegree S.faberConstantParameters.c4 5 hfirst
  intro hscale
  apply S.infinity_c4_scale_inconsistent hsdegree h3
  norm_num at hscale ⊢
  exact hscale

/-- An exact weight-seven terminal order forces the `c2` load to vanish. -/
theorem infinity_c2_eq_zero_of_terminal_order_eq_seven
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h4 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0)
    (hfirst : S.faberConstantParameters.c2 ≠ 0 →
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          7 * D.faber.scale.p) :
    S.faberConstantParameters.c2 = 0 := by
  apply S.infinity_load_eq_zero_of_terminal_order_eq_weight
    hsdegree S.faberConstantParameters.c2 7 hfirst
  intro hscale
  apply S.infinity_c2_scale_inconsistent hsdegree h4
  norm_num at hscale ⊢
  exact hscale

/-- An exact weight-eight terminal order forces the `c1` load to vanish. -/
theorem infinity_c1_eq_zero_of_terminal_order_eq_eight
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hcoordinate :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0 ∨
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading3 ≠ 0)
    (hfirst : S.faberConstantParameters.c1 ≠ 0 →
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          8 * D.faber.scale.p) :
    S.faberConstantParameters.c1 = 0 := by
  apply S.infinity_load_eq_zero_of_terminal_order_eq_weight
    hsdegree S.faberConstantParameters.c1 8 hfirst
  intro hscale
  apply S.infinity_c1_scale_inconsistent hsdegree hcoordinate
  norm_num at hscale ⊢
  exact hscale

/-- An exact weight-ten terminal order forces `rho1` to vanish. -/
theorem infinity_rho1_eq_zero_of_terminal_order_eq_ten
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h4 : (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0)
    (hfirst : S.faberFirstIntegralConstants.rho1 ≠ 0 →
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          10 * D.faber.scale.p) :
    S.faberFirstIntegralConstants.rho1 = 0 := by
  apply S.infinity_load_eq_zero_of_terminal_order_eq_weight
    hsdegree S.faberFirstIntegralConstants.rho1 10 hfirst
  intro hscale
  apply S.infinity_rho1_scale_inconsistent hsdegree h4
  norm_num at hscale ⊢
  exact hscale

/-- At `2 δ = 11 p`, an exact weight-eleven terminal order forces `rho2`
to vanish. -/
theorem infinity_rho2_eq_zero_of_terminal_order_eq_eleven
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hdelta : 2 * T.delta =
      11 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p)
    (hfirst : S.faberFirstIntegralConstants.rho2 ≠ 0 →
      let D := S.infinityCommonCoefficientData hsdegree
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          11 * D.faber.scale.p) :
    S.faberFirstIntegralConstants.rho2 = 0 := by
  apply S.infinity_load_eq_zero_of_terminal_order_eq_weight
    hsdegree S.faberFirstIntegralConstants.rho2 11 hfirst
  intro hscale
  apply S.infinity_rho2_scale_inconsistent hsdegree T hdelta
  norm_num at hscale ⊢
  exact hscale

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.infinity_terminal_scale_eq_of_constantCore_order_eq_weight
#print axioms GCD369CubePolynomialSource.infinity_c5_scale_inconsistent
#print axioms GCD369CubePolynomialSource.infinity_c4_scale_inconsistent
#print axioms GCD369CubePolynomialSource.infinity_c2_scale_inconsistent
#print axioms GCD369CubePolynomialSource.infinity_c1_scale_inconsistent
#print axioms GCD369CubePolynomialSource.infinity_rho1_scale_inconsistent
#print axioms GCD369CubePolynomialSource.infinity_rho2_scale_inconsistent
#print axioms
  GCD369CubePolynomialSource.infinity_c5_eq_zero_of_terminal_order_eq_four
#print axioms
  GCD369CubePolynomialSource.infinity_c4_eq_zero_of_terminal_order_eq_five
#print axioms
  GCD369CubePolynomialSource.infinity_c2_eq_zero_of_terminal_order_eq_seven
#print axioms
  GCD369CubePolynomialSource.infinity_c1_eq_zero_of_terminal_order_eq_eight
#print axioms
  GCD369CubePolynomialSource.infinity_rho1_eq_zero_of_terminal_order_eq_ten
#print axioms
  GCD369CubePolynomialSource.infinity_rho2_eq_zero_of_terminal_order_eq_eleven
