import FiniteBoundarySource

noncomputable section
open Polynomial

/-! # Common-cubic finite-pole jets

The original boundary values force every finite leading pole onto the
common-cubic component.  This file begins the next, genuinely infinitesimal,
step.  It records the limiting cubic root and proves that every nonzero
zero-load normal satisfying the four Faber quadrics shares a root with that
cubic.  Thus such a normal is not an early obstruction; it is precisely the
root-following branch that must be lifted until the first nonzero target
load.
-/

/-- A nonzero common-normal vector satisfying the four zero-load Faber rows
has an explicit common root with the underlying cubic. -/
theorem GCD369CubeZeroLoadNormal_commonRoot
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (hnonzero : Xn ≠ 0 ∨ Yn ≠ 0 ∨ Zn ≠ 0)
    (h1 : GCD369CubeNormalRow1 Xn Yn Zn u = 0)
    (h2 : GCD369CubeNormalRow2 Xn Yn Zn u v = 0)
    (h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0)
    (_h4 : GCD369CubeNormalRow4 Xn Yn Zn u v = 0) :
    ∃ r : K,
      r ^ 3 + u * r + v = 0 ∧
      Xn * r ^ 2 + Yn * r + Zn = 0 := by
  have he1 : u * Xn ^ 2 - 2 * Xn * Zn - Yn ^ 2 = 0 := by
    dsimp [GCD369CubeNormalRow1] at h1
    linear_combination (1 / 729) * h1
  have he2 : v * Xn ^ 2 + 2 * u * Xn * Yn - 2 * Yn * Zn = 0 := by
    dsimp [GCD369CubeNormalRow2] at h2
    linear_combination (-1 / 2187) * h2
  have he3 : Zn ^ 2 - 2 * v * Xn * Yn = 0 := by
    dsimp [GCD369CubeNormalRow3] at h3
    linear_combination (1 / 3) * h3 - (2 * u / 3) * he1
  have hX : Xn ≠ 0 := by
    intro hX
    have hY : Yn = 0 := by
      rw [hX] at he1
      norm_num at he1
      exact he1
    have hZ : Zn = 0 := by
      rw [hX, hY] at he3
      norm_num at he3
      exact he3
    exact hnonzero.elim (fun h => h hX)
      (fun h => h.elim (fun h => h hY) (fun h => h hZ))
  have hsquare : (Xn * Zn + 2 * Yn ^ 2) ^ 2 = 0 := by
    linear_combination Xn ^ 2 * he3 + 2 * Xn * Yn * he2 -
      4 * Yn ^ 2 * he1
  have hnormal : Xn * Zn + 2 * Yn ^ 2 = 0 :=
    (sq_eq_zero_iff).mp hsquare
  let r := Yn / Xn
  have hu : u = -3 * r ^ 2 := by
    dsimp only [r]
    field_simp [hX]
    linear_combination he1 + 2 * hnormal
  have hZ : Zn = -2 * r ^ 2 * Xn := by
    dsimp only [r]
    field_simp [hX]
    linear_combination hnormal
  have hv : v = 2 * r ^ 3 := by
    dsimp only [r] at hu hZ ⊢
    field_simp [hX] at hu hZ ⊢
    linear_combination Xn * he2 - 2 * Yn * hu + 2 * Yn * hZ
  refine ⟨r, ?_, ?_⟩
  · rw [hu, hv]
    ring
  · rw [hZ]
    dsimp only [r]
    field_simp [hX]
    ring

/-- A scaled original-value packet together with its certified nonzero
common-cubic leading component. -/
structure GCD369CubeHahnCommonValueData
    (k : Type*) [Field k] [CharZero k] where
  normal : GCD369CubeHahnNormalValueData k
  u : k
  v : k
  hprojective : u ≠ 0 ∨ v ≠ 0
  ha4 : normal.sextic.scale.leading4 = 2 * u
  ha3 : normal.sextic.scale.leading3 = 2 * v
  ha2 : normal.sextic.scale.leading2 = u ^ 2
  ha1 : normal.sextic.scale.leading1 = 2 * u * v
  ha0 : normal.sextic.scale.leading0 = v ^ 2

namespace GCD369CubeHahnCommonValueData

/-- The moving cubic coefficients read directly from the scaled sextic. -/
def cubicU {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.ratCast (1 / 2) * S.normal.sextic.scale.regular4

def cubicV {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.ratCast (1 / 2) * S.normal.sextic.scale.regular3

/-- Exact normal coordinates transverse to the moving common-cubic square. -/
def normal2 {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.scale.regular2 - S.cubicU ^ 2

def normal1 {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.scale.regular1 - 2 * S.cubicU * S.cubicV

def normal0 {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.scale.regular0 - S.cubicV ^ 2

/-- The moving cubic and its transverse quadratic evaluated at the recovered
scaled source coordinate. -/
def cubicValue {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.regularX ^ 3 +
    S.cubicU * S.normal.sextic.regularX + S.cubicV

def transverseValue {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal2 * S.normal.sextic.regularX ^ 2 +
    S.normal1 * S.normal.sextic.regularX + S.normal0

/-- The three exact transverse normal coordinates all have zero residue. -/
theorem normal_constantCoeff_zero
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    GCD369CubeHahnRegular.constantCoeff S.normal2 = 0 ∧
    GCD369CubeHahnRegular.constantCoeff S.normal1 = 0 ∧
    GCD369CubeHahnRegular.constantCoeff S.normal0 = 0 := by
  have hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = S.u := by
    simp only [cubicU, map_mul,
      GCD369CubeHahnRegular.constantCoeff_ratCast]
    change algebraMap ℚ k (1 / 2) * S.normal.sextic.scale.leading4 = S.u
    rw [S.ha4]
    norm_num
    ring
  have hv : GCD369CubeHahnRegular.constantCoeff S.cubicV = S.v := by
    simp only [cubicV, map_mul,
      GCD369CubeHahnRegular.constantCoeff_ratCast]
    change algebraMap ℚ k (1 / 2) * S.normal.sextic.scale.leading3 = S.v
    rw [S.ha3]
    norm_num
    ring
  constructor
  · simp only [normal2, map_sub, map_pow, hu]
    change S.normal.sextic.scale.leading2 - S.u ^ 2 = 0
    rw [S.ha2, sub_self]
  constructor
  · simp only [normal1, map_sub, map_mul, map_ofNat, hu, hv]
    change S.normal.sextic.scale.leading1 - 2 * S.u * S.v = 0
    rw [S.ha1, sub_self]
  · simp only [normal0, map_sub, map_pow, hv]
    change S.normal.sextic.scale.leading0 - S.v ^ 2 = 0
    rw [S.ha0, sub_self]

/-- The recovered residue is a root of the certified limiting common cubic. -/
theorem leadingCubicRoot
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let r := S.normal.sextic.scaledX.coeff 0
    r ^ 3 + S.u * r + S.v = 0 := by
  dsimp only
  have hf := S.normal.sextic.leadingSexticRoot
  rw [S.ha4, S.ha3, S.ha2, S.ha1, S.ha0] at hf
  have hsquare :
      (S.normal.sextic.scaledX.coeff 0 ^ 3 +
        S.u * S.normal.sextic.scaledX.coeff 0 + S.v) ^ 2 = 0 := by
    linear_combination hf
  exact (sq_eq_zero_iff).mp hsquare

/-- The scaled sextic value is exactly the moving cubic square plus its
transverse quadratic value. -/
theorem commonNormalEquation
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    S.cubicValue ^ 2 + S.transverseValue =
      S.normal.sextic.scale.weightedRegular 6 S.normal.sextic.value := by
  have hhalf :
      (2 : GCD369CubeHahnRegular k) *
        GCD369CubeHahnRegular.ratCast (1 / 2) = 1 := by
    have htwo : (2 : GCD369CubeHahnRegular k) =
        GCD369CubeHahnRegular.constant (2 : k) := by
      apply Subtype.ext
      exact (map_ofNat (HahnSeries.C : k →+* HahnSeries ℚ k) 2).symm
    have hrat : GCD369CubeHahnRegular.ratCast (1 / 2) =
        GCD369CubeHahnRegular.constant (1 / 2 : k) := by
      change GCD369CubeHahnRegular.constant (algebraMap ℚ k (1 / 2)) =
        GCD369CubeHahnRegular.constant (1 / 2 : k)
      congr 1
      norm_num
    calc
      _ = GCD369CubeHahnRegular.constant (2 : k) *
          GCD369CubeHahnRegular.constant (1 / 2 : k) := by rw [htwo, hrat]
      _ = GCD369CubeHahnRegular.constant ((2 : k) * (1 / 2 : k)) :=
        ((GCD369CubeHahnRegular.constant (k := k)).map_mul _ _).symm
      _ = 1 := by norm_num
  have ha4 : S.normal.sextic.scale.regular4 = 2 * S.cubicU := by
    dsimp only [cubicU]
    linear_combination
      -S.normal.sextic.scale.regular4 * hhalf
  have ha3 : S.normal.sextic.scale.regular3 = 2 * S.cubicV := by
    dsimp only [cubicV]
    linear_combination
      -S.normal.sextic.scale.regular3 * hhalf
  have hscaled :
      S.normal.sextic.regularX ^ 6 +
        (S.normal.sextic.scale.regular4 * S.normal.sextic.regularX ^ 4 +
          (S.normal.sextic.scale.regular3 * S.normal.sextic.regularX ^ 3 +
            (S.normal.sextic.scale.regular2 * S.normal.sextic.regularX ^ 2 +
              (S.normal.sextic.scale.regular1 * S.normal.sextic.regularX +
                S.normal.sextic.scale.regular0)))) =
        S.normal.sextic.scale.weightedRegular 6 S.normal.sextic.value := by
    apply Subtype.ext
    exact S.normal.sextic.scaledEquation
  rw [ha4, ha3] at hscaled
  dsimp only [cubicValue, transverseValue, normal2, normal1, normal0]
  linear_combination hscaled

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- The literal finite pole canonically supplies the complete moving
common-cubic normal-coordinate packet. -/
noncomputable def finiteCommonValueData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnCommonValueData k := by
  let N := S.finiteNormalValueData a hpole
  let hex := S.finiteLeadingComponent_common a hpole
  let u := Classical.choose hex
  let hu := Classical.choose_spec hex
  let v := Classical.choose hu
  let hv := Classical.choose_spec hu
  refine {
    normal := N
    u := u
    v := v
    hprojective := hv.1
    ha4 := ?_
    ha3 := ?_
    ha2 := ?_
    ha1 := ?_
    ha0 := ?_
  }
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2.1
  · exact hv.2.2.2.2.1
  · exact hv.2.2.2.2.2

/-- At every finite pole selected from the literal source, the recovered
translation residue is a root of the nonzero common cubic supplied by the
leading Faber component. -/
theorem finiteLeadingCommonCubicRoot
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    let B := S.finiteSexticValueData a hpole
    let r := B.scaledX.coeff 0
    ∃ u v : k, (u ≠ 0 ∨ v ≠ 0) ∧
      B.scale.leading4 = 2 * u ∧
      B.scale.leading3 = 2 * v ∧
      B.scale.leading2 = u ^ 2 ∧
      B.scale.leading1 = 2 * u * v ∧
      B.scale.leading0 = v ^ 2 ∧
      r ^ 3 + u * r + v = 0 := by
  let B := S.finiteSexticValueData a hpole
  let r := B.scaledX.coeff 0
  obtain ⟨u, v, hprojective, ha4, ha3, ha2, ha1, ha0⟩ :=
    S.finiteLeadingComponent_common a hpole
  have hf := B.leadingSexticRoot
  change r ^ 6 +
      (B.scale.leading4 * r ^ 4 +
        (B.scale.leading3 * r ^ 3 +
          (B.scale.leading2 * r ^ 2 +
            (B.scale.leading1 * r + B.scale.leading0)))) = 0 at hf
  have hsquare : (r ^ 3 + u * r + v) ^ 2 = 0 := by
    rw [ha4, ha3, ha2, ha1, ha0] at hf
    linear_combination hf
  exact ⟨u, v, hprojective, ha4, ha3, ha2, ha1, ha0,
    (sq_eq_zero_iff).mp hsquare⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubeZeroLoadNormal_commonRoot
#print axioms GCD369CubeHahnCommonValueData.normal_constantCoeff_zero
#print axioms GCD369CubeHahnCommonValueData.leadingCubicRoot
#print axioms GCD369CubeHahnCommonValueData.commonNormalEquation
#print axioms GCD369CubePolynomialSource.finiteCommonValueData
#print axioms GCD369CubePolynomialSource.finiteLeadingCommonCubicRoot
