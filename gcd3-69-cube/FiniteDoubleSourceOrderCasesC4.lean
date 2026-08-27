import FiniteDoubleSourceOrderCases
import FiniteC4SourceElimination

/-! # Early double-root source order case before `c4` -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- In the early moving-root range below `c4`, the sextic source equation
forces the Newton resonance `delta = 3 * nu`; ninth-Faber vanishing below the
weight-five load then gives the incompatible second residue equation. -/
theorem TransverseFactor.doubleRoot_sourceEarly_inconsistent_of_exactOrders_before_c4
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (nu : ℚ) (r A c : k)
    (hr : r ≠ 0) (hA : A ≠ 0) (hc : c ≠ 0)
    (hp : 3 * T.delta ≤ 5 * S.normal.sextic.scale.p)
    (hnu : 0 < nu) (hearly : 2 * nu < T.delta)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hK : S.cubicValue.1.orderTop =
      (↑(2 * nu) : WithTop ℚ))
    (hlcK : S.cubicValue.1.leadingCoeff = 3 * r * c ^ 2)
    (hphi : S.transverseValue.1.orderTop =
      (↑(T.delta + nu) : WithTop ℚ))
    (hlcphi : S.transverseValue.1.leadingCoeff = 3 * r * A * c) :
    False := by
  rcases S.commonNormal_orderAlternative
      (2 * nu) (T.delta + nu) hK hphi with hfar | hcancel
  · have hle : min (2 * (2 * nu)) (T.delta + nu) ≤ 4 * nu := by
      exact (min_le_left _ _).trans_eq (by ring)
    have hbound : 6 * S.normal.sextic.scale.p ≤ 4 * nu :=
      hfar.trans hle
    nlinarith [T.hdelta, hp]
  · have hdelta : T.delta = 3 * nu := by
      linarith [hcancel.1]
    have hf : 3 * r * c * (3 * r * c ^ 3 + A) = 0 := by
      rw [hlcK, hlcphi] at hcancel
      linear_combination hcancel.2
    have hK2 := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
      S.cubicValue S.cubicValue (2 * nu) (2 * nu) hK hK
    have hK2order : (S.cubicValue * S.cubicValue).1.orderTop =
        (↑(4 * nu) : WithTop ℚ) := by
      simpa only [show 2 * nu + 2 * nu = 4 * nu by ring] using hK2.1
    have hK3 := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
      (S.cubicValue * S.cubicValue) S.cubicValue
      (4 * nu) (2 * nu) hK2order hK
    have hKcubeEq : S.cubicValue ^ 3 =
        (S.cubicValue * S.cubicValue) * S.cubicValue := by ring
    have hKcubeOrder : (S.cubicValue ^ 3).1.orderTop =
        (↑(6 * nu) : WithTop ℚ) := by
      rw [hKcubeEq]
      simpa only [show 4 * nu + 2 * nu = 6 * nu by ring] using hK3.1
    have hKcubeLC : (S.cubicValue ^ 3).1.leadingCoeff =
        (3 * r * c ^ 2) ^ 3 := by
      rw [hKcubeEq, hK3.2, hK2.2, hlcK]
      ring
    have hKcubeCoeff : (S.cubicValue ^ 3).1.coeff (6 * nu) =
        27 * r ^ 3 * c ^ 6 := by
      rw [GCD369CubeHahnRegular.coeff_eq_leadingCoeff_of_orderTop_eq
        (S.cubicValue ^ 3) (6 * nu) hKcubeOrder, hKcubeLC]
      ring
    have hKphi := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
      S.cubicValue S.transverseValue (2 * nu) (T.delta + nu) hK hphi
    have hKphiOrder :
        (S.cubicValue * S.transverseValue).1.orderTop =
          (↑(6 * nu) : WithTop ℚ) := by
      rw [hdelta] at hKphi
      simpa only [show 2 * nu + (3 * nu + nu) = 6 * nu by ring]
        using hKphi.1
    have hKphiCoeff :
        (S.cubicValue * S.transverseValue).1.coeff (6 * nu) =
          (3 * r * c ^ 2) * (3 * r * A * c) := by
      rw [GCD369CubeHahnRegular.coeff_eq_leadingCoeff_of_orderTop_eq
        (S.cubicValue * S.transverseValue) (6 * nu) hKphiOrder,
        hKphi.2, hlcK, hlcphi]
    have hmidCoeff :
        (GCD369CubeHahnRegular.ratCast (3 / 2) *
          S.cubicValue * S.transverseValue).1.coeff (6 * nu) =
          algebraMap ℚ k (3 / 2) *
            ((3 * r * c ^ 2) * (3 * r * A * c)) := by
      have hassoc : GCD369CubeHahnRegular.ratCast (3 / 2) *
          S.cubicValue * S.transverseValue =
          GCD369CubeHahnRegular.ratCast (3 / 2) *
            (S.cubicValue * S.transverseValue) := by ring
      rw [hassoc]
      change ((GCD369CubeHahnRegular.ratCast (3 / 2) :
          GCD369CubeHahnRegular k).1 *
        (S.cubicValue * S.transverseValue).1).coeff (6 * nu) = _
      rw [GCD369CubeHahnRegular.coe_ratCast]
      have hqmap : algebraMap ℚ (HahnSeries ℚ k) =
          (HahnSeries.C : k →+* HahnSeries ℚ k).comp
            (algebraMap ℚ k) := Subsingleton.elim _ _
      rw [hqmap, RingHom.comp_apply]
      change (HahnSeries.C (algebraMap ℚ k (3 / 2)) *
        (S.cubicValue * S.transverseValue).1).coeff (6 * nu) = _
      rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
        hKphiCoeff]
    let E : GCD369CubeHahnRegular k :=
      GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
        (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
    have hEres : GCD369CubeHahnRegular.constantCoeff E =
        algebraMap ℚ k (9 / 8) * r * A ^ 2 := by
      dsimp only [E]
      simp only [map_mul, map_add, map_ofNat,
        GCD369CubeHahnRegular.constantCoeff_ratCast]
      rw [hx, hX, hY]
      norm_num
      ring
    have hlast0 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
      T.delta T.hdelta 2 E
    have hlast :
        (E * (GCD369CubeHahnRegular.monomial
          T.delta T.hdelta.le) ^ 2).1.coeff (6 * nu) =
          algebraMap ℚ k (9 / 8) * r * A ^ 2 := by
      have heq : 6 * nu = (2 : ℚ) * T.delta := by
        rw [hdelta]
        ring
      rw [heq]
      calc
        _ = GCD369CubeHahnRegular.constantCoeff E := by
          convert hlast0 using 1 <;> norm_num
        _ = _ := hEres
    have hexp := T.faberNineExactExpansion
    have hcoeff := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (6 * nu)) hexp
    change _ =
      (S.cubicValue ^ 3).1.coeff (6 * nu) +
        (GCD369CubeHahnRegular.ratCast (3 / 2) *
          S.cubicValue * S.transverseValue).1.coeff (6 * nu) +
        (E * (GCD369CubeHahnRegular.monomial
          T.delta T.hdelta.le) ^ 2).1.coeff (6 * nu) at hcoeff
    have hz := S.normal.faberNineCoeff_zero_before_c4 hd hc7 hc5
      (6 * nu) (by nlinarith) (by nlinarith [hp, hdelta])
    have hg : 27 * r ^ 3 * c ^ 6 +
        (27 / 2) * r ^ 2 * A * c ^ 3 +
        (9 / 8) * r * A ^ 2 = 0 := by
      rw [hKcubeCoeff, hmidCoeff, hlast] at hcoeff
      have hsum := hcoeff.symm.trans hz
      norm_num at hsum ⊢
      linear_combination hsum
    exact GCD369CubeDoubleSourceEarlyAlgebra_inconsistent
      r A c hr hA hc hf hg

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceEarly_inconsistent_of_exactOrders_before_c4
