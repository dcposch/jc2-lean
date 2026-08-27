import FiniteSimpleSourceFullScale
import FiniteSimpleSourceLoad

/-! # The nonic source coefficient at the weight-one load

At the exact exponent `p`, every normal-form term of weight at least two is
strictly later.  The literal nonic source equation therefore relates only
the ninth Faber value and the weight-one `d` multiple of the eighth Faber
value.  This is the source equation needed at the tied simple-root scale.
-/

noncomputable section

namespace GCD369CubeHahnNormalValueData

/-- At the first weight-one exponent, the coefficient of `F9 + d * F8`
vanishes.  No constancy hypothesis on the regular load parameters is needed.
-/
theorem faberNine_add_dFaberEightCoeff_zero_at_d
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnNormalValueData k) :
    let F9 := GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.sextic.scale.regular0 S.sextic.scale.regular1
      S.sextic.scale.regular2 S.sextic.scale.regular3
      S.sextic.scale.regular4 S.sextic.regularX
    let F8 := GCD369CubeFaberEightValueQ GCD369CubeHahnRegular.ratCast
      S.sextic.scale.regular0 S.sextic.scale.regular1
      S.sextic.scale.regular2 S.sextic.scale.regular3
      S.sextic.scale.regular4 S.sextic.regularX
    let d1 := S.sextic.scale.weightedRegular 1 S.d
    (F9 + d1 * F8).1.coeff S.sextic.scale.p = 0 := by
  dsimp only
  let F9 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.sextic.scale.regular0 S.sextic.scale.regular1
      S.sextic.scale.regular2 S.sextic.scale.regular3
      S.sextic.scale.regular4 S.sextic.regularX
  let F8 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberEightValueQ GCD369CubeHahnRegular.ratCast
      S.sextic.scale.regular0 S.sextic.scale.regular1
      S.sextic.scale.regular2 S.sextic.scale.regular3
      S.sextic.scale.regular4 S.sextic.regularX
  let d1 : GCD369CubeHahnRegular k :=
    S.sextic.scale.weightedRegular 1 S.d
  let main : GCD369CubeHahnRegular k := F9 + d1 * F8
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      S.sextic.scale.p S.sextic.scale.hp.le
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 2 ≤ w) :
      S.sextic.scale.p < (w : ℚ) * S.sextic.scale.p := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right
        (show (1 : ℚ) < (w : ℚ) by exact_mod_cast hw) S.sextic.scale.hp)
  have hkill (w : ℕ) (hw : 2 ≤ w)
      (x : GCD369CubeHahnRegular k) :
      q (S.sextic.scale.weightedRegular w x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (↑S.sextic.scale.p : WithTop ℚ) <
      (S.sextic.scale.weightedRegular w x).1.orderTop
    exact (WithTop.coe_lt_coe.mpr (hweight w hw)).trans_le
      (S.sextic.scale.weightedRegular_orderTop_lower w x)
  have hc7 := hkill 2 (by norm_num) S.c7
  have hc6 := hkill 3 (by norm_num) S.c6
  have hc5 := hkill 4 (by norm_num) S.c5
  have hc4 := hkill 5 (by norm_num) S.c4
  have hc3 := hkill 6 (by norm_num) S.c3
  have hc2 := hkill 7 (by norm_num) S.c2
  have hc1 := hkill 8 (by norm_num) S.c1
  have hc0 := hkill 9 (by norm_num) S.c0
  have hvalue := hkill 9 (by norm_num) S.value
  have hmap := congrArg q S.heval
  rw [GCD369CubeFaberNormalValueQ_map] at hmap
  rw [hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0, hvalue] at hmap
  simp only [GCD369CubeFaberNormalValueQ, zero_mul, add_zero] at hmap
  have hzero : q main = 0 := by
    dsimp only [main, F9, F8, d1]
    rw [map_add, map_mul]
    simpa only [GCD369CubeFaberNineValueQ,
      GCD369CubeFaberEightValueQ, RingHom.comp_apply,
      map_add, map_sub, map_mul, map_pow] using hmap
  have hmem : main ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hcoeff : main.1.coeff S.sextic.scale.p = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hmem
  simpa only [main, F9, F8, d1] using hcoeff

end GCD369CubeHahnNormalValueData

#print axioms
  GCD369CubeHahnNormalValueData.faberNine_add_dFaberEightCoeff_zero_at_d
