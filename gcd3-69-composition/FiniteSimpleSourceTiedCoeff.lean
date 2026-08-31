import FiniteSimpleSourceTiedRow

/-! # Residue equations at the tied simple-root scale

Given full-scale factorizations of the cubic value, transverse value, and
explicit second-order ninth-Faber term, the literal sextic and nonic source
equations reduce to two residue identities.  The second identity includes
the exact weight-one load computed in `FiniteSimpleSourceTiedRow`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- At `p = 3 * delta`, exact full-scale factorizations turn the literal
sextic and nonic source equations into their two residue equations. -/
theorem TransverseFactor.simpleRoot_tied_source_residue_equations
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (K1 L1 E1 : GCD369CubeHahnRegular k)
    (r D : k)
    (hp : S.normal.sextic.scale.p = 3 * T.delta)
    (hd : S.normal.d = GCD369CubeHahnRegular.constant D)
    (hu : S.u = -3 * r ^ 2) (hv : S.v = 2 * r ^ 3)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = -2 * r)
    (hK : S.cubicValue =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * K1)
    (hphi : S.transverseValue =
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 * L1)
    (hE :
      GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
          (T.Xn * S.normal.sextic.regularX + 2 * T.Yn) =
        GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * E1) :
    let k0 := GCD369CubeHahnRegular.constantCoeff K1
    let l0 := GCD369CubeHahnRegular.constantCoeff L1
    let e0 := GCD369CubeHahnRegular.constantCoeff E1
    k0 ^ 2 + l0 = 0 ∧
      k0 ^ 3 + (3 / 2) * k0 * l0 + e0 =
        -(D * ((130 / 9) * r ^ 8)) := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hsource := S.commonNormalEquation_orderTop_lower
  have hbelow : (↑(2 * T.delta) : WithTop ℚ) <
      (↑(6 * S.normal.sextic.scale.p) : WithTop ℚ) := by
    rw [WithTop.coe_lt_coe, hp]
    nlinarith [T.hdelta]
  have hsourceCoeff :
      (S.cubicValue ^ 2 + S.transverseValue).1.coeff
        (2 * T.delta) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (hbelow.trans_le hsource)
  have hsexticFac : S.cubicValue ^ 2 + S.transverseValue =
      H ^ 2 * (K1 ^ 2 + L1) := by
    rw [hK, hphi]
    dsimp only [H]
    ring
  rw [hsexticFac] at hsourceCoeff
  have hsexticShift := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 2 (K1 ^ 2 + L1)
  change (H ^ 2 * (K1 ^ 2 + L1)).1.coeff
    ((2 : ℕ) * T.delta) =
      GCD369CubeHahnRegular.constantCoeff (K1 ^ 2 + L1)
      at hsexticShift
  have hsexticShift' : (H ^ 2 * (K1 ^ 2 + L1)).1.coeff
      (2 * T.delta) =
        GCD369CubeHahnRegular.constantCoeff (K1 ^ 2 + L1) := by
    simpa only [Nat.cast_ofNat] using hsexticShift
  rw [hsexticShift'] at hsourceCoeff
  have hsextic :
      GCD369CubeHahnRegular.constantCoeff K1 ^ 2 +
        GCD369CubeHahnRegular.constantCoeff L1 = 0 := by
    simpa only [map_add, map_pow] using hsourceCoeff
  have hF9source := T.faberNineCoeff_at_d_simpleRoot r D hd hu hv hx
  rw [hp] at hF9source
  let F9 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.normal.sextic.scale.regular0
      S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2
      S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      S.normal.sextic.regularX
  let R : GCD369CubeHahnRegular k :=
    K1 ^ 3 + GCD369CubeHahnRegular.ratCast (3 / 2) * K1 * L1 + E1
  have hexp := T.faberNineExactExpansion
  have hF9fac : F9 = H ^ 3 * R := by
    dsimp only [F9, H, R]
    rw [hexp, hK, hphi, hE]
    ring
  have hF9coeff := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * T.delta)) hF9fac
  have hF9shift := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 3 R
  change (H ^ 3 * R).1.coeff ((3 : ℕ) * T.delta) =
    GCD369CubeHahnRegular.constantCoeff R at hF9shift
  have hF9shift' : (H ^ 3 * R).1.coeff (3 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff R := by
    simpa only [Nat.cast_ofNat] using hF9shift
  rw [hF9shift'] at hF9coeff
  have hRres : GCD369CubeHahnRegular.constantCoeff R =
      GCD369CubeHahnRegular.constantCoeff K1 ^ 3 +
        (3 / 2) * GCD369CubeHahnRegular.constantCoeff K1 *
          GCD369CubeHahnRegular.constantCoeff L1 +
        GCD369CubeHahnRegular.constantCoeff E1 := by
    dsimp only [R]
    simp only [map_add, map_mul, map_pow,
      GCD369CubeHahnRegular.constantCoeff_ratCast]
    norm_num
  have hnonic :
      GCD369CubeHahnRegular.constantCoeff K1 ^ 3 +
          (3 / 2) * GCD369CubeHahnRegular.constantCoeff K1 *
            GCD369CubeHahnRegular.constantCoeff L1 +
          GCD369CubeHahnRegular.constantCoeff E1 =
        -(D * ((130 / 9) * r ^ 8)) := by
    calc
      _ = GCD369CubeHahnRegular.constantCoeff R := hRres.symm
      _ = F9.1.coeff (3 * T.delta) := hF9coeff.symm
      _ = _ := by simpa only [F9] using hF9source
  exact ⟨hsextic, hnonic⟩

/-- Eliminating the transverse residue from the tied source equations gives
the denominator-cleared reduced nonic row. -/
theorem GCD369CubeSimpleSourceTied_reducedNonic
    {k : Type*} [Field k] [CharZero k]
    (k0 l0 e0 D r : k)
    (hsextic : k0 ^ 2 + l0 = 0)
    (hnonic : k0 ^ 3 + (3 / 2) * k0 * l0 + e0 =
      -(D * ((130 / 9) * r ^ 8))) :
    -36 * k0 ^ 3 + 72 * e0 + 1040 * D * r ^ 8 = 0 := by
  linear_combination 72 * hnonic - 108 * k0 * hsextic

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_tied_source_residue_equations
#print axioms GCD369CubeHahnCommonValueData.GCD369CubeSimpleSourceTied_reducedNonic
