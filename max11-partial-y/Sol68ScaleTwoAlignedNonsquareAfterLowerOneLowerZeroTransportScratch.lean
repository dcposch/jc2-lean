import Sol68ScaleTwoAlignedNonsquareAfterLowerOneLowerZeroScratch

/-! # Exact source transport of the larger terminal lower row -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section TerminalLowerZeroSourceTransport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance terminalLowerZeroTransportCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- The exact larger lower row already exported by the source residual packet. -/
theorem NonsquareAlignedSourceCurveData68.terminalLowerZeroRawSourceIdentity
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    let ck := algebraMap k F68
    let d := quadraticDerivation46 H
    let T := integratedT68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) (ck S.epsilon)
    let U := integratedU68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) 0 0
    let V := integratedV68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) 0 (ck S.epsilon) (ck S.eta)
    let SS := integratedS68 0 S.A S.B S.C0 S.D (ck S.alpha) 0 0
    U * d S.C0 + 2 * T * d S.D + 3 * SS * d S.E -
        3 * S.B * d V - 2 * S.C0 * d U - S.D * d T = 0 := by
  exact (S.residualPacket).2.2.1

/-- Literal denominator clearing of the larger source row into the canonical
base-polynomial expression. -/
theorem NonsquareAlignedSourceCurveData68.terminalLowerZeroClearedTransport_source
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    {g r t X Yd : k[X]}
    (hg : p.coeff 5 = H * g) (hgr : g = H * r)
    (ht : p.coeff 4 = H * t)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X)
    (hY : (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd) :
    terminalLowerZeroCleared68 H
      (terminalGReducedA68 H r X)
      (terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd (p.coeff 2))
      (terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2))
      (terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2))
      S.alpha S.gamma S.epsilon S.eta = 0 := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let M := quadraticCoefficientMap46 H
  let dQ := quadraticDerivation46 H
  let rF : F68 := M r
  let tF : F68 := M t
  let a3 : F68 := M (p.coeff 3)
  let a2 : F68 := M (p.coeff 2)
  let a1 : F68 := M (p.coeff 1)
  let a0 : F68 := M (p.coeff 0)
  have hroot : h ^ 2 = M H := alignedQuadraticRoot_sq46 H
  have hh : h ≠ 0 := S.scale_ne_zero
  have hM : Function.Injective M :=
    (algebraMap (RatFunc k) F68).injective.comp
      (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hcoeffC (c : k) : M (C c) = algebraMap k F68 c := by
    dsimp only [M]
    rw [quadraticCoefficientMap46_eq_algebraMap]
    simpa using (IsScalarTower.algebraMap_apply k k[X] F68 c).symm
  have hdmap (P : k[X]) : dQ (M P) = M P.derivative := by
    dsimp only [dQ, M]
    rw [quadraticDerivation46_apply, quadraticCoefficientMap46_eq_algebraMap,
      quadraticCoefficientMap46_eq_algebraMap]
    exact alignedQuadraticDeriv_polynomial46 H
      NonsquarePolynomial46.not_sq P
  have hpTop : M (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hroot]
    ring
  have hpRaw := sourceToQuadratic68_eq_rawSextic H p h hp hpTop
  have hsextic := S.sextic_eq
  rw [hpRaw] at hsextic
  let a5 : F68 := M (p.coeff 5)
  let a4 : F68 := M (p.coeff 4)
  have hcoeff5 := congrArg (fun f : F68[X] => f.coeff 5) hsextic
  have hcenter : S.r = sexticDepressionR68 h a5 := by
    apply r_eq_sexticDepression_of_coeff_five h S.r a5 a4 a3 a2 a1 a0 hh
    simpa only [depressedSextic68_coeff_five] using hcoeff5
  have hpDep := affineDepress_rawSextic68 h S.r a5 a4 a3 a2 a1 a0 hh hcenter
  have hsame := hpDep.symm.trans hsextic
  have hA : depressedA68 h S.r a5 a4 = S.A := by
    have hc := congrArg (fun f : F68[X] => f.coeff 4) hsame
    simpa [depressedSextic68] using hc
  have hB : depressedB68 h S.r a5 a4 a3 = S.B := by
    have hc := congrArg (fun f : F68[X] => f.coeff 3) hsame
    simpa [depressedSextic68] using hc
  have hC : depressedC68 h S.r a5 a4 a3 a2 = S.C0 := by
    have hc := congrArg (fun f : F68[X] => f.coeff 2) hsame
    simpa [depressedSextic68] using hc
  have hD : depressedD68 h S.r a5 a4 a3 a2 a1 = S.D := by
    have hc := congrArg (fun f : F68[X] => f.coeff 1) hsame
    simpa [depressedSextic68] using hc
  have hE : depressedE68 h S.r a5 a4 a3 a2 a1 a0 = S.E := by
    have hc := congrArg (fun f : F68[X] => f.coeff 0) hsame
    simpa [depressedSextic68] using hc
  have ha5 : a5 = h ^ 4 * rF := by
    dsimp only [a5, rF]
    rw [hg, hgr, map_mul, map_mul, ← hroot]
    ring
  have ha4 : a4 = h ^ 2 * tF := by
    dsimp only [a4, tF]
    rw [ht, map_mul, ← hroot]
  have hcenter' : S.r = rF / (6 * h) := by
    rw [hcenter, sexticDepressionR68, ha5]
    field_simp [hh]
  rw [ha5, ha4] at hA hB hC hD hE
  obtain ⟨hAc, hBc, hCc, hDc, hEc⟩ :=
    cubicDepressedCoordinates_cleared_68 h S.r rF tF a3 a2 a1 a0 hh
      hcenter'
  rw [hA] at hAc
  rw [hB] at hBc
  rw [hC] at hCc
  rw [hD] at hDc
  rw [hE] at hEc
  dsimp only [a3, a2, a1, a0, tF, rF] at hAc hBc hCc hDc hEc
  let A0 := terminalGReducedA68 H r X
  let b0 := terminalGReducedB68 r X Yd
  let C0 := terminalGReducedC68 H r X Yd (p.coeff 2)
  let D0 := terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2)
  let E0 := terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2)
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  have hAmap : M A0 = h ^ 2 * S.A := by
    dsimp only [A0]
    rw [← hAred]
    dsimp only [cubicANumerator68]
    simp only [map_sub, map_mul, map_pow, hcoeffC]
    simpa only [map_div₀, map_ofNat, map_one] using hAc.symm
  have hBmap : M b0 = h * S.B := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * M b0 = M (H * b0) := by rw [map_mul, ← hroot]
      _ = M (cubicBNumerator68 (p.coeff 3) t r) := by rw [hBred]
      _ = h ^ 3 * S.B := by
        dsimp only [cubicBNumerator68]
        simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
        simpa only [map_div₀, map_ofNat, map_one] using hBc.symm
      _ = h ^ 2 * (h * S.B) := by ring
  have hCmap : M C0 = h ^ 4 * S.C0 := by
    dsimp only [C0]
    rw [← hCred]
    dsimp only [cubicCNumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    rw [← hroot]
    convert hCc.symm using 1 <;>
      simp only [map_div₀, map_one, map_ofNat] <;> ring
  have hDmap : M D0 = h ^ 3 * S.D := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * M D0 = M (H * D0) := by rw [map_mul, ← hroot]
      _ = M (cubicDNumerator68 H (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) := by rw [hDred]
      _ = h ^ 5 * S.D := by
        dsimp only [cubicDNumerator68]
        simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
        rw [← hroot]
        convert hDc.symm using 1 <;>
          simp only [map_div₀, map_one, map_ofNat] <;> ring
      _ = h ^ 2 * (h ^ 3 * S.D) := by ring
  have hEmap : M E0 = h ^ 6 * S.E := by
    dsimp only [E0]
    rw [← hEred]
    dsimp only [cubicENumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    rw [← hroot]
    convert hEc.symm using 1 <;>
      simp only [map_div₀, map_one, map_ofNat] <;> ring
  let S0 := terminalLowerZeroSNumerator68 H A0 b0 D0 S.alpha
  let T0 := terminalLowerOneTNumerator68 H A0 b0 C0 E0
    S.alpha S.gamma S.epsilon
  let U0 := terminalLowerOneUNumerator68 H A0 b0 C0 D0 S.alpha S.gamma
  let V0 := terminalVNumerator68 H A0 b0 C0 D0 E0
    S.alpha S.gamma S.epsilon S.eta
  let SS := integratedS68 0 S.A S.B S.C0 S.D
    (algebraMap k F68 S.alpha) 0 0
  let T := integratedT68 0 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma)
    (algebraMap k F68 S.epsilon)
  let U := integratedU68 0 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0
  let V := integratedV68 0 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
    (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta)
  have hSmap : M S0 = h ^ 3 * SS := by
    dsimp only [S0, SS, terminalLowerZeroSNumerator68, integratedS68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [hAmap, hBmap, hDmap, ← hroot]
    ring
  have hTmap : M T0 = h ^ 6 * T := by
    dsimp only [T0, T, terminalLowerOneTNumerator68, integratedT68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [hAmap, hBmap, hCmap, hEmap, ← hroot]
    ring
  have hUmap : M U0 = h ^ 5 * U := by
    dsimp only [U0, U, terminalLowerOneUNumerator68, integratedU68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [hAmap, hBmap, hCmap, hDmap, ← hroot]
    ring
  have hVmap : M V0 = h ^ 8 * V := by
    dsimp only [V0, V, terminalVNumerator68, integratedV68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [hAmap, hBmap, hCmap, hDmap, hEmap, ← hroot]
    ring
  have hhder := congrArg dQ hroot
  simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul] at hhder
  rw [hdmap H] at hhder
  have hhder' : M H.derivative = 2 * h * dQ h := by
    calc
      M H.derivative = 2 * (h * dQ h) := by
        simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat] using hhder.symm
      _ = 2 * h * dQ h := by ring
  have hCder := congrArg dQ hCmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hCder
  rw [hdmap C0] at hCder
  have hCder' : M C0.derivative =
      4 * h ^ 3 * dQ h * S.C0 + h ^ 4 * dQ S.C0 := by
    linear_combination hCder
  have hDder := congrArg dQ hDmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hDder
  rw [hdmap D0] at hDder
  have hDder' : M D0.derivative =
      3 * h ^ 2 * dQ h * S.D + h ^ 3 * dQ S.D := by
    linear_combination hDder
  have hEder := congrArg dQ hEmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hEder
  rw [hdmap E0] at hEder
  have hEder' : M E0.derivative =
      6 * h ^ 5 * dQ h * S.E + h ^ 6 * dQ S.E := by
    linear_combination hEder
  have hTder := congrArg dQ hTmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hTder
  rw [hdmap T0] at hTder
  have hTder' : M T0.derivative =
      6 * h ^ 5 * dQ h * T + h ^ 6 * dQ T := by
    linear_combination hTder
  have hUder := congrArg dQ hUmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hUder
  rw [hdmap U0] at hUder
  have hUder' : M U0.derivative =
      5 * h ^ 4 * dQ h * U + h ^ 5 * dQ U := by
    linear_combination hUder
  have hVder := congrArg dQ hVmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hVder
  rw [hdmap V0] at hVder
  have hVder' : M V0.derivative =
      8 * h ^ 7 * dQ h * V + h ^ 8 * dQ V := by
    linear_combination hVder
  let CD0 := terminalLowerZeroCDot68 H C0
  let DD0 := terminalLowerOneDTwoDot68 H D0
  let ED0 := terminalEDerivativeNumerator68 H E0
  let VD0 := terminalVDerivativeNumerator68 H V0
  let UD0 := terminalLowerOneUTwoDot68 H U0
  let TD0 := terminalLowerZeroTDot68 H T0
  have hCDmap : M CD0 = h ^ 6 * dQ S.C0 := by
    dsimp only [CD0, terminalLowerZeroCDot68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hCmap, hhder', hCder']
    ring
  have hDDmap : M DD0 = 2 * h ^ 5 * dQ S.D := by
    dsimp only [DD0, terminalLowerOneDTwoDot68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hDmap, hhder', hDder']
    ring
  have hEDmap : M ED0 = h ^ 8 * dQ S.E := by
    dsimp only [ED0, terminalEDerivativeNumerator68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hEmap, hhder', hEder']
    ring
  have hVDmap : M VD0 = h ^ 10 * dQ V := by
    dsimp only [VD0, terminalVDerivativeNumerator68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hVmap, hhder', hVder']
    ring
  have hUDmap : M UD0 = 2 * h ^ 7 * dQ U := by
    dsimp only [UD0, terminalLowerOneUTwoDot68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hUmap, hhder', hUder']
    ring
  have hTDmap : M TD0 = h ^ 8 * dQ T := by
    dsimp only [TD0, terminalLowerZeroTDot68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hTmap, hhder', hTder']
    ring
  have hraw := S.terminalLowerZeroRawSourceIdentity (H := H)
  dsimp only at hraw
  have hclearF : M (terminalLowerZeroCleared68 H A0 b0 C0 D0 E0
      S.alpha S.gamma S.epsilon S.eta) = 0 := by
    change M (U0 * CD0 + T0 * DD0 + C 3 * S0 * ED0 -
      C 3 * b0 * VD0 - C0 * UD0 - D0 * TD0) = 0
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, hcoeffC,
      map_ofNat]
    convert terminalLowerZeroCleared_of_scaled_values_68
      h S.B S.C0 S.D SS T U (dQ S.C0) (dQ S.D) (dQ S.E)
      (dQ V) (dQ U) (dQ T)
      (M b0) (M C0) (M D0) (M S0) (M T0) (M U0)
      (M CD0) (M DD0) (M ED0) (M VD0) (M UD0) (M TD0)
      hBmap.symm hCmap.symm hDmap.symm hSmap.symm hTmap.symm hUmap.symm
      hCDmap.symm hDDmap.symm hEDmap.symm hVDmap.symm hUDmap.symm
      hTDmap.symm hraw using 1 <;> ring
  apply hM
  simpa only [A0, b0, C0, D0, E0, map_zero] using hclearF

/-- The new transported row deletes the component on which every core root
lies at the pure load wall.  Thus at least one core root remains on the
honest `r = 0` or `Phi₁ = 0` allocations. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneNoPureLoadWallPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r phi1 b2 d2 k1 : k[X]),
      (∀ a : k, H.eval a = 0 →
        r.eval a = 0 ∨ phi1.eval a = 0 ∨
          (b2.eval a = 0 ∧ b2.derivative.eval a = 0 ∧
           d2.eval a = 0 ∧ d2.derivative.eval a = 0 ∧
           k1.eval a ≠ 0)) ∧
      ¬ (∀ a : k, H.eval a = 0 →
        r.eval a ≠ 0 ∧ phi1.eval a ≠ 0) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
      hI4, hrow, hroots, hpure⟩ :=
    S.terminalAfterLowerOneDoubleZeroPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  refine ⟨r, phi1, b2, d2, k1, hroots, ?_⟩
  intro hall
  obtain ⟨b5, d4, hb5, hd4, _hI4f, _hrowf, hrootprod⟩ := hpure hall
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hdegree : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegree
  have hprodne : d4.eval a * k1.eval a ≠ 0 := by
    rw [hrootprod a ha]
    exact neg_ne_zero.mpr hj
  have hd4ne : d4.eval a ≠ 0 := by
    intro hd4z
    exact hprodne (by rw [hd4z, zero_mul])
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2 := by
    rw [hW1, hw2]
    ring
  have hCshape : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hWm := congrArg (algebraMap k[X] (RatFunc k)) hW2
    dsimp only [terminalScaledW68] at hWm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hWm ⊢
    linear_combination (9 / 4 : RatFunc k) * hWm
  have hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi, ← hb1]
    simp only [cubicPhiNumerator68]
  have hbshape : b1 = H ^ 6 * b5 := by
    rw [hb2, hb5]
    ring
  have hdshape : d1 = H ^ 5 * d4 := by
    rw [hd2, hd4]
    ring
  have hEshape : E0 = C (1 / 27 : k) * A0 ^ 3 +
      C (3 / 8 : k) * H * phi1 +
      H ^ 2 * (C (3 / 2 : k) * A0 * w2 -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H ^ 6 * b5)) ^ 2 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi
    have hCm := congrArg (algebraMap k[X] (RatFunc k)) hCshape
    dsimp only [terminalScaledPhi68] at hPm
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hPm hCm ⊢
    have hbm := congrArg (algebraMap k[X] (RatFunc k)) hbshape
    simp only [map_mul, map_pow] at hbm
    rw [hbm] at hPm
    linear_combination (3 / 8 : RatFunc k) * hPm +
      (2 / 3 * algebraMap k[X] (RatFunc k) A0) * hCm
  have htransport := S.terminalLowerZeroClearedTransport_source (H := H)
    hp hp6 hg hgr ht hX hY
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  have hbred : terminalGReducedB68 r X Yd = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hBred, ← hb1]
  have hdred : terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  exact terminalLowerZero_pureLoadWall_impossible_68
    H A0 b1 C0 d1 E0 b5 d4 phi1 w2
    S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hd4ne
    (hall a ha).2 hbshape hdshape hCshape hEshape hlower

end TerminalLowerZeroSourceTransport68

end Max11DegreeRoutes
