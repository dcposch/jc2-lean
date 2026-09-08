/-! ## Source-facing constant first integrals -/

section SourceFirstIntegrals610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 80000000 in
/-- Source-facing packet: the affine-depressed core has integrated `κ`,
`λ`, `μ`, and `ο` polynomials equal to ground constants. -/
theorem normalized610ScaleZero_firstIntegrals_eq_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cLam ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cKap ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cMu ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cOmi ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      _hrow, _homicron, hcore⟩ :=
    normalized610ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD, hE, hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX,
      hder, hdeg⟩ := hcore
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j', _hj', hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDjac : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j') := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambdaN, _a, _g0, _d0, _e, _z, _et, _th, _iot, _ka, _mu, _nu,
      _xi, _omicron0, hN, _hM, _hT, _hU, _hV, _hW, _hX, _hY, _hI, _hZ,
      _hJ, _hnu, _hxi, _homicron⟩ :=
    scaleZero_degreeOneClearedDefect_exists_C_610 hp hq hDjac ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  obtain ⟨aRes, haRes⟩ :=
    scaleZero_lambdaResidual_depressed_eq_C_610 hp hq ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10) hN
      hDjac
  let hRF : RatFunc k := RatFunc.C t
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    dsimp [hRF]
    rw [hp6, hHsq, map_pow, map_pow, RatFunc.algebraMap_C, ← pow_mul]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    dsimp [hRF]
    rw [hq10, hHsq, map_pow, map_pow, RatFunc.algebraMap_C, ← pow_mul]
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨_hg10, hg9, hg8, _hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg9L : g.coeff 9 =
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL610, depressedL810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hg8P : g.coeff 8 =
      depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg7 : g.coeff 7 =
      depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 : g.coeff 6 =
      depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 : g.coeff 5 =
      depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 : g.coeff 4 =
      depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
        b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg3 : g.coeff 3 =
      depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg2 : g.coeff 2 =
      depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg1 : g.coeff 1 =
      depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hmonic :=
    scaleZero_exists_monicDepressedBracket_610 hp hq ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10) hN
      hDjac
  obtain ⟨hf_high, hf6, hf5, hg_high, hg10, hLconst, hjacg⟩ := hmonic
  have hfg :
      kappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) =
        kappaResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgLam :
      algebraMap k[X] (RatFunc k)
          (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        lambdaResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroLambdaPolynomial610]
    rw [← lambdaResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgKap :
      algebraMap k[X] (RatFunc k)
          (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        kappaResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroKappaPolynomial610]
    rw [← kappaResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgMu :
      algebraMap k[X] (RatFunc k)
          (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        muResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroMuPolynomial610]
    rw [← muResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgOmi :
      algebraMap k[X] (RatFunc k)
          (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        fourteenthResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroOmicronPolynomial610]
    rw [← fourteenthResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have hderivLam :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgLam, haRes]
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      ratFuncDerivation68_C aRes
  have hderivKap :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroKappaPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgKap, ← hfg]
    have h0 :=
      kappaResidual610_deriv_zero_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C j' / hRF) hf_high hf6 hf5
        hg_high hg10 hLconst (by simpa [f, g, hRF] using hjacg)
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using h0
  have hfgMu :
      muResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) =
        muResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have hderivMu :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta
              eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgMu, ← hfgMu]
    have h0 :=
      muResidual610_deriv_zero_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C j' / hRF) hf_high hf6 hf5
        hg_high hg10 hLconst (by simpa [f, g, hRF] using hjacg)
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using h0
  have hfgOmi :
      fourteenthResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) =
        fourteenthResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have hderivOmi :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgOmi, ← hfgOmi]
    have h0 :=
      fourteenthResidual610_deriv_zero_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C j' / hRF) hf_high hf6 hf5
        hg_high hg10 hLconst (by simpa [f, g, hRF] using hjacg)
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using h0
  obtain ⟨cLam, hcLam⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivLam
  obtain ⟨cKap, hcKap⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivKap
  obtain ⟨cMu, hcMu⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivMu
  obtain ⟨cOmi, hcOmi⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivOmi
  exact ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht, hj,
    hjdiv, hHsq, hder, hdeg, hcLam,
    polynomial_natDegree_eq_zero_of_eq_C hcLam, hcKap,
    polynomial_natDegree_eq_zero_of_eq_C hcKap, hcMu,
    polynomial_natDegree_eq_zero_of_eq_C hcMu, hcOmi,
    polynomial_natDegree_eq_zero_of_eq_C hcOmi⟩

end SourceFirstIntegrals610
