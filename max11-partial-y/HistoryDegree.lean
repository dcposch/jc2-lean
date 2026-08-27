import HistoryRoute

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

theorem bivariate_coeff_coeff_eq_mvCoeff {K : Type*} [CommSemiring K]
    (P : MvPolynomial (Fin 2) K) (i j : ℕ) :
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff i).coeff j =
      P.coeff (Finsupp.single 0 j + Finsupp.single 1 i) := by
  rw [← canonicalBivariateEquiv_eq K]
  simp only [canonicalBivariateEquiv, canonicalYEquiv,
    AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv, Polynomial.coeff_map]
  rw [xCoefficientEquiv]
  change ((MvPolynomial.uniqueAlgEquiv K Unit)
      ((MvPolynomial.renameEquiv K xRestEquivUnit)
        (((MvPolynomial.optionEquivLeft K XRest)
          ((MvPolynomial.renameEquiv K
            (Equiv.optionSubtypeNe (1 : Fin 2)).symm) P)).coeff i))).coeff j = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  let x0 : XRest := ⟨0, by decide⟩
  have hsingle : Finsupp.single () j =
      (Finsupp.single x0 j).mapDomain xRestEquivUnit := by
    apply Finsupp.ext
    intro u
    cases u
    simp [x0, xRestEquivUnit]
  rw [hsingle]
  simp only [MvPolynomial.renameEquiv_apply]
  rw [MvPolynomial.coeff_rename_mapDomain xRestEquivUnit
    xRestEquivUnit.injective]
  rw [MvPolynomial.optionEquivLeft_coeff_coeff]
  let e := (Equiv.optionSubtypeNe (1 : Fin 2)).symm
  have hdmap :
      (Finsupp.single (0 : Fin 2) j + Finsupp.single (1 : Fin 2) i).mapDomain e =
        (Finsupp.single x0 j).optionElim i := by
    simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    ext o
    rcases o with _ | u
    · simp [e]
    · have hu : u = x0 :=
        xRestEquivUnit.injective (Subsingleton.elim _ _)
      subst u
      simp [e, x0]
  rw [← hdmap, MvPolynomial.coeff_rename_mapDomain e e.injective]

/-- The weighted degree attached to the source shear
`(x,y) ↦ (x,y+x^L)`. -/
def sourceShearWeight (L : ℕ) (d : Fin 2 →₀ ℕ) : ℕ :=
  d 0 + L * d 1

/-- A source shear cannot increase total degree beyond the largest source
weight occurring in the support. -/
theorem totalDegree_planeSourceShearHom_le_of_support
    {K : Type*} [Field K] (P : MvPolynomial (Fin 2) K)
    (L W : ℕ) (hL : 1 ≤ L)
    (hW : ∀ d ∈ P.support, sourceShearWeight L d ≤ W) :
    (planeSourceShearHom L P).totalDegree ≤ W := by
  rw [P.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  change ((MvPolynomial.bind₁ (planeSourceShearVars L))
      (MvPolynomial.monomial d (MvPolynomial.coeff d P))).totalDegree ≤ W
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ i ∈ d.support,
        (planeSourceShearVars (K := K) L i ^ d i).totalDegree
        ≤ ∑ i ∈ d.support,
            d i * (if i = 0 then 1 else L) := by
          apply Finset.sum_le_sum
          intro i hi
          refine (MvPolynomial.totalDegree_pow _ _).trans ?_
          gcongr
          fin_cases i
          · simpa [planeSourceShearVars] using
              (MvPolynomial.totalDegree_X (R := K) (0 : Fin 2)).le
          · rw [if_neg (by decide)]
            have hpow : (X 0 ^ L : MvPolynomial (Fin 2) K).totalDegree = L :=
              MvPolynomial.totalDegree_X_pow 0 L
            exact (MvPolynomial.totalDegree_add _ _).trans <| by
              rw [MvPolynomial.totalDegree_X, hpow]
              omega
    _ = sourceShearWeight L d := by
      classical
      change d.sum (fun i e => e * (if i = 0 then 1 else L)) = _
      simp [Finsupp.sum_fintype, Fin.sum_univ_two, sourceShearWeight,
        Nat.mul_comm]
    _ ≤ W := hW d hd

theorem totalDegree_pow_eq_of_ne_zero {K : Type*} [Field K]
    (F : MvPolynomial (Fin 2) K) (n : ℕ) (hF : F ≠ 0) :
    (F ^ n).totalDegree = n * F.totalDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MvPolynomial.totalDegree_mul_of_isDomain
        (pow_ne_zero n hF) hF, ih, Nat.succ_mul]

theorem monomial_fin_two_eq {K : Type*} [CommSemiring K]
    (d : Fin 2 →₀ ℕ) (c : K) :
    MvPolynomial.monomial d c =
      MvPolynomial.C c * X 0 ^ d 0 * X 1 ^ d 1 := by
  rw [MvPolynomial.monomial_eq]
  classical
  simp [Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

set_option maxHeartbeats 800000 in
/-- A nonzero source monomial realizes its source-shear weight as an exact
total degree once the shear exponent is larger than one. -/
theorem totalDegree_planeSourceShearHom_monomial
    {K : Type*} [Field K] (d : Fin 2 →₀ ℕ) (c : K)
    (hc : c ≠ 0) (L : ℕ) (hL : 1 < L) :
    (planeSourceShearHom L (MvPolynomial.monomial d c)).totalDegree =
      sourceShearWeight L d := by
  rw [monomial_fin_two_eq]
  simp only [map_mul, map_pow, planeSourceShearHom_X_zero,
    planeSourceShearHom_X_one]
  simp only [planeSourceShearHom, MvPolynomial.bind₁_C_right]
  have hX0 : (X 0 : MvPolynomial (Fin 2) K) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hX1 : (X 1 : MvPolynomial (Fin 2) K) ≠ 0 := MvPolynomial.X_ne_zero 1
  have hXL : (X 0 ^ L : MvPolynomial (Fin 2) K) ≠ 0 := pow_ne_zero L hX0
  have hadd : (X 1 + X 0 ^ L : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro hz
    have hne : Finsupp.single (0 : Fin 2) L ≠
        Finsupp.single (1 : Fin 2) 1 := by
      intro heq
      have heval := DFunLike.congr_fun heq (1 : Fin 2)
      simp at heval
    have hzcoeff := congrArg
      (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)) hz
    simpa [MvPolynomial.X_pow_eq_monomial, hne] using hzcoeff
  rw [MvPolynomial.totalDegree_mul_of_isDomain
      (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc) (pow_ne_zero _ hX0))
      (pow_ne_zero _ hadd),
    MvPolynomial.totalDegree_mul_of_isDomain
      (MvPolynomial.C_ne_zero.mpr hc) (pow_ne_zero _ hX0),
    MvPolynomial.totalDegree_C,
    totalDegree_pow_eq_of_ne_zero _ _ hX0,
    totalDegree_pow_eq_of_ne_zero _ _ hadd,
    MvPolynomial.totalDegree_X]
  have hdeglt :
      (X (1 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree <
        (X (0 : Fin 2) ^ L : MvPolynomial (Fin 2) K).totalDegree := by
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X_pow]
    exact hL
  have hsum : (X 1 + X 0 ^ L : MvPolynomial (Fin 2) K).totalDegree = L := by
    rw [MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt hdeglt,
      MvPolynomial.totalDegree_X_pow]
  rw [hsum]
  simp [sourceShearWeight, Nat.mul_comm]

/-- A unique source monomial of maximal shear weight determines the exact
total degree after shearing. -/
theorem totalDegree_planeSourceShearHom_eq_of_uniqueMax
    {K : Type*} [Field K] (P : MvPolynomial (Fin 2) K)
    (d₀ : Fin 2 →₀ ℕ) (L W : ℕ) (hL : 1 < L)
    (hWpos : 0 < W)
    (hd₀ : d₀ ∈ P.support) (hweight : sourceShearWeight L d₀ = W)
    (hmax : ∀ d ∈ P.support, d ≠ d₀ → sourceShearWeight L d < W) :
    (planeSourceShearHom L P).totalDegree = W := by
  classical
  let c := P.coeff d₀
  let R := P - MvPolynomial.monomial d₀ c
  have hc : c ≠ 0 := by
    simpa [c, MvPolynomial.mem_support_iff] using hd₀
  have hRsupport : ∀ d ∈ R.support, d ∈ P.support ∧ d ≠ d₀ := by
    intro d hd
    have hdsub := MvPolynomial.support_sub (Fin 2) P
      (MvPolynomial.monomial d₀ c) hd
    have hdne : d ≠ d₀ := by
      intro heq
      subst d
      rw [MvPolynomial.mem_support_iff] at hd
      exact hd (by simp [R, c])
    refine ⟨?_, hdne⟩
    rcases Finset.mem_union.mp hdsub with hdP | hdmono
    · exact hdP
    · rw [MvPolynomial.support_monomial] at hdmono
      split at hdmono
      · simp at hdmono
      · exact absurd (Finset.mem_singleton.mp hdmono) hdne
  have hRle : (planeSourceShearHom L R).totalDegree ≤ W - 1 := by
    apply totalDegree_planeSourceShearHom_le_of_support R L (W - 1) hL.le
    intro d hd
    have hdlt := hmax d (hRsupport d hd).1 (hRsupport d hd).2
    omega
  have hmono :
      (planeSourceShearHom L (MvPolynomial.monomial d₀ c)).totalDegree = W := by
    rw [totalDegree_planeSourceShearHom_monomial d₀ c hc L hL, hweight]
  have hRlt : (planeSourceShearHom L R).totalDegree <
      (planeSourceShearHom L (MvPolynomial.monomial d₀ c)).totalDegree := by
    rw [hmono]
    omega
  have hdecomp : P = MvPolynomial.monomial d₀ c + R := by
    simp [R]
  rw [hdecomp, map_add,
    MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hRlt, hmono]

theorem finsupp_fin_two_eq (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext i
  fin_cases i <;> simp

/-- Exact large-shear total degree from a nonzero top `y`-coefficient. -/
theorem totalDegree_planeSourceShearHom_eq_of_topCoefficient
    {K : Type*} [Field K] (P : MvPolynomial (Fin 2) K)
    (A : K[X]) (m dtop L : ℕ)
    (hmpos : 0 < m) (hdegree : degreeOf 1 P = m)
    (htop : ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m = A)
    (hA : A ≠ 0) (hAtop : A.natDegree = dtop)
    (hlarge : P.totalDegree < L) :
    (planeSourceShearHom L P).totalDegree = dtop + L * m := by
  let d₀ : Fin 2 →₀ ℕ :=
    Finsupp.single 0 dtop + Finsupp.single 1 m
  have hL : 1 < L := by
    have hmle : m ≤ P.totalDegree := by
      rw [← hdegree]
      exact MvPolynomial.degreeOf_le_totalDegree P 1
    omega
  have hd₀mem : d₀ ∈ P.support := by
    rw [MvPolynomial.mem_support_iff]
    rw [← bivariate_coeff_coeff_eq_mvCoeff P m dtop]
    rw [htop, ← hAtop, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hA
  have hweight : sourceShearWeight L d₀ = dtop + L * m := by
    simp [d₀, sourceShearWeight]
  apply totalDegree_planeSourceShearHom_eq_of_uniqueMax P d₀ L
    (dtop + L * m) hL
  · have hLm : 0 < L * m := Nat.mul_pos (by omega) hmpos
    omega
  · exact hd₀mem
  · exact hweight
  · intro d hd hdne
    have hdy : d 1 ≤ m := by
      rw [← hdegree]
      exact MvPolynomial.le_degreeOf_of_mem_support 1 hd
    by_cases hdm : d 1 = m
    · have hdrepr : d = Finsupp.single 0 (d 0) + Finsupp.single 1 m := by
        calc
          d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) :=
            finsupp_fin_two_eq d
          _ = Finsupp.single 0 (d 0) + Finsupp.single 1 m := by rw [hdm]
      have hcoeff : A.coeff (d 0) ≠ 0 := by
        rw [← htop, bivariate_coeff_coeff_eq_mvCoeff]
        rw [← hdrepr]
        exact MvPolynomial.mem_support_iff.mp hd
      have hdxle : d 0 ≤ dtop := by
        rw [← hAtop]
        exact Polynomial.le_natDegree_of_ne_zero hcoeff
      have hdxne : d 0 ≠ dtop := by
        intro hdx
        apply hdne
        rw [hdrepr, hdx]
      simp only [sourceShearWeight, hdm]
      omega
    · have hdylt : d 1 < m := lt_of_le_of_ne hdy hdm
      have hdxle : d 0 ≤ P.totalDegree :=
        (MvPolynomial.le_degreeOf_of_mem_support 0 hd).trans
          (MvPolynomial.degreeOf_le_totalDegree P 0)
      have hdxlt : d 0 < L := hdxle.trans_lt hlarge
      have hstep : d 0 + L * d 1 < L * (d 1 + 1) := by
        rw [Nat.mul_add]
        omega
      have hmul : L * (d 1 + 1) ≤ L * m :=
        Nat.mul_le_mul_left L hdylt
      simp only [sourceShearWeight]
      omega

/-- The leading coefficients `h²` and `h³` of a normalized `(6,9)` source
give the exact total degrees required by the historical large-shear route. -/
theorem planeKeller69SourceShearExactTotalDegree {K : Type*} [Field K] :
    PlaneKeller69SourceShearExactTotalDegreeRoute (K := K) := by
  intro P Q h hsource
  rcases hsource with ⟨hh, hPdegree, hQdegree, hPtop, hQtop, _hKeller⟩
  refine ⟨max P.totalDegree Q.totalDegree, ?_⟩
  intro L hlarge
  have hPlarge : P.totalDegree < L :=
    (Nat.le_max_left P.totalDegree Q.totalDegree).trans_lt hlarge
  have hQlarge : Q.totalDegree < L :=
    (Nat.le_max_right P.totalDegree Q.totalDegree).trans_lt hlarge
  have hPexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    P (h ^ 2) 6 (2 * h.natDegree) L (by norm_num) hPdegree hPtop
    (pow_ne_zero 2 hh) (by rw [Polynomial.natDegree_pow]) hPlarge
  have hQexact := totalDegree_planeSourceShearHom_eq_of_topCoefficient
    Q (h ^ 3) 9 (3 * h.natDegree) L (by norm_num) hQdegree hQtop
    (pow_ne_zero 3 hh) (by rw [Polynomial.natDegree_pow]) hQlarge
  constructor
  · rw [planeSourceShear_apply]
    rw [hPexact]
    omega
  · rw [planeSourceShear_apply]
    rw [hQexact]
    omega

end Max11DegreeRoutes
