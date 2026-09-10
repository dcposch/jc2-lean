import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateSourceScratch

/-! # Quotient residuals on the component-III `D`/`K` conjugate leaves

The refined-III conjugate global split ends in two component-III leaves where
`w` and `phi` both carry the nonsquare core and either `D` or `K` carries a
further core factor.  On each leaf the divided identities

* `b * phi1 + 6 * H * w1 * D1 = 0` and `b * w1 * e - D1 * K = C j * H ^ 2`
  (the `D` child), or
* `b * phi1 + 6 * w1 * D = 0` and `b * w1 * e - D * K1 = C j * H ^ 2`
  (the `K` child)

hold globally, while the exact lower-third jets of the transported lower-zero
row are available at *both* simple core roots.  This file consumes that pair
without opening any further loaded-row coefficient.

On the `K` child the component-III lower-third face divides exactly by the
simple-root unit `H'(x)` and, against the evaluated divided `I4`, reproduces
the conjugate-II two-by-two determinant one core power deeper: at every core
root `(A*b - 3*D)*(phi1 + 2*A*w1)` vanishes with an exact factor allocation,
so the product acquires the full core, `H ∣ (A*b - 3*D)*(phi1 + 2*A*w1)`.

On the `D` child the left-zero split of the lower-third row localizes the
quotients themselves: at every core root either `b` vanishes with the reduced
jet tie `b' * phi1 + 6 * H' * w1 * D1 = 0` and the dead product `D1 * K = 0`,
or `b` is a unit, `phi1` vanishes, and either `w1` dies (killing `D1 * K`) or
the apex value `A` dies with the exact transported row `b*w1*e = D1*K`.  In
all branches `A^2 * b * w1` vanishes, so `H ∣ A^2 * b * w1` globally.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

section RefinedIIIConjugateQuotientAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact finite residual at a core root on the component-III `D` child.
Either `b` dies there, taking `D1 * K` with it and reducing the divided-`I4`
jet, or `b` is a unit, forcing `phi1` to die, and the left-zero refinement
kills `w1` (and again `D1 * K`) or the apex value `A` with the exact
transported terminal row. -/
def terminalRefinedIIIConjugateDQuotientSplit68
    (A hprime bv bp wv phiv php dv kv ev : k) : Prop :=
  (bv = 0 ∧ dv * kv = 0 ∧ bp * phiv + 6 * hprime * wv * dv = 0) ∨
    (bv ≠ 0 ∧ phiv = 0 ∧ bv * php + 6 * hprime * wv * dv = 0 ∧
      ((wv = 0 ∧ dv * kv = 0) ∨ (wv ≠ 0 ∧ A = 0 ∧ bv * wv * ev = dv * kv)))

/-- Exact finite residual at a core root on the component-III `K` child: the
quotient-level `F`/`G` determinant split, one core power deeper than the
conjugate-II split. -/
def terminalRefinedIIIConjugateKQuotientSplit68
    (A bv wv dv phiv : k) : Prop :=
  ((A * bv - 3 * dv = 0) ∧ (bv = 0 ∨ phiv + 2 * A * wv = 0)) ∨
    ((phiv + 2 * A * wv = 0) ∧ (wv = 0 ∨ A * bv - 3 * dv = 0))

theorem terminalRefinedIII_conjugateD_quotient_split_68
    (A hprime bv bp wv phiv php dv kv ev : k)
    (hjet : bp * phiv + bv * php + 6 * hprime * wv * dv = 0)
    (hrow : bv * wv * ev - dv * kv = 0)
    (hleft : bv = 0 ∨ (phiv = 0 ∧ (A = 0 ∨ wv = 0))) :
    terminalRefinedIIIConjugateDQuotientSplit68
      A hprime bv bp wv phiv php dv kv ev := by
  rcases eq_or_ne bv 0 with hb | hb
  · left
    refine ⟨hb, ?_, ?_⟩
    · linear_combination wv * ev * hb - hrow
    · linear_combination hjet - php * hb
  · right
    have hright := hleft.resolve_left hb
    refine ⟨hb, hright.1, ?_, ?_⟩
    · linear_combination hjet - bp * hright.1
    · rcases eq_or_ne wv 0 with hw | hw
      · exact Or.inl ⟨hw, by linear_combination bv * ev * hw - hrow⟩
      · exact Or.inr ⟨hw, hright.2.resolve_right hw,
          by linear_combination hrow⟩

/-- The divided-`I4` value and the `H'`-divided component-III lower-third
face form the same two-by-two determinant as on the conjugate component II,
now entirely at the quotient level. -/
theorem terminalRefinedIII_conjugateK_quotient_split_68
    (A bv wv dv phiv : k)
    (hI4 : bv * phiv + 6 * wv * dv = 0)
    (hlower :
      2 * A * wv * (A * bv - 3 * dv) - 3 * dv * (phiv + 2 * A * wv) = 0) :
    terminalRefinedIIIConjugateKQuotientSplit68 A bv wv dv phiv := by
  let F := A * bv - 3 * dv
  let G := phiv + 2 * A * wv
  have hcross : bv * G - 2 * wv * F = 0 := by
    dsimp only [F, G]
    linear_combination hI4
  have hdet : F * G = 0 := by
    dsimp only [F, G] at hcross ⊢
    linear_combination A * hcross + hlower
  rcases mul_eq_zero.mp hdet with hF | hG
  · left
    refine ⟨hF, ?_⟩
    have hbG : bv * G = 0 := by
      rw [hF, mul_zero, sub_zero] at hcross
      exact hcross
    exact mul_eq_zero.mp hbG
  · right
    refine ⟨hG, ?_⟩
    have hwF : wv * F = 0 := by
      rw [hG, mul_zero, zero_sub] at hcross
      have htwo : (2 : k) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (by linear_combination -hcross)).resolve_left htwo
    exact mul_eq_zero.mp hwF

theorem terminalRefinedIIIConjugateDQuotientSplit68_core_zero
    {A hprime bv bp wv phiv php dv kv ev : k}
    (h : terminalRefinedIIIConjugateDQuotientSplit68
      A hprime bv bp wv phiv php dv kv ev) :
    A ^ 2 * bv * wv = 0 := by
  rcases h with ⟨hb, -, -⟩ | ⟨-, -, -, hsub⟩
  · simp [hb]
  · rcases hsub with ⟨hw, -⟩ | ⟨-, hA, -⟩
    · simp [hw]
    · simp [hA]

theorem terminalRefinedIIIConjugateKQuotientSplit68_product_zero
    {A bv wv dv phiv : k}
    (h : terminalRefinedIIIConjugateKQuotientSplit68 A bv wv dv phiv) :
    (A * bv - 3 * dv) * (phiv + 2 * A * wv) = 0 := by
  rcases h with ⟨hF, -⟩ | ⟨hG, -⟩
  · rw [hF, zero_mul]
  · rw [hG, mul_zero]

end RefinedIIIConjugateQuotientAlgebra68

section RefinedIIIConjugateQuotientPolynomial68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- On the component-III `D` child the left-zero lower-third jet, the first
jet of the cancelled `I4`, and the value of the `H^2`-loaded terminal row
produce the exact quotient residual at *every* core root; the surviving
product `A^2 * b * w1` then vanishes at both simple roots and globalizes to
core divisibility. -/
theorem terminalRefinedIII_conjugateD_global_quotient_68
    (H A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (w1 phi1 D1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1) (hD1 : D = H * D1)
    (hI4q : b * phi1 + 6 * H * w1 * D1 = 0)
    (hrowq : b * w1 * e - D1 * K = C j * H ^ 2)
    (hclass : ∀ x : k, H.eval x = 0 →
      terminalPhiDivisorLowerThirdClassification68 (A.eval x)
        (H.derivative.eval x) (6 * j * (H.derivative.eval x) ^ 3)
        b D w phi e K x) :
    (∀ x : k, H.eval x = 0 →
      terminalRefinedIIIConjugateDQuotientSplit68 (A.eval x)
        (H.derivative.eval x) (b.eval x) (b.derivative.eval x)
        (w1.eval x) (phi1.eval x) (phi1.derivative.eval x)
        (D1.eval x) (K.eval x) (e.eval x)) ∧
      ∃ P : k[X], A ^ 2 * b * w1 = H * P := by
  have hsplit : ∀ x : k, H.eval x = 0 →
      terminalRefinedIIIConjugateDQuotientSplit68 (A.eval x)
        (H.derivative.eval x) (b.eval x) (b.derivative.eval x)
        (w1.eval x) (phi1.eval x) (phi1.derivative.eval x)
        (D1.eval x) (K.eval x) (e.eval x) := by
    intro x hx
    have hh := hsimple x hx
    have hwx : w.eval x = 0 := by rw [hw1]; simp [eval_mul, hx]
    have hphix : phi.eval x = 0 := by rw [hphi1]; simp [eval_mul, hx]
    have hDx : D.eval x = 0 := by rw [hD1]; simp [eval_mul, hx]
    have hwd : w.derivative.eval x =
        H.derivative.eval x * w1.eval x := by
      have h := congrArg (fun P : k[X] => P.derivative.eval x) hw1
      simpa [derivative_mul, eval_add, eval_mul, hx] using h
    have hphid : phi.derivative.eval x =
        H.derivative.eval x * phi1.eval x := by
      have h := congrArg (fun P : k[X] => P.derivative.eval x) hphi1
      simpa [derivative_mul, eval_add, eval_mul, hx] using h
    have hleftRaw := (hclass x hx).2.2.2.2 hwx hphix hDx
    have hleft : b.eval x = 0 ∨
        (phi1.eval x = 0 ∧ (A.eval x = 0 ∨ w1.eval x = 0)) := by
      rcases hleftRaw with hb | ⟨hp, hAw⟩
      · exact Or.inl hb
      · right
        rw [hphid] at hp
        refine ⟨(mul_eq_zero.mp hp).resolve_left hh, ?_⟩
        rcases hAw with hA | hwv
        · exact Or.inl hA
        · rw [hwd] at hwv
          exact Or.inr ((mul_eq_zero.mp hwv).resolve_left hh)
    have hjet : b.derivative.eval x * phi1.eval x +
        b.eval x * phi1.derivative.eval x +
        6 * H.derivative.eval x * w1.eval x * D1.eval x = 0 := by
      have h := congrArg (fun P : k[X] => P.derivative.eval x) hI4q
      simp only [derivative_add, derivative_mul, derivative_ofNat,
        derivative_zero, eval_add, eval_mul, eval_ofNat, eval_zero, hx,
        zero_mul, mul_zero, zero_add, add_zero] at h
      linear_combination h
    have hrowx : b.eval x * w1.eval x * e.eval x -
        D1.eval x * K.eval x = 0 := by
      have h := congrArg (fun P : k[X] => P.eval x) hrowq
      simp only [eval_sub, eval_mul, eval_pow, eval_C, hx] at h
      linear_combination h
    exact terminalRefinedIII_conjugateD_quotient_split_68
      (A.eval x) (H.derivative.eval x) (b.eval x) (b.derivative.eval x)
      (w1.eval x) (phi1.eval x) (phi1.derivative.eval x)
      (D1.eval x) (K.eval x) (e.eval x) hjet hrowx hleft
  have hva : (A ^ 2 * b * w1).eval a = 0 := by
    have h := terminalRefinedIIIConjugateDQuotientSplit68_core_zero
      (hsplit a ha)
    simp only [eval_mul, eval_pow]
    linear_combination h
  have hvc : (A ^ 2 * b * w1).eval c = 0 := by
    have h := terminalRefinedIIIConjugateDQuotientSplit68_core_zero
      (hsplit c hc)
    simp only [eval_mul, eval_pow]
    linear_combination h
  obtain ⟨P, hP⟩ := dvd_of_two_simple_root_evals_68 H (A ^ 2 * b * w1)
    hdeg hsimple a c hac ha hc hva hvc
  exact ⟨hsplit, P, hP⟩

/-- On the component-III `K` child the cancelled `I4` and the `H'`-divided
component-III lower-third face give the quotient determinant split at every
core root, so `(A*b - 3*D)*(phi1 + 2*A*w1)` acquires the full core; at the
deep root the left-zero jet additionally splits the quotients themselves. -/
theorem terminalRefinedIII_conjugateK_global_quotient_68
    (H A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hDa : D.eval a = 0)
    (w1 phi1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1)
    (hI4q : b * phi1 + 6 * w1 * D = 0)
    (hclass : ∀ x : k, H.eval x = 0 →
      terminalPhiDivisorLowerThirdClassification68 (A.eval x)
        (H.derivative.eval x) (6 * j * (H.derivative.eval x) ^ 3)
        b D w phi e K x) :
    (∀ x : k, H.eval x = 0 →
      terminalRefinedIIIConjugateKQuotientSplit68 (A.eval x) (b.eval x)
        (w1.eval x) (D.eval x) (phi1.eval x)) ∧
      (∃ P : k[X], (A * b - 3 * D) * (phi1 + 2 * A * w1) = H * P) ∧
      (b.eval a = 0 ∨
        (phi1.eval a = 0 ∧ (A.eval a = 0 ∨ w1.eval a = 0))) := by
  have hderiv : ∀ x : k, H.eval x = 0 →
      w.derivative.eval x = H.derivative.eval x * w1.eval x ∧
      phi.derivative.eval x = H.derivative.eval x * phi1.eval x := by
    intro x hx
    constructor
    · have h := congrArg (fun P : k[X] => P.derivative.eval x) hw1
      simpa [derivative_mul, eval_add, eval_mul, hx] using h
    · have h := congrArg (fun P : k[X] => P.derivative.eval x) hphi1
      simpa [derivative_mul, eval_add, eval_mul, hx] using h
  have hsplit : ∀ x : k, H.eval x = 0 →
      terminalRefinedIIIConjugateKQuotientSplit68 (A.eval x) (b.eval x)
        (w1.eval x) (D.eval x) (phi1.eval x) := by
    intro x hx
    have hh := hsimple x hx
    have hwx : w.eval x = 0 := by rw [hw1]; simp [eval_mul, hx]
    have hphix : phi.eval x = 0 := by rw [hphi1]; simp [eval_mul, hx]
    obtain ⟨hwd, hphid⟩ := hderiv x hx
    have hface := (hclass x hx).2.2.2.1 hwx hphix
    rw [hwd, hphid] at hface
    have hfac : H.derivative.eval x *
        (2 * A.eval x * w1.eval x * (A.eval x * b.eval x - 3 * D.eval x) -
          3 * D.eval x * (phi1.eval x + 2 * A.eval x * w1.eval x)) = 0 := by
      linear_combination hface
    have hlower := (mul_eq_zero.mp hfac).resolve_left hh
    have hI4x : b.eval x * phi1.eval x +
        6 * w1.eval x * D.eval x = 0 := by
      have h := congrArg (fun P : k[X] => P.eval x) hI4q
      simp only [eval_add, eval_mul, eval_ofNat, eval_zero] at h
      linear_combination h
    exact terminalRefinedIII_conjugateK_quotient_split_68
      (A.eval x) (b.eval x) (w1.eval x) (D.eval x) (phi1.eval x)
      hI4x hlower
  have hva : ((A * b - 3 * D) * (phi1 + 2 * A * w1)).eval a = 0 := by
    have h := terminalRefinedIIIConjugateKQuotientSplit68_product_zero
      (hsplit a ha)
    simp only [eval_mul, eval_sub, eval_add, eval_ofNat]
    linear_combination h
  have hvc : ((A * b - 3 * D) * (phi1 + 2 * A * w1)).eval c = 0 := by
    have h := terminalRefinedIIIConjugateKQuotientSplit68_product_zero
      (hsplit c hc)
    simp only [eval_mul, eval_sub, eval_add, eval_ofNat]
    linear_combination h
  obtain ⟨P, hP⟩ := dvd_of_two_simple_root_evals_68 H
    ((A * b - 3 * D) * (phi1 + 2 * A * w1))
    hdeg hsimple a c hac ha hc hva hvc
  have hwa : w.eval a = 0 := by rw [hw1]; simp [eval_mul, ha]
  have hphia : phi.eval a = 0 := by rw [hphi1]; simp [eval_mul, ha]
  obtain ⟨hwda, hphida⟩ := hderiv a ha
  have hleftRaw := (hclass a ha).2.2.2.2 hwa hphia hDa
  have hleftq : b.eval a = 0 ∨
      (phi1.eval a = 0 ∧ (A.eval a = 0 ∨ w1.eval a = 0)) := by
    rcases hleftRaw with hb | ⟨hp, hAw⟩
    · exact Or.inl hb
    · right
      rw [hphida] at hp
      refine ⟨(mul_eq_zero.mp hp).resolve_left (hsimple a ha), ?_⟩
      rcases hAw with hA | hwv
      · exact Or.inl hA
      · rw [hwda] at hwv
        exact Or.inr ((mul_eq_zero.mp hwv).resolve_left (hsimple a ha))
  exact ⟨hsplit, ⟨P, hP⟩, hleftq⟩

/-- The conjugate global split with both component-III children refined by
their quotient residuals: every core root carries the exact finite split of
the divided data, and the surviving products `A^2 * b * w1` respectively
`(A*b - 3*D)*(phi1 + 2*A*w1)` divide by the core.  The common and
component-II children are retained verbatim. -/
def terminalRefinedIIIConjugateGlobalQuotientSplit68
    (H A b D w phi e K : k[X]) (j a : k) : Prop :=
  (∃ G : k[X],
      phi + 2 * A * w = H * G ∧
      H * b * G - 2 * w * (A * b - 3 * D) = 0) ∨
  (∃ D1 BW : k[X],
      D = H * D1 ∧ b * w = H * BW ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      BW * e - D1 * K = C j * H ^ 2) ∨
  ((∃ w1 phi1 D1 : k[X],
      w = H * w1 ∧ phi = H * phi1 ∧ D = H * D1 ∧
      b * phi1 + 6 * H * w1 * D1 = 0 ∧
      b * w1 * e - D1 * K = C j * H ^ 2 ∧
      (∀ x : k, H.eval x = 0 →
        terminalRefinedIIIConjugateDQuotientSplit68 (A.eval x)
          (H.derivative.eval x) (b.eval x) (b.derivative.eval x)
          (w1.eval x) (phi1.eval x) (phi1.derivative.eval x)
          (D1.eval x) (K.eval x) (e.eval x)) ∧
      (∃ P : k[X], A ^ 2 * b * w1 = H * P)) ∨
   (∃ w1 phi1 K1 : k[X],
      w = H * w1 ∧ phi = H * phi1 ∧ K = H * K1 ∧
      b * phi1 + 6 * w1 * D = 0 ∧
      b * w1 * e - D * K1 = C j * H ^ 2 ∧
      (∀ x : k, H.eval x = 0 →
        terminalRefinedIIIConjugateKQuotientSplit68 (A.eval x) (b.eval x)
          (w1.eval x) (D.eval x) (phi1.eval x)) ∧
      (∃ P : k[X], (A * b - 3 * D) * (phi1 + 2 * A * w1) = H * P) ∧
      (b.eval a = 0 ∨
        (phi1.eval a = 0 ∧ (A.eval a = 0 ∨ w1.eval a = 0)))))

end RefinedIIIConjugateQuotientPolynomial68

section RefinedIIIConjugateQuotientSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: at every deep component-III root the conjugate
matching persists and the global split returns with both component-III
children carrying their quotient residuals and the new core
divisibilities. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateGlobalQuotientPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X Yd phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      (H ∣ phi1 →
        ∃ phi2 k2 : k[X], phi1 = H * phi2 ∧ k1 = H * k2 ∧
          b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∧
          (let A0 := cubicANumerator68 t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           ∀ a : k, H.eval a = 0 → w2.eval a = 0 →
             phi2.eval a = 0 → d2.eval a = 0 → k2.eval a = 0 →
             ∃ c : k, c ≠ a ∧ H.eval c = 0 ∧
               terminalRefinedIIIConjugateMatching68
                 H A0 b2 d2 w2 phi2 eDot k2 j c ∧
               terminalRefinedIIIConjugateGlobalQuotientSplit68
                 H A0 b2 d2 w2 phi2 eDot k2 j a)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorRefinedIIIPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hroots ⊢
  intro a ha hwa hphia hDa hKa
  let A0 := cubicANumerator68 t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hclass : ∀ x : k, H.eval x = 0 →
      terminalPhiDivisorLowerThirdClassification68 (A0.eval x)
        (H.derivative.eval x) (6 * j * (H.derivative.eval x) ^ 3)
        b2 d2 w2 phi2 eDot k2 x := fun x hx => (hroots x hx).1
  obtain ⟨c, hca, hc, hmatch⟩ := terminalRefinedIII_conjugate_matching_68
    H A0 b2 d2 w2 phi2 eDot k2 j a hdeg hsimple ha hwa hphia hDa hKa hclass
  have hglobal := terminalRefinedIII_conjugate_global_split_68
    H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      hwa hphia hDa hKa hI4 hrow hmatch
  refine ⟨c, hca, hc, hmatch, ?_⟩
  rcases hglobal with hcommon | hII | hD | hK
  · exact Or.inl hcommon
  · exact Or.inr (Or.inl hII)
  · obtain ⟨w1, phi1x, D1, hw1, hphi1x, hD1, hI4L, hrowL⟩ := hD
    obtain ⟨hforall, P, hP⟩ := terminalRefinedIII_conjugateD_global_quotient_68
      H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      w1 phi1x D1 hw1 hphi1x hD1 hI4L hrowL hclass
    exact Or.inr (Or.inr (Or.inl
      ⟨w1, phi1x, D1, hw1, hphi1x, hD1, hI4L, hrowL, hforall, P, hP⟩))
  · obtain ⟨w1, phi1x, K1, hw1, hphi1x, hK1, hI4L, hrowL⟩ := hK
    obtain ⟨hforall, hFG, hleftA⟩ :=
      terminalRefinedIII_conjugateK_global_quotient_68
        H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm hDa
        w1 phi1x hw1 hphi1x hI4L hclass
    exact Or.inr (Or.inr (Or.inr
      ⟨w1, phi1x, K1, hw1, hphi1x, hK1, hI4L, hrowL, hforall, hFG, hleftA⟩))

end RefinedIIIConjugateQuotientSource68

end Max11DegreeRoutes
