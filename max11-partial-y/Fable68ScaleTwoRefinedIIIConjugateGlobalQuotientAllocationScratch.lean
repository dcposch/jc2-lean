import Fable68ScaleTwoRefinedIIIConjugateGlobalQuotientScratch

/-! # Root allocation of the conjugate quotient product divisibilities

The conjugate global quotient split ends its two component-III children with
one new product divisibility each: `H ∣ A^2 * b * w1` on the `D` child and
`H ∣ (A*b - 3*D) * (phi1 + 2*A*w1)` on the `K` child.  This file does not
open any further loaded-row coefficient; it allocates these products across
the two simple core roots `a` (deep) and `c` (conjugate), pinning at every
root which factor of the product dies there through the exact per-root
quotient splits, and globalizing every factor that dies at both roots.

On the `D` child the per-root split kills `b`, `w1` or the apex value `A`
at each root, giving a six-leaf allocation:

* `b` at both roots: `b = H*b1` with the once-cancelled divided `I4`
  `b1*phi1 + 6*w1*D1 = 0` and the exact core drop
  `D1*K = H*(b1*w1*e - C j*H)` of the terminal row;
* `w1` at both roots: the reduced jets force `phi1` to vanish to order two
  at both roots, so `w = H^2*w2` and `phi = H^3*phi3` — the `phi`-face goes
  *cube*-deep — with the twice-cancelled `I4` `b*phi3 + 6*w2*D1 = 0`,
  `b` a unit at both roots;
* apex at both roots: `A = H*A1`, `phi = H^2*phi2` with the cancelled `I4`
  `b*phi2 + 6*w1*D1 = 0`, all of `b`, `w1` units at both roots, and — since
  `K` still vanishes at the deep root — the terminal-row unit condition
  kills the derivative numerator there: `e(a) = 0`;
* three mixed allocations (`b`/`w1`, `b`/apex, `w1`/apex) carrying the
  transverse products `b*w1 = H*U`, `A*b = H*V`, `A*w1 = H*V` respectively,
  the per-root coordinate kills and unit conditions, `phi = H^2*phi2` with a
  pinned quotient root on the `w1`/apex leaf, and `e(a) = 0` whenever the
  apex kill sits at the deep root.

On the `K` child the divided `I4` gives the global cross identity
`b*(phi1 + 2*A*w1) = 2*w1*(A*b - 3*D)`, and the allocation has four leaves:

* `G`-face at both roots: `phi1 + 2*A*w1 = H*G1`, so the *common* sibling's
  face returns one core power deeper, `phi + 2*A*w = H^2*G1`, with the
  cross identity trading the core through `2*w1*(A*b - 3*D) = H*(b*G1)`;
* determinant face at both roots: `A*b - 3*D = H*F1` with the cross
  identity `b*(phi1 + 2*A*w1) = H*(2*w1*F1)`;
* `b`-kill mixed leaf (`G` a unit at `a`, determinant a unit at `c`):
  `b(a) = 0`, `w1(c) = phi1(c) = 0`, the transverse product `b*w1 = H*U`,
  and the conjugate row value dies, `D(c)*K1(c) = 0`; if `D(c) = 0` the
  core lifts to `D = H*D1` and the terminal row drops to `U*e - D1*K1 =
  C j*H`, one core power below every previous row, else `K1(c) = 0` with
  the exact `D*K1 = H*(U*e - C j*H)`;
* `w1`-kill mixed leaf (determinant a unit at `a`, `G` a unit at `c`): the
  two component-III children *merge* — `D = H*D1` joins `K = H*K1`, with
  `w1(a) = phi1(a) = 0`, `b(c) = D(c) = 0`, apex and `b` units at the deep
  root, `b*w1 = H*U`, the `D`-child `I4` shape `b*phi1 + 6*H*w1*D1 = 0`,
  and again the core-one row `U*e - D1*K1 = C j*H`.

The common and component-II siblings, both per-root quotient splits, the
two product divisibilities and the deep-root left-zero selector are all
retained verbatim; the allocation is attached as a further conjunct on each
component-III child of the source-level packet.
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

section RefinedIIIConjugateQuotientAllocation68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Allocation of the `D`-child product `H ∣ A^2 * b * w1` across the two
simple core roots.  Each leaf pins which factor of the product carries each
root, globalizes the factors dying at both roots, and records the exact
core drop of the cancelled rows together with the surviving unit
conditions; whenever the apex kill sits at the deep root the terminal-row
value there kills the derivative numerator, `e(a) = 0`. -/
def terminalRefinedIIIConjugateDQuotientAllocation68
    (H A b w phi e K D1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  (∃ b1 : k[X],
      b = H * b1 ∧
      b1 * phi1 + 6 * w1 * D1 = 0 ∧
      D1 * K = H * (b1 * w1 * e - C j * H)) ∨
  (b.eval a ≠ 0 ∧ b.eval c ≠ 0 ∧
    ∃ w2 phi3 : k[X],
      w1 = H * w2 ∧ phi1 = H ^ 2 * phi3 ∧
      w = H ^ 2 * w2 ∧ phi = H ^ 3 * phi3 ∧
      b * phi3 + 6 * w2 * D1 = 0 ∧
      D1 * K = H * (b * w2 * e - C j * H)) ∨
  (b.eval a ≠ 0 ∧ b.eval c ≠ 0 ∧ w1.eval a ≠ 0 ∧ w1.eval c ≠ 0 ∧
    e.eval a = 0 ∧
    ∃ A1 phi2 : k[X],
      A = H * A1 ∧ phi1 = H * phi2 ∧ phi = H ^ 2 * phi2 ∧
      b * phi2 + 6 * w1 * D1 = 0) ∨
  (((b.eval a = 0 ∧ b.eval c ≠ 0 ∧ w1.eval c = 0 ∧ phi1.eval c = 0 ∧
      phi1.derivative.eval c = 0) ∨
    (b.eval c = 0 ∧ b.eval a ≠ 0 ∧ w1.eval a = 0 ∧ phi1.eval a = 0 ∧
      phi1.derivative.eval a = 0)) ∧
    ∃ U : k[X],
      b * w1 = H * U ∧
      D1 * K = H * (U * e - C j * H)) ∨
  (((b.eval a = 0 ∧ D1.eval a * K.eval a = 0 ∧ b.eval c ≠ 0 ∧
      w1.eval c ≠ 0 ∧ A.eval c = 0 ∧ phi1.eval c = 0) ∨
    (b.eval c = 0 ∧ D1.eval c * K.eval c = 0 ∧ b.eval a ≠ 0 ∧
      w1.eval a ≠ 0 ∧ A.eval a = 0 ∧ phi1.eval a = 0 ∧ e.eval a = 0)) ∧
    ∃ V : k[X], A * b = H * V) ∨
  (b.eval a ≠ 0 ∧ b.eval c ≠ 0 ∧
    ∃ phi2 V : k[X],
      phi1 = H * phi2 ∧ phi = H ^ 2 * phi2 ∧
      b * phi2 + 6 * w1 * D1 = 0 ∧
      A * w1 = H * V ∧
      ((w1.eval a = 0 ∧ phi2.eval a = 0 ∧ w1.eval c ≠ 0 ∧
        A.eval c = 0) ∨
       (w1.eval c = 0 ∧ phi2.eval c = 0 ∧ w1.eval a ≠ 0 ∧
        A.eval a = 0 ∧ e.eval a = 0)))

/-- The `D`-child per-root quotient splits at the two simple roots, the
divided identities and the deep-root value `K(a) = 0` produce the six-leaf
allocation of `H ∣ A^2 * b * w1`. -/
theorem terminalRefinedIII_conjugateD_quotient_allocation_68
    (H A b w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hKa : K.eval a = 0)
    (w1 phi1 D1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1)
    (hI4q : b * phi1 + 6 * H * w1 * D1 = 0)
    (hrowq : b * w1 * e - D1 * K = C j * H ^ 2)
    (hsplit : ∀ x : k, H.eval x = 0 →
      terminalRefinedIIIConjugateDQuotientSplit68 (A.eval x)
        (H.derivative.eval x) (b.eval x) (b.derivative.eval x)
        (w1.eval x) (phi1.eval x) (phi1.derivative.eval x)
        (D1.eval x) (K.eval x) (e.eval x)) :
    terminalRefinedIIIConjugateDQuotientAllocation68
      H A b w phi e K D1 w1 phi1 j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have heaOf : b.eval a ≠ 0 → w1.eval a ≠ 0 → e.eval a = 0 := by
    intro hba hwa
    have hr := congrArg (fun P : k[X] => P.eval a) hrowq
    simp only [eval_sub, eval_mul, eval_pow, eval_C, ha] at hr
    have hkey : b.eval a * (w1.eval a * e.eval a) = 0 := by
      linear_combination hr + D1.eval a * hKa
    exact (mul_eq_zero.mp
      ((mul_eq_zero.mp hkey).resolve_left hba)).resolve_left hwa
  rcases hsplit a ha with ⟨hba, hDKa, hjeta⟩ | ⟨hba, hphia, hjeta, hsuba⟩
  · rcases hsplit c hc with ⟨hbc, hDKc, hjetc⟩ | ⟨hbc, hphic, hjetc, hsubc⟩
    · -- `b` carries both core roots
      left
      obtain ⟨b1, hb1⟩ := dvd_of_two_simple_root_evals_68 H b
        hdeg hsimple a c hac ha hc hba hbc
      refine ⟨b1, hb1, ?_, ?_⟩
      · apply mul_left_cancel₀ hH
        linear_combination hI4q - phi1 * hb1
      · linear_combination -hrowq + w1 * e * hb1
    · rcases hsubc with ⟨hwc, hDKc⟩ | ⟨hwc, hAc, hrowc⟩
      · -- `b` at the deep root, `w1` at the conjugate root
        right; right; right; left
        have hphipc : phi1.derivative.eval c = 0 := by
          have hkey : b.eval c * phi1.derivative.eval c = 0 := by
            linear_combination hjetc -
              6 * H.derivative.eval c * D1.eval c * hwc
          exact (mul_eq_zero.mp hkey).resolve_left hbc
        have hbwa : (b * w1).eval a = 0 := by simp [eval_mul, hba]
        have hbwc : (b * w1).eval c = 0 := by simp [eval_mul, hwc]
        obtain ⟨U, hU⟩ := dvd_of_two_simple_root_evals_68 H (b * w1)
          hdeg hsimple a c hac ha hc hbwa hbwc
        refine ⟨Or.inl ⟨hba, hbc, hwc, hphic, hphipc⟩, U, hU, ?_⟩
        linear_combination -hrowq + e * hU
      · -- `b` at the deep root, apex at the conjugate root
        right; right; right; right; left
        have hAba : (A * b).eval a = 0 := by simp [eval_mul, hba]
        have hAbc : (A * b).eval c = 0 := by simp [eval_mul, hAc]
        obtain ⟨V, hV⟩ := dvd_of_two_simple_root_evals_68 H (A * b)
          hdeg hsimple a c hac ha hc hAba hAbc
        exact ⟨Or.inl ⟨hba, hDKa, hbc, hwc, hAc, hphic⟩, V, hV⟩
  · rcases hsuba with ⟨hwa, hDKa⟩ | ⟨hwa, hAa, hrowa⟩
    · rcases hsplit c hc with ⟨hbc, hDKc, hjetc⟩ | ⟨hbc, hphic, hjetc, hsubc⟩
      · -- `w1` at the deep root, `b` at the conjugate root
        right; right; right; left
        have hphipa : phi1.derivative.eval a = 0 := by
          have hkey : b.eval a * phi1.derivative.eval a = 0 := by
            linear_combination hjeta -
              6 * H.derivative.eval a * D1.eval a * hwa
          exact (mul_eq_zero.mp hkey).resolve_left hba
        have hbwa : (b * w1).eval a = 0 := by simp [eval_mul, hwa]
        have hbwc : (b * w1).eval c = 0 := by simp [eval_mul, hbc]
        obtain ⟨U, hU⟩ := dvd_of_two_simple_root_evals_68 H (b * w1)
          hdeg hsimple a c hac ha hc hbwa hbwc
        refine ⟨Or.inr ⟨hbc, hba, hwa, hphia, hphipa⟩, U, hU, ?_⟩
        linear_combination -hrowq + e * hU
      · rcases hsubc with ⟨hwc, hDKc⟩ | ⟨hwc, hAc, hrowc⟩
        · -- `w1` at both roots: the `phi`-face goes cube-deep
          right; left
          have hphipa : phi1.derivative.eval a = 0 := by
            have hkey : b.eval a * phi1.derivative.eval a = 0 := by
              linear_combination hjeta -
                6 * H.derivative.eval a * D1.eval a * hwa
            exact (mul_eq_zero.mp hkey).resolve_left hba
          have hphipc : phi1.derivative.eval c = 0 := by
            have hkey : b.eval c * phi1.derivative.eval c = 0 := by
              linear_combination hjetc -
                6 * H.derivative.eval c * D1.eval c * hwc
            exact (mul_eq_zero.mp hkey).resolve_left hbc
          obtain ⟨w2, hw2⟩ := dvd_of_two_simple_root_evals_68 H w1
            hdeg hsimple a c hac ha hc hwa hwc
          obtain ⟨q2, hq2⟩ := dvd_of_two_simple_root_evals_68 H phi1
            hdeg hsimple a c hac ha hc hphia hphic
          have hqa : q2.eval a = 0 := by
            have hd : phi1.derivative.eval a =
                H.derivative.eval a * q2.eval a := by
              have h := congrArg (fun P : k[X] => P.derivative.eval a) hq2
              simpa [derivative_mul, eval_add, eval_mul, ha] using h
            have hkey : H.derivative.eval a * q2.eval a = 0 := by
              rw [← hd]; exact hphipa
            exact (mul_eq_zero.mp hkey).resolve_left (hsimple a ha)
          have hqc : q2.eval c = 0 := by
            have hd : phi1.derivative.eval c =
                H.derivative.eval c * q2.eval c := by
              have h := congrArg (fun P : k[X] => P.derivative.eval c) hq2
              simpa [derivative_mul, eval_add, eval_mul, hc] using h
            have hkey : H.derivative.eval c * q2.eval c = 0 := by
              rw [← hd]; exact hphipc
            exact (mul_eq_zero.mp hkey).resolve_left (hsimple c hc)
          obtain ⟨phi3, hphi3⟩ := dvd_of_two_simple_root_evals_68 H q2
            hdeg hsimple a c hac ha hc hqa hqc
          have hphi13 : phi1 = H ^ 2 * phi3 := by
            linear_combination hq2 + H * hphi3
          refine ⟨hba, hbc, w2, phi3, hw2, hphi13, ?_, ?_, ?_, ?_⟩
          · linear_combination hw1 + H * hw2
          · linear_combination hphi1 + H * hq2 + H ^ 2 * hphi3
          · apply mul_left_cancel₀ (pow_ne_zero 2 hH)
            linear_combination hI4q - b * hphi13 - 6 * H * D1 * hw2
          · linear_combination -hrowq + b * e * hw2
        · -- `w1` at the deep root, apex at the conjugate root
          right; right; right; right; right
          have hphipa : phi1.derivative.eval a = 0 := by
            have hkey : b.eval a * phi1.derivative.eval a = 0 := by
              linear_combination hjeta -
                6 * H.derivative.eval a * D1.eval a * hwa
            exact (mul_eq_zero.mp hkey).resolve_left hba
          obtain ⟨phi2, hphi2⟩ := dvd_of_two_simple_root_evals_68 H phi1
            hdeg hsimple a c hac ha hc hphia hphic
          have hphi2a : phi2.eval a = 0 := by
            have hd : phi1.derivative.eval a =
                H.derivative.eval a * phi2.eval a := by
              have h := congrArg (fun P : k[X] => P.derivative.eval a) hphi2
              simpa [derivative_mul, eval_add, eval_mul, ha] using h
            have hkey : H.derivative.eval a * phi2.eval a = 0 := by
              rw [← hd]; exact hphipa
            exact (mul_eq_zero.mp hkey).resolve_left (hsimple a ha)
          have hAwa : (A * w1).eval a = 0 := by simp [eval_mul, hwa]
          have hAwc : (A * w1).eval c = 0 := by simp [eval_mul, hAc]
          obtain ⟨V, hV⟩ := dvd_of_two_simple_root_evals_68 H (A * w1)
            hdeg hsimple a c hac ha hc hAwa hAwc
          refine ⟨hba, hbc, phi2, V, hphi2, ?_, ?_, hV,
            Or.inl ⟨hwa, hphi2a, hwc, hAc⟩⟩
          · linear_combination hphi1 + H * hphi2
          · apply mul_left_cancel₀ hH
            linear_combination hI4q - b * hphi2
    · rcases hsplit c hc with ⟨hbc, hDKc, hjetc⟩ | ⟨hbc, hphic, hjetc, hsubc⟩
      · -- apex at the deep root, `b` at the conjugate root
        right; right; right; right; left
        have hea := heaOf hba hwa
        have hAba : (A * b).eval a = 0 := by simp [eval_mul, hAa]
        have hAbc : (A * b).eval c = 0 := by simp [eval_mul, hbc]
        obtain ⟨V, hV⟩ := dvd_of_two_simple_root_evals_68 H (A * b)
          hdeg hsimple a c hac ha hc hAba hAbc
        exact ⟨Or.inr ⟨hbc, hDKc, hba, hwa, hAa, hphia, hea⟩, V, hV⟩
      · rcases hsubc with ⟨hwc, hDKc⟩ | ⟨hwc, hAc, hrowc⟩
        · -- apex at the deep root, `w1` at the conjugate root
          right; right; right; right; right
          have hea := heaOf hba hwa
          have hphipc : phi1.derivative.eval c = 0 := by
            have hkey : b.eval c * phi1.derivative.eval c = 0 := by
              linear_combination hjetc -
                6 * H.derivative.eval c * D1.eval c * hwc
            exact (mul_eq_zero.mp hkey).resolve_left hbc
          obtain ⟨phi2, hphi2⟩ := dvd_of_two_simple_root_evals_68 H phi1
            hdeg hsimple a c hac ha hc hphia hphic
          have hphi2c : phi2.eval c = 0 := by
            have hd : phi1.derivative.eval c =
                H.derivative.eval c * phi2.eval c := by
              have h := congrArg (fun P : k[X] => P.derivative.eval c) hphi2
              simpa [derivative_mul, eval_add, eval_mul, hc] using h
            have hkey : H.derivative.eval c * phi2.eval c = 0 := by
              rw [← hd]; exact hphipc
            exact (mul_eq_zero.mp hkey).resolve_left (hsimple c hc)
          have hAwa : (A * w1).eval a = 0 := by simp [eval_mul, hAa]
          have hAwc : (A * w1).eval c = 0 := by simp [eval_mul, hwc]
          obtain ⟨V, hV⟩ := dvd_of_two_simple_root_evals_68 H (A * w1)
            hdeg hsimple a c hac ha hc hAwa hAwc
          refine ⟨hba, hbc, phi2, V, hphi2, ?_, ?_, hV,
            Or.inr ⟨hwc, hphi2c, hwa, hAa, hea⟩⟩
          · linear_combination hphi1 + H * hphi2
          · apply mul_left_cancel₀ hH
            linear_combination hI4q - b * hphi2
        · -- apex at both roots
          right; right; left
          have hea := heaOf hba hwa
          obtain ⟨A1, hA1⟩ := dvd_of_two_simple_root_evals_68 H A
            hdeg hsimple a c hac ha hc hAa hAc
          obtain ⟨phi2, hphi2⟩ := dvd_of_two_simple_root_evals_68 H phi1
            hdeg hsimple a c hac ha hc hphia hphic
          refine ⟨hba, hbc, hwa, hwc, hea, A1, phi2, hA1, hphi2, ?_, ?_⟩
          · linear_combination hphi1 + H * hphi2
          · apply mul_left_cancel₀ hH
            linear_combination hI4q - b * hphi2

/-- Allocation of the `K`-child product
`H ∣ (A*b - 3*D) * (phi1 + 2*A*w1)` across the two simple core roots.  The
two global leaves lift one face of the quotient determinant to the full
core; the two mixed leaves carry unit conditions on the complementary
faces, the per-root coordinate kills, the transverse product `b*w1 = H*U`,
and drop the terminal row one further core power whenever `D` also
divides. -/
def terminalRefinedIIIConjugateKQuotientAllocation68
    (H A b D w phi e K1 w1 phi1 : k[X]) (j a c : k) : Prop :=
  (∃ G1 : k[X],
      phi1 + 2 * A * w1 = H * G1 ∧
      phi + 2 * A * w = H ^ 2 * G1 ∧
      2 * w1 * (A * b - 3 * D) = H * (b * G1)) ∨
  (∃ F1 : k[X],
      A * b - 3 * D = H * F1 ∧
      b * (phi1 + 2 * A * w1) = H * (2 * w1 * F1)) ∨
  (phi1.eval a + 2 * A.eval a * w1.eval a ≠ 0 ∧
    A.eval c * b.eval c - 3 * D.eval c ≠ 0 ∧
    b.eval a = 0 ∧ w1.eval c = 0 ∧ phi1.eval c = 0 ∧
    ∃ U : k[X],
      b * w1 = H * U ∧
      ((D.eval c = 0 ∧ A.eval c ≠ 0 ∧ b.eval c ≠ 0 ∧
         ∃ D1 : k[X], D = H * D1 ∧ U * e - D1 * K1 = C j * H) ∨
       (K1.eval c = 0 ∧ D * K1 = H * (U * e - C j * H)))) ∨
  (A.eval a * b.eval a - 3 * D.eval a ≠ 0 ∧
    phi1.eval c + 2 * A.eval c * w1.eval c ≠ 0 ∧
    A.eval a ≠ 0 ∧ b.eval a ≠ 0 ∧ w1.eval a = 0 ∧ phi1.eval a = 0 ∧
    b.eval c = 0 ∧ D.eval c = 0 ∧
    ∃ D1 U : k[X],
      D = H * D1 ∧ b * w1 = H * U ∧
      b * phi1 + 6 * H * w1 * D1 = 0 ∧
      U * e - D1 * K1 = C j * H)

/-- The `K`-child per-root quotient splits at the two simple roots, the
divided identities and the deep-root value `D(a) = 0` produce the four-leaf
allocation of `H ∣ (A*b - 3*D) * (phi1 + 2*A*w1)`. -/
theorem terminalRefinedIII_conjugateK_quotient_allocation_68
    (H A b D w phi e : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hDa : D.eval a = 0)
    (w1 phi1 K1 : k[X])
    (hw1 : w = H * w1) (hphi1 : phi = H * phi1)
    (hI4q : b * phi1 + 6 * w1 * D = 0)
    (hrowq : b * w1 * e - D * K1 = C j * H ^ 2)
    (hsplit : ∀ x : k, H.eval x = 0 →
      terminalRefinedIIIConjugateKQuotientSplit68 (A.eval x) (b.eval x)
        (w1.eval x) (D.eval x) (phi1.eval x)) :
    terminalRefinedIIIConjugateKQuotientAllocation68
      H A b D w phi e K1 w1 phi1 j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  rcases eq_or_ne (A.eval c * b.eval c - 3 * D.eval c) 0 with hFc | hFc
  · rcases eq_or_ne (A.eval a * b.eval a - 3 * D.eval a) 0 with hFa | hFa
    · -- the determinant face carries both core roots
      right; left
      have hFa' : (A * b - 3 * D).eval a = 0 := by
        simp only [eval_sub, eval_mul, eval_ofNat]
        linear_combination hFa
      have hFc' : (A * b - 3 * D).eval c = 0 := by
        simp only [eval_sub, eval_mul, eval_ofNat]
        linear_combination hFc
      obtain ⟨F1, hF1⟩ := dvd_of_two_simple_root_evals_68 H (A * b - 3 * D)
        hdeg hsimple a c hac ha hc hFa' hFc'
      refine ⟨F1, hF1, ?_⟩
      linear_combination hI4q + 2 * w1 * hF1
    · -- the deep root misses the determinant face: its `G`-face and `w1` die
      have hGwa : (phi1.eval a + 2 * A.eval a * w1.eval a = 0) ∧
          w1.eval a = 0 := by
        rcases hsplit a ha with ⟨hF, -⟩ | ⟨hG, hsub⟩
        · exact absurd hF hFa
        · exact ⟨hG, hsub.resolve_right hFa⟩
      obtain ⟨hGa0, hwa⟩ := hGwa
      have hphia : phi1.eval a = 0 := by
        linear_combination hGa0 - 2 * A.eval a * hwa
      rcases eq_or_ne (phi1.eval c + 2 * A.eval c * w1.eval c) 0 with
        hGc | hGc
      · -- the `G`-face carries both core roots after all
        left
        have hGa' : (phi1 + 2 * A * w1).eval a = 0 := by
          simp only [eval_add, eval_mul, eval_ofNat]
          linear_combination hGa0
        have hGc' : (phi1 + 2 * A * w1).eval c = 0 := by
          simp only [eval_add, eval_mul, eval_ofNat]
          linear_combination hGc
        obtain ⟨G1, hG1⟩ := dvd_of_two_simple_root_evals_68 H
          (phi1 + 2 * A * w1) hdeg hsimple a c hac ha hc hGa' hGc'
        refine ⟨G1, hG1, ?_, ?_⟩
        · linear_combination hphi1 + 2 * A * hw1 + H * hG1
        · linear_combination b * hG1 - hI4q
      · -- `w1`-kill allocation: the component-III children merge
        right; right; right
        have hbc : b.eval c = 0 := by
          rcases hsplit c hc with ⟨-, hsub⟩ | ⟨hG, -⟩
          · exact hsub.resolve_right hGc
          · exact absurd hG hGc
        have hDc : D.eval c = 0 := by
          linear_combination (-1 / 3 : k) * hFc + (A.eval c / 3) * hbc
        have hAa : A.eval a ≠ 0 := fun h =>
          hFa (by linear_combination b.eval a * h - 3 * hDa)
        have hba : b.eval a ≠ 0 := fun h =>
          hFa (by linear_combination A.eval a * h - 3 * hDa)
        obtain ⟨D1, hD1⟩ := dvd_of_two_simple_root_evals_68 H D
          hdeg hsimple a c hac ha hc hDa hDc
        have hbwa : (b * w1).eval a = 0 := by simp [eval_mul, hwa]
        have hbwc : (b * w1).eval c = 0 := by simp [eval_mul, hbc]
        obtain ⟨U, hU⟩ := dvd_of_two_simple_root_evals_68 H (b * w1)
          hdeg hsimple a c hac ha hc hbwa hbwc
        refine ⟨hFa, hGc, hAa, hba, hwa, hphia, hbc, hDc,
          D1, U, hD1, hU, ?_, ?_⟩
        · linear_combination hI4q - 6 * w1 * hD1
        · apply mul_left_cancel₀ hH
          linear_combination hrowq - e * hU + K1 * hD1
  · -- the conjugate root misses the determinant face
    have hGwc : (phi1.eval c + 2 * A.eval c * w1.eval c = 0) ∧
        w1.eval c = 0 := by
      rcases hsplit c hc with ⟨hF, -⟩ | ⟨hG, hsub⟩
      · exact absurd hF hFc
      · exact ⟨hG, hsub.resolve_right hFc⟩
    obtain ⟨hGc0, hwc⟩ := hGwc
    have hphic : phi1.eval c = 0 := by
      linear_combination hGc0 - 2 * A.eval c * hwc
    rcases eq_or_ne (phi1.eval a + 2 * A.eval a * w1.eval a) 0 with hGa | hGa
    · -- the `G`-face carries both core roots
      left
      have hGa' : (phi1 + 2 * A * w1).eval a = 0 := by
        simp only [eval_add, eval_mul, eval_ofNat]
        linear_combination hGa
      have hGc' : (phi1 + 2 * A * w1).eval c = 0 := by
        simp only [eval_add, eval_mul, eval_ofNat]
        linear_combination hGc0
      obtain ⟨G1, hG1⟩ := dvd_of_two_simple_root_evals_68 H
        (phi1 + 2 * A * w1) hdeg hsimple a c hac ha hc hGa' hGc'
      refine ⟨G1, hG1, ?_, ?_⟩
      · linear_combination hphi1 + 2 * A * hw1 + H * hG1
      · linear_combination b * hG1 - hI4q
    · -- `b`-kill allocation with the dead conjugate product `D*K1`
      right; right; left
      have hba : b.eval a = 0 := by
        rcases hsplit a ha with ⟨-, hsub⟩ | ⟨hG, -⟩
        · exact hsub.resolve_right hGa
        · exact absurd hG hGa
      have hbwa : (b * w1).eval a = 0 := by simp [eval_mul, hba]
      have hbwc : (b * w1).eval c = 0 := by simp [eval_mul, hwc]
      obtain ⟨U, hU⟩ := dvd_of_two_simple_root_evals_68 H (b * w1)
        hdeg hsimple a c hac ha hc hbwa hbwc
      have hr := congrArg (fun P : k[X] => P.eval c) hrowq
      simp only [eval_sub, eval_mul, eval_pow, eval_C, hc] at hr
      have hDKc : D.eval c * K1.eval c = 0 := by
        linear_combination -hr + b.eval c * e.eval c * hwc
      refine ⟨hGa, hFc, hba, hwc, hphic, U, hU, ?_⟩
      rcases mul_eq_zero.mp hDKc with hDc | hKc
      · left
        have hAc : A.eval c ≠ 0 := fun h =>
          hFc (by linear_combination b.eval c * h - 3 * hDc)
        have hbc : b.eval c ≠ 0 := fun h =>
          hFc (by linear_combination A.eval c * h - 3 * hDc)
        obtain ⟨D1, hD1⟩ := dvd_of_two_simple_root_evals_68 H D
          hdeg hsimple a c hac ha hc hDa hDc
        refine ⟨hDc, hAc, hbc, D1, hD1, ?_⟩
        apply mul_left_cancel₀ hH
        linear_combination hrowq - e * hU + K1 * hD1
      · right
        refine ⟨hKc, ?_⟩
        linear_combination -hrowq + e * hU

/-- The conjugate global split with both component-III children further
refined by the root allocation of their quotient product divisibilities.
The common and component-II children, the divided identities, the per-root
quotient splits, the product divisibilities and the deep-root left-zero
selector are retained verbatim. -/
def terminalRefinedIIIConjugateGlobalQuotientAllocationSplit68
    (H A b D w phi e K : k[X]) (j a c : k) : Prop :=
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
      (∃ P : k[X], A ^ 2 * b * w1 = H * P) ∧
      terminalRefinedIIIConjugateDQuotientAllocation68
        H A b w phi e K D1 w1 phi1 j a c) ∨
   (∃ w1 phi1 K1 : k[X],
      w = H * w1 ∧ phi = H * phi1 ∧ K = H * K1 ∧
      b * phi1 + 6 * w1 * D = 0 ∧
      b * w1 * e - D * K1 = C j * H ^ 2 ∧
      (∀ x : k, H.eval x = 0 →
        terminalRefinedIIIConjugateKQuotientSplit68 (A.eval x) (b.eval x)
          (w1.eval x) (D.eval x) (phi1.eval x)) ∧
      (∃ P : k[X], (A * b - 3 * D) * (phi1 + 2 * A * w1) = H * P) ∧
      (b.eval a = 0 ∨
        (phi1.eval a = 0 ∧ (A.eval a = 0 ∨ w1.eval a = 0))) ∧
      terminalRefinedIIIConjugateKQuotientAllocation68
        H A b D w phi e K1 w1 phi1 j a c))

end RefinedIIIConjugateQuotientAllocation68

section RefinedIIIConjugateQuotientAllocationSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: at every deep component-III root the conjugate
matching persists and the global split returns with both component-III
children carrying their quotient residuals, the product divisibilities and
the new root allocations across the deep/conjugate root pair. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateGlobalQuotientAllocationPacket
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
               terminalRefinedIIIConjugateGlobalQuotientAllocationSplit68
                 H A0 b2 d2 w2 phi2 eDot k2 j a c)) := by
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
    have halloc := terminalRefinedIII_conjugateD_quotient_allocation_68
      H A0 b2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm hKa
      w1 phi1x D1 hw1 hphi1x hI4L hrowL hforall
    exact Or.inr (Or.inr (Or.inl
      ⟨w1, phi1x, D1, hw1, hphi1x, hD1, hI4L, hrowL, hforall,
        ⟨P, hP⟩, halloc⟩))
  · obtain ⟨w1, phi1x, K1, hw1, hphi1x, hK1, hI4L, hrowL⟩ := hK
    obtain ⟨hforall, hFG, hleftA⟩ :=
      terminalRefinedIII_conjugateK_global_quotient_68
        H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm hDa
        w1 phi1x hw1 hphi1x hI4L hclass
    have halloc := terminalRefinedIII_conjugateK_quotient_allocation_68
      H A0 b2 d2 w2 phi2 eDot j a c hdeg hsimple ha hc hca.symm hDa
      w1 phi1x K1 hw1 hphi1x hI4L hrowL hforall
    exact Or.inr (Or.inr (Or.inr
      ⟨w1, phi1x, K1, hw1, hphi1x, hK1, hI4L, hrowL, hforall, hFG,
        hleftA, halloc⟩))

end RefinedIIIConjugateQuotientAllocationSource68

end Max11DegreeRoutes
