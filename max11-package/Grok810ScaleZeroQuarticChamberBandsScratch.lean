import Grok810ScaleZeroQuarticChamberAuxTowerScratch
import Grok810ScaleZeroQuarticLoadLadderScratch

/-! # The κ load bands of the chamber kills, `(8,10)` scale zero

One cascade over the `l → β → δ → ζ → θ` κ-column ladder of
`Grok810ScaleZeroQuarticLoadLadderScratch`, packaged as the five band
disjunctions `π = 0 ∨ ¬ QuarticKappaLoadTop<Π>810` the chamber kills
consume.  Monotonicity `Topθ → Topζ → Topδ → Topβ → Topl` makes the
cascade linear: in the branch where the first predicate fails, every
later one fails too and its band is vacuous.  `γ, ε, η` have no pure-`A`
column in `κ` and therefore no band here — that is corner `H`; the
chambers that need one are named in the residual.  Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticChamberBands810

/-! ## Monotonicity of the κ kill predicates -/

set_option maxHeartbeats 64000000 in
/-- The `beta` column tops `κ` only if the cheaper `l` column does. -/
theorem quarticKappaLoadTopBeta810_imp_L810
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopBeta810 A B C D E F G) :
    QuarticKappaLoadTopL810 A B C D E F G := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hB with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hC with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hD with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hE with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hF with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hG with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)

set_option maxHeartbeats 64000000 in
/-- The `delta` column tops `κ` only if the cheaper `beta` column does. -/
theorem quarticKappaLoadTopDelta810_imp_Beta810
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopDelta810 A B C D E F G) :
    QuarticKappaLoadTopBeta810 A B C D E F G := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hB with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hC with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hD with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hE with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hF with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hG with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)

set_option maxHeartbeats 64000000 in
/-- The `zeta` column tops `κ` only if the cheaper `delta` column does. -/
theorem quarticKappaLoadTopZeta810_imp_Delta810
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopZeta810 A B C D E F G) :
    QuarticKappaLoadTopDelta810 A B C D E F G := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl hB
  · rcases hC with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hD with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hE with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hF with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hG with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)

set_option maxHeartbeats 64000000 in
/-- The `theta` column tops `κ` only if the cheaper `zeta` column does. -/
theorem quarticKappaLoadTopTheta810_imp_Zeta810
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopTheta810 A B C D E F G) :
    QuarticKappaLoadTopZeta810 A B C D E F G := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hB
  · exact Or.inl hC
  · rcases hD with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hE with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hF with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hG with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr (by omega)

/-! ## The `zeta` band in usable shape -/

set_option maxHeartbeats 64000000 in
/-- File A's `quarticSigma_zeta_band_disjunction` renders the hard
`B = 0` conjunct of `QuarticKappaLoadTopZeta810` as the vacuous
`0 ≤ A.natDegree + 4 * B.natDegree`; this is the same disjunction with
that summand as `B ≠ 0`. -/
theorem quarticSigma_zeta_band_disjunction810'
    {zeta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopZeta810 A B C D E F G → zeta = 0) :
    zeta = 0 ∨
      B ≠ 0 ∨
      A.natDegree ≤ 4 * C.natDegree ∨
      3 * A.natDegree ≤ 4 * D.natDegree ∨
      5 * A.natDegree ≤ 4 * E.natDegree ∨
      7 * A.natDegree ≤ 4 * F.natDegree ∨
      9 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : B = 0
  · by_cases hC : 4 * C.natDegree < A.natDegree
    · by_cases hD : 4 * D.natDegree < 3 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 5 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 7 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 9 * A.natDegree
            · exact Or.inl (hkill ⟨hA, hB, Or.inr hC, Or.inr hD, Or.inr hE, Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · exact Or.inr (Or.inl hB)

/-! ## The five κ bands, from the ladder -/

set_option maxHeartbeats 64000000 in
/-- The `l → β → δ → ζ → θ` κ-column ladder, packaged as the five
band disjunctions the chamber kills consume.  In each branch the
first `QuarticKappaLoadTop` that fails kills nothing, but by
monotonicity every later one fails too, so its band holds vacuously. -/
theorem quarticSigma_kappaLoadBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    (l = 0 ∨
      5 * A.natDegree ≤ 4 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * C.natDegree ∨
      9 * A.natDegree ≤ 4 * D.natDegree ∨
      11 * A.natDegree ≤ 4 * E.natDegree ∨
      13 * A.natDegree ≤ 4 * F.natDegree ∨
      15 * A.natDegree ≤ 4 * G.natDegree) ∧
    (beta = 0 ∨
      3 * A.natDegree ≤ 4 * B.natDegree ∨
      5 * A.natDegree ≤ 4 * C.natDegree ∨
      7 * A.natDegree ≤ 4 * D.natDegree ∨
      9 * A.natDegree ≤ 4 * E.natDegree ∨
      11 * A.natDegree ≤ 4 * F.natDegree ∨
      13 * A.natDegree ≤ 4 * G.natDegree) ∧
    (delta = 0 ∨
      A.natDegree ≤ 4 * B.natDegree ∨
      3 * A.natDegree ≤ 4 * C.natDegree ∨
      5 * A.natDegree ≤ 4 * D.natDegree ∨
      7 * A.natDegree ≤ 4 * E.natDegree ∨
      9 * A.natDegree ≤ 4 * F.natDegree ∨
      11 * A.natDegree ≤ 4 * G.natDegree) ∧
    (zeta = 0 ∨
      B ≠ 0 ∨
      A.natDegree ≤ 4 * C.natDegree ∨
      3 * A.natDegree ≤ 4 * D.natDegree ∨
      5 * A.natDegree ≤ 4 * E.natDegree ∨
      7 * A.natDegree ≤ 4 * F.natDegree ∨
      9 * A.natDegree ≤ 4 * G.natDegree) ∧
    (theta = 0 ∨
      B ≠ 0 ∨
      C ≠ 0 ∨
      A.natDegree ≤ 4 * D.natDegree ∨
      3 * A.natDegree ≤ 4 * E.natDegree ∨
      A.natDegree ≤ F.natDegree ∨
      7 * A.natDegree ≤ 4 * G.natDegree) := by
  by_cases hTl : QuarticKappaLoadTopL810 A B C D E F G
  · have hl0 : l = 0 :=
      quarticSigma_l_eq_zero l beta gamma delta epsilon zeta eta theta
        A B C D E F G hTl hkap
    by_cases hTbeta : QuarticKappaLoadTopBeta810 A B C D E F G
    · have hbeta0 : beta = 0 :=
        quarticSigma_beta_eq_zero l beta gamma delta epsilon zeta eta theta
          A B C D E F G hTbeta hl0 hkap
      by_cases hTdelta : QuarticKappaLoadTopDelta810 A B C D E F G
      · have hdelta0 : delta = 0 :=
          quarticSigma_delta_eq_zero l beta gamma delta epsilon zeta eta theta
            A B C D E F G hTdelta hl0 hbeta0 hkap
        by_cases hTzeta : QuarticKappaLoadTopZeta810 A B C D E F G
        · have hzeta0 : zeta = 0 :=
            quarticSigma_zeta_eq_zero l beta gamma delta epsilon zeta eta theta
              A B C D E F G hTzeta hl0 hbeta0 hdelta0 hkap
          by_cases hTtheta : QuarticKappaLoadTopTheta810 A B C D E F G
          · have htheta0 : theta = 0 :=
              quarticSigma_theta_eq_zero l beta gamma delta epsilon zeta eta theta
                A B C D E F G hTtheta hl0 hbeta0 hdelta0 hzeta0 hkap
            exact ⟨Or.inl hl0, Or.inl hbeta0, Or.inl hdelta0, Or.inl hzeta0, Or.inl htheta0⟩
          · exact ⟨Or.inl hl0,
              Or.inl hbeta0,
              Or.inl hdelta0,
              Or.inl hzeta0,
              quarticSigma_theta_band_disjunction (A := A) (B := B) (C := C) (D := D)
                (E := E) (F := F) (G := G) (theta := theta) hA
                (fun htop => absurd (htop) hTtheta)⟩
        · exact ⟨Or.inl hl0,
            Or.inl hbeta0,
            Or.inl hdelta0,
            quarticSigma_zeta_band_disjunction810' (A := A) (B := B) (C := C) (D := D)
              (E := E) (F := F) (G := G) (zeta := zeta) hA
              (fun htop => absurd (htop) hTzeta),
            quarticSigma_theta_band_disjunction (A := A) (B := B) (C := C) (D := D)
              (E := E) (F := F) (G := G) (theta := theta) hA
              (fun htop => absurd (quarticKappaLoadTopTheta810_imp_Zeta810 (htop)) hTzeta)⟩
      · exact ⟨Or.inl hl0,
          Or.inl hbeta0,
          quarticSigma_delta_band_disjunction (A := A) (B := B) (C := C) (D := D)
            (E := E) (F := F) (G := G) (delta := delta) hA
            (fun htop => absurd (htop) hTdelta),
          quarticSigma_zeta_band_disjunction810' (A := A) (B := B) (C := C) (D := D)
            (E := E) (F := F) (G := G) (zeta := zeta) hA
            (fun htop => absurd (quarticKappaLoadTopZeta810_imp_Delta810 (htop)) hTdelta),
          quarticSigma_theta_band_disjunction (A := A) (B := B) (C := C) (D := D)
            (E := E) (F := F) (G := G) (theta := theta) hA
            (fun htop => absurd (quarticKappaLoadTopZeta810_imp_Delta810 (quarticKappaLoadTopTheta810_imp_Zeta810 (htop))) hTdelta)⟩
    · exact ⟨Or.inl hl0,
        quarticSigma_beta_band_disjunction (A := A) (B := B) (C := C) (D := D)
          (E := E) (F := F) (G := G) (beta := beta) hA
          (fun htop => absurd (htop) hTbeta),
        quarticSigma_delta_band_disjunction (A := A) (B := B) (C := C) (D := D)
          (E := E) (F := F) (G := G) (delta := delta) hA
          (fun htop => absurd (quarticKappaLoadTopDelta810_imp_Beta810 (htop)) hTbeta),
        quarticSigma_zeta_band_disjunction810' (A := A) (B := B) (C := C) (D := D)
          (E := E) (F := F) (G := G) (zeta := zeta) hA
          (fun htop => absurd (quarticKappaLoadTopDelta810_imp_Beta810 (quarticKappaLoadTopZeta810_imp_Delta810 (htop))) hTbeta),
        quarticSigma_theta_band_disjunction (A := A) (B := B) (C := C) (D := D)
          (E := E) (F := F) (G := G) (theta := theta) hA
          (fun htop => absurd (quarticKappaLoadTopDelta810_imp_Beta810 (quarticKappaLoadTopZeta810_imp_Delta810 (quarticKappaLoadTopTheta810_imp_Zeta810 (htop)))) hTbeta)⟩
  · exact ⟨quarticSigma_l_band_disjunction (A := A) (B := B) (C := C) (D := D)
        (E := E) (F := F) (G := G) (l := l) hA
        (fun htop => absurd (htop) hTl),
      quarticSigma_beta_band_disjunction (A := A) (B := B) (C := C) (D := D)
        (E := E) (F := F) (G := G) (beta := beta) hA
        (fun htop => absurd (quarticKappaLoadTopBeta810_imp_L810 (htop)) hTl),
      quarticSigma_delta_band_disjunction (A := A) (B := B) (C := C) (D := D)
        (E := E) (F := F) (G := G) (delta := delta) hA
        (fun htop => absurd (quarticKappaLoadTopBeta810_imp_L810 (quarticKappaLoadTopDelta810_imp_Beta810 (htop))) hTl),
      quarticSigma_zeta_band_disjunction810' (A := A) (B := B) (C := C) (D := D)
        (E := E) (F := F) (G := G) (zeta := zeta) hA
        (fun htop => absurd (quarticKappaLoadTopBeta810_imp_L810 (quarticKappaLoadTopDelta810_imp_Beta810 (quarticKappaLoadTopZeta810_imp_Delta810 (htop)))) hTl),
      quarticSigma_theta_band_disjunction (A := A) (B := B) (C := C) (D := D)
        (E := E) (F := F) (G := G) (theta := theta) hA
        (fun htop => absurd (quarticKappaLoadTopBeta810_imp_L810 (quarticKappaLoadTopDelta810_imp_Beta810 (quarticKappaLoadTopZeta810_imp_Delta810 (quarticKappaLoadTopTheta810_imp_Zeta810 (htop))))) hTl)⟩


end QuarticChamberBands810

end Max11DegreeRoutes
