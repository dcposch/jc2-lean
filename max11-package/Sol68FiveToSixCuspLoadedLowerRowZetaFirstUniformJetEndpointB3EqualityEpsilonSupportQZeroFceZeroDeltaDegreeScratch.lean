import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroGlobalScratch

/-! # Degree descent from the global zero-`Fce` identity -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDeltaDegree68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixQZeroFceZeroDeltaRest68
    (gamma epsilon i3:k) (B c d:k[X]):k[X]:=
  (16:k)•(B^3*c)+(6*gamma:k)•B^3-(36:k)•(B*d^2)+
    (81*epsilon*gamma:k)•B+(216*gamma:k)•(c*d)+
    (162*gamma^2:k)•d+(27*i3:k)•B

/-- The alternate global row lowers the discriminant degree from the old
support bound to `3D+Cc-V` on the zero-`Fce` branch. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_degree68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0)
    (hf:(((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B).coeff 0=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree≤3*D+Cc-V:=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let M:=3*D+Cc
  change Delta.natDegree≤M-V
  have hglobal:=fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3,hFzero,hRce,hK⟩
  let Rest':=FiveToSixQZeroFceZeroDeltaRest68 gamma epsilon i3 B c d
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrestSource⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hB':B.natDegree≤D:=by dsimp only [D];omega
  have hc':c.natDegree≤Cc:=by dsimp only [Cc];omega
  have hd':d.natDegree≤V:=by dsimp only [V];omega
  have hv:V=5*N-G-S:=by dsimp only [V];omega
  have hdcoeff:d.coeff V≠0:=by rw [hv];exact hdtop
  have hdne:d≠0:=by
    intro hdz
    subst d
    exact hdcoeff rfl
  have hddeg:d.natDegree=V:=
    natDegree_eq_of_le_of_coeff_ne_zero hd' hdcoeff
  have hRest:Rest'.natDegree≤M:=by
    dsimp only [Rest',FiveToSixQZeroFceZeroDeltaRest68,M]
    compute_degree <;> omega
  have hdecomp:(24:k)•(d*Delta)+Rest'=0:=by
    dsimp only [FiveToSixQZeroFceZeroDeltaDescent68] at hK
    dsimp only [Delta,Rest',FiveToSixQZeroFceZeroDeltaRest68]
    linear_combination hK
  have hscaled:((24:k)•(d*Delta)).natDegree≤M:=by
    rw [eq_neg_of_add_eq_zero_left hdecomp]
    simpa only [natDegree_neg] using hRest
  rw [natDegree_smul _ (by norm_num:(24:k)≠0)] at hscaled
  by_cases hDelta:Delta=0
  · rw [hDelta,natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_mul hdne hDelta,hddeg] at hscaled
    omega

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_degree68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDeltaDegree68

end Max11DegreeRoutes
