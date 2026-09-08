import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdAlgebraScratch

/-! # Exact third-jet load coefficients on `q=0` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact third-jet expansion of the row-two load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_third68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let V:=5*N-3*S
    let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    L2.coeff (p-4)=(6:k)*((p-3:ℕ):k)*
      FiveToSixQZeroBBDJetThree68
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3)):=by
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  change L2.coeff (p-4)=_
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrest⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have hD:3≤D:=by dsimp only [D];omega
  have hV:3≤V:=by dsimp only [V];omega
  have hpEq:p=2*D+V:=by dsimp only [p,D,V];omega
  have hprod0:=coeff_mul_mul_three_below_bounds68 B B d D D V
    hD hD hV hB' hB' hd'
  have hprod:(B^2*d).coeff (p-3)=
      FiveToSixQZeroBBDJetThree68
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3)):=by
    rw [hpEq,show 2*D+V-3=D+D+V-3 by omega,pow_two]
    rw [hprod0]
    dsimp only [FiveToSixQZeroBBDJetThree68]
    ring
  have hsq:derivative (B^2)=(2:k)•(B*derivative B):=by
    rw [show B^2=B*B by ring,derivative_mul]
    simp only [two_smul]
    ring
  have hder:derivative (B^2*d)=
      (2:k)•(B*derivative B*d)+B^2*derivative d:=by
    rw [derivative_mul,hsq]
    simp only [two_smul]
    ring
  have hL2poly:L2=(6:k)•derivative (B^2*d):=by
    dsimp only [L2,FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68]
    rw [hder]
    module
  have hidx:p-4+1=p-3:=by dsimp only [p];omega
  have hcast:(((p-4:ℕ):k)+1)=((p-3:ℕ):k):=by exact_mod_cast hidx
  rw [hL2poly,coeff_smul,coeff_derivative,hidx,hcast,hprod]
  ring

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdSource68
end Max11DegreeRoutes
