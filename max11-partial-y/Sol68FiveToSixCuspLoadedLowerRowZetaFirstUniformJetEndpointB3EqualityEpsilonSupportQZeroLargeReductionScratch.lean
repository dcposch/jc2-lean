import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderScratch

/-! # The reduced `q=0` one-lower companion

On the `14 ≤ N` side of the exact arithmetic split, both literal source
remainders vanish.  In the minimal `(N,S)=(7,9)` chart they are nonzero but
cancel exactly in the companion resultant.  The retained support contraction
then eliminates the top `J` coefficient uniformly.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLargeReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The companion has neither an unnamed remainder nor a top `J` coefficient,
uniformly across the minimal and large arithmetic charts. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_reduction68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let V:=5*N-3*S
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    (3:k)*((p-1:ℕ):k)*A.coeff (p-1)*
        ((3:k)*((2*p-1:ℕ):k)*A.coeff p*Fce.coeff 0+
          (2:k)*((p-1:ℕ):k)*B.coeff D^2*d.coeff V)+
      (6:k)*((p-1:ℕ):k)*L0.coeff (2*p-2)+
        ((p:ℕ):k)*A.coeff p*L2.coeff (p-2)=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hpacket:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_source_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  rcases hpacket with ⟨hcomp,hsplit⟩
  dsimp only at hsplit
  have hWcancel:
      (6:k)*(((2*N-1:ℕ):k))*W0.coeff (4*N-2)+
        (((2*N:ℕ):k))*A.coeff (2*N)*W2.coeff (2*N-2)=0:=by
    rcases hsplit with hsmall|hbig
    · rcases hsmall with ⟨hN,hS,h0,h2⟩
      subst N
      subst S
      dsimp only [W0,W2]
      rw [h0,h2]
      norm_num
      ring
    · dsimp only [W0,W2]
      rw [hbig.2.1,hbig.2.2]
      ring
  have hcontract:=
    fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68]
    at hcontract
  have htop:=hcontract.2.1
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hpOld:11*N-7*S=p:=by dsimp only [p];omega
  rw [hq,hpOld] at htop
  simp only [Nat.cast_zero,sub_zero] at htop
  have hN:0<N:=by omega
  have hNk:((N:ℕ):k)≠0:=by exact_mod_cast (show N≠0 by omega)
  have hpcast:((p:ℕ):k)=(2:k)*((N:ℕ):k):=by
    dsimp only [p]
    push_cast
    rfl
  have htopReduced:
      A.coeff p*Fce.coeff 0+
        (2:k)*(J.coeff p+B.coeff D^2*d.coeff V)=0:=by
    have hprod:((N:ℕ):k)*
        (A.coeff p*Fce.coeff 0+
          (2:k)*(J.coeff p+B.coeff D^2*d.coeff V))=0:=by
      dsimp only [p,D,V,Fce,J] at htop ⊢
      rw [hpcast] at htop
      linear_combination htop
    exact (mul_eq_zero.mp hprod).resolve_left hNk
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionScalar68]
    at hcomp
  have hcompClean:
      (3:k)*(((2*N-1:ℕ):k))*A.coeff (2*N-1)*
          (A.coeff (2*N)*(((5*(2*N)-2:ℕ):k))*Fce.coeff 0-
            (2:k)*(((2*N-1:ℕ):k))*J.coeff (2*N))+
        (6:k)*(((2*N-1:ℕ):k))*L0.coeff (4*N-2)+
          (((2*N:ℕ):k))*A.coeff (2*N)*L2.coeff (2*N-2)=0:=by
    dsimp only [p,D,V,Fce,J,L0,L2,W0,W2]
      at hcomp hWcancel ⊢
    linear_combination hcomp-hWcancel
  dsimp only [p,D,V,Fce,J,L0,L2,W0,W2]
    at htopReduced ⊢
  have hcast:
      (((5*(2*N)-2:ℕ):k))+(((2*N-1:ℕ):k))=
        (3:k)*(((4*N-1:ℕ):k)):=by
    exact_mod_cast (show (5*(2*N)-2)+(2*N-1)=3*(4*N-1) by omega)
  have hinner:
      A.coeff (2*N)*(((5*(2*N)-2:ℕ):k))*Fce.coeff 0-
          (2:k)*(((2*N-1:ℕ):k))*J.coeff (2*N)=
        (3:k)*(((4*N-1:ℕ):k))*A.coeff (2*N)*Fce.coeff 0+
          (2:k)*(((2*N-1:ℕ):k))*
            B.coeff (3*N-2*S)^2*d.coeff (5*N-3*S):=by
    dsimp only [Fce,J]
    linear_combination
      -(((2*N-1:ℕ):k))*htopReduced+
        A.coeff (2*N)*
          (B*e+c*d-(1/9:k)•B^3+(3/2*gamma:k)•d+
            (3/4*epsilon:k)•B).coeff 0*hcast
  rw [hinner] at hcompClean
  simpa only [show 2*(2*N)-1=4*N-1 by omega,
    show 2*(2*N)-2=4*N-2 by omega] using hcompClean

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_reduction68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLargeReduction68

end Max11DegreeRoutes
