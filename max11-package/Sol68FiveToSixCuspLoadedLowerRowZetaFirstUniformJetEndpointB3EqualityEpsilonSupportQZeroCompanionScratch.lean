import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroNextScratch

/-! # The row-zero companion on the exact `q=0` support wall

At `9*N=7*S`, the positive row-zero coefficient `4*N-2` and the verified
row-two coefficient `2*N-2` contain the same new `J_(2*N-1)` jet.  This
file extracts row zero from the same source packet and eliminates that jet
without division.  The two literal one-lower remainders are retained.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
    (alpha gamma epsilon zeta eta:k) (A B c d e:k[X]):k[X]:=
  secondaryResidualRowZeroPolynomial68 A B c d e+
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1/3:k)•(A*B)+d) e

def FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    (alpha gamma epsilon zeta eta:k) (A B c d e:k[X]):k[X]:=
  FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
      alpha gamma epsilon zeta eta A B c d e-
    (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
      (3/2*gamma:k)•(A*derivative A*d)+
      (3/4*epsilon:k)•(A*B*derivative A)+
      FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e)

def FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionScalar68
    (alpha gamma epsilon zeta eta:k) (A B c d e:k[X])
    (N S:ℕ):Prop:=
  let p:=2*N
  let i0:=4*N-2
  let i2:=p-2
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  (3:k)*((p-1:ℕ):k)*A.coeff (p-1)*
      (A.coeff p*((5*p-2:ℕ):k)*Fce.coeff 0-
        (2:k)*((p-1:ℕ):k)*J.coeff p)+
    (6:k)*((p-1:ℕ):k)*(L0.coeff i0+W0.coeff i0)+
      ((p:ℕ):k)*A.coeff p*(L2.coeff i2+W2.coeff i2)=0

/-- Source-exact division-free elimination of the first lower `J` jet. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionScalar68
      alpha gamma epsilon zeta eta A B c d e N S:=by
  let p:=2*N
  let i0:=4*N-2
  let i2:=p-2
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt with ⟨harith,hexact,hrow2,hp1cast⟩
  rcases hexact with ⟨i4,i3,hFce,hRce,hRceDeg⟩
  have hpOld0:11*N-7*S=p:=by dsimp only [p];omega
  rw [hpOld0] at hrow2
  change (((p-1:ℕ):k)*
      ((3:k)*A.coeff (p-1)*Fce.coeff 0+
        (6:k)*J.coeff (p-1))+L2.coeff i2+W2.coeff i2=0) at hrow2
  have hFce':Fce=(3/8:k)•C i4:=by exact hFce
  have hloaded:=hs.1
  rcases hloaded with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  rcases hstop with ⟨hcur,ht,hstate,hclass,hraw0,hraw2⟩
  let D:=3*N-2*S
  let w:=2*D
  let T:=S-w
  let t:=min D T
  have htT:t=T:=by dsimp only [t];exact Nat.min_eq_right hTD
  have hstate':=hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
  have hpOld:11*N-7*S=p:=by dsimp only [p];omega
  have hjidx:5*N-2*S-(t-1)-1=p:=by
    dsimp only [D,w,T] at htT
    omega
  rw [hjidx] at hstate'
  have hJ:J.natDegree≤p:=by exact hstate'.2
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
      ⟨⟨⟨hcur,ht,hstate,hclass,hraw0,hraw2⟩,hTD⟩,hrows⟩ with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hp0,hrest⟩
  rcases hp0 with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hA':A.natDegree≤p:=by dsimp only [p];exact hA
  have hdA0:=natDegree_derivative_le A
  have hdA:(derivative A).natDegree≤p-1:=by dsimp only [p];omega
  have hpgt:1<p:=by dsimp only [p];omega
  have hi0:p+(p-1)-1=i0:=by dsimp only [p,i0];omega
  have hAAraw:=coeff_mul_at_reflect_one_cusp68 A (derivative A)
    p (p-1) hA' hdA (by omega)
  rw [hi0] at hAAraw
  have hA0:(A.reflect p).coeff 0=A.coeff p:=by
    simp only [coeff_reflect,revAt_zero]
  have hA1:(A.reflect p).coeff 1=A.coeff (p-1):=by
    rw [coeff_reflect,revAt_le (by omega)]
  have hdA0':((derivative A).reflect (p-1)).coeff 0=
      A.coeff p*((p:ℕ):k):=by
    simp only [coeff_reflect,revAt_zero,coeff_derivative]
    have hpcast:(((p-1:ℕ):k)+1)=((p:ℕ):k):=by exact_mod_cast (by omega:p-1+1=p)
    rw [show p-1+1=p by omega,hpcast]
  have hdA1:((derivative A).reflect (p-1)).coeff 1=
      A.coeff (p-1)*((p-1:ℕ):k):=by
    rw [coeff_reflect,revAt_le (by omega),coeff_derivative]
    have hi:p-1-1+1=p-1:=by omega
    rw [hi]
    have hic:(((p-1-1:ℕ):k)+1)=((p-1:ℕ):k):=by exact_mod_cast hi
    rw [hic]
  rw [hA0,hA1,hdA0',hdA1] at hAAraw
  have hAA:(A*derivative A).coeff i0=
      ((2*p-1:ℕ):k)*A.coeff p*A.coeff (p-1):=by
    have hcast:((p:ℕ):k)+((p-1:ℕ):k)=((2*p-1:ℕ):k):=by
      exact_mod_cast (by omega:p+(p-1)=2*p-1)
    rw [←hcast]
    linear_combination hAAraw
  have hAJraw:=coeff_mul_at_reflect_one_cusp68 (derivative A) J
    (p-1) p hdA hJ (by omega)
  rw [show (p-1)+p-1=i0 by omega] at hAJraw
  have hJ0:(J.reflect p).coeff 0=J.coeff p:=by
    simp only [coeff_reflect,revAt_zero]
  have hJ1:(J.reflect p).coeff 1=J.coeff (p-1):=by
    rw [coeff_reflect,revAt_le (by omega)]
  rw [hdA0',hdA1,hJ0,hJ1] at hAJraw
  have hAJ:(derivative A*J).coeff i0=
      ((p:ℕ):k)*A.coeff p*J.coeff (p-1)+
        ((p-1:ℕ):k)*A.coeff (p-1)*J.coeff p:=by
    linear_combination hAJraw
  rcases had with ⟨j4,j3,hj4,hj3,hrow0,hrow1,hrowTwo,hpos,hiff⟩
  have hi0pos : 0 < (i0 : ℕ) := by
    dsimp only [i0,p]
    omega
  have hfull:=hpos i0 hi0pos
  have hfactor:=fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hdecomp:
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
          alpha gamma epsilon zeta eta A B c d e=
        (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
          (3/2*gamma:k)•(A*derivative A*d)+
          (3/4*epsilon:k)•(A*B*derivative A)+L0)+W0:=by
    dsimp only [W0,L0,
      FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68]
    module
  change (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
    alpha gamma epsilon zeta eta A B c d e).coeff i0=0 at hfull
  rw [hdecomp,hfactor.1] at hfull
  change (A*derivative A*Fce-derivative A*J+L0+W0).coeff i0=0 at hfull
  have hFconst:Fce=C (Fce.coeff 0):=by
    apply eq_C_of_natDegree_le_zero
    rw [hFce']
    compute_degree
  have hAAF:(A*derivative A*Fce).coeff i0=
      Fce.coeff 0*((2*p-1:ℕ):k)*A.coeff p*A.coeff (p-1):=by
    have heq:A*derivative A*Fce=Fce.coeff 0•(A*derivative A):=by
      calc
        A*derivative A*Fce=(A*derivative A)*C (Fce.coeff 0):=by
          conv_lhs => rw [hFconst]
        _=Fce.coeff 0•(A*derivative A):=by
          simp only [smul_eq_C_mul]
          ring
    rw [heq,coeff_smul,hAA]
    ring
  simp only [coeff_add,coeff_sub,hAAF,hAJ] at hfull
  have hrow0main:
      Fce.coeff 0*((2*p-1:ℕ):k)*A.coeff p*A.coeff (p-1)-
        (((p:ℕ):k)*A.coeff p*J.coeff (p-1)+
          ((p-1:ℕ):k)*A.coeff (p-1)*J.coeff p)+
        L0.coeff i0+W0.coeff i0=0:=by
    linear_combination hfull
  have hresult:
      (3:k)*((p-1:ℕ):k)*A.coeff (p-1)*
          (A.coeff p*((5*p-2:ℕ):k)*Fce.coeff 0-
            (2:k)*((p-1:ℕ):k)*J.coeff p)+
        (6:k)*((p-1:ℕ):k)*(L0.coeff i0+W0.coeff i0)+
          ((p:ℕ):k)*A.coeff p*(L2.coeff i2+W2.coeff i2)=0:=by
    have hc5:
        (6:k)*((2*p-1:ℕ):k)+(3:k)*((p:ℕ):k)=
          (3:k)*((5*p-2:ℕ):k):=by
      exact_mod_cast (show 6*(2*p-1)+3*p=3*(5*p-2) by omega)
    linear_combination
      (6:k)*((p-1:ℕ):k)*hrow0main+
        ((p:ℕ):k)*A.coeff p*hrow2-
        ((p-1:ℕ):k)*A.coeff p*A.coeff (p-1)*Fce.coeff 0*hc5
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionScalar68,
    p,i0,i2,Fce,J,L0,W0,L2,W2]
  exact hresult

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanion68

end Max11DegreeRoutes
