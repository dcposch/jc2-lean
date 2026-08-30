import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNextScratch

/-! # Second-jet load coefficients on `q=0` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Two coefficients below a product of four separate degree bounds. -/
theorem coeff_mul_mul_mul_two_below_bounds68 (p q r s:k[X])
    (u v w z:ℕ) (hu:2≤u) (hv:2≤v) (hw:2≤w) (hz:2≤z)
    (hp:p.natDegree≤u) (hq:q.natDegree≤v) (hr:r.natDegree≤w)
    (hs:s.natDegree≤z):
    (p*q*r*s).coeff (u+v+w+z-2)=
      p.coeff (u-2)*q.coeff v*r.coeff w*s.coeff z+
      p.coeff (u-1)*q.coeff (v-1)*r.coeff w*s.coeff z+
      p.coeff u*q.coeff (v-2)*r.coeff w*s.coeff z+
      p.coeff (u-1)*q.coeff v*r.coeff (w-1)*s.coeff z+
      p.coeff u*q.coeff (v-1)*r.coeff (w-1)*s.coeff z+
      p.coeff u*q.coeff v*r.coeff (w-2)*s.coeff z+
      p.coeff (u-1)*q.coeff v*r.coeff w*s.coeff (z-1)+
      p.coeff u*q.coeff (v-1)*r.coeff w*s.coeff (z-1)+
      p.coeff u*q.coeff v*r.coeff (w-1)*s.coeff (z-1)+
      p.coeff u*q.coeff v*r.coeff w*s.coeff (z-2):=by
  have hpqr:(p*q*r).natDegree≤u+v+w:=by compute_degree;omega
  rw [coeff_mul_two_below_bounds68 (p*q*r) s (u+v+w) z
      (by omega) hz hpqr hs,
    coeff_mul_mul_two_below_bounds68 p q r u v w hu hv hw hp hq hr,
    coeff_mul_mul_one_below_bounds68 p q r u v w
      (by omega) (by omega) (by omega) hp hq hr,
    coeff_mul_mul_at_bounds68 p q r u v w hp hq hr]
  ring

/-- Exact second-jet expansion of the row-two load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_next68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let V:=5*N-3*S
    let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    L2.coeff (p-3)=
      (6:k)*((p-2:ℕ):k)*
        (B.coeff D^2*d.coeff (V-2)+
          (2:k)*B.coeff D*B.coeff (D-1)*d.coeff (V-1)+
          (2:k)*B.coeff D*B.coeff (D-2)*d.coeff V+
          B.coeff (D-1)^2*d.coeff V):=by
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  change L2.coeff (p-3)=_
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
  have hD:2≤D:=by dsimp only [D];omega
  have hV:2≤V:=by dsimp only [V];omega
  have hpEq:p=2*D+V:=by dsimp only [p,D,V];omega
  have hprod0:=coeff_mul_mul_two_below_bounds68 B B d D D V
    hD hD hV hB' hB' hd'
  have hprod:(B^2*d).coeff (p-2)=
      B.coeff D^2*d.coeff (V-2)+
        (2:k)*B.coeff D*B.coeff (D-1)*d.coeff (V-1)+
        (2:k)*B.coeff D*B.coeff (D-2)*d.coeff V+
        B.coeff (D-1)^2*d.coeff V:=by
    rw [hpEq]
    rw [show 2*D+V-2=D+D+V-2 by omega,pow_two]
    rw [hprod0]
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
  have hidx:p-3+1=p-2:=by dsimp only [p];omega
  have hcast:(((p-3:ℕ):k)+1)=((p-2:ℕ):k):=by exact_mod_cast hidx
  rw [hL2poly,coeff_smul,coeff_derivative,hidx,hcast,hprod]
  dsimp only [p]
  ring

/-- Exact second-jet expansion of the row-zero load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_next68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    L0.coeff (2*p-3)=
      (((V:ℕ):k)+((D:ℕ):k))*
          A.coeff (p-2)*B.coeff D^2*d.coeff V+
      ((2:k)*((V:ℕ):k)+(2:k)*((D:ℕ):k)-1)*
          A.coeff (p-1)*B.coeff D*B.coeff (D-1)*d.coeff V+
      (((V:ℕ):k)+((D:ℕ):k)-1)*
          A.coeff (p-1)*B.coeff D^2*d.coeff (V-1)+
      (2:k)*(((V:ℕ):k)+((D:ℕ):k)-1)*
          A.coeff p*B.coeff D*B.coeff (D-2)*d.coeff V+
      (((V:ℕ):k)+((D:ℕ):k)-1)*
          A.coeff p*B.coeff (D-1)^2*d.coeff V+
      ((2:k)*((V:ℕ):k)+(2:k)*((D:ℕ):k)-3)*
          A.coeff p*B.coeff D*B.coeff (D-1)*d.coeff (V-1)+
      (((V:ℕ):k)+((D:ℕ):k)-2)*
          A.coeff p*B.coeff D^2*d.coeff (V-2)-
      (3:k)*(((E:ℕ):k)*B.coeff (D-2)*c.coeff Cc*e.coeff E+
        ((E:ℕ):k)*B.coeff (D-1)*c.coeff (Cc-1)*e.coeff E+
        (((E:ℕ):k)-1)*B.coeff (D-1)*c.coeff Cc*e.coeff (E-1)+
        ((E:ℕ):k)*B.coeff D*c.coeff (Cc-2)*e.coeff E+
        (((E:ℕ):k)-1)*B.coeff D*c.coeff (Cc-1)*e.coeff (E-1)+
        (((E:ℕ):k)-2)*B.coeff D*c.coeff Cc*e.coeff (E-2))+
      (3:k)*(((2:k)*((Cc:ℕ):k)-2)*
          c.coeff Cc*c.coeff (Cc-2)*d.coeff V+
        (((Cc:ℕ):k)-1)*c.coeff (Cc-1)^2*d.coeff V+
        ((2:k)*((Cc:ℕ):k)-1)*
          c.coeff Cc*c.coeff (Cc-1)*d.coeff (V-1)+
        ((Cc:ℕ):k)*c.coeff Cc^2*d.coeff (V-2)):=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  change L0.coeff (2*p-3)=_
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
  have hA':A.natDegree≤p:=by simpa [p] using hA
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have hp:2≤p:=by dsimp only [p];omega
  have hD:2≤D:=by dsimp only [D];omega
  have hC:2≤Cc:=by dsimp only [Cc];omega
  have hV:3≤V:=by dsimp only [V];omega
  have hE:3≤E:=by dsimp only [E];omega
  have hdd:(derivative d).natDegree≤V-1:=
    (natDegree_derivative_le d).trans (Nat.sub_le_sub_right hd' 1)
  have hde:(derivative e).natDegree≤E-1:=
    (natDegree_derivative_le e).trans (Nat.sub_le_sub_right he' 1)
  have hdB:(derivative B).natDegree≤D-1:=
    (natDegree_derivative_le B).trans (Nat.sub_le_sub_right hB' 1)
  have hdc:(derivative c).natDegree≤Cc-1:=
    (natDegree_derivative_le c).trans (Nat.sub_le_sub_right hc' 1)
  have hdt:=coeff_derivative_at_bound68 d V (by omega)
  have hdn:=coeff_derivative_at_bound68 d (V-1) (by omega)
  have hdn2:=coeff_derivative_at_bound68 d (V-2) (by omega)
  have het:=coeff_derivative_at_bound68 e E (by omega)
  have hen:=coeff_derivative_at_bound68 e (E-1) (by omega)
  have hen2:=coeff_derivative_at_bound68 e (E-2) (by omega)
  have hBt:=coeff_derivative_at_bound68 B D (by omega)
  have hBn:=coeff_derivative_at_bound68 B (D-1) (by omega)
  have hBn2:=coeff_derivative_at_bound68 B (D-2) (by omega)
  have hct:=coeff_derivative_at_bound68 c Cc (by omega)
  have hcn:=coeff_derivative_at_bound68 c (Cc-1) (by omega)
  have hcn2:=coeff_derivative_at_bound68 c (Cc-2) (by omega)
  have hcastV1:(((V-1:ℕ):k))=((V:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hcastV2:(((V-2:ℕ):k))=((V:ℕ):k)-2:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hcastD1:(((D-1:ℕ):k))=((D:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hcastD2:(((D-2:ℕ):k))=((D:ℕ):k)-2:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hcastE1:(((E-1:ℕ):k))=((E:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hcastE2:(((E-2:ℕ):k))=((E:ℕ):k)-2:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hcastC1:(((Cc-1:ℕ):k))=((Cc:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hcastC2:(((Cc-2:ℕ):k))=((Cc:ℕ):k)-2:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have h1raw:=coeff_mul_mul_mul_two_below_bounds68 A B B (derivative d)
    p D D (V-1) hp hD hD (by omega) hA' hB' hB' hdd
  have h1:(A*B^2*derivative d).coeff (2*p-3)=
      A.coeff (p-2)*B.coeff D^2*d.coeff V*((V:ℕ):k)+
      (2:k)*A.coeff (p-1)*B.coeff D*B.coeff (D-1)*d.coeff V*((V:ℕ):k)+
      A.coeff (p-1)*B.coeff D^2*d.coeff (V-1)*(((V:ℕ):k)-1)+
      (2:k)*A.coeff p*B.coeff D*B.coeff (D-2)*d.coeff V*((V:ℕ):k)+
      A.coeff p*B.coeff (D-1)^2*d.coeff V*((V:ℕ):k)+
      (2:k)*A.coeff p*B.coeff D*B.coeff (D-1)*d.coeff (V-1)*(((V:ℕ):k)-1)+
      A.coeff p*B.coeff D^2*d.coeff (V-2)*(((V:ℕ):k)-2):=by
    rw [show p+D+D+(V-1)-2=2*p-3 by omega] at h1raw
    rw [show V-1-2=V-2-1 by omega] at h1raw
    rw [hdt,hdn,hdn2,hcastV1,hcastV2] at h1raw
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm,Nat.cast_one] at h1raw ⊢
    linear_combination h1raw
  have h2raw:=coeff_mul_mul_mul_two_below_bounds68 A B d (derivative B)
    p D V (D-1) hp hD (by omega) (by omega) hA' hB' hd' hdB
  have h2:(A*B*derivative B*d).coeff (2*p-3)=
      A.coeff (p-2)*B.coeff D^2*d.coeff V*((D:ℕ):k)+
      A.coeff (p-1)*B.coeff D*B.coeff (D-1)*d.coeff V*
        ((2:k)*((D:ℕ):k)-1)+
      A.coeff (p-1)*B.coeff D^2*d.coeff (V-1)*((D:ℕ):k)+
      (2:k)*A.coeff p*B.coeff D*B.coeff (D-2)*d.coeff V*
        (((D:ℕ):k)-1)+
      A.coeff p*B.coeff (D-1)^2*d.coeff V*(((D:ℕ):k)-1)+
      A.coeff p*B.coeff D*B.coeff (D-1)*d.coeff (V-1)*
        ((2:k)*((D:ℕ):k)-1)+
      A.coeff p*B.coeff D^2*d.coeff (V-2)*((D:ℕ):k):=by
    rw [show p+D+V+(D-1)-2=2*p-3 by omega] at h2raw
    rw [show D-1-2=D-2-1 by omega] at h2raw
    rw [hBt,hBn,hBn2,hcastD1,hcastD2] at h2raw
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm,Nat.cast_one] at h2raw ⊢
    linear_combination h2raw
  have h3raw:=coeff_mul_mul_two_below_bounds68 B c (derivative e)
    D Cc (E-1) hD hC (by omega) hB' hc' hde
  have h3:(B*c*derivative e).coeff (2*p-3)=
      B.coeff (D-2)*c.coeff Cc*e.coeff E*((E:ℕ):k)+
      B.coeff (D-1)*c.coeff (Cc-1)*e.coeff E*((E:ℕ):k)+
      B.coeff (D-1)*c.coeff Cc*e.coeff (E-1)*(((E:ℕ):k)-1)+
      B.coeff D*c.coeff (Cc-2)*e.coeff E*((E:ℕ):k)+
      B.coeff D*c.coeff (Cc-1)*e.coeff (E-1)*(((E:ℕ):k)-1)+
      B.coeff D*c.coeff Cc*e.coeff (E-2)*(((E:ℕ):k)-2):=by
    rw [show D+Cc+(E-1)-2=2*p-3 by omega] at h3raw
    rw [show E-1-2=E-2-1 by omega] at h3raw
    rw [het,hen,hen2,hcastE1,hcastE2] at h3raw
    simp only [mul_assoc,mul_comm,mul_left_comm,Nat.cast_one] at h3raw ⊢
    linear_combination h3raw
  have h4raw:=coeff_mul_mul_two_below_bounds68 c d (derivative c)
    Cc V (Cc-1) hC (by omega) (by omega) hc' hd' hdc
  have h4:(c*derivative c*d).coeff (2*p-3)=
      ((2:k)*((Cc:ℕ):k)-2)*c.coeff Cc*c.coeff (Cc-2)*d.coeff V+
      (((Cc:ℕ):k)-1)*c.coeff (Cc-1)^2*d.coeff V+
      ((2:k)*((Cc:ℕ):k)-1)*c.coeff Cc*c.coeff (Cc-1)*d.coeff (V-1)+
      ((Cc:ℕ):k)*c.coeff Cc^2*d.coeff (V-2):=by
    rw [show Cc+V+(Cc-1)-2=2*p-3 by omega] at h4raw
    rw [show Cc-1-2=Cc-2-1 by omega] at h4raw
    rw [hct,hcn,hcn2,hcastC1,hcastC2] at h4raw
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm,Nat.cast_one] at h4raw ⊢
    linear_combination h4raw
  dsimp only [L0,FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68]
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,h1,h2,h3,h4]
  ring

#print axioms coeff_mul_mul_mul_two_below_bounds68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_next68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_next68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadNext68

end Max11DegreeRoutes
