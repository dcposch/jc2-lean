import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderPart03Scratch

/-! # Expanded one-lower remainders on the `q=0` support wall

Both named remainders are normalized back to the literal source rows and
expanded before applying degree bounds.  The equation `9*N=7*S` leaves
exactly the minimal chart `(N,S)=(7,9)` or `14≤N`.  Only in the latter are
the remaining `B*c'`, `c*B'`, and `B*A'*c` terms deleted by degree.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

private structure Leaf68Bound (p : k[X]) (u : ℕ) : Prop where
  le : p.natDegree ≤ u

private theorem leaf68_bd_of_le {p : k[X]} {u : ℕ} (h : p.natDegree ≤ u) :
    Leaf68Bound p u := ⟨h⟩

private theorem leaf68_bd_C (a : k) : Leaf68Bound (C a) 0 :=
  ⟨(natDegree_C a).le⟩

private theorem leaf68_bd_smul (r : k) {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (r • p) u :=
  ⟨(natDegree_smul_le r p).trans hp.le⟩

private theorem leaf68_bd_neg {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (-p) u :=
  ⟨(natDegree_neg p).le.trans hp.le⟩

private theorem leaf68_bd_add {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p + q) (max u v) :=
  ⟨(natDegree_add_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_sub {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p - q) (max u v) :=
  ⟨(natDegree_sub_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_mul {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p * q) (u + v) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add hp.le hq.le)⟩

private theorem leaf68_bd_pow {p : k[X]} {u : ℕ} (m : ℕ)
    (hp : Leaf68Bound p u) : Leaf68Bound (p ^ m) (m * u) :=
  ⟨natDegree_pow_le.trans (Nat.mul_le_mul (le_refl m) hp.le)⟩

private theorem leaf68_bd_deriv {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (derivative p) (u - 1) :=
  ⟨(natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp.le 1)⟩

private theorem leaf68_lt_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u < b) : p.natDegree < b :=
  lt_of_le_of_lt hp.le h

private theorem leaf68_le_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u ≤ b) : p.natDegree ≤ b :=
  hp.le.trans h


set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact arithmetic and coefficient split.  No term is deleted in the
minimal chart. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_clean_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let i0:=4*N-2
    let i2:=2*N-2
    let W0:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
      gamma epsilon A B c d e
    let W2:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
      gamma epsilon B c d
    (N=7 ∧ S=9 ∧
      W0.coeff i0=-(21:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff Cc ∧
      W2.coeff i2=(117:k)*gamma*B.coeff D*c.coeff Cc) ∨
    (14≤N ∧ W0.coeff i0=0 ∧ W2.coeff i2=0):=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let i0:=4*N-2
  let i2:=2*N-2
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
    gamma epsilon A B c d e
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
    gamma epsilon B c d
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases hs.1 with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  have hEq:9*N=7*S:=by dsimp only at hTD;omega
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have harith:(N=7 ∧ S=9) ∨ 14≤N:=by omega
  rcases harith with hsmall|hlarge
  · left
    rcases hsmall with ⟨hN7,hS9⟩
    subst N;subst S
    norm_num [D,Cc,V,E] at hB' hc' hd' he'
    have hBAc:=coeff_mul_mul_derivative_at_bounds68 B c A 3 10 14
      (by norm_num) hB' hc' hA
    norm_num at hBAc
    have hBAc':(B*derivative A*c).coeff 26=
        B.coeff 3*A.coeff 14*c.coeff 10*(14:k):=by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hBAc
    have hBc:=coeff_mul_derivative_at_bounds68 B c 3 10
      (by norm_num) hB' hc'
    norm_num at hBc
    have hcB:=coeff_mul_derivative_at_bounds68 c B 10 3
      (by norm_num) hc' hB'
    norm_num at hcB
    have hlow0:(
        (3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
          (9/2*gamma:k)•(B*derivative e)+
          (9/2*gamma:k)•(d*derivative c)+
          (9/4*epsilon:k)•(d*derivative A)).natDegree<26:=by
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hB'
        | with_reducible exact leaf68_bd_of_le hc'
        | with_reducible exact leaf68_bd_of_le hd'
        | with_reducible exact leaf68_bd_of_le he'
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    have hlow2:((27/2*epsilon:k)•derivative d).natDegree<12:=by
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hB'
        | with_reducible exact leaf68_bd_of_le hc'
        | with_reducible exact leaf68_bd_of_le hd'
        | with_reducible exact leaf68_bd_of_le he'
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    refine ⟨rfl,rfl,?_,?_⟩
    · have hdecomp:
          FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
              gamma epsilon A B c d e=
            -(3/2*gamma:k)•(B*derivative A*c)+
              ((3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
                (9/2*gamma:k)•(B*derivative e)+
                (9/2*gamma:k)•(d*derivative c)+
                (9/4*epsilon:k)•(d*derivative A)):=by
          dsimp only [
            FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
          module
      simp only [hdecomp,coeff_add,coeff_smul,hBAc',
        coeff_eq_zero_of_natDegree_lt hlow0,smul_eq_mul,add_zero]
      norm_num
      ring
    · have hdecomp:
          FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
              gamma epsilon B c d=
            ((9*gamma:k)•(B*derivative c)+
              (9*gamma:k)•(c*derivative B))-
              (27/2*epsilon:k)•derivative d:=by rfl
      simp only [hdecomp,coeff_sub,coeff_add,coeff_smul,hBc,hcB,
        coeff_eq_zero_of_natDegree_lt hlow2,smul_eq_mul,sub_zero]
      norm_num
      ring
  · right
    refine ⟨hlarge,?_,?_⟩
    · apply coeff_eq_zero_of_natDegree_lt
      dsimp only [W0,i0,
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hB'
        | with_reducible exact leaf68_bd_of_le hc'
        | with_reducible exact leaf68_bd_of_le hd'
        | with_reducible exact leaf68_bd_of_le he'
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    · apply coeff_eq_zero_of_natDegree_lt
      dsimp only [W2,i2,
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68]
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hB'
        | with_reducible exact leaf68_bd_of_le hc'
        | with_reducible exact leaf68_bd_of_le hd'
        | with_reducible exact leaf68_bd_of_le he'
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68
end Max11DegreeRoutes
