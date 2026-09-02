import Sol68FiveToSixCuspTerminalDepthSevenScratch

/-! # Parametric finite stopping for the terminal cusp ladder

Put `R=7N-2G`, `L=3G-7N`, and
`D=floor(3N/2)+1`.  The exact identity `3R+2L=7N` prevents both gaps
from reaching `D`, while `D<2N` keeps every I4 coefficient used by the
iteration positive.  The source argument is organized around the single
compensated polynomial `F+(3/2)gamma d`; this absorbs every gamma wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalFiniteStopping68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The explicit stopping depth is still inside the positive I4 range, but
five copies of it exceed the exact weighted gap sum. -/
theorem fiveToSix_terminal_stopping_depth_arithmetic68
    (N G : ℕ) (hN : 2 < N)
    (hwindow : 5*N < 2*G ∧ 2*G ≤ 6*N) :
    let R:=7*N-2*G
    let L:=3*G-7*N
    let D:=3*N/2+1
    3*R+2*L=7*N ∧ 0<D ∧ D<2*N ∧ 5*D>7*N ∧
      0<2*N-D ∧ 0<6*N-D-1 ∧ ¬(D≤R ∧ D≤L) := by
  dsimp only
  omega

/-- Abstract finite stopping: any genuine step which advances both gaps
unless it returns a residual must return such a residual before `D`.
This theorem contains no analytic recurrence assumption. -/
theorem fiveToSix_terminal_finite_stopping_of_uniform_step68
    (N G : ℕ) (Residual : Prop) (hN : 2 < N)
    (hwindow : 5*N < 2*G ∧ 2*G ≤ 6*N)
    (hR7 : 7≤7*N-2*G) (hL7 : 7≤3*G-7*N)
    (hstep : ∀ q, 7≤q → q<3*N/2+1 →
      q≤7*N-2*G → q≤3*G-7*N →
      Residual ∨ (q+1≤7*N-2*G ∧ q+1≤3*G-7*N)) :
    Residual := by
  let D:=3*N/2+1
  have hD:=fiveToSix_terminal_stopping_depth_arithmetic68 N G hN hwindow
  have h7D:7≤D:=by omega
  have advance:∀ j, j≤D-7 →
      Residual ∨ (7+j≤7*N-2*G ∧ 7+j≤3*G-7*N):=by
    intro j hj
    induction j with
    | zero => exact Or.inr ⟨by simpa,by simpa⟩
    | succ j ih =>
        rcases ih (by omega) with hres | hb
        · exact Or.inl hres
        · simpa [Nat.succ_eq_add_one,add_assoc] using
            hstep (7+j) (by omega) (by dsimp only [D] at hj ⊢;omega) hb.1 hb.2
  rcases advance (D-7) (by omega) with hres | hb
  · exact hres
  · exfalso
    apply hD.2.2.2.2.2.2
    simpa only [show 7+(D-7)=D by omega] using hb

/-- The full polynomial I4 identity in compensated coordinates.  Unlike a
fixed coefficient statement, this retains the constant source RHS. -/
theorem fiveToSix_terminal_compensatedI4_polynomial68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G:ℕ)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G)) (hz:zeta=0) :
    ∃ i4:k,
      (B*e+c*d)+(3/2*gamma:k) • d =
        (1/9:k) • B^3-(3/4*epsilon:k) • B+(3/8:k) • C i4 := by
  rcases hp with ⟨_hn,_hgt,_hle,_hA,_hB,_hc,_hd,_he,_ha,_hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,_hi3,_row0,_row1,_row2,_hpos,_hiff⟩
  refine ⟨i4,?_⟩
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,hz] at hi4
  simp only [secondaryResidualInvariantFourPolynomial68] at hi4
  rw [← hi4]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_pow,map_neg,
    map_zero,RatFunc.algebraMap_C,map_div₀,map_ofNat,map_natCast,map_one]
  ring

/-- Every coefficient used before the explicit stopping depth is positive,
and the epsilon/B term is strictly lower. -/
theorem fiveToSix_terminal_uniform_index_arithmetic68
    (N G q:ℕ) (hN:2<N) (hwindow:5*N<2*G ∧ 2*G≤6*N)
    (hq:q<3*N/2+1):
    q<2*N ∧ q<G-N ∧ 0<2*N-q ∧ 0<6*N-q-1 := by
  omega

/-- Uniform support consequence of the compensated polynomial I4 identity.
No coefficient expansion is used here. -/
theorem fiveToSix_terminal_compensatedI4_support68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G q:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hz:zeta=0) (hq:q<3*N/2+1) (hL:q≤3*G-7*N) :
    ((B*e+c*d)+(3/2*gamma:k) • d).natDegree≤2*N-q := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases fiveToSix_terminal_compensatedI4_polynomial68 alpha gamma epsilon
    zeta eta terminal A B c d e N G
    ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩ hz with ⟨i4,hpoly⟩
  rw [hpoly]
  compute_degree
  omega

/-- Uniform positive I4 coefficient.  The only surviving compensated load
is the literal `B^3` face at `q=L`; gamma walls have already cancelled. -/
theorem fiveToSix_terminal_compensatedI4_coeff68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G q:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hz:zeta=0) (hq:q<3*N/2+1) (hL:q≤3*G-7*N) :
    ((B*e+c*d)+(3/2*gamma:k) • d).coeff (2*N-q)=
      if 3*G-7*N=q then (1/9:k)*B.coeff (3*N-G)^3 else 0 := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hidx:=fiveToSix_terminal_uniform_index_arithmetic68 N G q hN ⟨hgt,hle⟩ hq
  rcases fiveToSix_terminal_compensatedI4_polynomial68 alpha gamma epsilon
    zeta eta terminal A B c d e N G
    ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩ hz with ⟨i4,hpoly⟩
  rw [hpoly,coeff_add,coeff_sub,coeff_smul,coeff_smul,coeff_smul]
  have hBlow:B.natDegree<2*N-q:=by omega
  have hClow:(C i4).natDegree<2*N-q:=by compute_degree;omega
  rw [coeff_eq_zero_of_natDegree_lt hBlow,coeff_eq_zero_of_natDegree_lt hClow]
  simp only [smul_eq_mul,mul_zero,sub_zero,add_zero]
  by_cases wall:3*G-7*N=q
  · have hB3:=coeff_pow_at_bound68 B (3*N-G) 3 hB
    rw [show 3*(3*N-G)=2*N-q from by omega] at hB3
    rw [if_pos wall,hB3]
  · have low:(B^3).natDegree<2*N-q:=by compute_degree;omega
    rw [if_neg wall,coeff_eq_zero_of_natDegree_lt low,mul_zero]

/-- Uniform compensated `A A'` coefficient, now a top-coefficient product
thanks to the polynomial I4 support bound. -/
theorem fiveToSix_terminal_compensatedAAF_uniform68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G q:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hz:zeta=0) (hq:q<3*N/2+1) (hL:q≤3*G-7*N) :
    (A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)).coeff (6*N-q-1)=
      A.coeff (2*N)^2*(((2*N:ℕ):k))*
        (if 3*G-7*N=q then (1/9:k)*B.coeff (3*N-G)^3 else 0) := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  let K:=(B*e+c*d)+(3/2*gamma:k) • d
  have hK:K.natDegree≤2*N-q:=by
    simpa only [K] using fiveToSix_terminal_compensatedI4_support68 alpha gamma epsilon
      zeta eta terminal A B c d e N G q hN
      ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩ hz hq hL
  have hP:(A*derivative A).natDegree≤4*N-1:=by compute_degree;omega
  have topP:=coeff_mul_derivative_at_bounds68 A A (2*N) (2*N) (by omega) hA hA
  rw [show 2*N+2*N-1=4*N-1 from by omega] at topP
  have top:=coeff_mul_at_bounds68 (A*derivative A) K (4*N-1) (2*N-q) hP hK
  rw [show (4*N-1)+(2*N-q)=6*N-q-1 from by omega] at top
  have topK:=fiveToSix_terminal_compensatedI4_coeff68 alpha gamma epsilon zeta eta
    terminal A B c d e N G q hN
    ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩ hz hq hL
  simpa only [K,topP,topK,pow_two] using top

/-- Literal positive row-zero coefficient at an arbitrary pre-stopping
depth, obtained directly from the terminal RHS adapter. -/
theorem fiveToSix_terminal_rowZero_uniform_source68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G q:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G)) (hq:q<3*N/2+1) :
    (secondaryResidualRowZeroPolynomial68 A B c d e+
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1/3:k) • (A*B)+d) e).coeff (6*N-q-1)=0 := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd,he,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  exact hpos (6*N-q-1)
    (fiveToSix_terminal_uniform_index_arithmetic68 N G q hN ⟨hgt,hle⟩ hq).2.2.2

/-- Uniform row-zero reduction after combining the pinned gamma term with
the compensated I4 face.  All discarded loads are strictly below this
positive coefficient throughout the stopping interval. -/
theorem fiveToSix_terminal_row_uniform_reduced68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G q:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hd:d.natDegree≤G-2*N) (he:e.natDegree≤G-N) (hz:zeta=0)
    (hq:q<3*N/2+1) (hR:q≤7*N-2*G) (hL:q≤3*G-7*N) :
    (-4/27:k)*(A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)).coeff (6*N-q-1)+
      (4/27:k)*(derivative A*B*c^2).coeff (6*N-q-1)-
      (4/9:k)*(derivative A*d*e).coeff (6*N-q-1)=0 := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,
    ⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have hidx:=fiveToSix_terminal_uniform_index_arithmetic68 N G q hN ⟨hgt,hle⟩ hq
  have hr:=fiveToSix_terminal_rowZero_uniform_source68 alpha gamma epsilon zeta eta
    terminal A B c d e N G q hN
    ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hq
  have h1:(A*B^2*derivative d).natDegree<6*N-q-1:=by compute_degree;omega
  have h2:(A*B*derivative B*d).natDegree<6*N-q-1:=by compute_degree;omega
  have h4:(B*c*derivative e).natDegree<6*N-q-1:=by compute_degree;omega
  have h5:(B*d*derivative d).natDegree<6*N-q-1:=by compute_degree;omega
  have h6:(derivative B*d^2).natDegree<6*N-q-1:=by compute_degree;omega
  have h7:(c*derivative c*d).natDegree<6*N-q-1:=by compute_degree;omega
  have x1:(B*derivative A*c).natDegree<6*N-q-1:=by compute_degree;omega
  have x2:(B*derivative e).natDegree<6*N-q-1:=by compute_degree;omega
  have x3:(A*B*derivative A).natDegree<6*N-q-1:=by compute_degree;omega
  have x5:(d*derivative c).natDegree<6*N-q-1:=by compute_degree;omega
  have x6:(d*derivative A).natDegree<6*N-q-1:=by compute_degree;omega
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hr
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,coeff_sub,coeff_neg,
    coeff_eq_zero_of_natDegree_lt h1,coeff_eq_zero_of_natDegree_lt h2,
    coeff_eq_zero_of_natDegree_lt h4,coeff_eq_zero_of_natDegree_lt h5,
    coeff_eq_zero_of_natDegree_lt h6,coeff_eq_zero_of_natDegree_lt h7,
    coeff_eq_zero_of_natDegree_lt x1,coeff_eq_zero_of_natDegree_lt x2,
    coeff_eq_zero_of_natDegree_lt x3,coeff_eq_zero_of_natDegree_lt x5,
    coeff_eq_zero_of_natDegree_lt x6,smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hr
  have hF:(A*derivative A*B*e).coeff (6*N-q-1)+
      (A*derivative A*c*d).coeff (6*N-q-1)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-q-1):=by rw [mul_add,coeff_add];ring
  have hKpoly:A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)=
      A*derivative A*(B*e+c*d)+(3/2*gamma:k) • (A*derivative A*d):=by
    rw [mul_add]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  have hK:(A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)).coeff (6*N-q-1)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-q-1)+
        (3/2*gamma:k)*(A*derivative A*d).coeff (6*N-q-1):=by
    rw [hKpoly,coeff_add,coeff_smul]
    ring
  have raw:(-4/27:k)*(A*derivative A*(B*e+c*d)).coeff (6*N-q-1)+
      (4/27:k)*(derivative A*B*c^2).coeff (6*N-q-1)-
      (4/9:k)*(derivative A*d*e).coeff (6*N-q-1)-
      (2/9*gamma:k)*(A*derivative A*d).coeff (6*N-q-1)=0:=by
    linear_combination hr+(4/27:k)*hF
  rw [hK]
  linear_combination raw

/-- The uniform scalar row has exactly the two gap faces and no hidden
gamma, epsilon, or terminal-constant load. -/
theorem fiveToSix_terminal_uniform_scalar_row68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G q:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hd:d.natDegree≤G-2*N) (he:e.natDegree≤G-N) (hz:zeta=0)
    (hq:q<3*N/2+1) (hR:q≤7*N-2*G) (hL:q≤3*G-7*N) :
    (-4/27:k)*(A.coeff (2*N)^2*(((2*N:ℕ):k))*
      (if 3*G-7*N=q then (1/9:k)*B.coeff (3*N-G)^3 else 0))+
      (4/27:k)*(if 3*G-7*N=q then
        A.coeff (2*N)*B.coeff (3*N-G)*c.coeff (4*N-G)^2*(((2*N:ℕ):k)) else 0)-
      (4/9:k)*(if 7*N-2*G=q then
        A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)*(((2*N:ℕ):k)) else 0)=0 := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have row:=fiveToSix_terminal_row_uniform_reduced68 alpha gamma epsilon zeta eta terminal
    A B c d e N G q hN ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hq hR hL
  have hK:=fiveToSix_terminal_compensatedAAF_uniform68 alpha gamma epsilon zeta eta
    terminal A B c d e N G q hN ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hz hq hL
  rw [hK] at row
  have hmain:(derivative A*B*c^2).coeff (6*N-q-1)=
      if 3*G-7*N=q then
        A.coeff (2*N)*B.coeff (3*N-G)*c.coeff (4*N-G)^2*(((2*N:ℕ):k)) else 0:=by
    by_cases lw:3*G-7*N=q
    · have hm:=coeff_mul_mul_mul_derivative_at_bounds68 B c c A (3*N-G) (4*N-G)
        (4*N-G) (2*N) (by omega) hB hc hc hA
      rw [show (3*N-G)+(4*N-G)+(4*N-G)+2*N-1=6*N-q-1 from by omega] at hm
      rw [if_pos lw]
      simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hm
    · have ml:(derivative A*B*c^2).natDegree<6*N-q-1:=by compute_degree;omega
      rw [if_neg lw,coeff_eq_zero_of_natDegree_lt ml]
  have hde:(derivative A*d*e).coeff (6*N-q-1)=
      if 7*N-2*G=q then
        A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)*(((2*N:ℕ):k)) else 0:=by
    by_cases rw0:7*N-2*G=q
    · have hm:=coeff_mul_mul_derivative_at_bounds68 d e A (G-2*N) (G-N) (2*N)
        (by omega) hd he hA
      rw [show (G-2*N)+(G-N)+2*N-1=6*N-q-1 from by omega] at hm
      rw [if_pos rw0]
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hm
    · have ml:(derivative A*d*e).natDegree<6*N-q-1:=by compute_degree;omega
      rw [if_neg rw0,coeff_eq_zero_of_natDegree_lt ml]
  rw [hmain,hde] at row
  exact row

/-- The sole uniform step residual: both gap faces arrive together and the
row fixes their exact terminal scalar. -/
def FiveToSixTerminalSimultaneousScalar68
    (A B d e:k[X]) (N G q:ℕ):Prop:=
  7≤q ∧ q<3*N/2+1 ∧ 7*N-2*G=q ∧ 3*G-7*N=q ∧ 5*q=7*N ∧
    4*A.coeff (2*N)*B.coeff (3*N-G)^3+
      27*d.coeff (G-2*N)*e.coeff (G-N)=0

/-- A genuinely uniform source-backed depth step.  Both non-simultaneous
faces contradict the all-nonzero cusp packet; only the simultaneous scalar
is retained. -/
theorem fiveToSix_terminal_uniform_step68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G q:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hd:d.natDegree≤G-2*N) (he:e.natDegree≤G-N) (hz:zeta=0)
    (hq7:7≤q) (hq:q<3*N/2+1) (hR:q≤7*N-2*G) (hL:q≤3*G-7*N) :
    FiveToSixTerminalSimultaneousScalar68 A B d e N G q ∨
      (q+1≤7*N-2*G ∧ q+1≤3*G-7*N) := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have row:=fiveToSix_terminal_uniform_scalar_row68 alpha gamma epsilon zeta eta terminal
    A B c d e N G q hN ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hq hR hL
  have cast:(((2*N:ℕ):k))≠0:=by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have dn:d.coeff (G-2*N)≠0:=by
    simpa only [show 5*N-G-(7*N-2*G)=G-2*N by omega] using hds
  have en:e.coeff (G-N)≠0:=by
    simpa only [show 6*N-G-(7*N-2*G)=G-N by omega] using hes
  by_cases rw0:7*N-2*G=q
  · by_cases lw:3*G-7*N=q
    · simp only [if_pos lw,if_pos rw0] at row
      have fact:(((2*N:ℕ):k))*A.coeff (2*N)*
          (4*A.coeff (2*N)*B.coeff (3*N-G)^3+
            27*d.coeff (G-2*N)*e.coeff (G-N))=0:=by
        linear_combination (-243/4:k)*row+
          3*(((2*N:ℕ):k))*A.coeff (2*N)*B.coeff (3*N-G)*hcusp
      have scalar:4*A.coeff (2*N)*B.coeff (3*N-G)^3+
          27*d.coeff (G-2*N)*e.coeff (G-N)=0:=
        (mul_eq_zero.mp fact).resolve_left (mul_ne_zero cast ha)
      exact Or.inl ⟨hq7,hq,rw0,lw,by omega,scalar⟩
    · simp only [if_neg lw,if_pos rw0] at row
      have z:(((2*N:ℕ):k))*A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)=0:=by
        linear_combination (-9/4:k)*row
      exact False.elim ((mul_ne_zero (mul_ne_zero (mul_ne_zero cast ha) dn) en) z)
  · by_cases lw:3*G-7*N=q
    · simp only [if_pos lw,if_neg rw0] at row
      have z:(((2*N:ℕ):k))*A.coeff (2*N)^2*B.coeff (3*N-G)^3=0:=by
        linear_combination (-243/16:k)*row+
          (3/4:k)*(((2*N:ℕ):k))*A.coeff (2*N)*B.coeff (3*N-G)*hcusp
      exact False.elim ((mul_ne_zero (mul_ne_zero cast (pow_ne_zero 2 ha))
        (pow_ne_zero 3 hb)) z)
    · exact Or.inr ⟨by omega,by omega⟩

/-- Source-provenance-preserving finite residual. -/
def FiveToSixTerminalFiniteStoppingResidual68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ):Prop:=
  FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal
      A B c d e N G ∧
    ∃ q, FiveToSixTerminalSimultaneousScalar68 A B d e N G q

/-- The verified depth-seven packet cannot generate an unbounded ladder:
the uniform source step reaches one exact simultaneous scalar strictly
before `D=floor(3N/2)+1`. -/
theorem fiveToSix_terminal_cusp_finite_stopping68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hres:FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal
      A B c d e N G):
    FiveToSixTerminalFiniteStoppingResidual68 alpha gamma epsilon zeta eta terminal
      A B c d e N G:=by
  have h0:=hres
  rcases hres with ⟨h6,hR7,hL7,row6⟩
  rcases h6 with ⟨h5,_r6,_l6,_row5⟩
  rcases h5 with ⟨h4,_r5,_l5,_row4⟩
  rcases h4 with ⟨h3,_r4,_l4,_row3⟩
  rcases h3 with ⟨h2,_r3,_l3,_i4,_row2⟩
  rcases h2 with ⟨hn,hd,he,hz,_r2,_l2,hp,_row1⟩
  rcases hp with ⟨hn0,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  refine ⟨h0,?_⟩
  apply fiveToSix_terminal_finite_stopping_of_uniform_step68 N G
    (∃ q,FiveToSixTerminalSimultaneousScalar68 A B d e N G q)
    hn ⟨hgt,hle⟩ hR7 hL7
  intro q hq7 hq hRq hLq
  rcases fiveToSix_terminal_uniform_step68 alpha gamma epsilon zeta eta terminal
    A B c d e N G q hn ⟨hn0,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
    hd he hz hq7 hq hRq hLq with hs | hnext
  · exact Or.inl ⟨q,hs⟩
  · exact Or.inr hnext

/-- Literal preservation of the already verified depth-seven corner.  Any
other simultaneous stopping wall occurs at depth at least eight. -/
theorem fiveToSix_terminal_cusp_finite_stopping_split68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hres:FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal
      A B c d e N G):
    FiveToSixTerminalSevenCorner68 alpha gamma epsilon zeta eta terminal
        A B c d e N G ∨
      (FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal
          A B c d e N G ∧
        ∃ q, 8≤q ∧ FiveToSixTerminalSimultaneousScalar68 A B d e N G q) := by
  have hf:=fiveToSix_terminal_cusp_finite_stopping68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hres
  rcases hf with ⟨h0,q,hq⟩
  rcases hq with ⟨hq7,hqD,hR,hL,hident,hscalar⟩
  by_cases q7:q=7
  · left
    apply fiveToSix_terminal_seven_corner68 alpha gamma epsilon zeta eta terminal
      A B c d e N G h0
    · omega
    · omega
  · exact Or.inr ⟨h0,q,by omega,⟨hq7,hqD,hR,hL,hident,hscalar⟩⟩

#print axioms fiveToSix_terminal_stopping_depth_arithmetic68
#print axioms fiveToSix_terminal_finite_stopping_of_uniform_step68
#print axioms fiveToSix_terminal_compensatedI4_polynomial68
#print axioms fiveToSix_terminal_compensatedI4_support68
#print axioms fiveToSix_terminal_compensatedI4_coeff68
#print axioms fiveToSix_terminal_compensatedAAF_uniform68
#print axioms fiveToSix_terminal_row_uniform_reduced68
#print axioms fiveToSix_terminal_uniform_scalar_row68
#print axioms fiveToSix_terminal_uniform_step68
#print axioms fiveToSix_terminal_cusp_finite_stopping68
#print axioms fiveToSix_terminal_cusp_finite_stopping_split68

end FiveToSixCuspTerminalFiniteStopping68

end Max11DegreeRoutes
