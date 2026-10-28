import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets

/-! Time bounds for the same actual source/prepared caps used by the literal
query provider. The resource record supplies the combinatorial exponent;
its ordinary fields are not asserted to measure the actual physical phases.
Frontend, preparation, seed and return work are paid separately below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds

open SqrtLog SqrtLog.Statement CostAssembly.Polynomial NativeQueryInputBounds

/-- One physical allowance for every scalar in the actual high-loop budget. -/
def physicalCap (Cp dp Cn dn Cl dl Cf df N L k : ℕ) : ℕ :=
  let S := sourceCap Cn dn Cl dl N L k
  let F := frontendCap Cf df L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  30*(S+F+P+4*N+6+1)+QueryHeadBudgets.compact (12*P+4*N+6)

/-- The cap is polynomial in the original input independently of all later
candidates, marks, nodes, or preserved caller words. -/
theorem physicalCap_polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C e : ℕ, ∀ N L : ℕ, L ≤ C0*(N+1)^d0 →
      physicalCap Cp dp Cn dn Cl dl Cf df N L k ≤ C*(N+1)^e := by
  obtain ⟨Cw,ew,hw⟩ := cap_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  obtain ⟨Cc,ec,hc⟩ := QueryHeadBudgets.caps_polynomial
  let V := fun N => Cw*(N+1)^ew
  have hV : Ordinary V := ordinary_mul (ordinary_const Cw)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) ew)
  obtain ⟨C,e,hpoly⟩ := ordinary_add
    (ordinary_mul (ordinary_const 30) (ordinary_add hV (ordinary_const 1)))
    (ordinary_mul (ordinary_const Cc) (ordinary_pow
      (ordinary_add (ordinary_mul (ordinary_const 12) hV) (ordinary_const 1)) ec))
  refine ⟨C,e,?_⟩
  intro N L hL
  let S := sourceCap Cn dn Cl dl N L k
  let F := frontendCap Cf df L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  have hW : S+F+P+4*N+6 ≤ V N := hw N L hL
  have hA : 12*P+4*N+6 ≤ 12*V N := by omega
  have hcompact := (hc (12*P+4*N+6)).1.trans
    (Nat.mul_le_mul_left Cc (Nat.pow_le_pow_left (Nat.add_le_add_right hA 1) ec))
  have hraw : physicalCap Cp dp Cn dn Cl dl Cf df N L k ≤
      30*(V N+1)+Cc*(12*V N+1)^ec := by
    change 30*(S+F+P+4*N+6+1)+QueryHeadBudgets.compact (12*P+4*N+6) ≤ _
    omega
  exact hraw.trans (hpoly N)

/-- Both exact complete-query budgets have one uniform ETH-scale bound.
The caller supplies the actual produced resource record, its sharp fields,
and the equality between its branch count and the actual high mask. -/
theorem runtime_bound (k qi ql recordDegree Cp dp Cn dn Cl dl Cf df C0 d0 : ℕ) :
    ∃ C E : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
      ∀ n ≥ cutoff, ∀ N L : ℕ, n ≤ N → L ≤ C0*(N+1)^d0 →
      ∀ r : CostAssembly.Resources, CostAssembly.Bounds qi ql recordDegree n r →
      ∀ f t d Q J h : ℕ,
      let S := sourceCap Cn dn Cl dl N L k
      let F := frontendCap Cf df L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      let A := 12*P+4*N+6
      let T := A+S+2
      let cost := Cp*(S+f+1)^dp
      let loop := HighQueryCorrect.loopBudget n h t d Q J A T
        (CostAssembly.assembledWork k n r)
      f ≤ F → t ≤ S → d ≤ S → Q ≤ S → J ≤ S → h ≤ n → h = r.branchVars →
      (HighQueryCorrect.markedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
        runtimeBound C E degree N n ∧
      (HighQueryCorrect.acceptedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
        runtimeBound C E degree N n := by
  obtain ⟨K,p,hphysical⟩ := physicalCap_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  obtain ⟨C,E,degree,cutoff,hC,hE,hdegree,hloop⟩ :=
    QueryStreamBudgets.high_loop_runtimeBound k qi ql recordDegree K p
  refine ⟨C+(10000*(K+1) : ℕ),E,degree+p,cutoff,by have := Nat.cast_nonneg (α := ℝ) (10000*(K+1)); linarith,hE,by omega,?_⟩
  intro n hn N L hN hL r hr f t d Q J h S F P A T cost loop hf ht hd hQ hJ hh heq
  let U := physicalCap Cp dp Cn dn Cl dl Cf df N L k
  have hU : U ≤ K*(N+1)^p := hphysical N L hL
  have hbase : S+F+P+4*N+6+1 ≤ U := by
    dsimp only [U,physicalCap,S,F,P]
    omega
  have hA : A ≤ U := by
    dsimp only [A,U,physicalCap,S,F,P]
    omega
  have hT : T ≤ U := by
    dsimp only [T,A,U,physicalCap,S,F,P]
    omega
  have hcompact : QueryHeadBudgets.compact A ≤ U := by
    dsimp only [A,U,physicalCap,S,F,P]
    omega
  have hcore : (loop : ℝ) ≤ runtimeBound C E degree N n :=
    hloop n hn r hr n t d Q J A T U (QueryHeadBudgets.compact A) h N
      (by omega) (by omega) (by omega) (by omega) (by omega) hA hT hcompact
      (by omega) heq hU
  let extra := F+cost+110*HighQuerySetup.localBound (S+f) cost+
    3430*QueryHeadBudgets.compact A+5229
  have hsetup := setup_time_le Cp dp Cn dn Cl dl Cf df N L k f hf
  have hextra : extra ≤ 10000*(U+1) := by
    change F+cost+110*HighQuerySetup.localBound (S+f) cost+
      3430*QueryHeadBudgets.compact A+5229 ≤ _
    change f+cost+110*HighQuerySetup.localBound (S+f) cost+81 ≤ F+111*P+81 at hsetup
    omega
  have hone : 1 ≤ (N+1)^p := Nat.one_le_pow' _ _
  have huone : U+1 ≤ (K+1)*(N+1)^p := by nlinarith only [hU,hone]
  have hextra' : extra ≤ (10000*(K+1))*(N+1)^p :=
    hextra.trans ((Nat.mul_le_mul_left 10000 huone).trans_eq (by ring))
  have htotal := QueryStreamBudgets.polynomial_overhead_runtime C E degree
    (10000*(K+1)) p N n loop extra (by linarith) (by linarith) hcore hextra'
  have hmarked : HighQueryCorrect.markedBudget F (S+f) cost loop
      (QueryHeadBudgets.compact A) ≤ loop+extra := by
    dsimp only [HighQueryCorrect.markedBudget,extra]
    omega
  have haccepted : HighQueryCorrect.acceptedBudget F (S+f) cost loop
      (QueryHeadBudgets.compact A) = loop+extra := by
    dsimp only [HighQueryCorrect.acceptedBudget,extra]
    omega
  exact ⟨(Nat.cast_le.mpr hmarked).trans htotal,by simpa only [haccepted] using htotal⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds
