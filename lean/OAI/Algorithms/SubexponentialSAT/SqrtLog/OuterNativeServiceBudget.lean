import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeUniform
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostFinal

namespace OAI.Algorithms

/-! Actual whole-selector cost, including all marked and failed trials,
substituted back through the paid initial-code source-size bound. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram HashSelectProgram Filter
open scoped Topology
noncomputable section

def tailCoefficient (k : ℕ) : ℝ :=
  (3000000*4^8*queryCoefficient k)*400^(8+queryDegree k)
def tailExponent (k qi : ℕ) : ℝ := 16+queryExponent k qi+((8+queryDegree k:ℕ):ℝ)*2
def tailDegree (k p : ℕ) : ℕ := (p+1)*(8+queryDegree k)

 theorem tailCoefficient_ge_one (k : ℕ) : 1 ≤ tailCoefficient k := by
  have h := queryCoefficient_ge_one k
  have hp : (1:ℝ) ≤ 400^(8+queryDegree k) := one_le_pow₀ (by norm_num)
  unfold tailCoefficient
  nlinarith
 theorem tailExponent_nonneg (k qi : ℕ) : 0 ≤ tailExponent k qi := by
  have h := queryExponent_nonneg k qi
  unfold tailExponent
  positivity
 theorem tailDegree_pos (k p : ℕ) : 0 < tailDegree k p := by
  unfold tailDegree
  positivity

 theorem eventually_native_history_services (k qi C d p : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀(F : OuterQuery.Formula n) B (a : Data),
      StartReady a n (formulaRecords F).length B →
      0 < (formulaRecords F).length →
      (∀clause∈F,clause.length ≤ k) → F.length ≤ n*B →
      0 < B → B ≤ Asymptotic.L n^qi →
      a.stacks 784=Encoding.encodeList id (formulaRecords F) →
      ∀(s : SparseCode.SuppliedShifts (formulaRecords F).length B)
        (code : SparseCode.SuppliedLocal (formulaRecords F).length B),
      a.stacks 777=candidateEncoding (OuterQuery.initial F a s code) →
      ∀W V, SubexpSetupStorage.WordBound V a →
      V ≤ Execution.SelectorCost.initialSize C d qi p n W →
      ∃svc : HistoryServices (formulaClauses F) (LeafOuterNative.mass k)
        (LeafOuterNative.acceptedCount k) a (OuterQuery.initial F a s code),
        (svc.budget:ℝ) ≤ Statement.runtimeBound (tailCoefficient k) (tailExponent k qi)
          (tailDegree k p) W n := by
  filter_upwards [eventually_uniform_runtime k qi,
    Execution.SelectorCost.eventually_history_runtime (queryCoefficient_ge_one k)
      (queryExponent_nonneg k qi) (queryDegree k) qi,
    Execution.SelectorCost.eventually_history_source_bound C d qi p (Aq:=queryExponent k qi)
      (le_trans (by norm_num) (queryCoefficient_ge_one k)) (queryDegree k),
    eventually_ge_atTop 2] with n hrt hcost hsource hn
  intro F B a ha hm hk hcount hB hBL hformula s code hrows W V hw hV
  let P := CounterPrograms.value (a.stacks 773)
  let K := CounterPrograms.value (a.stacks 774)
  let L := V+K*(2*(P*(a.stacks 768).length)+2)+P*(a.stacks 768).length
  let X := 7*L+(formulaRecords F).length+2
  let Q := uniformQueryLimit k qi X n
  obtain ⟨svc,hmass,hsteps,hbits⟩ := native_history_services F a ha hm hn hk hcount hformula s code
    hrows V L Q hw le_rfl (hrt B X hB hBL)
  have hVX : V ≤ X := by dsimp [X,L]; omega
  have hLX : L ≤ X := by dsimp [X]; omega
  have hd : P=SparseCode.distanceDenom F.length B := by
    simpa only [P,CounterPrograms.value_eq_toNat,formulaRecords_length] using ha.depth
  have hr : K=HashSelect.loopCap n F.length := by
    simpa only [K,CounterPrograms.value_eq_toNat,formulaRecords_length] using ha.rounds
  have hmid := hcost F.length B X (a.stacks 768) (a.stacks 773) (a.stacks 774)
    Q svc.massSteps svc.countSteps svc.countBits
    (by simpa only [formulaRecords_length] using hm) hcount hBL
    (by simpa only [CounterPrograms.value_eq_toNat,formulaRecords_length] using ha.count)
    hd hr ((hw 768).trans hVX) ((hw 773).trans hVX) ((hw 774).trans hVX) le_rfl
    (by rw [hmass]; unfold LeafOuterNative.overhead; gcongr)
    (by rw [hsteps]; omega) (by rw [hbits])
  have hX : X ≤ Execution.SelectorCost.physicalSource V (a.stacks 768).length
      (SparseCode.distanceDenom F.length B) (HashSelect.loopCap n F.length) F.length := by
    dsimp [X,L]
    rw [hd,hr,formulaRecords_length]
    simp only [Execution.SelectorCost.physicalSource,Nat.mul_assoc]
    exact le_rfl
  have hfinal := hsource F.length B W V (a.stacks 768).length X hcount hBL hV (hw 768) hX
  exact ⟨svc,hmid.trans hfinal⟩

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
