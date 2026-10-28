import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputNative

namespace OAI.Algorithms

/-! The native linear-plan builder has cubic cost in its actual input size. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Cost
open SubexponentialSAT.Subexp

theorem rows_budget_le (h n J : ℕ) (js : List ℕ) (hj : ∀ j ∈ js, j ≤ J) :
    Rows.budget h n js ≤ js.length * (207*(h+n+J+1)) := by
  induction js with
  | nil => simp [Rows.budget]
  | cons j js ih =>
      have hb := hj j (by simp)
      have ht := ih (fun k hk => hj k (by simp [hk]))
      simp only [Rows.budget,Rows.callbackBound,List.length_cons]
      nlinarith

theorem step_budget_le (scopes : List (List ℕ)) (n v z W : ℕ)
    (hW : 1 ≤ W) (hL : (Scan.scopeBits scopes).length ≤ W)
    (hq : scopes.length ≤ W) (hn : n ≤ W) (hv : v ≤ W) (hz : z ≤ W) :
    Step.bound scopes n v z ≤ 3000*W^2 := by
  have hW2 : W ≤ W^2 := by nlinarith
  have hd : (Scan.indices scopes v).length ≤ W :=
    (SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes).trans hq
  have hs := SubexpIncidencePlanScan.scanBudget_le v 0 scopes
  have hc : 128*(v+2)+16*(0+scopes.length+2)+20 ≤ 452*W := by omega
  have hs' : SubexpIncidencePlanScan.scanBudget v 0 scopes ≤ 452*W^2 := by
    calc
      _ ≤ (128*(v+2)+16*(0+scopes.length+2)+20)*(Scan.scopeBits scopes).length := hs
      _ ≤ (452*W)*W := Nat.mul_le_mul hc hL
      _ = _ := by ring
  have hj : ∀ j ∈ (Scan.indices scopes v).reverse, j ≤ scopes.length := by
    intro j hj
    exact (IncidencePlanSpec.incidentIndex_lt scopes v j (List.mem_reverse.mp hj)).le
  have hr := rows_budget_le v n scopes.length (Scan.indices scopes v).reverse hj
  have hr' : Rows.budget v n (Scan.indices scopes v).reverse ≤ 828*W^2 := by
    have hcoef : 207*(v+n+scopes.length+1) ≤ 828*W := by omega
    have hlen : (Scan.indices scopes v).reverse.length ≤ W := by simpa using hd
    calc
      _ ≤ (Scan.indices scopes v).reverse.length*(207*(v+n+scopes.length+1)) := hr
      _ ≤ W*(828*W) := Nat.mul_le_mul hlen hcoef
      _ = _ := by ring
  have hcall : Rows.callbackBound v n z ≤ 800*W := by dsimp [Rows.callbackBound]; omega
  have hclean : Lift.cleanBound scopes v [false] ≤ 53*W := by
    simp only [Lift.cleanBound,List.length_cons,List.length_nil]
    omega
  dsimp [Step.bound,Scan.bound]
  nlinarith

theorem loop_budget_le (scopes : List (List ℕ)) (n W : ℕ) (mask : List Bool)
    (hW : 1 ≤ W) (hL : (Scan.scopeBits scopes).length ≤ W)
    (hq : scopes.length ≤ W) (hn : n ≤ W) :
    ∀ v z, v+mask.length ≤ W → z+mask.length ≤ W →
      Loop.budget scopes n v z mask ≤ 3005*mask.length*W^2+2 := by
  induction mask with
  | nil => simp [Loop.budget]
  | cons high mask ih =>
      intro v z hv hz
      have hv' : v+1+mask.length ≤ W := by simp only [List.length_cons] at hv; omega
      have hz' : (if high then z else Step.next scopes v z)+mask.length ≤ W := by
        cases high <;> simp only [Bool.false_eq_true,ite_false,ite_true]
        · unfold Step.next; split <;> simp only [List.length_cons] at hz <;> omega
        · simp only [List.length_cons] at hz; omega
      have ht := ih (v+1) (if high then z else Step.next scopes v z) hv' hz'
      have hs := step_budget_le scopes n v z W hW hL hq hn (by omega) (by omega)
      cases high <;> simp only [Loop.budget,ite_true,Bool.false_eq_true,ite_false,List.length_cons] at * <;>
        nlinarith

def inputSize (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  (Scan.scopeBits scopes).length+n+mask.length+1

theorem native_cubic (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    Boot.fullBudget scopes n mask ≤ 4000*(inputSize scopes n mask)^3 := by
  let W := inputSize scopes n mask
  have hW : 1 ≤ W := by dsimp [W,inputSize]; omega
  have hL : (Scan.scopeBits scopes).length ≤ W := by dsimp [W,inputSize]; omega
  have hq : scopes.length+1 ≤ (Scan.scopeBits scopes).length :=
    Encoding.length_encodeList_lower _ scopes
  have hloop := loop_budget_le scopes n W mask hW hL (by omega)
    (by dsimp [W,inputSize]; omega) 0 scopes.length
    (by dsimp [W,inputSize]; omega) (by dsimp [W,inputSize] at *; omega)
  have hcounter := SubexpSunflowerProgram.CountRecords.steps_le_encoded (Boot.records scopes)
  rw [← Boot.scope_eq] at hcounter
  have hboot : Boot.budget scopes ≤ 10*W+9 := by
    dsimp [Boot.budget,SubexpSunflowerProgram.CountRecords.steps] at *
    omega
  have hm : mask.length ≤ W := by dsimp [W,inputSize]; omega
  have hprod := Nat.mul_le_mul_right (3005*W^2) hm
  have hW2 : W ≤ W^2 := by nlinarith
  have hW3 : W ≤ W^3 := by nlinarith [Nat.mul_le_mul_left (W^2) hW]
  dsimp [Boot.fullBudget]
  nlinarith
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Cost

end OAI.Algorithms
