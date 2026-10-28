import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanProgram

namespace OAI.Algorithms

/-! Polynomial bounds for the concrete encoded incidence-plan producer. -/
namespace SubexponentialSAT.SubexpIncidencePlanProgram

def inputSize (D Δ v : ℕ) (scopes : List (List ℕ)) : ℕ :=
  (Encoding.encodeList SubexpIncidencePlanScan.scopeBytes scopes).length + D + Δ + v + 1

theorem inputSize_eq_stack_lengths (regs : Fin 10 → Bool) (D Δ v : ℕ)
    (scopes : List (List ℕ)) :
    (∑ i : Fin 16, ((input regs D Δ v scopes).stacks i).length) = inputSize D Δ v scopes := by
  simp [input,extend,SubexpIncidencePlanScan.data,inputSize,Fin.sum_univ_succ,
    Encoding.length_encodeNat]
  omega

theorem incidencePrefix_length_le (v : ℕ) (scopes : List (List ℕ)) :
    (incidencePrefix v scopes).length ≤ scopes.length * (2*scopes.length+2) := by
  have h := SubexpIncidencePlanScan.indexPrefix_length_le
    (Subexp.IncidencePlanSpec.incidentIndices scopes v).reverse scopes.length
      (fun j hj => Subexp.IncidencePlanSpec.incidentIndex_lt scopes v j
        (List.mem_reverse.mp hj))
  have hd := SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes
  change (Subexp.IncidencePlanSpec.incidentIndices scopes v).length ≤ scopes.length at hd
  simp only [List.length_reverse] at h
  exact h.trans (Nat.mul_le_mul_right _ hd)

/-- A cubic bound in the actual unary-and-record input length. Neither the
program's register bank nor its control table depends on these parameters. -/
theorem bound_le_cubic (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    bound D Δ v scopes ≤ 1000*(inputSize D Δ v scopes)^3 := by
  let W := inputSize D Δ v scopes
  let L := (Encoding.encodeList SubexpIncidencePlanScan.scopeBytes scopes).length
  let E := scopes.length
  let d := Subexp.IncidencePlanSpec.degree scopes v
  have hw : 1 ≤ W := by dsimp [W,inputSize]; omega
  have hL : L ≤ W := by dsimp [L,W,inputSize]; omega
  have hD : D ≤ W := by dsimp [W,inputSize]; omega
  have hΔ : Δ ≤ W := by dsimp [W,inputSize]; omega
  have hv : v ≤ W := by dsimp [W,inputSize]; omega
  have hE : E ≤ W := by
    have h := Encoding.length_encodeList_lower SubexpIncidencePlanScan.scopeBytes scopes
    dsimp [E,L] at *
    omega
  have hdW : d ≤ W := hd.trans hΔ
  have hW2 : W ≤ W^2 := by
    simpa only [Nat.mul_one,pow_two] using Nat.mul_le_mul_left W hw
  have hW3 : W^2 ≤ W^3 := by
    change W^2 ≤ W^2*W
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (W^2) hw
  have hprod : v*Δ ≤ W^2 := by simpa [pow_two] using Nat.mul_le_mul hv hΔ
  have hinc := incidencePrefix_length_le v scopes
  have hincW : (incidencePrefix v scopes).length ≤ 4*W^2 := by
    have h := Nat.mul_le_mul hE (show 2*E+2 ≤ 4*W by omega)
    dsimp [E] at h
    calc
      _ ≤ scopes.length*(2*scopes.length+2) := hinc
      _ ≤ W*(4*W) := h
      _ = 4*W^2 := by ring
  have hscan := SubexpIncidencePlanScan.scanBudget_le v 0 scopes
  have hscanW : SubexpIncidencePlanScan.scanBudget v 0 scopes ≤ 452*W^2 := by
    have hcoef : 128*(v+2)+16*(0+scopes.length+2)+20 ≤ 452*W := by
      dsimp [E] at hE
      omega
    have h := Nat.mul_le_mul hcoef hL
    dsimp [L] at h
    calc
      _ ≤ (128*(v+2)+16*(0+scopes.length+2)+20)*L := hscan
      _ ≤ (452*W)*W := h
      _ = 452*W^2 := by ring
  have hhead : 19*v+12*scopes.length+6*(incidencePrefix v scopes).length+44 ≤ 99*W^2 := by
    dsimp [E] at hE
    omega
  have hprep : 7*Δ+20*d+7*D+7*scopes.length+14*v+7*v*Δ+41 ≤ 103*W^2 := by
    dsimp [E] at hE
    simp only [Nat.mul_assoc]
    omega
  let start := SubexpIncidencePlanFinish.paddingStart v E d D Δ
  have hstart : start ≤ 4*W^2 := by
    dsimp [start,SubexpIncidencePlanFinish.paddingStart]
    omega
  have hcount : Δ-d ≤ W := (Nat.sub_le Δ d).trans hΔ
  have hsteps := SubexpUnaryRangeProgram.steps_le start (Δ-d)
  have hstepW : SubexpUnaryRangeProgram.steps start (Δ-d)+2 ≤ 86*W^3 := by
    have hfactor : 12*(start+(Δ-d))+23 ≤ 83*W^2 := by omega
    have hmul := Nat.mul_le_mul hcount hfactor
    have hm : (Δ-d)*(12*(start+(Δ-d))+23) ≤ 83*W^3 := by
      calc
        _ ≤ W*(83*W^2) := hmul
        _ = 83*W^3 := by ring
    omega
  dsimp [bound]
  change _ ≤ 1000*W^3
  dsimp [start,E,d] at hstepW hprep
  omega

theorem encoded_plan_length_le (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) (v : Fin D) :
    (ProgramEncoding.encodeRecords
      ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v.val).map unary)).length ≤
      1+(2*(scopes.length+(Δ+1)*D)+2)*(Δ+1) := by
  have h := Encoding.length_encodeList_upper id
    ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v.val).map unary)
    (scopes.length+(Δ+1)*D) (by
      intro bits hb
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
      have hj' : j ∈ Subexp.IncidencePlanSpec.vertexPlan D Δ scopes v.val := by
        simpa [Subexp.IncidencePlanSpec.producedPlan] using hj
      have hjlt := Subexp.IncidencePlanSpec.vertexPlan_valid D Δ scopes hd v j hj'
      simpa using Nat.le_of_lt hjlt)
  have hlen := Subexp.IncidencePlanSpec.vertexPlan_length D Δ scopes v.val (hd v)
  simpa only [ProgramEncoding.encodeRecords, List.length_map,
    Subexp.IncidencePlanSpec.producedPlan, List.length_reverse, hlen] using h

end SubexponentialSAT.SubexpIncidencePlanProgram

end OAI.Algorithms
