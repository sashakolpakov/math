import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpVertexPairProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetBounds
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCost

namespace OAI.Algorithms

/-! A polynomial bound for the actual all-vertices record iterator. -/
namespace SubexponentialSAT.SubexpPlanAlphabetBase

/-- A uniform bound independent of the currently visited vertex. All terms
are polynomial in the encoded input length and unary D and Delta. -/
def uniformCallbackBound (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  1000*(SubexpIncidencePlanProgram.inputSize D Δ D scopes)^3 +
    7*((scopeBytes scopes).length+D+Δ+D) + 34*planWordBound D Δ scopes +
    2*(2*scopes.length+2*D+D*Δ+3*Δ+3*D+1)+106

theorem callbackBound_le_uniform (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) (v : Fin D) :
    callbackBound D Δ v.val scopes ≤ uniformCallbackBound D Δ scopes := by
  have hv : v.val ≤ D := Nat.le_of_lt v.isLt
  have hi : SubexpIncidencePlanProgram.inputSize D Δ v.val scopes ≤
      SubexpIncidencePlanProgram.inputSize D Δ D scopes := by
    dsimp [SubexpIncidencePlanProgram.inputSize]
    omega
  have hm := (SubexpIncidencePlanProgram.bound_le_cubic D Δ v.val scopes (hd v)).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hi 3))
  have hr := SubexpIncidencePlanProgram.encoded_plan_length_le D Δ scopes hd v
  have hp := planBytes_length_le D Δ scopes hd v
  have hprod := Nat.mul_le_mul_right Δ hv
  have hdeg := hd v
  change _ ≤ planWordBound D Δ scopes at hr
  have hcopy : 7*((scopeBytes scopes).length+D+Δ+v.val) ≤
      7*((scopeBytes scopes).length+D+Δ+D) := by omega
  have hclear : 2*(2*scopes.length+2*D+v.val*Δ+2*Δ+
      Subexp.IncidencePlanSpec.degree scopes v.val+3*v.val+1) ≤
      2*(2*scopes.length+2*D+D*Δ+3*Δ+3*D+1) := by omega
  dsimp [callbackBound,uniformCallbackBound]
  change (ProgramEncoding.encodeRecords (Subexp.ReadPlan.unaryPlan
    (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v.val))).length ≤
      planWordBound D Δ scopes at hr
  omega

theorem budget_le_uniform (cost : List Bool → ℕ) (records : List (List Bool))
    (L C : ℕ) (hl : ∀ bits ∈ records, bits.length ≤ L)
    (hc : ∀ bits ∈ records, cost bits ≤ C) :
    RecordPrograms.budget cost records ≤ records.length*(6*L+C+7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
      have hbits := hl bits (by simp)
      have hcost := hc bits (by simp)
      have hrest := ih (fun b hb => hl b (by simp [hb])) (fun b hb => hc b (by simp [hb]))
      simp only [RecordPrograms.budget,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

def polynomialBound (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  6*D^2+17*D+15+D*(6*D+uniformCallbackBound D Δ scopes+7)

theorem totalBound_le_polynomial (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    totalBound D Δ scopes ≤ polynomialBound D Δ scopes := by
  have hb := budget_le_uniform (recordCost D Δ scopes)
    ((List.range' 0 D).reverse.map unary) D (uniformCallbackBound D Δ scopes)
    (by
      intro bits h
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      obtain ⟨i,hi,he⟩ := List.mem_range'.mp (List.mem_reverse.mp hv)
      simp only [List.length_replicate]
      omega)
    (by
      intro bits h
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      obtain ⟨i,hi,he⟩ := List.mem_range'.mp (List.mem_reverse.mp hv)
      have hv' : v < D := by omega
      simpa only [recordCost,List.length_replicate] using
        callbackBound_le_uniform D Δ scopes hd ⟨v,hv'⟩)
  simpa only [totalBound, polynomialBound, List.length_map,List.length_reverse,
    List.length_range'] using
    Nat.add_le_add_left hb (6*D^2+17*D+15)

end SubexponentialSAT.SubexpPlanAlphabetBase

/-! A polynomial instruction bound for the complete raw-pair producer. -/
namespace SubexponentialSAT.SubexpVertexPairProgram

open SubexpPlanAlphabetBase Subexp.TupleProgram SubexpNodeCost

theorem powerCost_two (a : List (List Bool)) :
    powerCost a 2 [[]] =
      payloadSize a*(61*a.length+45)+48*a.length^2+73*a.length+65 := by
  simp only [powerCost,stepCost_eq,payloadSize_cartesian,cartesianOutput_length,
    payloadSize_cons,payloadSize_nil,List.length_cons,List.length_nil]
  ring

def polynomialBound (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  SubexpPlanAlphabetBase.polynomialBound D Δ scopes +
    (D*(2*planWordBound D Δ scopes+1))*(61*D+45)+48*D^2+73*D+78

theorem bound_le_polynomial (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    bound D Δ scopes ≤ polynomialBound D Δ scopes := by
  have htotal := totalBound_le_polynomial D Δ scopes hd
  have hsize := payloadSize_le (alphabet D Δ scopes) (2*planWordBound D Δ scopes+1)
    (alphabet_payload_length_le D Δ scopes hd)
  simp only [alphabet_length] at hsize
  have hmul := Nat.mul_le_mul_right (61*D+45) hsize
  dsimp [bound,polynomialBound]
  rw [powerCost_two,alphabet_length]
  omega

end SubexponentialSAT.SubexpVertexPairProgram

end OAI.Algorithms
