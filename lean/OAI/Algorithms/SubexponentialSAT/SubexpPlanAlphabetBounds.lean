import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanComplexity

namespace OAI.Algorithms

/-! Byte-size bounds for the actual forward-plan alphabet. -/
namespace SubexponentialSAT.SubexpPlanAlphabetBase

/-- One ordinary (single-framed-record-list) forward plan. -/
def planWordBound (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  1+(2*(scopes.length+(Δ+1)*D)+2)*(Δ+1)

theorem planBytes_length_le (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) (v : Fin D) :
    (planBytes D Δ scopes v.val).length ≤ planWordBound D Δ scopes := by
  have h := SubexpIncidencePlanProgram.encoded_plan_length_le D Δ scopes hd v
  simpa [planBytes,planWordBound,ProgramEncoding.encodeRecords_length,
    Subexp.ReadPlan.unaryPlan,Subexp.IncidencePlanSpec.producedPlan,List.map_reverse] using h

/-- Each alphabet payload has one additional frame around the ordinary plan. -/
theorem alphabet_payload_length_le (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (bits : List Bool) (hb : bits ∈ alphabet D Δ scopes) :
    bits.length ≤ 2*planWordBound D Δ scopes+1 := by
  rw [alphabet_eq_finRange] at hb
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
  have h := planBytes_length_le D Δ scopes hd v
  rw [Encoding.length_frame]
  omega

theorem alphabet_encoded_length_le (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    (ProgramEncoding.encodeRecords (alphabet D Δ scopes)).length ≤
      1+(2*(2*planWordBound D Δ scopes+1)+2)*D := by
  have h := Encoding.length_encodeList_upper id (alphabet D Δ scopes)
    (2*planWordBound D Δ scopes+1) (alphabet_payload_length_le D Δ scopes hd)
  simpa only [ProgramEncoding.encodeRecords,alphabet_length] using h

end SubexponentialSAT.SubexpPlanAlphabetBase

end OAI.Algorithms
