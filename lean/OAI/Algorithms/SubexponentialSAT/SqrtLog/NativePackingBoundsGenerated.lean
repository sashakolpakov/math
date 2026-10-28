import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNativePacking
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingTupleBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBudgetArithmetic
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Native address-plan frontend bounds. The source size includes the actual
input plans and the number of represented types, not a scope-generated plan. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp LayoutProgram LayoutProgram.NativePacking
variable {U : Type*} [DecidableEq U]

def sourceSize (s : Spec U) : ℕ :=
  s.params.D+s.params.Δ+s.types.values.length+s.params.width.length+
    s.params.rows.flatten.length+(ProgramEncoding.encodeRecords s.params.alphabet).length+
    s.params.planStream.length+1

theorem sourceSize_pos (s : Spec U) : 1 ≤ sourceSize s := by unfold sourceSize; omega
theorem dimension_le (s : Spec U) : s.params.D ≤ sourceSize s := by unfold sourceSize; omega
theorem depth_le (s : Spec U) : s.params.Δ+1 ≤ sourceSize s := by unfold sourceSize; omega
theorem count_le (s : Spec U) : s.types.values.length ≤ sourceSize s := by unfold sourceSize; omega
theorem width_le (s : Spec U) : s.params.width.length ≤ sourceSize s := by unfold sourceSize; omega
theorem alphabet_bytes_le (s : Spec U) : (ProgramEncoding.encodeRecords s.params.alphabet).length ≤ sourceSize s := by unfold sourceSize; omega
theorem plan_stream_input_le (s : Spec U) : s.params.planStream.length ≤ sourceSize s := by unfold sourceSize; omega
theorem plan_stream_le (s : Spec U) : s.params.planStream.length ≤ 33*sourceSize s^4 := by
  have h := PackingBudgetArithmetic.le_power (sourceSize_pos s) (by decide : 1 ≤ 4)
  have h' := plan_stream_input_le s
  omega

theorem label_cost_le (s : Spec U) :
    PackingVertexLabels.traceCost s.params.width.length s.params.planList 0 ≤
      21000 * sourceSize s ^ 7 := by
  have hp : ∀ plan ∈ s.params.planList, (PackingVertexLabels.planBytes plan).length ≤ sourceSize s := by
    intro plan hm
    have h := PackingTupleBounds.member_length_le
      (s.params.planList.map PackingVertexLabels.planPayload)
      (PackingVertexLabels.planPayload plan) (List.mem_map.mpr ⟨plan,hm,rfl⟩)
    have hframe : (PackingVertexLabels.planBytes plan).length ≤
        (PackingVertexLabels.planPayload plan).length := by
      simp only [PackingVertexLabels.planPayload,PackingVertexLabels.planBytes,Encoding.length_frame]
      omega
    exact (hframe.trans h).trans (plan_stream_input_le s)
  have hb := PackingVertexLabels.traceCost_le s.params.width.length s.params.planList 0 _ hp
  rw [NativeFrontend.Params.planList_length] at hb
  exact hb.trans (PackingBudgetArithmetic.label_trace_le _ _ _ _
    (sourceSize_pos s) (dimension_le s) (width_le s) (by have h := PackingBudgetArithmetic.le_power (sourceSize_pos s) (by decide : 1 ≤ 3); omega))

/-- The label tape starts empty, so its length is bounded by its actual
executed instruction count. No output-length certificate is assumed. -/
theorem label_stream_le (s : Spec U) : s.params.labelStream.length ≤ 21000 * sourceSize s ^ 7 := by
  have hvalid := s.plans_valid
  obtain ⟨n, rf, hn, ht⟩ := PackingVertexLabels.program_trace s.params.rows s.params.width
    s.params.planList (fun _ => false) 0 [] [] s.rows_width hvalid
  have hg := SequentialProgram.trace_stack_length_le ht (13 : Fin 15)
  have hl : s.params.labelStream.length ≤ n := by
    simpa [NativeFrontend.Params.labelStream, PackingVertexLabels.state,
      StructuredProgram.State.withPC] using hg
  exact (hl.trans hn).trans (label_cost_le s)

theorem type_rows_count (s : Spec U) : s.params.typeRows.length = s.types.values.length := by
  rw [s.type_records, List.length_map]

theorem type_power_count (s : Spec U) :
    s.params.alphabet.length ^ (s.params.Δ + 1) = s.types.values.length := by
  have h := type_rows_count s
  simpa only [NativeFrontend.Params.typeRows, TupleProgram.powerRows_length,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] using h

theorem type_word_le (s : Spec U) :
    ∀ row ∈ s.params.typeRows, row.length ≤ sourceSize s ^ 2 := by
  have hw : ∀ x ∈ s.params.alphabet,
      x.length ≤ (ProgramEncoding.encodeRecords s.params.alphabet).length :=
    PackingTupleBounds.member_length_le s.params.alphabet
  have hp := PackingTupleBounds.powerRows_width s.params.alphabet [[]] (s.params.Δ + 1) 0 _
    (by simp) hw
  intro row hr
  have h := hp row hr
  have hm : (s.params.Δ + 1) * (ProgramEncoding.encodeRecords s.params.alphabet).length ≤
      sourceSize s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (depth_le s) (alphabet_bytes_le s)
  calc
    row.length ≤ (s.params.Δ + 1) * (ProgramEncoding.encodeRecords s.params.alphabet).length := by
      simpa only [Nat.zero_add] using h
    _ ≤ sourceSize s ^ 2 := hm

theorem type_stream_le (s : Spec U) : s.params.typeStream.length ≤ 5 * sourceSize s ^ 3 := by
  have h := ProgramEncoding.encodeRecords_length_le s.params.typeRows (sourceSize s ^ 2) (type_word_le s)
  rw [type_rows_count s] at h
  exact h.trans (PackingBudgetArithmetic.type_stream_le _ _ (sourceSize_pos s) (count_le s))

theorem type_cost_le (s : Spec U) :
    UniversalTypeProgram.budget s.params.alphabet s.params.Δ ≤ 10012 * sourceSize s ^ 4 := by
  have h := PackingTupleBounds.generated_powerCost_le s.params.alphabet (s.params.Δ + 1)
    (ProgramEncoding.encodeRecords s.params.alphabet).length
    (PackingTupleBounds.member_length_le s.params.alphabet)
  rw [type_power_count s] at h
  unfold UniversalTypeProgram.budget
  exact (Nat.add_le_add_right h 12).trans
    (PackingBudgetArithmetic.type_cost_le _ _ _ _ (sourceSize_pos s)
      (depth_le s) (count_le s) (alphabet_bytes_le s))

theorem frontend_bound_le (s : Spec U) :
    s.params.labelsBound+s.params.typesBound+2 ≤ 200000*sourceSize s^7 := by
  have hd : s.params.Δ ≤ sourceSize s := by have := depth_le s; omega
  have hrows : s.params.rows.flatten.length ≤ sourceSize s := by unfold sourceSize; omega
  have h := PackingBudgetArithmetic.frontend_le (sourceSize s) 0 _ _ _ _ _ _ _ _ _
    (sourceSize_pos s) (Nat.zero_le _) (dimension_le s) hd (width_le s) hrows
    (alphabet_bytes_le s) (plan_stream_le s) (label_stream_le s)
    (type_cost_le s) (type_stream_le s)
  have hl := label_cost_le s
  unfold NativeFrontend.Params.labelsBound NativeFrontend.Params.typesBound
  omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
