import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecutionSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingTupleBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBudgetArithmetic
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Bounds on the actual generated plans, labels and type rows. The size
uses only the initial records and the number of represented types. -/

namespace SubexponentialSAT.Subexp.PackingExecutionBounds

open PackingExecution

variable {U : Type*} [DecidableEq U]

def sourceSize (s : Spec U) : ℕ :=
  s.params.D + s.params.Δ + s.params.scopes.length + s.types.values.length +
    s.params.width.length + (SubexpPlanAlphabetBase.scopeBytes s.params.scopes).length +
    s.params.rows.flatten.length + (ProgramEncoding.encodeRecords s.params.alphabet).length + 1

theorem row_bytes_eq (s : Spec U) :
    s.params.rows.flatten.length =
      (s.params.scopes.length + (s.params.Δ + 1) * s.params.D) * s.params.width.length := by
  have hflat (rows : List (List Bool))
      (hw : ∀ row ∈ rows, row.length = s.params.width.length) :
      rows.flatten.length = rows.length * s.params.width.length := by
    induction rows with
    | nil => simp
    | cons row rows ih =>
      have hr := hw row (by simp)
      have ht := ih (fun x hx => hw x (by simp [hx]))
      simp only [List.flatten_cons, List.length_append, List.length_cons, hr, ht]
      ring
  rw [hflat s.params.rows s.rows_width, s.rows_count]

/-- The row-byte summand is fixed by the genuine input shape, so it is not
an independently supplied size parameter. -/
theorem sourceSize_eq (s : Spec U) :
    sourceSize s = s.params.D + s.params.Δ + s.params.scopes.length + s.types.values.length +
      s.params.width.length + (SubexpPlanAlphabetBase.scopeBytes s.params.scopes).length +
      (s.params.scopes.length + (s.params.Δ + 1) * s.params.D) * s.params.width.length +
      (ProgramEncoding.encodeRecords s.params.alphabet).length + 1 := by
  unfold sourceSize
  rw [row_bytes_eq s]

theorem sourceSize_pos (s : Spec U) : 1 ≤ sourceSize s := by unfold sourceSize; omega

theorem dimension_le (s : Spec U) : s.params.D ≤ sourceSize s := by unfold sourceSize; omega
theorem depth_le (s : Spec U) : s.params.Δ + 1 ≤ sourceSize s := by unfold sourceSize; omega
theorem count_le (s : Spec U) : s.types.values.length ≤ sourceSize s := by unfold sourceSize; omega
theorem width_le (s : Spec U) : s.params.width.length ≤ sourceSize s := by unfold sourceSize; omega
theorem alphabet_bytes_le (s : Spec U) :
    (ProgramEncoding.encodeRecords s.params.alphabet).length ≤ sourceSize s := by unfold sourceSize; omega

theorem plan_input_le (s : Spec U) :
    s.params.D + s.params.scopes.length + s.params.Δ +
      (SubexpPlanAlphabetBase.scopeBytes s.params.scopes).length + 1 ≤ sourceSize s := by
  unfold sourceSize
  omega

theorem plan_word_le (s : Spec U) :
    SubexpPlanAlphabetBase.planWordBound s.params.D s.params.Δ s.params.scopes ≤ 7 * sourceSize s ^ 3 :=
  PackingBudgetArithmetic.plan_wordBound_le _ _ _ _ (plan_input_le s)

theorem plan_stream_le (s : Spec U) : s.params.planStream.length ≤ 33 * sourceSize s ^ 4 := by
  have hp := SubexpPlanAlphabetBase.alphabet_encoded_length_le
    s.params.D s.params.Δ s.params.scopes s.degree_bound
  change s.params.planStream.length ≤ _ at hp
  apply hp.trans
  convert PackingBudgetArithmetic.plan_stream_le (sourceSize s) s.params.D
    (SubexpPlanAlphabetBase.planWordBound s.params.D s.params.Δ s.params.scopes)
    (sourceSize_pos s) (dimension_le s) (plan_word_le s) using 1
  all_goals ring

theorem plan_cost_le (s : Spec U) :
    SubexpPlanAlphabetBase.totalBound s.params.D s.params.Δ s.params.scopes ≤
      10100 * sourceSize s ^ 4 :=
  PackingBudgetArithmetic.plan_totalBound_le _ _ _ _ (plan_input_le s) s.degree_bound

theorem label_cost_le (s : Spec U) :
    PackingVertexLabels.traceCost s.params.width.length s.params.planList 0 ≤
      21000 * sourceSize s ^ 7 := by
  have hp : ∀ plan ∈ s.params.planList, (PackingVertexLabels.planBytes plan).length ≤
      SubexpPlanAlphabetBase.planWordBound s.params.D s.params.Δ s.params.scopes := by
    intro plan hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    exact SubexpPlanAlphabetBase.planBytes_length_le s.params.D s.params.Δ s.params.scopes
      s.degree_bound v
  have hb := PackingVertexLabels.traceCost_le s.params.width.length s.params.planList 0 _ hp
  rw [PackingFrontend.Params.planList_length] at hb
  exact hb.trans (PackingBudgetArithmetic.label_trace_le _ _ _ _
    (sourceSize_pos s) (dimension_le s) (width_le s) (plan_word_le s))

/-- The label tape starts empty, so its length is bounded by its actual
executed instruction count. No output-length certificate is assumed. -/
theorem label_stream_le (s : Spec U) : s.params.labelStream.length ≤ 21000 * sourceSize s ^ 7 := by
  have hvalid : ∀ plan ∈ s.params.planList, ∀ i ∈ plan, i < s.params.rows.length := by
    intro plan hp i hi
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    rw [s.rows_count]
    exact IncidencePlanSpec.vertexPlan_valid s.params.D s.params.Δ s.params.scopes s.degree_bound v i hi
  obtain ⟨n, rf, hn, ht⟩ := PackingVertexLabels.program_trace s.params.rows s.params.width
    s.params.planList (fun _ => false) 0 [] [] s.rows_width hvalid
  have hg := SequentialProgram.trace_stack_length_le ht (13 : Fin 15)
  have hl : s.params.labelStream.length ≤ n := by
    simpa [PackingFrontend.Params.labelStream, PackingVertexLabels.state,
      StructuredProgram.State.withPC] using hg
  exact (hl.trans hn).trans (label_cost_le s)

theorem type_rows_count (s : Spec U) : s.params.typeRows.length = s.types.values.length := by
  rw [s.type_records, List.length_map]

theorem type_power_count (s : Spec U) :
    s.params.alphabet.length ^ (s.params.Δ + 1) = s.types.values.length := by
  have h := type_rows_count s
  simpa only [PackingFrontend.Params.typeRows, TupleProgram.powerRows_length,
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

theorem frontend_bound_le (s : Spec U) : s.params.bound ≤ 200000 * sourceSize s ^ 7 := by
  have hscope : (SubexpPlanAlphabetBase.scopeBytes s.params.scopes).length ≤ sourceSize s := by
    unfold sourceSize
    omega
  have hd : s.params.Δ ≤ sourceSize s := by have := depth_le s; omega
  have hrows : s.params.rows.flatten.length ≤ sourceSize s := by unfold sourceSize; omega
  apply le_trans ?_ (PackingBudgetArithmetic.frontend_le (sourceSize s) _ _ _ _ _ _ _ _ _ _
    (sourceSize_pos s) hscope (dimension_le s) hd (width_le s) hrows (alphabet_bytes_le s)
    (plan_stream_le s) (label_stream_le s) (type_cost_le s) (type_stream_le s))
  unfold PackingFrontend.Params.bound PackingFrontend.Params.plansBound
    PackingFrontend.Params.labelsBound PackingFrontend.Params.typesBound
  have hp := plan_cost_le s
  have hl := label_cost_le s
  omega

end SubexponentialSAT.Subexp.PackingExecutionBounds

end OAI.Algorithms
