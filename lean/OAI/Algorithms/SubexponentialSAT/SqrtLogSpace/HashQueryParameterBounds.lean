import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryParameterBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFrontendBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets

/-! Actual trial and accepted queries inherit the width-fixed scalar caps.
Every generic validity and raw-scope premise is discharged from the literal
formula, produced code rows, attained history and physical master words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry ProducedQueryResources

/-- Fixed-before-input scalar caps for the literal trial query. Numeric
values are bounded independently of arbitrary physical padding. -/
theorem trial_numeric_caps (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n inputLength : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
        F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (e : Fin F.length) (d : State 40 896),
        (d.stacks 783).length = HashCandidates.digitWidth F.length →
        BinaryArithmetic.toNat (d.stacks 782) = F.length →
        BinaryArithmetic.toNat (d.stacks 785) = n →
      let q := trialQuery F hm shifts Q rounds word e d
      let S := C * (inputLength + 1) ^ degree
      q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
        1 ≤ S ∧ n ^ 2 ≤ S ∧ (q.input k).incidences ≤ S ∧
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
            (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
          (LeafParametersProgram.Execute.guardedModel (q.input k) padding).val j ≤ S := by
  obtain ⟨C, degree, cutoff₁, hcap⟩ := chosen_scalar_input_cap_of_scope_resources k hk
  obtain ⟨cutoff₂, hscan⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  refine ⟨C, degree, max cutoff₁ cutoff₂, ?_⟩
  intro n inputLength hn hinput B F hv hm hmb shifts Q rounds hr word e d hwidth hmod hamb q S
  have hnpos : 0 < n := by have h := (hscan n (by omega)).1; omega
  have hB : 0 < B := by
    dsimp only [B, SparseBudget.chooseM]
    positivity
  have hvq : q.Valid := by
    apply rawQueryFromRows_valid F _ (some e) (Encoding.encodeNat e.val)
      (d.stacks 783) (d.stacks 782) (d.stacks 785) hnpos
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases Option.some.inj he
      rfl
    · exact hmod
    · exact hamb
  have hqn : ambient q = n := hamb
  have hcl : q.clauses.length = F.length := by
    simp [q, trialQuery, trialRows, rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords]
  obtain ⟨hlen, hmass, harity, _hnd⟩ := HashQueryResources.trial_uniform_resources F hv hnpos hm hB hmb
    shifts Q rounds (CounterPrograms.value word) hr (some e) (Encoding.encodeNat e.val)
    (d.stacks 783) (d.stacks 782) (d.stacks 785)
  have hlen' : q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 := by
    rw [hcl]
    exact hlen
  have hmass' : HighIncidenceProgram.Prepare.mass q.scopeRows ≤
      (3 * n * SparseCode.degreeBound q.clauses.length B +
        (HashSelect.loopCap n q.clauses.length + 1) *
          SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact hmass
  have harity' : ∀ row ∈ q.scopeRows, row.length ≤
      (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact harity
  have hs := (hscan n (by omega)).2.2 q hvq hqn
    (by simpa only [hcl] using hm) (by simpa only [hcl] using hmb) hlen' hmass' harity'
  obtain ⟨hS, hnS, hiS, hvalues⟩ := hcap n inputLength (by omega) hinput q hvq hqn
    (by simpa only [hcl] using hm) (by simpa only [hcl] using hmb) hlen' hmass' harity'
  refine ⟨hvq, hqn, hs.1, hs.2, hS, hnS, hiS, ?_⟩
  intro padding j
  exact ⟨hvalues padding j,
    QueryModelBudgets.serialized_model_values_le (q.input k) padding S (hvalues padding) j⟩

/-- Fixed-before-input scalar caps for the literal accepted query. Numeric
values are bounded independently of arbitrary physical padding. -/
theorem accepted_numeric_caps (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n inputLength : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
        F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (d : State 40 896),
        (d.stacks 783).length = HashCandidates.digitWidth F.length →
        BinaryArithmetic.toNat (d.stacks 782) = F.length →
        BinaryArithmetic.toNat (d.stacks 785) = n →
      let q := acceptedQuery F hm shifts Q rounds d
      let S := C * (inputLength + 1) ^ degree
      q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
        1 ≤ S ∧ n ^ 2 ≤ S ∧ (q.input k).incidences ≤ S ∧
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
            (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
          (LeafParametersProgram.Execute.guardedModel (q.input k) padding).val j ≤ S := by
  obtain ⟨C, degree, cutoff₁, hcap⟩ := chosen_scalar_input_cap_of_scope_resources k hk
  obtain ⟨cutoff₂, hscan⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  refine ⟨C, degree, max cutoff₁ cutoff₂, ?_⟩
  intro n inputLength hn hinput B F hv hm hmb shifts Q rounds hr d hwidth hmod hamb q S
  have hnpos : 0 < n := by have h := (hscan n (by omega)).1; omega
  have hB : 0 < B := by
    dsimp only [B, SparseBudget.chooseM]
    positivity
  have hvq : q.Valid := by
    apply rawQueryFromRows_valid F _ none [false]
      (d.stacks 783) (d.stacks 782) (d.stacks 785) hnpos
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases he
    · exact hmod
    · exact hamb
  have hqn : ambient q = n := hamb
  have hcl : q.clauses.length = F.length := by
    simp [q, acceptedQuery, rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords]
  obtain ⟨hlen, hmass, harity, _hnd⟩ := HashQueryResources.history_uniform_resources F hv hnpos hm hB hmb
    shifts Q rounds hr none [false]
    (d.stacks 783) (d.stacks 782) (d.stacks 785)
  have hlen' : q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 := by
    rw [hcl]
    exact hlen
  have hmass' : HighIncidenceProgram.Prepare.mass q.scopeRows ≤
      (3 * n * SparseCode.degreeBound q.clauses.length B +
        (HashSelect.loopCap n q.clauses.length + 1) *
          SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact hmass
  have harity' : ∀ row ∈ q.scopeRows, row.length ≤
      (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact harity
  have hs := (hscan n (by omega)).2.2 q hvq hqn
    (by simpa only [hcl] using hm) (by simpa only [hcl] using hmb) hlen' hmass' harity'
  obtain ⟨hS, hnS, hiS, hvalues⟩ := hcap n inputLength (by omega) hinput q hvq hqn
    (by simpa only [hcl] using hm) (by simpa only [hcl] using hmb) hlen' hmass' harity'
  refine ⟨hvq, hqn, hs.1, hs.2, hS, hnS, hiS, ?_⟩
  intro padding j
  exact ⟨hvalues padding j,
    QueryModelBudgets.serialized_model_values_le (q.input k) padding S (hvalues padding) j⟩

/-- The actual marked frontend reads only its six source words. The suspended
collector tail and accumulator remain unrestricted in this time bound. -/
theorem trial_frontend_budget :
    ∃ C degree : ℕ, ∀ (n k B wordBound : ℕ) (F : RawCNF n)
      (_hn : 0 < n) (hm : 0 < F.length)
      (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
      (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (d a : State 40 896) (e : Fin F.length) (_tail : List Bool),
      word.length = HashCandidates.payloadWidth F.length (SparseCode.distanceDenom F.length B) →
      (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ wordBound) →
      d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      (d.stacks 783).length = HashCandidates.digitWidth F.length →
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) → d.stacks 767 = [] →
      HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
        (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
          (SparseCode.distanceDenom F.length B) word))) a →
      LeafScopeInputBounds.capacity (trialQuery F hm shifts Q rounds word e d) k ≤
          106 * (HashQueryInputBounds.commonCap n F.length B wordBound + k) ^ 3 ∧
        (trialQuery F hm shifts Q rounds word e d).inputBudget k ≤
          C * (HashQueryInputBounds.commonCap n F.length B wordBound + k + 1) ^ degree := by
  obtain ⟨C, degree, hcost⟩ := query_frontend_cubic_sources_polynomial
  refine ⟨C, degree, ?_⟩
  intro n k B wordBound F hn hm shifts Q rounds hr word d a e tail hword hmasters
    hformula hhistory hwidth hmod hamb hclean hscratch hready
  let S := HashQueryInputBounds.commonCap n F.length B wordBound + k
  have hS : 1 ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hnS : n ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hmS : F.length ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hkS : k ≤ S := by unfold S; omega
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  let staged := LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
    (SparseCode.distanceDenom F.length B) word)
  let input := recordState a tail (Encoding.encodeNat e.val)
  let q := trialQuery F hm shifts Q rounds word e d
  have he := trial_entry F hn hm shifts Q rounds word d a e tail hword hformula hhistory
    hwidth hmod hamb hclean hscratch hready
  have hstage := HashQueryInputBounds.staged_sources_commonCap (NativeLeafSemantics.indexed F)
    shifts Q wordBound d rounds hr hmasters hhistory word
  have hstage' : ∀ i ∈ HashMassStaged.stagedPorts, (staged.stacks i).length ≤ 16 * S ^ 3 := by
    intro i hi
    exact (hstage i hi).trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by unfold S; omega) 3))
  have hrecord := HashQueryInputBounds.record_input_sources staged a S hready hstage'
    tail (Encoding.encodeNat e.val)
  have hw : ∀ i ∈ ([700,701,705,707,708,709] : List (Fin 768)),
      ((LeafProgram.Query.markedInput (HighMarkedFrontend.project input)).stacks i).length ≤ 16 * S ^ 3 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [LeafProgram.Query.markedInput_frame _ 700 (by decide) (by decide) (by decide)]
      change (input.stacks 700).length ≤ 16 * S ^ 3
      exact hrecord 700 (by decide)
    · rw [LeafProgram.Query.markedInput_frame _ 701 (by decide) (by decide) (by decide)]
      change (input.stacks 701).length ≤ 16 * S ^ 3
      exact hrecord 701 (by decide)
    · rw [LeafProgram.Query.markedInput_index _ (he.clean 699 (by decide) (by decide))
        (he.clean 705 (by decide) (by decide)), List.length_reverse]
      change (input.stacks 321).length ≤ 16 * S ^ 3
      rw [he.index]
      change (Encoding.encodeNat e.val).reverse.length ≤ 16 * S ^ 3
      rw [List.length_reverse, Encoding.length_encodeNat]
      have hei := e.isLt
      omega
    · rw [LeafProgram.Query.markedInput_frame _ 707 (by decide) (by decide) (by decide)]
      change (input.stacks 707).length ≤ 16 * S ^ 3
      exact hrecord 707 (by decide)
    · rw [LeafProgram.Query.markedInput_frame _ 708 (by decide) (by decide) (by decide)]
      change (input.stacks 708).length ≤ 16 * S ^ 3
      exact hrecord 708 (by decide)
    · rw [LeafProgram.Query.markedInput_frame _ 709 (by decide) (by decide) (by decide)]
      change (input.stacks 709).length ≤ 16 * S ^ 3
      exact hrecord 709 (by decide)
  have hnq : BinaryArithmetic.toNat q.ambient = n := hamb
  have hcapacity := query_capacity_of_sources q k (16 * S ^ 3)
    (LeafProgram.Query.markedInput (HighMarkedFrontend.project input)) he.frontend hw
  rw [hnq] at hcapacity
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  refine ⟨by change LeafScopeInputBounds.capacity q k ≤ 106 * S ^ 3; omega, ?_⟩
  exact hcost q k S _ he.valid he.frontend (by rw [hnq]; exact hnS) hkS hw


/-- The final unmarked frontend receives only the attained history. Its
capacity and running-time envelope use actual source bytes, never query time. -/
theorem accepted_frontend_budget :
    ∃ C degree : ℕ, ∀ (n k B wordBound : ℕ) (F : RawCNF n)
      (_hn : 0 < n) (hm : 0 < F.length)
      (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
      (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ d : State 40 896,
      (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ wordBound) →
      d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      (d.stacks 783).length = HashCandidates.digitWidth F.length →
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) →
      LeafScopeInputBounds.capacity (acceptedQuery F hm shifts Q rounds d) k ≤
          106 * (HashQueryInputBounds.commonCap n F.length B wordBound + k) ^ 3 ∧
        (acceptedQuery F hm shifts Q rounds d).inputBudget k ≤
          C * (HashQueryInputBounds.commonCap n F.length B wordBound + k + 1) ^ degree := by
  obtain ⟨C, degree, hcost⟩ := query_frontend_cubic_sources_polynomial
  refine ⟨C, degree, ?_⟩
  intro n k B wordBound F hn hm shifts Q rounds hr d hmasters hformula hhistory
    hwidth hmod hamb hclean
  let S := HashQueryInputBounds.commonCap n F.length B wordBound + k
  have hS : 1 ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hnS : n ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hkS : k ≤ S := by unfold S; omega
  have hwS : wordBound ≤ S := by unfold S HashQueryInputBounds.commonCap; omega
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  let input := AcceptedQueryStage.staged d
  let q := acceptedQuery F hm shifts Q rounds d
  have he := accepted_entry F hn hm shifts Q rounds d hformula hhistory hwidth hmod hamb hclean
  have hsources := AcceptedQueryStage.staged_sources d
  obtain ⟨hT, hrows, hdegree, hdepth, hwidth', hrounds, _hw⟩ :=
    HashQueryInputBounds.commonCap_bounds n F.length B wordBound
  have hhistoryBound := (HashQueryInputBounds.serialized_bounds (NativeLeafSemantics.indexed F)
    shifts Q _ hT hrows hdegree hdepth hwidth' hrounds rounds 0 hr).2.1
  have hhistoryBound' : (d.stacks 777).length ≤ 16 * S ^ 3 := by
    rw [hhistory]
    have hp : (HashQueryInputBounds.commonCap n F.length B wordBound) ^ 3 ≤ S ^ 3 :=
      Nat.pow_le_pow_left (by unfold S; omega) 3
    omega
  have hw : ∀ i ∈ ([700,701,705,707,708,709] : List (Fin 768)),
      ((LeafProgram.Query.unmarkedInput (HighMarkedFrontend.project input)).stacks i).length ≤ 16 * S ^ 3 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [LeafProgram.Query.unmarkedInput_frame _ 700 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 700).length ≤ 16 * S ^ 3
      rw [hsources.1]
      have h := hmasters 784 (by decide)
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 701 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 701).length ≤ 16 * S ^ 3
      rw [hsources.2.1]
      exact hhistoryBound'
    · rw [LeafProgram.Query.unmarkedInput_index _ he.index_empty]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 707 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 707).length ≤ 16 * S ^ 3
      rw [hsources.2.2.1]
      have h := hmasters 782 (by decide)
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 708 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 708).length ≤ 16 * S ^ 3
      rw [hsources.2.2.2.1]
      have h := hmasters 783 (by decide)
      omega
    · rw [LeafProgram.Query.unmarkedInput_frame _ 709 (by decide) (by decide)]
      change ((AcceptedQueryStage.staged d).stacks 709).length ≤ 16 * S ^ 3
      rw [hsources.2.2.2.2]
      have h := hmasters 785 (by decide)
      omega
  have hnq : BinaryArithmetic.toNat q.ambient = n := hamb
  have hcapacity := query_capacity_of_sources q k (16 * S ^ 3)
    (LeafProgram.Query.unmarkedInput (HighMarkedFrontend.project input)) he.frontend hw
  rw [hnq] at hcapacity
  refine ⟨by change LeafScopeInputBounds.capacity q k ≤ 106 * S ^ 3; omega, ?_⟩
  exact hcost q k S _ he.valid he.frontend (by rw [hnq]; exact hnS) hkS hw


open CostAssembly MulticolorTypes

/-- The same literal trial query and actual complete output alphabet
inherit the original resource envelope. All constants and the cutoff precede
the formula, attained history, candidate, mark and physical parameter words. -/
theorem trial_envelope (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
        F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (mark : Fin F.length) (state : State 40 896),
        (state.stacks 783).length = HashCandidates.digitWidth F.length →
        BinaryArithmetic.toNat (state.stacks 782) = F.length →
        BinaryArithmetic.toNat (state.stacks 785) = n →
      let q := trialQuery F hm shifts Q rounds word mark state
      q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
        ∀ (hg : LeafParametersProgram.Guard (q.input k))
          (a : Word (problem q k hg).r (problem q k hg).Q)
          (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
          (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
          let p := ofPacking q k B C d (2 * (k - 1) + 1) e hg a tail
          Bounds (2 * (k - 1) + 1) (4 * k + 3) (9 * e + 8) n p ∧
          (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
            (18 : ℝ) ^ power * (2 : ℝ) ^
              ((1 + (power : ℝ) * exponentConstant k (4 * k + 3)) * Statement.runtimeScale n) := by
  obtain ⟨cutoff, hbound⟩ := QueryEnvelopeBudgets.chosen_ofPacking_cutoff k C d e power ordinaryPower hk
  refine ⟨max cutoff 1, ?_⟩
  intro n hn B F hv hm hmb shifts Q rounds hr word mark state hwidth hmod hamb q
  have hnpos : 0 < n := by omega
  have hB : 0 < B := by
    dsimp only [B, SparseBudget.chooseM]
    positivity
  have hvq : q.Valid := by
    apply rawQueryFromRows_valid F _ (some mark) (Encoding.encodeNat mark.val)
      (state.stacks 783) (state.stacks 782) (state.stacks 785) hnpos
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases Option.some.inj he
      rfl
    · exact hmod
    · exact hamb
  have hqn : ambient q = n := hamb
  have hcl : q.clauses.length = F.length := by
    simp [q, trialQuery, trialRows, rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords]
  obtain ⟨hlen, hmass, harity, _hnd⟩ := HashQueryResources.trial_uniform_resources F hv hnpos hm hB hmb
    shifts Q rounds (CounterPrograms.value word) hr (some mark) (Encoding.encodeNat mark.val)
    (state.stacks 783) (state.stacks 782) (state.stacks 785)
  have hlen' : q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 := by
    rw [hcl]
    exact hlen
  have hmass' : HighIncidenceProgram.Prepare.mass q.scopeRows ≤
      (3 * n * SparseCode.degreeBound q.clauses.length B +
        (HashSelect.loopCap n q.clauses.length + 1) *
          SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact hmass
  have harity' : ∀ row ∈ q.scopeRows, row.length ≤
      (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact harity
  exact ⟨hvq, hqn, hbound n (by omega) q hvq hqn
    (by simpa only [hcl] using hm) (by simpa only [hcl] using hmb) hlen' hmass' harity'⟩

/-- The same literal accepted query and actual complete output alphabet
inherit the original resource envelope. All constants and the cutoff precede
the formula, attained history, candidate, mark and physical parameter words. -/
theorem accepted_envelope (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
        F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (state : State 40 896),
        (state.stacks 783).length = HashCandidates.digitWidth F.length →
        BinaryArithmetic.toNat (state.stacks 782) = F.length →
        BinaryArithmetic.toNat (state.stacks 785) = n →
      let q := acceptedQuery F hm shifts Q rounds state
      q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
        ∀ (hg : LeafParametersProgram.Guard (q.input k))
          (a : Word (problem q k hg).r (problem q k hg).Q)
          (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
          (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
          let p := ofPacking q k B C d (2 * (k - 1) + 1) e hg a tail
          Bounds (2 * (k - 1) + 1) (4 * k + 3) (9 * e + 8) n p ∧
          (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
            (18 : ℝ) ^ power * (2 : ℝ) ^
              ((1 + (power : ℝ) * exponentConstant k (4 * k + 3)) * Statement.runtimeScale n) := by
  obtain ⟨cutoff, hbound⟩ := QueryEnvelopeBudgets.chosen_ofPacking_cutoff k C d e power ordinaryPower hk
  refine ⟨max cutoff 1, ?_⟩
  intro n hn B F hv hm hmb shifts Q rounds hr state hwidth hmod hamb q
  have hnpos : 0 < n := by omega
  have hB : 0 < B := by
    dsimp only [B, SparseBudget.chooseM]
    positivity
  have hvq : q.Valid := by
    apply rawQueryFromRows_valid F _ none [false]
      (state.stacks 783) (state.stacks 782) (state.stacks 785) hnpos
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases he
    · exact hmod
    · exact hamb
  have hqn : ambient q = n := hamb
  have hcl : q.clauses.length = F.length := by
    simp [q, acceptedQuery, rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords]
  obtain ⟨hlen, hmass, harity, _hnd⟩ := HashQueryResources.history_uniform_resources F hv hnpos hm hB hmb
    shifts Q rounds hr none [false]
    (state.stacks 783) (state.stacks 782) (state.stacks 785)
  have hlen' : q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 := by
    rw [hcl]
    exact hlen
  have hmass' : HighIncidenceProgram.Prepare.mass q.scopeRows ≤
      (3 * n * SparseCode.degreeBound q.clauses.length B +
        (HashSelect.loopCap n q.clauses.length + 1) *
          SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact hmass
  have harity' : ∀ row ∈ q.scopeRows, row.length ≤
      (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact harity
  exact ⟨hvq, hqn, hbound n (by omega) q hvq hqn
    (by simpa only [hcl] using hm) (by simpa only [hcl] using hmb) hlen' hmass' harity'⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds
