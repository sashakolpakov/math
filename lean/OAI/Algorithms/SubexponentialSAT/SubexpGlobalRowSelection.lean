import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowLookup

namespace OAI.Algorithms

/-! The global row dispatcher follows actual lookup flags and bit comparisons.
This file derives its semantic cases from those concrete executions. -/

namespace SubexponentialSAT.SubexpGlobalRowSelection

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpGlobalRowBranch SubexpGlobalRowLookup

def HighClean (a : Data) : Prop := ∀ i : Fin 288, 270 ≤ i.val → a.stacks i = []

def firstStore (s : Fin 288 → Word) (m : Metadata) : Fin 288 → Word :=
  Function.update (Function.update (Function.update s 271 m.block) 272 m.typeCode) 273 m.rank

def secondStore (s : Fin 288 → Word) (m : Metadata) : Fin 288 → Word :=
  Function.update (Function.update (Function.update s 274 m.block) 275 m.typeCode) 276 m.rank

theorem first_high (a : Data) (ha : HighClean a) :
    ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → a.stacks (firstPorts i) = [] := by
  intro i h0 h1
  fin_cases i <;> simp_all [firstPorts, HighClean]

theorem first_store (a : Data) (records : List (Word × Word)) (v : ℕ) (m : Metadata)
    (hmaster : a.stacks 265 = Subexp.SelectorProgram.rawRecords records)
    (hv : a.stacks 260 = unary v) (ha : HighClean a) :
    (metadataResult firstPorts a records (unary v) m).stacks = firstStore a.stacks m := by
  exact metadataResult_stacks firstPorts firstPorts_injective a records (unary v) m
    hmaster hv (first_high a ha)

theorem firstStore_low (a : Data) (m : Metadata) (i : Fin 288) (hi : i.val < 270) :
    firstStore a.stacks m i = a.stacks i := by
  have h271 : i ≠ 271 := by intro h; subst i; change (271 : ℕ) < 270 at hi; omega
  have h272 : i ≠ 272 := by intro h; subst i; change (272 : ℕ) < 270 at hi; omega
  have h273 : i ≠ 273 := by intro h; subst i; change (273 : ℕ) < 270 at hi; omega
  simp [firstStore, h271, h272, h273]

theorem secondStore_low (s : Fin 288 → Word) (m : Metadata) (i : Fin 288) (hi : i.val < 270) :
    secondStore s m i = s i := by
  have h274 : i ≠ 274 := by intro h; subst i; change (274 : ℕ) < 270 at hi; omega
  have h275 : i ≠ 275 := by intro h; subst i; change (275 : ℕ) < 270 at hi; omega
  have h276 : i ≠ 276 := by intro h; subst i; change (276 : ℕ) < 270 at hi; omega
  simp [secondStore, h274, h275, h276]

/-- A leftover source vertex chooses its identity row by comparing the
two actual unary vertex words. It does not invoke the universal service. -/
theorem leftover_run (a : Data) (records : List (Word × Word)) (v w : ℕ) (rank : Word)
    (hlookup : records.lookup (unary v) = some (Subexp.GlobalBasisMetadata.Metadata.leftover rank).encode)
    (hmaster : a.stacks 265 = Subexp.SelectorProgram.rawRecords records)
    (hv : a.stacks 260 = unary v) (hw : a.stacks 262 = unary w) (ha : HighClean a) :
    ∃ n ≤ 400 * (Subexp.GlobalBasisMetadata.volume records (unary v))^2 +
      18 * v + 9 * w + 28, ∃ b : Data,
      Eval classify n a b ∧ b.regs 5 = false ∧ b.regs 6 = decide (v = w) ∧
      b.stacks = firstStore a.stacks (.leftover rank) := by
  let first := metadataResult firstPorts a records (unary v) (.leftover rank)
  obtain ⟨n, hn, hfirst⟩ := metadata_eval firstPorts firstPorts_injective a records (unary v)
    (.leftover rank) hlookup hmaster hv (first_high a ha)
  have hstore : first.stacks = firstStore a.stacks (.leftover rank) :=
    first_store a records v (.leftover rank) hmaster hv ha
  have hflag : first.regs 4 = false := metadataResult_flag firstPorts a records (unary v)
    (.leftover rank)
  have h270 : first.stacks 270 = [] := by rw [hstore]; simpa [firstStore] using ha 270 (by decide)
  have h284 : first.stacks 284 = [] := by rw [hstore]; simpa [firstStore] using ha 284 (by decide)
  have h285 : first.stacks 285 = [] := by rw [hstore]; simpa [firstStore] using ha 285 (by decide)
  have hv' : first.stacks 260 = unary v := by rw [hstore]; simpa [firstStore] using hv
  have hw' : first.stacks 262 = unary w := by rw [hstore]; simpa [firstStore] using hw
  obtain ⟨m, hm, regs, hc, heq, _⟩ := compare_eval 260 262 first
    (by decide) (by decide) (by decide) (by decide) (by decide) h284 h285 h270
  let middle : Data := ⟨regs, first.stacks⟩
  let last := marked middle false (middle.regs 4)
  have heq' : middle.regs 4 = decide (v = w) := by
    simpa [middle, hv', hw', unary_eq_iff] using heq
  have hrun : Eval classify (n + (m + 2 + 1)) a last :=
    classify_leftover hfirst hflag hc
  refine ⟨n + (m + 2 + 1), ?_, last, hrun, ?_, ?_, ?_⟩
  · simp only [hv', hw', unary, List.length_replicate] at hm
    omega
  · simp [last, marked]
  · simpa [last, marked] using heq'
  · exact hstore

theorem second_run (a : Data) (records : List (Word × Word)) (v w : ℕ)
    (left right : Metadata)
    (hlookup : records.lookup (unary w) = some right.encode)
    (hmaster : a.stacks 265 = Subexp.SelectorProgram.rawRecords records)
    (hv : a.stacks 260 = unary v) (hw : a.stacks 262 = unary w) (ha : HighClean a) :
    let first := metadataResult firstPorts a records (unary v) left
    let second := metadataResult secondPorts first records (unary w) right
    ∃ n ≤ 400 * (Subexp.GlobalBasisMetadata.volume records (unary w))^2,
      Eval (metadata secondPorts) n first second ∧
      second.stacks = secondStore (firstStore a.stacks left) right := by
  let first := metadataResult firstPorts a records (unary v) left
  have hs : first.stacks = firstStore a.stacks left := first_store a records v left hmaster hv ha
  have hm : first.stacks (secondPorts 0) = Subexp.SelectorProgram.rawRecords records := by
    rw [hs]
    simpa [secondPorts, firstStore] using hmaster
  have hq : first.stacks (secondPorts 1) = unary w := by
    rw [hs]
    simpa [secondPorts, firstStore] using hw
  have hwork : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → first.stacks (secondPorts i) = [] := by
    intro i h0 h1
    rw [hs]
    fin_cases i <;> simp_all [secondPorts, firstStore, HighClean]
  obtain ⟨n, hn, he⟩ := metadata_eval secondPorts secondPorts_injective first records (unary w)
    right hlookup hm hq hwork
  refine ⟨n, hn, he, ?_⟩
  have ht := metadataResult_stacks secondPorts secondPorts_injective first records (unary w)
    right hm hq hwork
  calc
    (metadataResult secondPorts first records (unary w) right).stacks =
        secondStore first.stacks right := by
      simpa [secondStore, secondPorts] using ht
    _ = secondStore (firstStore a.stacks left) right :=
      congrArg (fun store => secondStore store right) hs

/-- A selected source and a leftover target produce the zero-row mode after
two actual preserving table lookups. -/
theorem rightLeftover_run (a : Data) (records : List (Word × Word)) (v w : ℕ)
    (block typeCode rank : Word)
    (hl : records.lookup (unary v) = some (Subexp.GlobalBasisMetadata.Metadata.covered block typeCode).encode)
    (hr : records.lookup (unary w) = some (Subexp.GlobalBasisMetadata.Metadata.leftover rank).encode)
    (hmaster : a.stacks 265 = Subexp.SelectorProgram.rawRecords records)
    (hv : a.stacks 260 = unary v) (hw : a.stacks 262 = unary w) (ha : HighClean a) :
    ∃ n ≤ 400 * (Subexp.GlobalBasisMetadata.volume records (unary v))^2 +
      400 * (Subexp.GlobalBasisMetadata.volume records (unary w))^2 + 4, ∃ b : Data,
      Eval classify n a b ∧ b.regs 5 = false ∧ b.regs 6 = false ∧
      b.stacks = secondStore (firstStore a.stacks (.covered block typeCode)) (.leftover rank) := by
  let left := Subexp.GlobalBasisMetadata.Metadata.covered block typeCode
  let right := Subexp.GlobalBasisMetadata.Metadata.leftover rank
  let first := metadataResult firstPorts a records (unary v) left
  let second := metadataResult secondPorts first records (unary w) right
  obtain ⟨n, hn, hfirst⟩ := metadata_eval firstPorts firstPorts_injective a records (unary v)
    left hl hmaster hv (first_high a ha)
  obtain ⟨m, hm, hsecond, hstore⟩ := second_run a records v w left right hr hmaster hv hw ha
  have hf : first.regs 4 = true := metadataResult_flag firstPorts a records (unary v) left
  have hs : second.regs 4 = false := metadataResult_flag secondPorts first records (unary w) right
  let last := marked second false false
  refine ⟨n + (m + (2 + 1) + 1), by omega, last,
    classify_rightLeftover hfirst hf hsecond hs, ?_, ?_, ?_⟩
  · simp [last, marked]
  · simp [last, marked]
  · exact hstore

/-- Different covered blocks also produce the zero-row mode; the block IDs
are compared as actual runtime words, with both originals preserved. -/
theorem differentBlock_run (a : Data) (records : List (Word × Word)) (v w : ℕ)
    (blockLeft typeLeft blockRight typeRight : Word) (hne : blockLeft ≠ blockRight)
    (hl : records.lookup (unary v) = some (Subexp.GlobalBasisMetadata.Metadata.covered blockLeft typeLeft).encode)
    (hr : records.lookup (unary w) = some (Subexp.GlobalBasisMetadata.Metadata.covered blockRight typeRight).encode)
    (hmaster : a.stacks 265 = Subexp.SelectorProgram.rawRecords records)
    (hv : a.stacks 260 = unary v) (hw : a.stacks 262 = unary w) (ha : HighClean a) :
    ∃ n ≤ 400 * (Subexp.GlobalBasisMetadata.volume records (unary v))^2 +
      400 * (Subexp.GlobalBasisMetadata.volume records (unary w))^2 +
      18 * blockLeft.length + 9 * blockRight.length + 30, ∃ b : Data,
      Eval classify n a b ∧ b.regs 5 = false ∧ b.regs 6 = false ∧
      b.stacks = secondStore (firstStore a.stacks (.covered blockLeft typeLeft))
        (.covered blockRight typeRight) := by
  let left := Subexp.GlobalBasisMetadata.Metadata.covered blockLeft typeLeft
  let right := Subexp.GlobalBasisMetadata.Metadata.covered blockRight typeRight
  let first := metadataResult firstPorts a records (unary v) left
  let second := metadataResult secondPorts first records (unary w) right
  obtain ⟨n, hn, hfirst⟩ := metadata_eval firstPorts firstPorts_injective a records (unary v)
    left hl hmaster hv (first_high a ha)
  obtain ⟨m, hm, hsecond, hstore⟩ := second_run a records v w left right hr hmaster hv hw ha
  have hf : first.regs 4 = true := metadataResult_flag firstPorts a records (unary v) left
  have hs : second.regs 4 = true := metadataResult_flag secondPorts first records (unary w) right
  have h270 : second.stacks 270 = [] := by
    rw [hstore]; simpa [secondStore, firstStore] using ha 270 (by decide)
  have h284 : second.stacks 284 = [] := by
    rw [hstore]; simpa [secondStore, firstStore] using ha 284 (by decide)
  have h285 : second.stacks 285 = [] := by
    rw [hstore]; simpa [secondStore, firstStore] using ha 285 (by decide)
  have hleft : second.stacks 271 = blockLeft := by
    rw [hstore]; simp [firstStore, secondStore, left, Subexp.GlobalBasisMetadata.Metadata.block]
  have hright : second.stacks 274 = blockRight := by
    rw [hstore]; simp [secondStore, right, Subexp.GlobalBasisMetadata.Metadata.block]
  obtain ⟨k, hk, regs, hc, heq, _⟩ := compare_eval 271 274 second
    (by decide) (by decide) (by decide) (by decide) (by decide) h284 h285 h270
  let compared : Data := ⟨regs, second.stacks⟩
  have hne' : compared.regs 4 = false := by
    simpa [compared, hleft, hright, hne] using heq
  let last := marked compared false false
  refine ⟨n + (m + ((k + (2 + 1)) + 1) + 1), ?_, last,
    classify_differentBlock hfirst hf hsecond hs hc hne', ?_, ?_, ?_⟩
  · rw [hleft, hright] at hk
    omega
  · simp [last, marked]
  · simp [last, marked]
  · exact hstore

/-- Same-block selection obtains the local incidence slot by scanning the
actual prefix of the scope family. Both types and the one-based slot are
available to the universal source-row program. -/
theorem sameBlock_run (a : Data) (records : List (Word × Word))
    (scopes : List (List ℕ)) (e v w : ℕ) (he : e ≤ scopes.length)
    (block typeLeft typeRight : Word)
    (hl : records.lookup (unary v) =
      some (Subexp.GlobalBasisMetadata.Metadata.covered block typeLeft).encode)
    (hr : records.lookup (unary w) =
      some (Subexp.GlobalBasisMetadata.Metadata.covered block typeRight).encode)
    (hmaster : a.stacks 265 = Subexp.SelectorProgram.rawRecords records)
    (hscopes : a.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (hfactor : a.stacks 261 = unary e)
    (hv : a.stacks 260 = unary v) (hw : a.stacks 262 = unary w) (ha : HighClean a) :
    ∃ n ≤ 400 * (Subexp.GlobalBasisMetadata.volume records (unary v))^2 +
      400 * (Subexp.GlobalBasisMetadata.volume records (unary w))^2 +
      27 * block.length + SubexpIncidenceSlotProgram.budget scopes e v + 30,
      ∃ b : Data, Eval classify n a b ∧ b.regs 5 = true ∧ b.regs 6 = false ∧
        b.stacks = Function.update
          (secondStore (firstStore a.stacks (.covered block typeLeft))
            (.covered block typeRight)) 284
          (unary (SubexpIncidenceSlotProgram.degree scopes e v + 1)) := by
  let left := Subexp.GlobalBasisMetadata.Metadata.covered block typeLeft
  let right := Subexp.GlobalBasisMetadata.Metadata.covered block typeRight
  let first := metadataResult firstPorts a records (unary v) left
  let second := metadataResult secondPorts first records (unary w) right
  obtain ⟨n, hn, hfirst⟩ := metadata_eval firstPorts firstPorts_injective a records (unary v)
    left hl hmaster hv (first_high a ha)
  obtain ⟨m, hm, hsecond, hstore⟩ := second_run a records v w left right hr hmaster hv hw ha
  have hf : first.regs 4 = true := metadataResult_flag firstPorts a records (unary v) left
  have hs : second.regs 4 = true := metadataResult_flag secondPorts first records (unary w) right
  have h270 : second.stacks 270 = [] := by
    rw [hstore]; simpa [secondStore, firstStore] using ha 270 (by decide)
  have h284 : second.stacks 284 = [] := by
    rw [hstore]; simpa [secondStore, firstStore] using ha 284 (by decide)
  have h285 : second.stacks 285 = [] := by
    rw [hstore]; simpa [secondStore, firstStore] using ha 285 (by decide)
  have hleft : second.stacks 271 = block := by
    rw [hstore]; simp [firstStore, secondStore, left, Subexp.GlobalBasisMetadata.Metadata.block]
  have hright : second.stacks 274 = block := by
    rw [hstore]; simp [secondStore, right, Subexp.GlobalBasisMetadata.Metadata.block]
  obtain ⟨k, hk, regs, hc, heq, _⟩ := compare_eval 271 274 second
    (by decide) (by decide) (by decide) (by decide) (by decide) h284 h285 h270
  let compared : Data := ⟨regs, second.stacks⟩
  have heq' : compared.regs 4 = true := by
    simpa [compared, hleft, hright] using heq
  have hscopes' : compared.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes := by
    change second.stacks 256 = _
    rw [hstore]
    simpa [firstStore, secondStore] using hscopes
  have hfactor' : compared.stacks 261 = unary e := by
    change second.stacks 261 = _
    rw [hstore]
    simpa [firstStore, secondStore] using hfactor
  have hvertex' : compared.stacks 260 = unary v := by
    change second.stacks 260 = _
    rw [hstore]
    simpa [firstStore, secondStore] using hv
  have hwork : ∀ i : Fin 13, 3 ≤ i.val → compared.stacks (slotPorts i) = [] := by
    intro i hi
    change second.stacks (slotPorts i) = _
    rw [hstore]
    fin_cases i <;> simp_all [slotPorts, firstStore, secondStore, HighClean]
  obtain ⟨q, hq, rs, hslot⟩ := slot_eval compared scopes e v he
    hscopes' hfactor' hvertex' hwork
  let last := marked (slotResult compared rs scopes e v) true false
  have hlast := slotResult_stacks compared rs scopes e v hscopes' hfactor' hvertex' hwork
  refine ⟨n + (m + ((k + ((q + 2) + 1)) + 1) + 1), ?_, last,
    classify_sameBlock hfirst hf hsecond hs hc heq' hslot, ?_, ?_, ?_⟩
  · rw [hleft, hright] at hk
    omega
  · simp [last, marked]
  · simp [last, marked]
  · change (slotResult compared rs scopes e v).stacks = _
    rw [hlast]
    change Function.update second.stacks 284
      (unary (SubexpIncidenceSlotProgram.degree scopes e v + 1)) = _
    rw [hstore]

theorem cleanup_mem_high (i : Fin 288) (hi : i ∈ cleanupPorts) : 270 ≤ i.val := by
  simp only [cleanupPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The actual cleanup restores the caller's high bank when only the
explicit metadata ports and the emitted code were changed. -/
theorem cleanup_restores (a b : Data) (code : Word) (ha : HighClean a)
    (hframe : ∀ i : Fin 288, i ∉ cleanupPorts →
      b.stacks i = Function.update a.stacks 26 code i) :
    (WorkspaceCleanupProgram.finish 0 1 cleanupPorts b).stacks =
      Function.update a.stacks 26 code := by
  funext i
  by_cases hi : i ∈ cleanupPorts
  · have hn : i ≠ 26 := by
      intro heq
      subst i
      simp [cleanupPorts] at hi
    simp [WorkspaceCleanupProgram.finish_stack, hi, hn, ha i (cleanup_mem_high i hi)]
  · simpa [WorkspaceCleanupProgram.finish_stack, hi] using hframe i hi

def constantPort (one : Bool) : Fin 288 := if one then 132 else 131

theorem constantPort_not_cleanup (one : Bool) : constantPort one ∉ cleanupPorts := by
  cases one <;> decide

/-- A concrete constant branch includes the actual literal writer and high
workspace cleanup. The arbitrary universal program is never executed on
this branch. Only the forward postfix word on26 changes. -/
theorem prepare_constant_eval (universal : Code) (one : Bool) {n : ℕ} (a b : Data)
    (ha : HighClean a) (ha26 : a.stacks 26 = [])
    (hclassify : Eval classify n a b) (h5 : b.regs 5 = false) (h6 : b.regs 6 = one)
    (h284 : b.stacks 284 = []) (h285 : b.stacks 285 = [])
    (hframe : ∀ i : Fin 288, i ∉ cleanupPorts → b.stacks i = a.stacks i) :
    ∃ regs, Eval (prepare universal)
      (n + ((14 * (a.stacks (constantPort one)).length + 18) + 1 + 1) +
        WorkspaceCleanupProgram.cost cleanupPorts b) a
      ⟨regs, Function.update a.stacks 26 (literalWord (a.stacks (constantPort one)))⟩ := by
  have h26 : b.stacks 26 = [] := (hframe 26 (by decide)).trans ha26
  have hconstant : b.stacks (constantPort one) = a.stacks (constantPort one) :=
    hframe _ (constantPort_not_cleanup one)
  obtain ⟨regs, hliteral⟩ := literal_eval (constantPort one) b
    (by cases one <;> decide) (by cases one <;> decide) h26 h284 h285
  let c := literalResult (constantPort one) b regs
  have hsource : Eval (source universal)
      (n + ((14 * (b.stacks (constantPort one)).length + 18) + 1 + 1)) a c := by
    cases one with
    | false => exact hclassify.seq (Eval.ite_false h5 (Eval.ite_false h6 hliteral))
    | true => exact hclassify.seq (Eval.ite_false h5 (Eval.ite_true h6 hliteral))
  have hcost : WorkspaceCleanupProgram.cost cleanupPorts c =
      WorkspaceCleanupProgram.cost cleanupPorts b := by
    simp [WorkspaceCleanupProgram.cost, cleanupPorts, c, literalResult]
  have hstore : (WorkspaceCleanupProgram.finish 0 1 cleanupPorts c).stacks =
      Function.update a.stacks 26 (literalWord (a.stacks (constantPort one))) := by
    apply cleanup_restores a c _ ha
    intro i hi
    by_cases h26i : i = 26
    · subst i
      simp [c, literalResult, hconstant]
    · simp [c, literalResult, h26i, hframe i hi]
  have hrun := prepare_execution universal hsource
  refine ⟨(WorkspaceCleanupProgram.finish 0 1 cleanupPorts c).regs, ?_⟩
  have hfinal : WorkspaceCleanupProgram.finish 0 1 cleanupPorts c =
      ⟨(WorkspaceCleanupProgram.finish 0 1 cleanupPorts c).regs,
        Function.update a.stacks 26 (literalWord (a.stacks (constantPort one)))⟩ := by
    exact congrArg (StructuredProgram.State.mk _) hstore
  rw [hfinal] at hrun
  simpa only [hconstant, hcost] using hrun

theorem firstStore_frame (s : Fin 288 → Word) (m : Metadata) (i : Fin 288)
    (hi : i ∉ cleanupPorts) : firstStore s m i = s i := by
  have h271 : i ≠ 271 := by intro h; subst i; exact hi (by decide)
  have h272 : i ≠ 272 := by intro h; subst i; exact hi (by decide)
  have h273 : i ≠ 273 := by intro h; subst i; exact hi (by decide)
  simp [firstStore, h271, h272, h273]

theorem secondStore_frame (s : Fin 288 → Word) (m : Metadata) (i : Fin 288)
    (hi : i ∉ cleanupPorts) : secondStore s m i = s i := by
  have h274 : i ≠ 274 := by intro h; subst i; exact hi (by decide)
  have h275 : i ≠ 275 := by intro h; subst i; exact hi (by decide)
  have h276 : i ≠ 276 := by intro h; subst i; exact hi (by decide)
  simp [secondStore, h274, h275, h276]

private theorem highClean_tail_values (a : Data) (ha : HighClean a) :
    a.stacks 274 = [] ∧ a.stacks 275 = [] ∧ a.stacks 276 = [] ∧ a.stacks 277 = [] ∧
      a.stacks 278 = [] ∧ a.stacks 279 = [] ∧ a.stacks 280 = [] ∧ a.stacks 281 = [] ∧
      a.stacks 282 = [] ∧ a.stacks 283 = [] ∧ a.stacks 284 = [] ∧ a.stacks 285 = [] ∧
      a.stacks 286 = [] ∧ a.stacks 287 = [] :=
  ⟨ha 274 (by decide), ha 275 (by decide), ha 276 (by decide), ha 277 (by decide),
    ha 278 (by decide), ha 279 (by decide), ha 280 (by decide), ha 281 (by decide),
    ha 282 (by decide), ha 283 (by decide), ha 284 (by decide), ha 285 (by decide),
    ha 286 (by decide), ha 287 (by decide)⟩

theorem cleanup_cost_first (a : Data) (m : Metadata) (regs : Fin 25 → Bool)
    (ha : HighClean a) :
    WorkspaceCleanupProgram.cost cleanupPorts (⟨regs, firstStore a.stacks m⟩ : Data) =
      2 * (m.block.length + m.typeCode.length + m.rank.length) + 51 := by
  obtain ⟨h274,h275,h276,h277,h278,h279,h280,h281,h282,h283,h284,h285,h286,h287⟩ :=
    highClean_tail_values a ha
  simp [WorkspaceCleanupProgram.cost, cleanupPorts, firstStore,
    h274,h275,h276,h277,h278,h279,h280,h281,h282,h283,h284,h285,h286,h287]
  omega

theorem cleanup_cost_second (a : Data) (left right : Metadata) (regs : Fin 25 → Bool)
    (ha : HighClean a) :
    WorkspaceCleanupProgram.cost cleanupPorts
      (⟨regs, secondStore (firstStore a.stacks left) right⟩ : Data) =
      2 * (left.block.length + left.typeCode.length + left.rank.length +
        right.block.length + right.typeCode.length + right.rank.length) + 51 := by
  obtain ⟨_,_,_,h277,h278,h279,h280,h281,h282,h283,h284,h285,h286,h287⟩ :=
    highClean_tail_values a ha
  simp [WorkspaceCleanupProgram.cost, cleanupPorts, firstStore, secondStore,
    h277,h278,h279,h280,h281,h282,h283,h284,h285,h286,h287]
  omega

/-- Fully executed source-code production for an unselected source vertex.
The table lookup, vertex comparison, chosen cached literal and all metadata
cleanup are charged. Only code26 changes, even if the caller has live tables
or partially accumulated rows on other stacks. -/
theorem prepare_leftover_run (universal : Code) (a : Data)
    (records : List (Word × Word)) (v w : ℕ) (rank : Word)
    (hlookup : records.lookup (unary v) =
      some (Subexp.GlobalBasisMetadata.Metadata.leftover rank).encode)
    (hmaster : a.stacks 265 = Subexp.SelectorProgram.rawRecords records)
    (hv : a.stacks 260 = unary v) (hw : a.stacks 262 = unary w)
    (ha : HighClean a) (h26 : a.stacks 26 = []) :
    ∃ n ≤ 400 * (Subexp.GlobalBasisMetadata.volume records (unary v))^2 +
      18 * v + 9 * w + 14 * (a.stacks (constantPort (decide (v = w)))).length +
      2 * rank.length + 99, ∃ regs,
      Eval (prepare universal) n a
        ⟨regs, Function.update a.stacks 26
          (literalWord (a.stacks (constantPort (decide (v = w)))))⟩ := by
  obtain ⟨n, hn, b, he, h5, h6, hb⟩ := leftover_run a records v w rank
    hlookup hmaster hv hw ha
  have h284 : b.stacks 284 = [] := by
    rw [hb]
    simpa [firstStore] using ha 284 (by decide)
  have h285 : b.stacks 285 = [] := by
    rw [hb]
    simpa [firstStore] using ha 285 (by decide)
  have hframe (i : Fin 288) (hi : i ∉ cleanupPorts) : b.stacks i = a.stacks i := by
    rw [hb]
    exact firstStore_frame a.stacks _ i hi
  obtain ⟨regs, hprepare⟩ := prepare_constant_eval universal (decide (v = w)) a b
    ha h26 he h5 h6 h284 h285 hframe
  have hcleanup : WorkspaceCleanupProgram.cost cleanupPorts b = 2 * rank.length + 51 := by
    have heq : b = (⟨b.regs, firstStore a.stacks (.leftover rank)⟩ : Data) :=
      congrArg (StructuredProgram.State.mk b.regs) hb
    rw [heq]
    simpa [Subexp.GlobalBasisMetadata.Metadata.block,
      Subexp.GlobalBasisMetadata.Metadata.typeCode, Subexp.GlobalBasisMetadata.Metadata.rank] using
      cleanup_cost_first a (.leftover rank) b.regs ha
  refine ⟨_, ?_, regs, hprepare⟩
  rw [hcleanup]
  omega

/-- The zero cases share the same real cached-literal and cleanup suffix.
Their two metadata lookups and comparison have already been executed by
the supplied classification trace. -/
theorem prepare_zero_after_run (universal : Code) {n : ℕ} (a b : Data)
    (left right : Metadata) (ha : HighClean a) (h26 : a.stacks 26 = [])
    (hrun : Eval classify n a b) (h5 : b.regs 5 = false) (h6 : b.regs 6 = false)
    (hb : b.stacks = secondStore (firstStore a.stacks left) right) :
    ∃ regs, Eval (prepare universal)
      (n + 14 * (a.stacks 131).length +
        2 * (left.block.length + left.typeCode.length + left.rank.length +
          right.block.length + right.typeCode.length + right.rank.length) + 71) a
      ⟨regs, Function.update a.stacks 26 (literalWord (a.stacks 131))⟩ := by
  have h284 : b.stacks 284 = [] := by
    rw [hb]
    simpa [firstStore, secondStore] using ha 284 (by decide)
  have h285 : b.stacks 285 = [] := by
    rw [hb]
    simpa [firstStore, secondStore] using ha 285 (by decide)
  have hframe (i : Fin 288) (hi : i ∉ cleanupPorts) : b.stacks i = a.stacks i := by
    rw [hb, secondStore_frame _ _ i hi, firstStore_frame _ _ i hi]
  obtain ⟨regs, he⟩ := prepare_constant_eval universal false a b
    ha h26 hrun h5 h6 h284 h285 hframe
  have hcleanup : WorkspaceCleanupProgram.cost cleanupPorts b =
      2 * (left.block.length + left.typeCode.length + left.rank.length +
        right.block.length + right.typeCode.length + right.rank.length) + 51 := by
    have heq : b = (⟨b.regs, secondStore (firstStore a.stacks left) right⟩ : Data) :=
      congrArg (StructuredProgram.State.mk b.regs) hb
    rw [heq]
    exact cleanup_cost_second a left right b.regs ha
  refine ⟨regs, ?_⟩
  change Eval (prepare universal)
    (n + ((14 * (a.stacks 131).length + 18) + 1 + 1) +
      WorkspaceCleanupProgram.cost cleanupPorts b) a
    ⟨regs, Function.update a.stacks 26 (literalWord (a.stacks 131))⟩ at he
  have hcost : n + ((14 * (a.stacks 131).length + 18) + 1 + 1) +
      WorkspaceCleanupProgram.cost cleanupPorts b =
      n + 14 * (a.stacks 131).length +
        2 * (left.block.length + left.typeCode.length + left.rank.length +
          right.block.length + right.typeCode.length + right.rank.length) + 71 := by
    rw [hcleanup]
    omega
  rw [hcost] at he
  exact he

/-- The same-block suffix invokes the actual staged universal program,
then clears the metadata/slot bank. Its premise is an execution of that
fixed program, which the independent source-row compiler must provide. -/
theorem prepare_universal_after_run (universal : Code) {n m : ℕ}
    (a b c : Data) (code : Word) (ha : HighClean a)
    (hclassify : Eval classify n a b) (h5 : b.regs 5 = true)
    (huniversal : Eval universal m b c)
    (hc : c.stacks = Function.update b.stacks 26 code)
    (hframe : ∀ i : Fin 288, i ∉ cleanupPorts → b.stacks i = a.stacks i) :
    ∃ regs, Eval (prepare universal)
      (n + (m + 1) + WorkspaceCleanupProgram.cost cleanupPorts c) a
      ⟨regs, Function.update a.stacks 26 code⟩ := by
  have hs : Eval (source universal) (n + (m + 1)) a c :=
    hclassify.seq (Eval.ite_true h5 huniversal)
  have hstore : (WorkspaceCleanupProgram.finish 0 1 cleanupPorts c).stacks =
      Function.update a.stacks 26 code := by
    apply cleanup_restores a c code ha
    intro i hi
    rw [hc]
    by_cases h26 : i = 26
    · subst i; simp
    · simp [h26, hframe i hi]
  have hrun := prepare_execution universal hs
  refine ⟨(WorkspaceCleanupProgram.finish 0 1 cleanupPorts c).regs, ?_⟩
  have heq : WorkspaceCleanupProgram.finish 0 1 cleanupPorts c =
      ⟨(WorkspaceCleanupProgram.finish 0 1 cleanupPorts c).regs,
        Function.update a.stacks 26 code⟩ :=
    congrArg (StructuredProgram.State.mk _) hstore
  rw [heq] at hrun
  exact hrun

end SubexponentialSAT.SubexpGlobalRowSelection

end OAI.Algorithms
