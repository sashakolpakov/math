import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorPacketCoordinates
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-! Build factor-row packets from raw binary labels, a reusable incidence
prefix list, and the complete Lagrange cache. Both orders are restored by
actual record-reversal programs. -/

namespace SubexponentialSAT.Subexp.FactorPacketRows

open BitProgram StructuredCalls
open FactorPacketCoordinates (Word Prefix prefixBytes cacheBytes coordinate)

abbrev Data := State 8 22

structure RawRow where
  value : Word
  labels : List Word

def rawRowBytes (row : RawRow) : Word :=
  Encoding.frame row.value ++ Encoding.encodeList id row.labels

def prefixStream (prefixes : List Prefix) : Word := Encoding.encodeList prefixBytes prefixes

def pairs (prefixes : List Prefix) (row : RawRow) : List (Word × Prefix) :=
  row.labels.zip prefixes

def blueprintRow (cache : List (List Word)) (prefixes : List Prefix) (row : RawRow) :
    FactorBlueprint.Row :=
  ⟨row.value, (pairs prefixes row).map (coordinate cache)⟩

def Valid (cache : List (List Word)) (prefixes : List Prefix) (row : RawRow) : Prop :=
  row.labels.length = prefixes.length ∧
    ∀ label ∈ row.labels, CounterPrograms.value label < cache.length

theorem valid_pairs (cache : List (List Word)) (prefixes : List Prefix) (row : RawRow)
    (h : Valid cache prefixes row) :
    ∀ pair ∈ pairs prefixes row, CounterPrograms.value pair.1 < cache.length := by
  intro pair hp
  exact h.2 pair.1 (List.of_mem_zip hp).1

private theorem encodeList_map {A B : Type*} (encode : B → Word) (f : A → B) (xs : List A) :
    Encoding.encodeList encode (xs.map f) = Encoding.encodeList (encode ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, Function.comp_apply, ih]

private theorem encodeList_id_map {A : Type*} (encode : A → Word) (xs : List A) :
    Encoding.encodeList id (xs.map encode) = Encoding.encodeList encode xs := by
  simpa only [Function.comp_def, id_eq] using encodeList_map id encode xs

theorem pairs_streams (prefixes : List Prefix) (row : RawRow)
    (h : row.labels.length = prefixes.length) :
    FactorPacketCoordinates.labelsBytes (pairs prefixes row) = Encoding.encodeList id row.labels ∧
    FactorPacketCoordinates.prefixesBytes (pairs prefixes row) = prefixStream prefixes := by
  have hf := List.map_fst_zip (l₁ := row.labels) (l₂ := prefixes) (Nat.le_of_eq h)
  have hs := List.map_snd_zip (l₁ := row.labels) (l₂ := prefixes) (Nat.le_of_eq h.symm)
  constructor
  · simpa only [pairs, FactorPacketCoordinates.labelsBytes, encodeList_map,
      Function.comp_def, id_eq] using congrArg (Encoding.encodeList id) hf
  · simpa only [pairs, FactorPacketCoordinates.prefixesBytes, prefixStream, encodeList_map,
      Function.comp_def] using congrArg (Encoding.encodeList prefixBytes) hs

structure View where
  cache : Word
  master : Word
  source : Word
  labels : Word
  coefficient : Word
  prefixCursor : Word
  coordinates : Word
  forward : Word
  rowAcc : Word
  output : Word
  payload : Word

def store (v : View) : Fin 22 → Word := fun i =>
  if i = 7 then v.cache else if i = 11 then v.coordinates else if i = 12 then v.master
  else if i = 13 then v.source else if i = 14 then v.labels else if i = 15 then v.coefficient
  else if i = 16 then v.prefixCursor else if i = 18 then v.forward else if i = 19 then v.rowAcc
  else if i = 20 then v.output else if i = 21 then v.payload else []

def state (regs : Fin 8 → Bool) (v : View) : Data := ⟨regs, store v⟩

@[simp] theorem store_cache (v : View) : store v 7 = v.cache := rfl
@[simp] theorem store_coordinates (v : View) : store v 11 = v.coordinates := rfl
@[simp] theorem store_master (v : View) : store v 12 = v.master := rfl
@[simp] theorem store_source (v : View) : store v 13 = v.source := rfl
@[simp] theorem store_labels (v : View) : store v 14 = v.labels := rfl
@[simp] theorem store_coefficient (v : View) : store v 15 = v.coefficient := rfl
@[simp] theorem store_prefixCursor (v : View) : store v 16 = v.prefixCursor := rfl
@[simp] theorem store_forward (v : View) : store v 18 = v.forward := rfl
@[simp] theorem store_rowAcc (v : View) : store v 19 = v.rowAcc := rfl
@[simp] theorem store_output (v : View) : store v 20 = v.output := rfl
@[simp] theorem store_payload (v : View) : store v 21 = v.payload := rfl

@[simp] theorem update_coordinates (v : View) (w : Word) :
    Function.update (store v) 11 w = store {v with coordinates := w} := by
  funext i; by_cases h : i = 11 <;> simp [store, h]
@[simp] theorem update_source (v : View) (w : Word) :
    Function.update (store v) 13 w = store {v with source := w} := by
  funext i; by_cases h : i = 13 <;> simp [store, h]
@[simp] theorem update_labels (v : View) (w : Word) :
    Function.update (store v) 14 w = store {v with labels := w} := by
  funext i; by_cases h : i = 14 <;> simp [store, h]
@[simp] theorem update_coefficient (v : View) (w : Word) :
    Function.update (store v) 15 w = store {v with coefficient := w} := by
  funext i; by_cases h : i = 15 <;> simp [store, h]
@[simp] theorem update_prefixCursor (v : View) (w : Word) :
    Function.update (store v) 16 w = store {v with prefixCursor := w} := by
  funext i; by_cases h : i = 16 <;> simp [store, h]
@[simp] theorem update_forward (v : View) (w : Word) :
    Function.update (store v) 18 w = store {v with forward := w} := by
  funext i; by_cases h : i = 18 <;> simp [store, h]
@[simp] theorem update_rowAcc (v : View) (w : Word) :
    Function.update (store v) 19 w = store {v with rowAcc := w} := by
  funext i; by_cases h : i = 19 <;> simp [store, h]
@[simp] theorem update_output (v : View) (w : Word) :
    Function.update (store v) 20 w = store {v with output := w} := by
  funext i; by_cases h : i = 20 <;> simp [store, h]
@[simp] theorem update_payload (v : View) (w : Word) :
    Function.update (store v) 21 w = store {v with payload := w} := by
  funext i; by_cases h : i = 21 <;> simp [store, h]

private theorem embed_restricted {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 22)
    (hr : Function.Injective register) (hs : Function.Injective stack) (d : Data) :
    embedState register stack d ⟨d.regs ∘ register, d.stacks ∘ stack⟩ = d := by
  apply embedState_eq_of_ports _ _ _ _ _ hr hs
  all_goals intros; rfl

private theorem embed_stacks {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 22)
    (hs : Function.Injective stack) (frame : Data) (source : State r s)
    (target : Fin 22 → Word)
    (hp : ∀ i, target (stack i) = source.stacks i)
    (hf : ∀ i, (¬ ∃ j, stack j = i) → target i = frame.stacks i) :
    embedState register stack frame source =
      (⟨(embedState register stack frame source).regs, target⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    by_cases h : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_stack _ _ _ _ hs j).trans (hp j).symm
    · exact (embedState_stack_frame _ _ _ _ _ h).trans (hf i h).symm

def smallRegs : Fin 3 → Fin 8 := Fin.castAdd 5
theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _

abbrev reverseAt (p : Fin 4 ↪ Fin 22) : Cmd 8 22 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram smallRegs p)

theorem reverseAt_eval (p : Fin 4 ↪ Fin 22) (d : Data) (records acc : List Word)
    (h0 : d.stacks (p 0) = Encoding.encodeList id records)
    (h2 : d.stacks (p 2) = Encoding.encodeList id acc) (h3 : d.stacks (p 3) = []) :
    ∃ t ≤ 10 * (Encoding.encodeList id records).length, ∃ rf,
      Eval (reverseAt p) t d
        ⟨rf, Function.update (Function.update d.stacks (p 0) []) (p 2)
          (Encoding.encodeList id (records.reverse ++ acc))⟩ := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (Encoding.encodeList id records) (d.stacks (p 1)) (Encoding.encodeList id acc) []
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks (p 1))
    (Encoding.encodeList id (records.reverse ++ acc)) []
  have ha : a = ⟨d.regs ∘ smallRegs, d.stacks ∘ p⟩ := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [a, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, h0, h2, h3]
  obtain ⟨t, ht, htrace⟩ := SubexpNormalizeProgram.reverseRecords_runsIn
    records acc [] (d.stacks (p 1)) (d.regs 0) (d.regs 1) (d.regs 2)
  simp only [List.append_nil] at htrace
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram smallRegs p d
    smallRegs_injective p.injective htrace
  change Eval (reverseAt p) t (embedState smallRegs p d a) (embedState smallRegs p d b) at he
  rw [ha, embed_restricted _ _ smallRegs_injective p.injective] at he
  have hb := embed_stacks smallRegs p p.injective d b
    (Function.update (Function.update d.stacks (p 0) []) (p 2)
      (Encoding.encodeList id (records.reverse ++ acc)))
    (by intro i; fin_cases i <;> simp [b, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple, p.injective.eq_iff, h3])
    (by
      intro i hi
      have h0' : i ≠ p 0 := fun h => hi ⟨0, h.symm⟩
      have h2' : i ≠ p 2 := fun h => hi ⟨2, h.symm⟩
      simp [h0', h2'])
  rw [hb] at he
  exact ⟨t, ht, _, he⟩

abbrev emitAt (p : Fin 4 ↪ Fin 22) : Cmd 8 22 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram smallRegs p)

theorem emitAt_eval (p : Fin 4 ↪ Fin 22) (d : Data) (bits : Word)
    (h3 : d.stacks (p 3) = bits.reverse) :
    ∃ rf, Eval (emitAt p) (5 * bits.length + 7) d
      ⟨rf, Function.update (Function.update d.stacks (p 3) []) (p 2)
        (TupleProgram.prependRecord bits (d.stacks (p 2)))⟩ := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks (p 0)) (d.stacks (p 1)) (d.stacks (p 2)) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks (p 0)) (d.stacks (p 1)) (TupleProgram.prependRecord bits (d.stacks (p 2))) []
  have ha : a = ⟨d.regs ∘ smallRegs, d.stacks ∘ p⟩ := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [a, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, h3]
  have htrace := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks (p 0))
    (d.stacks (p 1)) (d.stacks (p 2)) (d.regs 0) (d.regs 1) (d.regs 2)
  have he := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram smallRegs p d
    smallRegs_injective p.injective htrace
  change Eval (emitAt p) _ (embedState smallRegs p d a) (embedState smallRegs p d b) at he
  rw [ha, embed_restricted _ _ smallRegs_injective p.injective] at he
  have hb := embed_stacks smallRegs p p.injective d b
    (Function.update (Function.update d.stacks (p 3) []) (p 2)
      (TupleProgram.prependRecord bits (d.stacks (p 2))))
    (by intro i; fin_cases i <;> simp [b, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple, p.injective.eq_iff])
    (by
      intro i hi
      have h3' : i ≠ p 3 := fun h => hi ⟨3, h.symm⟩
      have h2' : i ≠ p 2 := fun h => hi ⟨2, h.symm⟩
      simp [h3', h2'])
  rw [hb] at he
  exact ⟨_, he⟩

abbrev readRow : Cmd 8 22 := SubexpInputFrames.readField 13 21 (by decide)
abbrev restoreRow : Cmd 8 22 := .call (StackRoutines.transferProgram 21 14 0 1)
abbrev readValue : Cmd 8 22 := SubexpInputFrames.readField 14 15 (by decide)
abbrev copyPrefixes : Cmd 8 22 := .call (StackRoutines.copyProgram 12 16 4 0 1)

theorem readRow_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval readRow (6 * bits.length + 4)
      (state regs {v with source := Encoding.frame bits ++ tail, payload := []})
      (state rf {v with source := tail, payload := bits.reverse}) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 13 21 (by decide)
    (state regs {v with source := Encoding.frame bits ++ tail, payload := []}) bits tail rfl rfl
  have heq : e = state e.regs {v with source := tail, payload := bits.reverse} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_source, update_payload] using hs
  exact ⟨_, by rw [heq] at he; exact he⟩

theorem restoreRow_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval restoreRow (3 * bits.length + 3)
      (state regs {v with labels := [], payload := bits.reverse})
      (state (readRegs regs 0 1 none) {v with labels := bits, payload := []}) := by
  have h := TupleProgram.transfer_eval (21 : Fin 22) 14 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with labels := [], payload := bits.reverse})
  simpa only [state, StackRoutines.transferStacks, store_payload, store_labels,
    List.length_reverse, List.reverse_reverse, List.append_nil,
    update_payload, update_labels] using h

theorem readValue_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval readValue (6 * bits.length + 4)
      (state regs {v with labels := Encoding.frame bits ++ tail, coefficient := []})
      (state rf {v with labels := tail, coefficient := bits.reverse}) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 14 15 (by decide)
    (state regs {v with labels := Encoding.frame bits ++ tail, coefficient := []}) bits tail rfl rfl
  have heq : e = state e.regs {v with labels := tail, coefficient := bits.reverse} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_labels, update_coefficient] using hs
  exact ⟨_, by rw [heq] at he; exact he⟩

theorem copyPrefixes_eval (regs : Fin 8 → Bool) (v : View) :
    Eval copyPrefixes (7 * v.master.length + 5)
      (state regs {v with prefixCursor := []})
      (state (readRegs regs 0 1 none) {v with prefixCursor := v.master}) := by
  have h := TupleProgram.copy_eval (12 : Fin 22) 16 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) (state regs {v with prefixCursor := []}) rfl
  simpa only [state, StackRoutines.copyStacks, store_master, store_prefixCursor,
    List.append_nil, update_prefixCursor] using h

def coordinatesPorts : Fin 14 → Fin 22 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 16]
theorem coordinatesPorts_injective : Function.Injective coordinatesPorts := by decide

abbrev makeCoordinates : Cmd 8 22 :=
  .call (ProgramLinking.liftProgram FactorPacketCoordinates.program id coordinatesPorts)

private theorem embed_coordinates (regs oldRegs : Fin 8 → Bool) (v : View)
    (cache labels prefixes acc : Word) :
    embedState id coordinatesPorts (state oldRegs {v with cache := cache})
      (FactorPacketCoordinates.resting regs cache labels prefixes acc) =
      state regs {v with cache := cache, labels := labels, prefixCursor := prefixes, coordinates := acc} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id coordinatesPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨12, h.symm⟩
    have h16 : i ≠ 16 := fun h => hi ⟨13, h.symm⟩
    simp only [state, store, h11, h14, h16, ite_false]

theorem makeCoordinates_eval (regs : Fin 8 → Bool) (v : View) (cache : List (List Word))
    (ps : List (Word × Prefix))
    (valid : ∀ p ∈ ps, CounterPrograms.value p.1 < cache.length) :
    ∃ t ≤ FactorPacketCoordinates.budget cache ps + 4, ∃ rf,
      Eval makeCoordinates t
        (state regs {v with
          cache := cacheBytes cache
          labels := FactorPacketCoordinates.labelsBytes ps
          prefixCursor := FactorPacketCoordinates.prefixesBytes ps
          coordinates := [false]})
        (state rf {v with
          cache := cacheBytes cache
          labels := []
          prefixCursor := []
          coordinates := Encoding.encodeList FactorBlueprint.encodeCoordinate
            ((ps.map (coordinate cache)).reverse)}) := by
  obtain ⟨rf, t, ht, htrace⟩ := FactorPacketCoordinates.program_runsIn cache ps valid regs [] [] []
  have he := eval_call_lifted FactorPacketCoordinates.program id coordinatesPorts
    (state regs {v with cache := cacheBytes cache}) Function.injective_id
    coordinatesPorts_injective htrace
  simp only [List.append_nil, embed_coordinates, Encoding.encodeList] at he
  exact ⟨t, ht, rf, he⟩

def coordinateReversePorts : Fin 4 ↪ Fin 22 := ⟨![11, 0, 18, 1], by decide⟩
def rowReversePorts : Fin 4 ↪ Fin 22 := ⟨![19, 0, 20, 1], by decide⟩
def rowEmitPorts : Fin 4 ↪ Fin 22 := ⟨![13, 16, 19, 21], by decide⟩

@[simp] theorem coordinateReversePorts_zero : coordinateReversePorts 0 = 11 := rfl
@[simp] theorem coordinateReversePorts_two : coordinateReversePorts 2 = 18 := rfl
@[simp] theorem rowReversePorts_zero : rowReversePorts 0 = 19 := rfl
@[simp] theorem rowReversePorts_two : rowReversePorts 2 = 20 := rfl
@[simp] theorem rowEmitPorts_two : rowEmitPorts 2 = 19 := rfl
@[simp] theorem rowEmitPorts_three : rowEmitPorts 3 = 21 := rfl

abbrev reverseCoordinates : Cmd 8 22 := reverseAt coordinateReversePorts
abbrev reverseRows : Cmd 8 22 := reverseAt rowReversePorts

theorem reverseCoordinates_eval (regs : Fin 8 → Bool) (v : View)
    (coordinates : List FactorBlueprint.Coordinate) :
    ∃ t ≤ 10 * (Encoding.encodeList FactorBlueprint.encodeCoordinate coordinates.reverse).length, ∃ rf,
      Eval reverseCoordinates t
        (state regs {v with
          coordinates := Encoding.encodeList FactorBlueprint.encodeCoordinate coordinates.reverse
          forward := [false]})
        (state rf {v with
          coordinates := []
          forward := Encoding.encodeList FactorBlueprint.encodeCoordinate coordinates}) := by
  obtain ⟨t, ht, rf, he⟩ := reverseAt_eval coordinateReversePorts
    (state regs {v with
      coordinates := Encoding.encodeList FactorBlueprint.encodeCoordinate coordinates.reverse
      forward := [false]}) (coordinates.reverse.map FactorBlueprint.encodeCoordinate) []
    (by rw [encodeList_map]; rfl) rfl rfl
  rw [encodeList_id_map] at ht
  have hrev : (coordinates.reverse.map FactorBlueprint.encodeCoordinate).reverse =
      coordinates.map FactorBlueprint.encodeCoordinate := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [hrev, List.append_nil, encodeList_id_map] at he
  exact ⟨t, ht, rf, by simpa only [state, coordinateReversePorts_zero, coordinateReversePorts_two, update_coordinates, update_forward] using he⟩

def valuePorts : RecordPrograms.Ports 8 22 :=
  ⟨0, 1, 2, 15, 18, by decide, by decide, by decide, by decide⟩

abbrev prependValue : Cmd 8 22 :=
  .seq (TupleProgram.pushConst 18 0 false) (TupleProgram.escape valuePorts)

theorem prependValue_eval (regs : Fin 8 → Bool) (v : View) (bits body : Word) :
    ∃ rf, Eval prependValue (5 * bits.length + 5)
      (state regs {v with coefficient := bits.reverse, forward := body})
      (state rf {v with coefficient := [], forward := Encoding.frame bits ++ body}) := by
  let a := state regs {v with coefficient := bits.reverse, forward := body}
  let b := TupleProgram.pushedState (18 : Fin 22) (0 : Fin 8) false a
  have h1 := TupleProgram.pushConst_eval (18 : Fin 22) (0 : Fin 8) false a
  have h2 := TupleProgram.escape_eval_state valuePorts b
  have heq : TupleProgram.escapedState valuePorts b =
      state (TupleProgram.escapedState valuePorts b).regs
        {v with coefficient := [], forward := Encoding.frame bits ++ body} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simp only [ valuePorts, b, a, state,
        store_coefficient, store_forward, update_forward, update_coefficient,
        List.reverse_reverse, TupleProgram.frame_eq_escaped, List.append_assoc, List.singleton_append]
  rw [heq] at h2
  have hlen : (b.stacks valuePorts.source).length = bits.length := by
    simp [b, a, state, valuePorts, store]
  rw [hlen] at h2
  refine ⟨(TupleProgram.escapedState valuePorts b).regs, ?_⟩
  have hcost : 2 + (5 * bits.length + 3) = 5 * bits.length + 5 := by omega
  simpa only [prependValue, hcost, a] using h1.seq h2

abbrev emitRow : Cmd 8 22 := .seq (.call (StackRoutines.transferProgram 18 21 0 1)) (emitAt rowEmitPorts)

theorem emitRow_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    ∃ rf, Eval emitRow (8 * bits.length + 10)
      (state regs {v with forward := bits, payload := []})
      (state rf {v with forward := [], payload := [], rowAcc := TupleProgram.prependRecord bits v.rowAcc}) := by
  have h1 := TupleProgram.transfer_eval (18 : Fin 22) 21 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with forward := bits, payload := []})
  have ht : Eval (.call (StackRoutines.transferProgram (18 : Fin 22) 21 (0 : Fin 8) 1))
      (3 * bits.length + 3) (state regs {v with forward := bits, payload := []})
      (state (readRegs regs 0 1 none) {v with forward := [], payload := bits.reverse}) := by
    simpa only [state, StackRoutines.transferStacks, store_forward, store_payload,
      List.append_nil, update_forward, update_payload] using h1
  obtain ⟨rf, h2⟩ := emitAt_eval rowEmitPorts
    (state (readRegs regs 0 1 none) {v with forward := [], payload := bits.reverse}) bits rfl
  simp only [state, rowEmitPorts_two, rowEmitPorts_three, store_rowAcc, update_payload, update_rowAcc] at h2
  refine ⟨rf, ?_⟩
  have hcost : (3 * bits.length + 3) + (5 * bits.length + 7) = 8 * bits.length + 10 := by omega
  simpa only [emitRow, hcost, state] using ht.seq h2

abbrev seedCoordinates : Cmd 8 22 := TupleProgram.pushConst 11 0 false
abbrev seedForward : Cmd 8 22 := TupleProgram.pushConst 18 0 false
abbrev seedRows : Cmd 8 22 := TupleProgram.pushConst 19 0 false
abbrev seedOutput : Cmd 8 22 := TupleProgram.pushConst 20 0 false

theorem seedCoordinates_eval (regs : Fin 8 → Bool) (v : View) :
    Eval seedCoordinates 2 (state regs {v with coordinates := []})
      (state (Function.update regs 0 false) {v with coordinates := [false]}) := by
  simpa only [state, TupleProgram.pushedState, store_coordinates, update_coordinates] using
    TupleProgram.pushConst_eval (11 : Fin 22) (0 : Fin 8) false (state regs {v with coordinates := []})

theorem seedForward_eval (regs : Fin 8 → Bool) (v : View) :
    Eval seedForward 2 (state regs {v with forward := []})
      (state (Function.update regs 0 false) {v with forward := [false]}) := by
  simpa only [state, TupleProgram.pushedState, store_forward, update_forward] using
    TupleProgram.pushConst_eval (18 : Fin 22) (0 : Fin 8) false (state regs {v with forward := []})

theorem seedRows_eval (regs : Fin 8 → Bool) (v : View) :
    Eval seedRows 2 (state regs {v with rowAcc := []})
      (state (Function.update regs 0 false) {v with rowAcc := [false]}) := by
  simpa only [state, TupleProgram.pushedState, store_rowAcc, update_rowAcc] using
    TupleProgram.pushConst_eval (19 : Fin 22) (0 : Fin 8) false (state regs {v with rowAcc := []})

theorem seedOutput_eval (regs : Fin 8 → Bool) (v : View) :
    Eval seedOutput 2 (state regs {v with output := []})
      (state (Function.update regs 0 false) {v with output := [false]}) := by
  simpa only [state, TupleProgram.pushedState, store_output, update_output] using
    TupleProgram.pushConst_eval (20 : Fin 22) (0 : Fin 8) false (state regs {v with output := []})

def baseView (cache : List (List Word)) (prefixes : List Prefix)
    (source rowAcc output : Word) : View :=
  ⟨cacheBytes cache, prefixStream prefixes, source, [], [], [], [], [], rowAcc, output, []⟩

abbrev rowCommand : Cmd 8 22 := .seq readRow (.seq restoreRow (.seq readValue (.seq copyPrefixes
  (.seq seedCoordinates (.seq makeCoordinates (.seq seedForward (.seq reverseCoordinates
    (.seq prependValue emitRow))))))))

def rowCost (cache : List (List Word)) (prefixes : List Prefix) (row : RawRow) : ℕ :=
  (6 * (rawRowBytes row).length + 4) + (3 * (rawRowBytes row).length + 3) +
  (6 * row.value.length + 4) + (7 * (prefixStream prefixes).length + 5) + 2 +
  (FactorPacketCoordinates.budget cache (pairs prefixes row) + 4) + 2 +
  10 * (Encoding.encodeList FactorBlueprint.encodeCoordinate
    ((pairs prefixes row).map (coordinate cache)).reverse).length +
  (5 * row.value.length + 5) + (8 * (FactorBlueprint.encodeRow (blueprintRow cache prefixes row)).length + 10)

/-- One complete raw row is parsed, paired with a physical prefix copy,
selected from the full cache, reordered, and framed. -/
theorem row_eval (regs : Fin 8 → Bool) (cache : List (List Word)) (prefixes : List Prefix)
    (row : RawRow) (valid : Valid cache prefixes row) (tail output : Word)
    (acc : List FactorBlueprint.Row) :
    ∃ t ≤ rowCost cache prefixes row, ∃ rf,
      Eval rowCommand t
        (state regs (baseView cache prefixes (Encoding.frame (rawRowBytes row) ++ tail)
          (FactorBlueprint.encodeRows acc) output))
        (state rf (baseView cache prefixes tail
          (FactorBlueprint.encodeRows (blueprintRow cache prefixes row :: acc)) output)) := by
  let v0 := baseView cache prefixes (Encoding.frame (rawRowBytes row) ++ tail)
    (FactorBlueprint.encodeRows acc) output
  let v1 := {v0 with source := tail, payload := (rawRowBytes row).reverse}
  let v2 := {v1 with labels := rawRowBytes row, payload := []}
  let v3 := {v2 with labels := Encoding.encodeList id row.labels, coefficient := row.value.reverse}
  let v4 := {v3 with prefixCursor := prefixStream prefixes}
  let v5 := {v4 with coordinates := [false]}
  let coords := (pairs prefixes row).map (coordinate cache)
  let v6 := {v5 with
    labels := []
    prefixCursor := []
    coordinates := Encoding.encodeList FactorBlueprint.encodeCoordinate coords.reverse}
  let v7 := {v6 with forward := [false]}
  let v8 := {v7 with coordinates := [], forward := Encoding.encodeList FactorBlueprint.encodeCoordinate coords}
  let v9 := {v8 with coefficient := [], forward := FactorBlueprint.encodeRow (blueprintRow cache prefixes row)}
  obtain ⟨r1, h1⟩ := readRow_eval regs v0 (rawRowBytes row) tail
  change Eval readRow _ (state regs v0) (state r1 v1) at h1
  have h2 := restoreRow_eval r1 v1 (rawRowBytes row)
  change Eval restoreRow _ (state r1 v1) (state (readRegs r1 0 1 none) v2) at h2
  obtain ⟨r3, h3⟩ := readValue_eval (readRegs r1 0 1 none) v2 row.value (Encoding.encodeList id row.labels)
  change Eval readValue _ (state (readRegs r1 0 1 none) v2) (state r3 v3) at h3
  have h4 := copyPrefixes_eval r3 v3
  change Eval copyPrefixes (7 * (prefixStream prefixes).length + 5)
    (state r3 v3) (state (readRegs r3 0 1 none) v4) at h4
  have h5 := seedCoordinates_eval (readRegs r3 0 1 none) v4
  change Eval seedCoordinates 2 (state (readRegs r3 0 1 none) v4)
    (state (Function.update (readRegs r3 0 1 none) 0 false) v5) at h5
  obtain ⟨tc, htc, rc, hc⟩ := makeCoordinates_eval
    (Function.update (readRegs r3 0 1 none) 0 false) v5 cache (pairs prefixes row)
    (valid_pairs cache prefixes row valid)
  obtain ⟨hlabels, hprefixes⟩ := pairs_streams prefixes row valid.1
  rw [hlabels, hprefixes] at hc
  change Eval makeCoordinates tc
    (state (Function.update (readRegs r3 0 1 none) 0 false) v5) (state rc v6) at hc
  have h7 := seedForward_eval rc v6
  change Eval seedForward 2 (state rc v6) (state (Function.update rc 0 false) v7) at h7
  obtain ⟨tr, htr, rr, hr⟩ := reverseCoordinates_eval (Function.update rc 0 false) v7 coords
  change Eval reverseCoordinates tr (state (Function.update rc 0 false) v7) (state rr v8) at hr
  obtain ⟨rv, hv⟩ := prependValue_eval rr v8 row.value (Encoding.encodeList FactorBlueprint.encodeCoordinate coords)
  change Eval prependValue (5 * row.value.length + 5) (state rr v8) (state rv v9) at hv
  obtain ⟨rf, hf⟩ := emitRow_eval rv v9 (FactorBlueprint.encodeRow (blueprintRow cache prefixes row))
  change Eval emitRow (8 * (FactorBlueprint.encodeRow (blueprintRow cache prefixes row)).length + 10)
    (state rv v9) (state rf (baseView cache prefixes tail
      (FactorBlueprint.encodeRows (blueprintRow cache prefixes row :: acc)) output)) at hf
  refine ⟨_, ?_, rf, h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (hc.seq (h7.seq (hr.seq (hv.seq hf))))))))⟩
  unfold rowCost
  change tr ≤ 10 * (Encoding.encodeList FactorBlueprint.encodeCoordinate
    ((pairs prefixes row).map (coordinate cache)).reverse).length at htr
  omega

abbrev readTag : Cmd 8 22 := SubexpInputFrames.readTag 13

theorem readTag_eval (regs : Fin 8 → Bool) (v : View) (bit : Bool) (tail : Word) :
    ∃ rf, Eval readTag 1 (state regs {v with source := bit :: tail})
      (state rf {v with source := tail}) ∧ rf 7 = bit := by
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 13
    (state regs {v with source := bit :: tail}) bit tail rfl
  have heq : e = state e.regs {v with source := tail} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_source] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he, hf⟩

def rowFlag : List RawRow → Bool
  | [] => false
  | _ :: _ => true

def afterRows : List RawRow → Word → Word
  | [], tail => tail
  | row :: rest, tail => Encoding.frame (rawRowBytes row) ++ (Encoding.encodeList rawRowBytes rest ++ tail)

theorem rawRows_tag (rows : List RawRow) (tail : Word) :
    Encoding.encodeList rawRowBytes rows ++ tail = rowFlag rows :: afterRows rows tail := by
  cases rows <;> simp [Encoding.encodeList, rowFlag, afterRows, List.append_assoc]

abbrev loop : Cmd 8 22 := .while 7 (.seq rowCommand readTag)

def rowsBudget (cache : List (List Word)) (prefixes : List Prefix) : List RawRow → ℕ
  | [] => 0
  | row :: rest => rowCost cache prefixes row + 2 + rowsBudget cache prefixes rest

theorem loop_eval (cache : List (List Word)) (prefixes : List Prefix) (rows : List RawRow)
    (valid : ∀ row ∈ rows, Valid cache prefixes row)
    (regs : Fin 8 → Bool) (tail output : Word) (acc : List FactorBlueprint.Row)
    (hg : regs 7 = rowFlag rows) :
    ∃ t ≤ rowsBudget cache prefixes rows + 1, ∃ rf,
      Eval loop t
        (state regs (baseView cache prefixes (afterRows rows tail) (FactorBlueprint.encodeRows acc) output))
        (state rf (baseView cache prefixes tail
          (FactorBlueprint.encodeRows ((rows.map (blueprintRow cache prefixes)).reverse ++ acc)) output)) := by
  induction rows generalizing regs acc with
  | nil =>
      refine ⟨1, by simp [rowsBudget], regs, ?_⟩
      simpa only [afterRows, List.map_nil, List.reverse_nil, List.nil_append] using
        (Eval.while_false (body := .seq rowCommand readTag)
          (a := state regs (baseView cache prefixes tail (FactorBlueprint.encodeRows acc) output)) hg)
  | cons row rest ih =>
      obtain ⟨nr, hnr, rr, hr⟩ := row_eval regs cache prefixes row (valid row (by simp))
        (Encoding.encodeList rawRowBytes rest ++ tail) output acc
      obtain ⟨rt, ht, hrt⟩ := readTag_eval rr
        (baseView cache prefixes [] (FactorBlueprint.encodeRows (blueprintRow cache prefixes row :: acc)) output)
        (rowFlag rest) (afterRows rest tail)
      rw [← rawRows_tag] at ht
      obtain ⟨nl, hnl, rf, hl⟩ := ih (fun r h => valid r (by simp [h])) rt
        (blueprintRow cache prefixes row :: acc) hrt
      refine ⟨nr + 1 + nl + 1, ?_, rf, ?_⟩
      · simp only [rowsBudget]
        omega
      · have h := Eval.while_true (by exact hg) (hr.seq ht) hl
        simpa only [loop, afterRows, List.map_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append] using h

theorem reverseRows_eval (regs : Fin 8 → Bool) (v : View) (rows : List FactorBlueprint.Row) :
    ∃ t ≤ 10 * (FactorBlueprint.encodeRows rows.reverse).length, ∃ rf,
      Eval reverseRows t
        (state regs {v with rowAcc := FactorBlueprint.encodeRows rows.reverse, output := [false]})
        (state rf {v with rowAcc := [], output := FactorBlueprint.encodeRows rows}) := by
  obtain ⟨t, ht, rf, he⟩ := reverseAt_eval rowReversePorts
    (state regs {v with rowAcc := FactorBlueprint.encodeRows rows.reverse, output := [false]})
    (rows.reverse.map FactorBlueprint.encodeRow) []
    (by rw [encodeList_map]; rfl) rfl rfl
  rw [encodeList_id_map] at ht
  have hrev : (rows.reverse.map FactorBlueprint.encodeRow).reverse =
      rows.map FactorBlueprint.encodeRow := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [hrev, List.append_nil, encodeList_id_map] at he
  exact ⟨t, ht, rf, by
    simpa only [reverseRows, FactorBlueprint.encodeRows, state, rowReversePorts_zero,
      rowReversePorts_two, update_rowAcc, update_output] using he⟩

abbrev command : Cmd 8 22 := .seq seedRows (.seq readTag (.seq loop (.seq seedOutput reverseRows)))
def program := compiled command (13 : Fin 22) 20

def runtimeBound (cache : List (List Word)) (prefixes : List Prefix) (rows : List RawRow) : ℕ :=
  rowsBudget cache prefixes rows +
    10 * (FactorBlueprint.encodeRows ((rows.map (blueprintRow cache prefixes)).reverse)).length + 7

def initialState (regs : Fin 8 → Bool) (cache : List (List Word))
    (prefixes : List Prefix) (rows : List RawRow) : Data :=
  state regs (baseView cache prefixes (Encoding.encodeList rawRowBytes rows) [] [])

def outputState (regs : Fin 8 → Bool) (cache : List (List Word))
    (prefixes : List Prefix) (rows : List RawRow) : Data :=
  state regs (baseView cache prefixes [] []
    (FactorBlueprint.encodeRows (rows.map (blueprintRow cache prefixes))))

/-- Both orders are exact: the coordinate list follows the prefix/label
scope order, and the output rows follow the raw input table order. -/
theorem program_runsIn (regs : Fin 8 → Bool) (cache : List (List Word))
    (prefixes : List Prefix) (rows : List RawRow)
    (valid : ∀ row ∈ rows, Valid cache prefixes row) :
    ∃ rf, RunsIn program (runtimeBound cache prefixes rows)
      ((initialState regs cache prefixes rows).withPC (some program.entry))
      ((outputState rf cache prefixes rows).withPC none) := by
  let v0 := baseView cache prefixes (Encoding.encodeList rawRowBytes rows) [] []
  have hseed := seedRows_eval regs v0
  obtain ⟨rt, ht, hrt⟩ := readTag_eval (Function.update regs 0 false)
    {v0 with rowAcc := [false]} (rowFlag rows) (afterRows rows [])
  rw [← rawRows_tag, List.append_nil] at ht
  obtain ⟨nl, hnl, rl, hl⟩ := loop_eval cache prefixes rows valid rt [] [] [] hrt
  simp only [List.append_nil] at hl
  let outRows := rows.map (blueprintRow cache prefixes)
  let v1 := baseView cache prefixes [] (FactorBlueprint.encodeRows outRows.reverse) []
  have hout := seedOutput_eval rl v1
  obtain ⟨nr, hnr, rf, hr⟩ := reverseRows_eval (Function.update rl 0 false) v1 outRows
  have hall := hseed.seq (ht.seq (hl.seq (hout.seq hr)))
  refine ⟨rf, 2 + (1 + (nl + (2 + nr))) + 1, ?_, ?_⟩
  · unfold runtimeBound
    change nr ≤ 10 * (FactorBlueprint.encodeRows (rows.map (blueprintRow cache prefixes)).reverse).length at hnr
    omega
  · exact compiled_halt_trace hall 13 20

theorem lifted_execution {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 22 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : State R S) (regs : Fin 8 → Bool) (cache : List (List Word))
    (prefixes : List Prefix) (rows : List RawRow)
    (valid : ∀ row ∈ rows, Valid cache prefixes row) :
    ∃ t ≤ runtimeBound cache prefixes rows, ∃ rf,
      Eval (.call (ProgramLinking.liftProgram program register stack)) t
        (embedState register stack frame (initialState regs cache prefixes rows))
        (embedState register stack frame (outputState rf cache prefixes rows)) := by
  obtain ⟨rf, t, ht, he⟩ := program_runsIn regs cache prefixes rows valid
  exact ⟨t, ht, rf, eval_call_lifted program register stack frame hregister hstack he⟩

theorem primitive_execution (regs : Fin 8 → Bool) (cache : List (List Word))
    (prefixes : List Prefix) (rows : List RawRow)
    (valid : ∀ row ∈ rows, Valid cache prefixes row) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * runtimeBound cache prefixes rows)
      (primitiveCfg program ((initialState regs cache prefixes rows).withPC (some program.entry)))
      (primitiveCfg program ((outputState rf cache prefixes rows).withPC none)) := by
  obtain ⟨rf, h⟩ := program_runsIn regs cache prefixes rows valid
  exact ⟨rf, BitProgram.primitive_execution program h⟩

theorem output_master_fields (regs : Fin 8 → Bool) (cache : List (List Word))
    (prefixes : List Prefix) (rows : List RawRow) :
    (outputState regs cache prefixes rows).stacks 7 = cacheBytes cache ∧
    (outputState regs cache prefixes rows).stacks 12 = prefixStream prefixes ∧
    (outputState regs cache prefixes rows).stacks 20 =
      FactorBlueprint.encodeRows (rows.map (blueprintRow cache prefixes)) := ⟨rfl, rfl, rfl⟩

end SubexponentialSAT.Subexp.FactorPacketRows

end OAI.Algorithms
