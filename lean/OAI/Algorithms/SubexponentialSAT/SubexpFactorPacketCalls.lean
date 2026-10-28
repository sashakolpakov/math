import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketControl
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRowExecution
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRowValues
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixControl

namespace OAI.Algorithms

/-! Actual local calls used by the original-order outer factor mapper. -/

namespace SubexponentialSAT.SubexpFactorPacketCalls

open BitProgram StructuredCalls SubexpScanPrimitives SubexpFactorPacketControl
open Subexp.FactorPacketCoordinates (Prefix cacheBytes)
open Subexp.FactorPacketRows (prefixStream rawRowBytes blueprintRow)
open SubexpFactorRowStream (tableRows)

structure View where
  masters : Masters
  acc : Word := []
  output : Word := []
  todoGroups : Word := []
  todoTables : Word := []
  payload : Word := []
  arity : Word := []
  prefixRev : Word := []
  answers : Word := []
  raw : Word := []
  prefixes : Word := []
  packet : Word := []
  group : Word := []

def workStore (v : View) : Fin 64 → Word := fun i =>
  if i = 40 then v.masters.cache else if i = 41 then v.masters.groups else if i = 42 then v.masters.tables else if i = 43 then v.masters.modulus else if i = 44 then v.masters.zero else if i = 45 then v.masters.one else if i = 46 then v.acc else if i = 47 then v.output else if i = 48 then v.todoGroups else if i = 49 then v.todoTables else if i = 50 then v.payload else if i = 51 then v.arity else if i = 52 then v.prefixRev else if i = 53 then v.answers else if i = 54 then v.raw else if i = 55 then v.prefixes else if i = 56 then v.packet else if i = 57 then v.group else []

def workState (regs : Fin 8 → Bool) (v : View) : Data := ⟨regs, workStore v⟩

@[simp] theorem workStore_cache (v : View) : workStore v 40 = v.masters.cache := rfl

@[simp] theorem workStore_groups (v : View) : workStore v 41 = v.masters.groups := rfl

@[simp] theorem workStore_tables (v : View) : workStore v 42 = v.masters.tables := rfl

@[simp] theorem workStore_modulus (v : View) : workStore v 43 = v.masters.modulus := rfl

@[simp] theorem workStore_zero (v : View) : workStore v 44 = v.masters.zero := rfl

@[simp] theorem workStore_one (v : View) : workStore v 45 = v.masters.one := rfl

@[simp] theorem workStore_acc (v : View) : workStore v 46 = v.acc := rfl
@[simp] theorem update_acc (v : View) (w : Word) :
    Function.update (workStore v) 46 w = workStore {v with acc := w} := by
  funext i
  by_cases h : i = 46 <;> simp [workStore, h]

@[simp] theorem workStore_output (v : View) : workStore v 47 = v.output := rfl
@[simp] theorem update_output (v : View) (w : Word) :
    Function.update (workStore v) 47 w = workStore {v with output := w} := by
  funext i
  by_cases h : i = 47 <;> simp [workStore, h]

@[simp] theorem workStore_todoGroups (v : View) : workStore v 48 = v.todoGroups := rfl
@[simp] theorem update_todoGroups (v : View) (w : Word) :
    Function.update (workStore v) 48 w = workStore {v with todoGroups := w} := by
  funext i
  by_cases h : i = 48 <;> simp [workStore, h]

@[simp] theorem workStore_todoTables (v : View) : workStore v 49 = v.todoTables := rfl
@[simp] theorem update_todoTables (v : View) (w : Word) :
    Function.update (workStore v) 49 w = workStore {v with todoTables := w} := by
  funext i
  by_cases h : i = 49 <;> simp [workStore, h]

@[simp] theorem workStore_payload (v : View) : workStore v 50 = v.payload := rfl
@[simp] theorem update_payload (v : View) (w : Word) :
    Function.update (workStore v) 50 w = workStore {v with payload := w} := by
  funext i
  by_cases h : i = 50 <;> simp [workStore, h]

@[simp] theorem workStore_arity (v : View) : workStore v 51 = v.arity := rfl
@[simp] theorem update_arity (v : View) (w : Word) :
    Function.update (workStore v) 51 w = workStore {v with arity := w} := by
  funext i
  by_cases h : i = 51 <;> simp [workStore, h]

@[simp] theorem workStore_prefixRev (v : View) : workStore v 52 = v.prefixRev := rfl
@[simp] theorem update_prefixRev (v : View) (w : Word) :
    Function.update (workStore v) 52 w = workStore {v with prefixRev := w} := by
  funext i
  by_cases h : i = 52 <;> simp [workStore, h]

@[simp] theorem workStore_answers (v : View) : workStore v 53 = v.answers := rfl
@[simp] theorem update_answers (v : View) (w : Word) :
    Function.update (workStore v) 53 w = workStore {v with answers := w} := by
  funext i
  by_cases h : i = 53 <;> simp [workStore, h]

@[simp] theorem workStore_raw (v : View) : workStore v 54 = v.raw := rfl
@[simp] theorem update_raw (v : View) (w : Word) :
    Function.update (workStore v) 54 w = workStore {v with raw := w} := by
  funext i
  by_cases h : i = 54 <;> simp [workStore, h]

@[simp] theorem workStore_prefixes (v : View) : workStore v 55 = v.prefixes := rfl
@[simp] theorem update_prefixes (v : View) (w : Word) :
    Function.update (workStore v) 55 w = workStore {v with prefixes := w} := by
  funext i
  by_cases h : i = 55 <;> simp [workStore, h]

@[simp] theorem workStore_packet (v : View) : workStore v 56 = v.packet := rfl
@[simp] theorem update_packet (v : View) (w : Word) :
    Function.update (workStore v) 56 w = workStore {v with packet := w} := by
  funext i
  by_cases h : i = 56 <;> simp [workStore, h]

@[simp] theorem workStore_group (v : View) : workStore v 57 = v.group := rfl
@[simp] theorem update_group (v : View) (w : Word) :
    Function.update (workStore v) 57 w = workStore {v with group := w} := by
  funext i
  by_cases h : i = 57 <;> simp [workStore, h]

private theorem embed_rows (regs oldRegs : Fin 8 → Bool) (v : View) (k : ℕ)
    (answers raw : Word) :
    embedState id rowPorts (workState oldRegs v)
      (SubexpFactorRowStream.state regs
        (SubexpFactorRowStream.resting v.masters.modulus [] k answers
          v.masters.zero v.masters.one raw)) =
      workState regs {v with arity := List.replicate k true, answers := answers, raw := raw} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rowPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h51 : i ≠ 51 := fun h => hi ⟨14, h.symm⟩
    have h53 : i ≠ 53 := fun h => hi ⟨17, h.symm⟩
    have h54 : i ≠ 54 := fun h => hi ⟨22, h.symm⟩
    simp [workState, workStore, h51, h53, h54]

theorem rows_eval (regs : Fin 8 → Bool) (v : View) (k : ℕ) (answers : Word) :
    ∃ n ≤ SubexpFactorRowStream.runtimeBound v.masters.modulus k
        v.masters.zero v.masters.one answers, ∃ rf,
      Eval rows n
        (workState regs {v with arity := List.replicate k true, answers := answers.reverse, raw := []})
        (workState rf {v with arity := List.replicate k true, answers := [], raw := (Encoding.encodeList rawRowBytes (tableRows v.masters.modulus k v.masters.zero v.masters.one answers))}) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpFactorRowStream.program_runsIn regs
    v.masters.modulus k v.masters.zero v.masters.one answers
  have he := eval_call_lifted SubexpFactorRowStream.program id rowPorts
    (workState regs v) Function.injective_id rowPorts_injective ht
  rw [embed_rows, embed_rows] at he
  exact ⟨n, hn, rf, he⟩

private theorem embed_factor (regs oldRegs : Fin 8 → Bool) (v : View)
    (cache : List (List Word)) (ps : List Prefix) (source result : Word)
    (hc : v.masters.cache = cacheBytes cache) :
    embedState id factorPorts (workState oldRegs v)
      (Subexp.FactorPacketRows.state regs
        (Subexp.FactorPacketRows.baseView cache ps source [] result)) =
      workState regs {v with prefixes := prefixStream ps, raw := source, packet := result} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id factorPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [workState, workStore, factorPorts,
      Subexp.FactorPacketRows.state, Subexp.FactorPacketRows.baseView,
      Subexp.FactorPacketRows.store, hc]
  · intro i hi
    have h54 : i ≠ 54 := fun h => hi ⟨13, h.symm⟩
    have h55 : i ≠ 55 := fun h => hi ⟨12, h.symm⟩
    have h56 : i ≠ 56 := fun h => hi ⟨20, h.symm⟩
    simp [workState, workStore, h54, h55, h56]

theorem factor_eval (regs : Fin 8 → Bool) (v : View) (cache : List (List Word))
    (ps : List Prefix) (rs : List Subexp.FactorPacketRows.RawRow)
    (hc : v.masters.cache = cacheBytes cache)
    (valid : ∀ r ∈ rs, Subexp.FactorPacketRows.Valid cache ps r) :
    ∃ n ≤ Subexp.FactorPacketRows.runtimeBound cache ps rs, ∃ rf,
      Eval factor n
        (workState regs {v with prefixes := prefixStream ps, raw := Encoding.encodeList rawRowBytes rs, packet := []})
        (workState rf {v with prefixes := prefixStream ps, raw := [], packet := Subexp.FactorBlueprint.encodeRows (rs.map (blueprintRow cache ps))}) := by
  obtain ⟨rf, n, hn, ht⟩ := Subexp.FactorPacketRows.program_runsIn regs cache ps rs valid
  have he := eval_call_lifted Subexp.FactorPacketRows.program id factorPorts
    (workState regs v) Function.injective_id factorPorts_injective ht
  change Eval factor n
    (embedState id factorPorts (workState regs v)
      (Subexp.FactorPacketRows.state regs
        (Subexp.FactorPacketRows.baseView cache ps (Encoding.encodeList rawRowBytes rs) [] [])))
    (embedState id factorPorts (workState regs v)
      (Subexp.FactorPacketRows.state rf
        (Subexp.FactorPacketRows.baseView cache ps [] []
          (Subexp.FactorBlueprint.encodeRows (rs.map (blueprintRow cache ps)))))) at he
  rw [embed_factor _ _ _ _ _ _ _ hc, embed_factor _ _ _ _ _ _ _ hc] at he
  exact ⟨n, hn, rf, he⟩


theorem readGroupField_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval (SubexpInputFrames.readField 48 50 (by decide)) (6 * bits.length + 4)
      (workState regs {v with todoGroups := Encoding.frame bits ++ tail, payload := []})
      (workState rf {v with todoGroups := tail, payload := bits.reverse}) := by
  let a := {v with todoGroups := Encoding.frame bits ++ tail, payload := []}
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 48 50 (by decide)
    (workState regs a) bits tail rfl rfl
  have heq : e = workState e.regs {v with todoGroups := tail, payload := bits.reverse} := by
    refine SubexpScanPrimitives.state_ext (by rfl) ?_
    rw [hs]
    simp only [workState, update_todoGroups, update_payload]
    rfl
  rw [heq] at he
  exact ⟨e.regs, he⟩

theorem readArityField_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval (SubexpInputFrames.readField 57 51 (by decide)) (6 * bits.length + 4)
      (workState regs {v with group := Encoding.frame bits ++ tail, arity := []})
      (workState rf {v with group := tail, arity := bits.reverse}) := by
  let a := {v with group := Encoding.frame bits ++ tail, arity := []}
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 57 51 (by decide)
    (workState regs a) bits tail rfl rfl
  have heq : e = workState e.regs {v with group := tail, arity := bits.reverse} := by
    refine SubexpScanPrimitives.state_ext (by rfl) ?_
    rw [hs]
    simp only [workState, update_group, update_arity]
    rfl
  rw [heq] at he
  exact ⟨e.regs, he⟩

theorem readPrefixField_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval (SubexpInputFrames.readField 57 52 (by decide)) (6 * bits.length + 4)
      (workState regs {v with group := Encoding.frame bits ++ tail, prefixRev := []})
      (workState rf {v with group := tail, prefixRev := bits.reverse}) := by
  let a := {v with group := Encoding.frame bits ++ tail, prefixRev := []}
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 57 52 (by decide)
    (workState regs a) bits tail rfl rfl
  have heq : e = workState e.regs {v with group := tail, prefixRev := bits.reverse} := by
    refine SubexpScanPrimitives.state_ext (by rfl) ?_
    rw [hs]
    simp only [workState, update_group, update_prefixRev]
    rfl
  rw [heq] at he
  exact ⟨e.regs, he⟩

theorem readTableField_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval (SubexpInputFrames.readField 49 53 (by decide)) (6 * bits.length + 4)
      (workState regs {v with todoTables := Encoding.frame bits ++ tail, answers := []})
      (workState rf {v with todoTables := tail, answers := bits.reverse}) := by
  let a := {v with todoTables := Encoding.frame bits ++ tail, answers := []}
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 49 53 (by decide)
    (workState regs a) bits tail rfl rfl
  have heq : e = workState e.regs {v with todoTables := tail, answers := bits.reverse} := by
    refine SubexpScanPrimitives.state_ext (by rfl) ?_
    rw [hs]
    simp only [workState, update_todoTables, update_answers]
    rfl
  rw [heq] at he
  exact ⟨e.regs, he⟩

theorem moveGroup_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval (transfer 50 57) (3 * bits.length + 3)
      (workState regs {v with payload := bits.reverse, group := []})
      (workState (readRegs regs 0 1 none) {v with payload := [], group := bits}) := by
  have he := transfer_eval
    (workState regs {v with payload := bits.reverse, group := []})
    50 57 0 1 (by decide) (by decide)
  simpa only [transfer, afterTransfer, StackRoutines.transferStacks, workState,
    workStore_payload, workStore_group, update_payload, update_group,
    List.length_reverse, List.reverse_reverse, List.append_nil] using he

theorem movePrefixes_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval (transfer 52 55) (3 * bits.length + 3)
      (workState regs {v with prefixRev := bits.reverse, prefixes := []})
      (workState (readRegs regs 0 1 none) {v with prefixRev := [], prefixes := bits}) := by
  have he := transfer_eval
    (workState regs {v with prefixRev := bits.reverse, prefixes := []})
    52 55 0 1 (by decide) (by decide)
  simpa only [transfer, afterTransfer, StackRoutines.transferStacks, workState,
    workStore_prefixRev, workStore_prefixes, update_prefixRev, update_prefixes,
    List.length_reverse, List.reverse_reverse, List.append_nil] using he

theorem movePacket_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval (transfer 56 50) (3 * bits.length + 3)
      (workState regs {v with packet := bits.reverse, payload := []})
      (workState (readRegs regs 0 1 none) {v with packet := [], payload := bits}) := by
  have he := transfer_eval
    (workState regs {v with packet := bits.reverse, payload := []})
    56 50 0 1 (by decide) (by decide)
  simpa only [transfer, afterTransfer, StackRoutines.transferStacks, workState,
    workStore_packet, workStore_payload, update_packet, update_payload,
    List.length_reverse, List.reverse_reverse, List.append_nil] using he

theorem readGroup_eval (regs : Fin 8 → Bool) (v : View) (ps : List Prefix) (tail : Word) :
    ∃ rf, Eval readGroup
      (9 * (SubexpFactorPrefixProgram.groupBytes ps).length +
        6 * ps.length + 9 * (prefixStream ps).length + 18)
      (workState regs {v with todoGroups := Encoding.frame (SubexpFactorPrefixProgram.groupBytes ps) ++ tail, payload := [], group := [], arity := [], prefixRev := [], prefixes := []})
      (workState rf {v with todoGroups := tail, payload := [], group := [], arity := List.replicate ps.length true, prefixRev := [], prefixes := prefixStream ps}) := by
  let a := {v with todoGroups := Encoding.frame (SubexpFactorPrefixProgram.groupBytes ps) ++ tail, payload := [], group := [], arity := [], prefixRev := [], prefixes := []}
  obtain ⟨r1, h1⟩ := readGroupField_eval regs a (SubexpFactorPrefixProgram.groupBytes ps) tail
  let b := {a with todoGroups := tail, payload := (SubexpFactorPrefixProgram.groupBytes ps).reverse}
  have h2 := moveGroup_eval r1 b (SubexpFactorPrefixProgram.groupBytes ps)
  let c := {b with payload := [], group := SubexpFactorPrefixProgram.groupBytes ps}
  obtain ⟨r3, h3⟩ := readArityField_eval (readRegs r1 0 1 none) c
    (List.replicate ps.length true) (Encoding.frame (prefixStream ps))
  let d := {c with group := Encoding.frame (prefixStream ps), arity := (List.replicate ps.length true).reverse}
  obtain ⟨r4, h4⟩ := readPrefixField_eval r3 d (prefixStream ps) []
  simp only [List.append_nil] at h4
  let e := {d with group := [], prefixRev := (prefixStream ps).reverse}
  have h5 := movePrefixes_eval r4 e (prefixStream ps)
  refine ⟨readRegs r4 0 1 none, ?_⟩
  have hall := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert hall using 1
  all_goals simp only [readGroup, a, b, c, d, e,
    SubexpFactorPrefixProgram.groupBytes, List.length_replicate, List.reverse_replicate]
  all_goals omega



private theorem embed_restricted {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 64)
    (hr : Function.Injective register) (hs : Function.Injective stack) (d : Data) :
    embedState register stack d ⟨d.regs ∘ register, d.stacks ∘ stack⟩ = d := by
  apply embedState_eq_of_ports _ _ _ _ _ hr hs
  all_goals intros; rfl

theorem emitFactor_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval emitFactor (5 * bits.length + 7)
      (workState regs {v with payload := bits.reverse})
      (workState (Function.update (Function.update regs 0 true) 1 false)
        {v with payload := [], acc := true :: (Encoding.frame bits ++ v.acc)}) := by
  let d := workState regs {v with payload := bits.reverse}
  let small : State 5 6 := ⟨d.regs ∘ writerRegs, d.stacks ∘ writerPorts⟩
  have hw := SubexpArgumentProgram.writer_eval true small bits (by rfl)
  have hi := embed_restricted writerRegs writerPorts
    writerRegs_injective writerPorts_injective d
  change embedState writerRegs writerPorts d small = d at hi
  have ho : embedState writerRegs writerPorts d
      (SubexpArgumentProgram.afterWriter true small bits) =
      workState (Function.update (Function.update regs 0 true) 1 false)
        {v with payload := [], acc := true :: (Encoding.frame bits ++ v.acc)} := by
    apply embedState_eq_of_ports _ _ _ _ _ writerRegs_injective writerPorts_injective
    · intro i
      fin_cases i <;> simp [workState, small, d, writerRegs,
        SubexpArgumentProgram.finishedRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [workState, d, h0, h1]
    · intro i
      fin_cases i <;> simp [workState, workStore, small, d, writerPorts,
        SubexpArgumentProgram.destination]
    · intro i hi
      have h46 : i ≠ 46 := fun h => hi ⟨3, h.symm⟩
      have h50 : i ≠ 50 := fun h => hi ⟨1, h.symm⟩
      simp [workState, workStore, d, h46, h50]
  cases hw with
  | call _ ht =>
      have he := eval_call_lifted (SubexpArgumentProgram.writer true) writerRegs writerPorts d
        writerRegs_injective writerPorts_injective ht
      simpa only [emitFactor, hi, ho] using he


theorem clear_arity_eval (regs : Fin 8 → Bool) (v : View) :
    Eval (clear 51) (2 * v.arity.length + 3) (workState regs v)
      (workState (readRegs regs 0 1 none) {v with arity := []}) := by
  have ht := ListRegisterProgram.clear_run (51 : Fin 64) (0 : Fin 8) 1 regs (workStore v)
  apply Eval.call
  simpa only [workState, StackRoutines.clearStacks, update_arity, workStore_arity] using ht

theorem clear_prefixes_eval (regs : Fin 8 → Bool) (v : View) :
    Eval (clear 55) (2 * v.prefixes.length + 3) (workState regs v)
      (workState (readRegs regs 0 1 none) {v with prefixes := []}) := by
  have ht := ListRegisterProgram.clear_run (55 : Fin 64) (0 : Fin 8) 1 regs (workStore v)
  apply Eval.call
  simpa only [workState, StackRoutines.clearStacks, update_prefixes,
    workStore_prefixes] using ht

theorem copy_groups_eval (regs : Fin 8 → Bool) (v : View) :
    Eval (copy 41 48) (7 * v.masters.groups.length + 5)
      (workState regs {v with todoGroups := []})
      (workState (readRegs regs 0 1 none) {v with todoGroups := v.masters.groups}) := by
  have he := copy_eval (workState regs {v with todoGroups := []})
    41 48 60 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy, afterCopy, StackRoutines.copyStacks, workState,
    workStore_groups, workStore_todoGroups, update_todoGroups, List.append_nil] using he

theorem copy_tables_eval (regs : Fin 8 → Bool) (v : View) :
    Eval (copy 42 49) (7 * v.masters.tables.length + 5)
      (workState regs {v with todoTables := []})
      (workState (readRegs regs 0 1 none) {v with todoTables := v.masters.tables}) := by
  have he := copy_eval (workState regs {v with todoTables := []})
    42 49 60 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy, afterCopy, StackRoutines.copyStacks, workState,
    workStore_tables, workStore_todoTables, update_todoTables, List.append_nil] using he

theorem readTags_eval (regs : Fin 8 → Bool) (v : View) (g b : Bool) (gs bs : Word) :
    Eval readTags 2
      (workState regs {v with todoGroups := g :: gs, todoTables := b :: bs})
      (workState (readRegs (readRegs regs 7 6 (some g)) 0 1 (some b))
        {v with todoGroups := gs, todoTables := bs}) := by
  let a := workState regs {v with todoGroups := g :: gs, todoTables := b :: bs}
  let mid := workState (readRegs regs 7 6 (some g))
    {v with todoGroups := gs, todoTables := b :: bs}
  have h1 : Eval (SubexpInputFrames.readTag 48) 1 a mid := by
    apply Eval.base
    convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (48 : Fin 64) 7 6) a using 1
    apply state_ext
    · rfl
    · simp [a, mid, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, workState]
  have h2 : Eval (.base (.atom (.pop 49 0 1))) 1 mid
      (workState (readRegs (readRegs regs 7 6 (some g)) 0 1 (some b))
        {v with todoGroups := gs, todoTables := bs}) := by
    apply Eval.base
    convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (49 : Fin 64) 0 1) mid using 1
    apply state_ext
    · rfl
    · simp [mid, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, workState]
  exact h1.seq h2



theorem seed_acc_eval (regs : Fin 8 → Bool) (v : View) :
    Eval (seed 46) 2 (workState regs {v with acc := []})
      (workState (Function.update regs 0 false) {v with acc := [false]}) := by
  have he := Subexp.TupleProgram.pushConst_eval 46 0 false (workState regs {v with acc := []})
  simpa only [seed, Subexp.TupleProgram.pushedState, workState, workStore_acc, update_acc] using he

theorem seed_output_eval (regs : Fin 8 → Bool) (v : View) :
    Eval (seed 47) 2 (workState regs {v with output := []})
      (workState (Function.update regs 0 false) {v with output := [false]}) := by
  have he := Subexp.TupleProgram.pushConst_eval 47 0 false (workState regs {v with output := []})
  simpa only [seed, Subexp.TupleProgram.pushedState, workState, workStore_output, update_output] using he

private theorem embed_reverse (_regs oldRegs : Fin 8 → Bool) (v : View)
    (a b c : Bool) (src dst : Word) :
    embedState reverseRegs reversePorts (workState oldRegs v)
      (SubexpNormalizeProgram.filterState a b c src [] dst []) =
      workState (Function.update (Function.update (Function.update oldRegs 0 a) 1 b) 2 c)
        {v with acc := src, output := dst} := by
  apply embedState_eq_of_ports _ _ _ _ _ reverseRegs_injective reversePorts_injective
  · intro i
    fin_cases i <;> simp [reverseRegs, workState, SubexpNormalizeProgram.filterState]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
    simp [workState, h0, h1, h2]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h46 : i ≠ 46 := fun h => hi ⟨0, h.symm⟩
    have h47 : i ≠ 47 := fun h => hi ⟨2, h.symm⟩
    simp [workState, workStore, h46, h47]

theorem reverseFactors_eval (regs : Fin 8 → Bool) (v : View) (records : List Word) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ rf,
      Eval reverseFactors n
        (workState regs {v with acc := Encoding.encodeList id records, output := [false]})
        (workState rf {v with acc := [], output := Encoding.encodeList id records.reverse}) := by
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] []
    (regs 0) (regs 1) (regs 2)
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram reverseRegs reversePorts
    (workState regs v) reverseRegs_injective reversePorts_injective ht
  rw [embed_reverse regs, embed_reverse regs] at he
  have hr : Function.update (Function.update (Function.update regs 0 (regs 0)) 1 (regs 1)) 2 (regs 2) = regs := by
    funext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
      simp [h0, h1, h2]
  refine ⟨n, hn, Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false, ?_⟩
  simpa only [reverseFactors, hr, List.append_nil, Encoding.encodeList] using he


end SubexponentialSAT.SubexpFactorPacketCalls


end OAI.Algorithms
