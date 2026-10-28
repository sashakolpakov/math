import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! Physical storage, dictionary deduplication/counting, and header assembly
for the raw-identifier transport. The raw input remains on 23 until its second
read; the unary dimension on 22 lies outside both 22-stack parser calls. -/

namespace SubexponentialSAT.SubexpRawIDTransport

open BitProgram StructuredCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Word := List Bool
abbrev Data := State 10 24
abbrev Command := Cmd 10 24

structure View where
  source : Word := []
  dictionary : Word := []
  collected : Word := []
  output : Word := []
  dimension : Word := []
  raw : Word := []

def store (v : View) : Fin 24 → Word := fun i =>
  if i = 0 then v.source else if i = 4 then v.dictionary else if i = 6 then v.collected
  else if i = 8 then v.output else if i = 22 then v.dimension else if i = 23 then v.raw else []

def state (regs : Fin 10 → Bool) (v : View) : Data := ⟨regs, store v⟩

@[simp] theorem store_source (v : View) : store v 0 = v.source := rfl
@[simp] theorem store_dictionary (v : View) : store v 4 = v.dictionary := rfl
@[simp] theorem store_collected (v : View) : store v 6 = v.collected := rfl
@[simp] theorem store_output (v : View) : store v 8 = v.output := rfl
@[simp] theorem store_dimension (v : View) : store v 22 = v.dimension := rfl
@[simp] theorem store_raw (v : View) : store v 23 = v.raw := rfl

@[simp] theorem update_source (v : View) (w : Word) :
    Function.update (store v) 0 w = store {v with source := w} := by
  funext i; by_cases hi : i = 0 <;> simp [store, hi]
@[simp] theorem update_dictionary (v : View) (w : Word) :
    Function.update (store v) 4 w = store {v with dictionary := w} := by
  funext i; by_cases hi : i = 4 <;> simp [store, hi]
@[simp] theorem update_collected (v : View) (w : Word) :
    Function.update (store v) 6 w = store {v with collected := w} := by
  funext i; by_cases hi : i = 6 <;> simp [store, hi]
@[simp] theorem update_output (v : View) (w : Word) :
    Function.update (store v) 8 w = store {v with output := w} := by
  funext i; by_cases hi : i = 8 <;> simp [store, hi]
@[simp] theorem update_dimension (v : View) (w : Word) :
    Function.update (store v) 22 w = store {v with dimension := w} := by
  funext i; by_cases hi : i = 22 <;> simp [store, hi]
@[simp] theorem update_raw (v : View) (w : Word) :
    Function.update (store v) 23 w = store {v with raw := w} := by
  funext i; by_cases hi : i = 23 <;> simp [store, hi]

/-- Preserve order through a real copy followed by a real source clear. -/
abbrev moveWord {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r) : Cmd r s :=
  .seq (.call (StackRoutines.copyProgram src dst tmp value present))
    (.call (StackRoutines.clearProgram src value present))

theorem moveWord_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (a : State r s) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hvp : value ≠ present) (htmp : a.stacks tmp = []) :
    Eval (moveWord src dst tmp value present) (9 * (a.stacks src).length + 8) a
      ⟨readRegs a.regs value present none,
        Function.update (Function.update a.stacks dst (a.stacks src ++ a.stacks dst)) src []⟩ := by
  have hc := Subexp.TupleProgram.copy_eval src dst tmp value present hsd hst htd hvp a htmp
  have hz := Subexp.TupleProgram.clear_eval src value present
    (⟨readRegs a.regs value present none, StackRoutines.copyStacks src dst a.stacks⟩ : State r s)
  have h := hc.seq hz
  have h' : Eval (moveWord src dst tmp value present)
      ((7 * (a.stacks src).length + 5) + (2 * (a.stacks src).length + 3)) a
      ⟨readRegs a.regs value present none,
        Function.update (Function.update a.stacks dst (a.stacks src ++ a.stacks dst)) src []⟩ := by
    simpa [moveWord, StackRoutines.copyStacks, StackRoutines.clearStacks,
      StackRoutines.readRegs_reset, hsd] using h
  convert h' using 1
  omega

def copyRaw : Command := .call (StackRoutines.copyProgram 23 0 1 0 1)
def moveCollected : Command := moveWord 6 0 1 0 1
def moveDictionary : Command := moveWord 0 4 1 0 1
def copyDictionary : Command := .call (StackRoutines.copyProgram 4 0 1 0 1)
def restoreRaw : Command := moveWord 23 0 1 0 1

theorem copyRaw_eval (regs : Fin 10 → Bool) (raw : Word) :
    Eval copyRaw (7 * raw.length + 5) (state regs {raw := raw})
      (state (readRegs regs 0 1 none) {source := raw, raw := raw}) := by
  simpa [copyRaw, state, StackRoutines.copyStacks] using
    Subexp.TupleProgram.copy_eval (23 : Fin 24) 0 1 (0 : Fin 10) 1
      (by decide) (by decide) (by decide) (by decide) (state regs {raw := raw}) (by rfl)

theorem moveCollected_eval (regs : Fin 10 → Bool) (ids raw : Word) :
    Eval moveCollected (9 * ids.length + 8) (state regs {collected := ids, raw := raw})
      (state (readRegs regs 0 1 none) {source := ids, raw := raw}) := by
  simpa only [moveCollected, state, store_collected, store_source, List.append_nil,
    update_source, update_collected] using
    moveWord_eval (6 : Fin 24) 0 1 (0 : Fin 10) 1
      (state regs {collected := ids, raw := raw}) (by decide) (by decide)
      (by decide) (by decide) (by rfl)

theorem moveDictionary_eval (regs : Fin 10 → Bool) (dictionary raw : Word) :
    Eval moveDictionary (9 * dictionary.length + 8) (state regs {source := dictionary, raw := raw})
      (state (readRegs regs 0 1 none) {dictionary := dictionary, raw := raw}) := by
  simpa only [moveDictionary, state, store_source, store_dictionary, List.append_nil,
    update_dictionary, update_source] using
    moveWord_eval (0 : Fin 24) 4 1 (0 : Fin 10) 1
      (state regs {source := dictionary, raw := raw}) (by decide) (by decide)
      (by decide) (by decide) (by rfl)

theorem copyDictionary_eval (regs : Fin 10 → Bool) (dictionary raw : Word) :
    Eval copyDictionary (7 * dictionary.length + 5) (state regs {dictionary := dictionary, raw := raw})
      (state (readRegs regs 0 1 none) {source := dictionary, dictionary := dictionary, raw := raw}) := by
  simpa [copyDictionary, state, StackRoutines.copyStacks] using
    Subexp.TupleProgram.copy_eval (4 : Fin 24) 0 1 (0 : Fin 10) 1
      (by decide) (by decide) (by decide) (by decide)
      (state regs {dictionary := dictionary, raw := raw}) (by rfl)

theorem restoreRaw_eval (regs : Fin 10 → Bool) (dictionary dimension raw : Word) :
    Eval restoreRaw (9 * raw.length + 8)
      (state regs {dictionary := dictionary, dimension := dimension, raw := raw})
      (state (readRegs regs 0 1 none)
        {source := raw, dictionary := dictionary, dimension := dimension}) := by
  simpa only [restoreRaw, state, store_raw, store_source, List.append_nil,
    update_source, update_raw] using
    moveWord_eval (23 : Fin 24) 0 1 (0 : Fin 10) 1
      (state regs {dictionary := dictionary, dimension := dimension, raw := raw})
      (by decide) (by decide) (by decide) (by decide) (by rfl)

def parserRegisters : Fin 8 → Fin 10 := Fin.castAdd 2
def parserStacks : Fin 22 → Fin 24 := Fin.castAdd 2
def parserState (regs : Fin 8 → Bool) (v : View) : State 8 22 :=
  ⟨regs, store v ∘ parserStacks⟩
noncomputable def parserResultRegs (regs : Fin 10 → Bool) (rf : Fin 8 → Bool) : Fin 10 → Bool :=
  Function.extend parserRegisters rf regs

theorem parserRegisters_injective : Function.Injective parserRegisters := Fin.castAdd_injective _ _
theorem parserStacks_injective : Function.Injective parserStacks := Fin.castAdd_injective _ _

theorem parserState_project (regs : Fin 10 → Bool) (v : View) :
    projectState parserRegisters parserStacks (state regs v) = parserState (regs ∘ parserRegisters) v := rfl

theorem parserState_install (regs : Fin 10 → Bool) (rf : Fin 8 → Bool) (v w : View)
    (hdim : w.dimension = v.dimension) (hraw : w.raw = v.raw) :
    embedState parserRegisters parserStacks (state regs v) (parserState rf w) =
      state (parserResultRegs regs rf) w := by
  apply SubexpScanPrimitives.embedState_eq _ _ parserRegisters_injective parserStacks_injective
  · intro i
    exact parserRegisters_injective.extend_apply _ _ i
  · intro i; rfl
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i hi
    have hl : ¬ i.val < 22 := by
      intro h
      exact hi ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    have cases : i = 22 ∨ i = 23 := by
      have : i.val = 22 ∨ i.val = 23 := by omega
      exact this.imp Fin.ext Fin.ext
    rcases cases with rfl | rfl <;> simp [state, hdim, hraw]

def dedupStacks : Fin 8 → Fin 24 := Fin.castAdd 16
def dedupCall : Command := .call (ProgramLinking.liftProgram
  ExecLiteralDedupProgram.dedupProgram id dedupStacks)

theorem dedupCall_eval (regs : Fin 10 → Bool) (records : List Word) (raw : Word) :
    ∃ n ≤ 120 * ((Encoding.encodeList id records).length + 1)^2, ∃ rf,
      Eval dedupCall n (state regs {source := Encoding.encodeList id records, raw := raw})
        (state rf {source := Encoding.encodeList id (ExecCNF.dedupLiterals records), raw := raw}) := by
  let a : Data := state regs {source := Encoding.encodeList id records, raw := raw}
  let small := projectState id dedupStacks a
  have hz : ExecLiteralDedupProgram.Ready small := by
    simp [ExecLiteralDedupProgram.Ready, ExecLiteralDedupProgram.Clean,
      small, projectState, dedupStacks, a, state, store]
  obtain ⟨out, hout, hsource, n, hn, ht⟩ :=
    ExecLiteralDedupProgram.dedup_runsIn records small rfl hz
  have he := eval_call_from_state ExecLiteralDedupProgram.dedupProgram id dedupStacks a
    Function.injective_id (Fin.castAdd_injective _ _) ht
  have hend : embedState id dedupStacks a out =
      state out.regs {source := Encoding.encodeList id (ExecCNF.dedupLiterals records), raw := raw} := by
    apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i
      rcases hout with ⟨⟨h3, h4, h5, h6, h7⟩, h1, h2⟩
      fin_cases i
      · simpa [state, store, dedupStacks] using hsource.symm
      · simpa [state, store, dedupStacks] using h1.symm
      · simpa [state, store, dedupStacks] using h2.symm
      · simpa [state, store, dedupStacks] using h3.symm
      · simpa [state, store, dedupStacks] using h4.symm
      · simpa [state, store, dedupStacks] using h5.symm
      · simpa [state, store, dedupStacks] using h6.symm
      · simpa [state, store, dedupStacks] using h7.symm
    · intro i hi
      exact (hi ⟨i, rfl⟩).elim
    · intro i hi
      have hl : ¬ i.val < 8 := by
        intro h
        exact hi ⟨⟨i.val, h⟩, Fin.ext rfl⟩
      have h0 : i ≠ 0 := by intro h; subst i; exact hl (by decide)
      have h4 : i ≠ 4 := by intro h; subst i; exact hl (by decide)
      have h6 : i ≠ 6 := by intro h; subst i; exact hl (by decide)
      simp [a, state, store, h0, h4, h6]
  exact ⟨n, hn, out.regs, by simpa only [dedupCall, hend] using he⟩

def counterRegisters : Fin 2 → Fin 10 := Fin.castAdd 8
def counterStacks : Fin 2 → Fin 24 := ![0, 22]
def countCall : Command := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram counterRegisters counterStacks)

theorem countCall_eval (regs : Fin 10 → Bool) (records : List Word) (raw : Word) :
    Eval countCall (SubexpSunflowerProgram.CountRecords.loopSteps records)
      (state regs {source := Encoding.encodeList id records, dictionary := Encoding.encodeList id records, raw := raw})
      (state (readRegs regs 0 1 none) {dictionary := Encoding.encodeList id records, dimension := List.replicate records.length true, raw := raw}) := by
  let a := state regs {source := Encoding.encodeList id records, dictionary := Encoding.encodeList id records, raw := raw}
  let out := SubexpScopeCountSetup.counterState false false [] (List.replicate records.length true)
  have ht := SubexpScopeCountSetup.counter_trace records (regs 0) (regs 1)
  have hstart : projectState counterRegisters counterStacks a =
      SubexpScopeCountSetup.counterState (regs 0) (regs 1) (Encoding.encodeList id records) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [← hstart] at ht
  have he := eval_call_from_state SubexpScopeCountSetup.counterProgram counterRegisters counterStacks a
    (Fin.castAdd_injective _ _) (by decide) ht
  have hend : embedState counterRegisters counterStacks a out =
      state (readRegs regs 0 1 none) {dictionary := Encoding.encodeList id records, dimension := List.replicate records.length true, raw := raw} := by
    apply SubexpScanPrimitives.embedState_eq _ _ (Fin.castAdd_injective _ _) (by decide)
    · intro i
      fin_cases i <;> simp [state, readRegs, out,
        SubexpScopeCountSetup.counterState, ParserProgram.pair]
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := by rintro rfl; exact hi ⟨0, rfl⟩
      have h1 : i ≠ 1 := by rintro rfl; exact hi ⟨1, rfl⟩
      simp [a, state, readRegs, h0, h1]
    · intro i hi
      have h0 : i ≠ 0 := by rintro rfl; exact hi ⟨0, rfl⟩
      have h22 : i ≠ 22 := by rintro rfl; exact hi ⟨1, rfl⟩
      simp [a, state, store, h0, h22]
  change Eval countCall (SubexpSunflowerProgram.CountRecords.loopSteps records) a
    (embedState counterRegisters counterStacks a out) at he
  rw [hend] at he
  exact he

def finish : Command := .seq (.call (StackRoutines.clearProgram 4 0 1))
  (.seq (Subexp.TupleProgram.pushConst 8 0 false)
    (.seq (.call (StackRoutines.transferProgram 22 8 0 1)) RegisterResetProgram.all))

theorem finish_eval (regs : Fin 10 → Bool) (dictionary body : Word) (n : ℕ) :
    Eval finish (2 * dictionary.length + 3 * n + 18)
      (state regs {dictionary := dictionary, output := body, dimension := List.replicate n true})
      (StructuredProgram.ioState (8 : Fin 24) (Encoding.encodeNat n ++ body)) := by
  let a := state regs {dictionary := dictionary, output := body, dimension := List.replicate n true}
  let b := state (readRegs regs 0 1 none) {output := body, dimension := List.replicate n true}
  have hclear : Eval (.call (StackRoutines.clearProgram (4 : Fin 24) (0 : Fin 10) 1))
      (2 * dictionary.length + 3) a b := by
    simpa [a, b, state, StackRoutines.clearStacks] using Subexp.TupleProgram.clear_eval 4 0 1 a
  let c := state (Function.update b.regs 0 false)
    {output := false :: body, dimension := List.replicate n true}
  have hpush : Eval (Subexp.TupleProgram.pushConst 8 0 false) 2 b c := by
    simpa [b, c, state, Subexp.TupleProgram.pushedState] using
      Subexp.TupleProgram.pushConst_eval (8 : Fin 24) (0 : Fin 10) false b
  let d := state (readRegs c.regs 0 1 none) {output := Encoding.encodeNat n ++ body}
  have hmove : Eval (.call (StackRoutines.transferProgram (22 : Fin 24) 8 (0 : Fin 10) 1))
      (3 * n + 3) c d := by
    simpa [c, d, state, StackRoutines.transferStacks, Encoding.encodeNat,
      List.reverse_replicate, List.append_assoc] using
      Subexp.TupleProgram.transfer_eval (22 : Fin 24) 8 (0 : Fin 10) 1
        (by decide) (by decide) c
  have hreset := RegisterResetProgram.all_eval d
  have hend : RegisterResetProgram.zeroed d =
      StructuredProgram.ioState (8 : Fin 24) (Encoding.encodeNat n ++ body) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i = 8
      · subst i; rfl
      · simp [d, state, store, hi]
  have h := hclear.seq (hpush.seq (hmove.seq hreset))
  rw [hend] at h
  convert h using 1 <;> first | rfl | omega

end SubexponentialSAT.SubexpRawIDTransport

end OAI.Algorithms
