import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorIndices

namespace OAI.Algorithms

/-!
# Building the selector table at runtime

A fixed program scans framed unary seed indices, pairs each with the current
unary candidate-array position, and increments that position. The output is
the raw sequence `frame key ++ frame value`, with no outer list tags.
-/

namespace SubexponentialSAT.Subexp.SelectionTableProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 3 6

def state (value present found : Bool)
    (source payload counter output acc scratch : List Bool) : Data :=
  ⟨![value, present, found], ![source, payload, counter, output, acc, scratch]⟩

def ports : RecordPrograms.Ports 3 6 where
  tag := 0
  present := 1
  found := 2
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def emitStack : Fin 4 → Fin 6 := ![0, 2, 3, 1]

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

abbrev emitter : Program 3 6 17 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id emitStack

/-- Remove the emitter's record tag, then reverse the raw frame into the
stream accumulator. -/
abbrev emitToAcc : Cmd 3 6 :=
  .seq (.call emitter)
    (.seq (RecordPrograms.atom (.pop 3 0 1))
      (.call (transferProgram (3 : Fin 6) 4 (0 : Fin 3) 1)))

abbrev advance : Cmd 3 6 :=
  .seq (RecordPrograms.atom (.set 0 true))
    (.seq (RecordPrograms.atom (.push 2 0))
      (.seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.set 1 true))))

abbrev callback : Cmd 3 6 :=
  .seq emitToAcc
    (.seq (.call (copyProgram (2 : Fin 6) 1 5 (0 : Fin 3) 1))
      (.seq emitToAcc advance))

abbrev command : Cmd 3 6 :=
  .seq (RecordPrograms.iterate ports callback)
    (.call (transferProgram (4 : Fin 6) 3 (0 : Fin 3) 1))

abbrev program : Program 3 6 (size command + 1) := compiled command 0 3

theorem program_label_count : size command + 1 = 74 := rfl

private theorem embed_eq {r s R S : ℕ} (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (base target : State R S) (inner : State r s)
    (hreg : ∀ i, target.regs (reg i) = inner.regs i)
    (hstk : ∀ i, target.stacks (stk i) = inner.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = base.regs j)
    (hfs : ∀ j, (¬ ∃ i, stk i = j) → target.stacks j = base.stacks j) :
    embedState reg stk base inner = target := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_register reg stk base inner hr i).trans (hreg i).symm
    · exact (embedState_register_frame reg stk base inner j hj).trans (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stk i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_stack reg stk base inner hs i).trans (hstk i).symm
    · exact (embedState_stack_frame reg stk base inner j hj).trans (hfs j hj).symm

private theorem emitter_eval (bits source counter acc : List Bool) (v p f : Bool) :
    Eval (.call emitter) (5 * bits.length + 7)
      (state v p f source bits.reverse counter [] acc [])
      (state true false f source [] counter (true :: Encoding.frame bits) acc []) := by
  let a := SubexpNormalizeProgram.filterState v p f source counter [] bits.reverse
  let b := SubexpNormalizeProgram.filterState true false f source counter
    (true :: Encoding.frame bits) []
  let base := state v p f source bits.reverse counter [] acc []
  have ha : embedState id emitStack base a = base := by
    apply embed_eq _ _ Function.injective_id emitStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj; rfl
  have hb : embedState id emitStack base b =
      state true false f source [] counter (true :: Encoding.frame bits) acc [] := by
    apply embed_eq _ _ Function.injective_id emitStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨3, by simpa [emitStack] using h.symm⟩
      have h3 : j ≠ 3 := fun h => hj ⟨2, by simpa [emitStack] using h.symm⟩
      fin_cases j <;> simp_all [emitStack, state, base]
  have ht : Trace SubexpNormalizeProgram.emitRecordProgram (5 * bits.length + 7)
      (a.withPC (some SubexpNormalizeProgram.emitRecordProgram.entry)) (b.withPC none) := by
    simpa [a, b] using SubexpNormalizeProgram.emitRecord_trace bits source counter [] v p f
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id emitStack base
    Function.injective_id emitStack_injective (a := a) (b := b) ht
  simpa only [ha, hb, emitter] using h

private theorem transfer_eval (src dst : Fin 6) (hne : src ≠ dst)
    (regs : Fin 3 → Bool) (stk : Stacks (Fin 6)) :
    Eval (.call (transferProgram src dst (0 : Fin 3) 1)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have ht := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 3) 1 hne (by decide) regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using ht

private theorem copy_eval (src dst tmp : Fin 6) (hsd : src ≠ dst)
    (hst : src ≠ tmp) (htd : tmp ≠ dst) (regs : Fin 3 → Bool) (stk : Stacks (Fin 6))
    (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp (0 : Fin 3) 1)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have ht := halt_after_trace _
    (copyProgram_trace src dst tmp (0 : Fin 3) 1 hsd hst htd (by decide) regs stk htmp) 7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using ht

private theorem pop_tag_eval (bits source counter acc : List Bool) (f : Bool) :
    Eval (RecordPrograms.atom (.pop 3 0 1)) 1
      (state true false f source [] counter (true :: Encoding.frame bits) acc [])
      (state true true f source [] counter (Encoding.frame bits) acc []) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (3 : Fin 6) (0 : Fin 3) 1)
    (state true false f source [] counter (true :: Encoding.frame bits) acc []) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem emitToAcc_eval (bits source counter acc : List Bool) (v p f : Bool) :
    Eval emitToAcc (11 * bits.length + 14)
      (state v p f source bits.reverse counter [] acc [])
      (state false false f source [] counter [] ((Encoding.frame bits).reverse ++ acc) []) := by
  have h₁ := emitter_eval bits source counter acc v p f
  have h₂ := pop_tag_eval bits source counter acc f
  have h₃ := transfer_eval (3 : Fin 6) 4 (by decide)
    (state true true f source [] counter (Encoding.frame bits) acc []).regs
    (state true true f source [] counter (Encoding.frame bits) acc []).stacks
  have hout : (⟨readRegs (state true true f source [] counter (Encoding.frame bits) acc []).regs 0 1 none,
      transferStacks 3 4 (state true true f source [] counter (Encoding.frame bits) acc []).stacks⟩ : Data) =
      state false false f source [] counter [] ((Encoding.frame bits).reverse ++ acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [state, transferStacks]
  rw [hout] at h₃
  have ht := Eval.seq h₁ (Eval.seq h₂ h₃)
  convert ht using 1
  all_goals simp [ state, Encoding.length_frame]
  all_goals omega

private theorem atom_eval_to (op : StructuredProgram.Atom 3 6) (a b : Data)
    (h : op.eval a = b) : Eval (RecordPrograms.atom op) 1 a b := by
  rw [← h]
  exact .base (.atom op a)

theorem advance_eval (source counter acc : List Bool) :
    Eval advance 4 (state false false false source [] counter [] acc [])
      (state false true false source [] (true :: counter) [] acc []) := by
  have h₁ : Eval (RecordPrograms.atom (.set 0 true)) 1
      (state false false false source [] counter [] acc [])
      (state true false false source [] counter [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  have h₂ : Eval (RecordPrograms.atom (.push 2 0)) 1
      (state true false false source [] counter [] acc [])
      (state true false false source [] (true :: counter) [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  have h₃ : Eval (RecordPrograms.atom (.set 0 false)) 1
      (state true false false source [] (true :: counter) [] acc [])
      (state false false false source [] (true :: counter) [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  have h₄ : Eval (RecordPrograms.atom (.set 1 true)) 1
      (state false false false source [] (true :: counter) [] acc [])
      (state false true false source [] (true :: counter) [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  exact Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))

def unary (n : ℕ) : List Bool := List.replicate n true

def pairBytes (key value : ℕ) : List Bool := Encoding.frame (unary key) ++ Encoding.frame (unary value)

def tableBytes (M : ℕ) (remaining : List ℕ) : List Bool :=
  (ReadPlan.selectionTable M remaining).flatMap (fun p => pairBytes p.1 p.2)

theorem tableBytes_eq_rawRecords (M : ℕ) (remaining : List ℕ) :
    tableBytes M remaining =
      SelectorProgram.rawRecords (SelectorProgram.selectionEntries M remaining) := by
  simp [tableBytes, SelectorProgram.rawRecords, SelectorProgram.selectionEntries,
    SelectorProgram.encodeEntries, List.flatMap_map, pairBytes, unary,
    SelectorProgram.unaryIndex ]

@[simp] theorem tableBytes_nil (M : ℕ) : tableBytes M [] = [] := rfl

@[simp] theorem tableBytes_cons (M n : ℕ) (remaining : List ℕ) :
    tableBytes M (n :: remaining) = pairBytes n M ++ tableBytes (M + 1) remaining := rfl

def callbackCost (M n : ℕ) : ℕ := 11 * n + 18 * M + 37

theorem callback_eval (M n : ℕ) (source acc : List Bool) :
    Eval callback (callbackCost M n)
      (state false true false source (unary n).reverse (unary M) [] acc [])
      (state false true false source [] (unary (M + 1)) [] ((pairBytes n M).reverse ++ acc) []) := by
  let acc₁ := (Encoding.frame (unary n)).reverse ++ acc
  let acc₂ := (Encoding.frame (unary M)).reverse ++ acc₁
  have h₁ := emitToAcc_eval (unary n) source (unary M) acc false true false
  have h₂ := copy_eval (2 : Fin 6) 1 5 (by decide) (by decide) (by decide)
    (state false false false source [] (unary M) [] acc₁ []).regs
    (state false false false source [] (unary M) [] acc₁ []).stacks rfl
  have hcopy : (⟨readRegs (state false false false source [] (unary M) [] acc₁ []).regs 0 1 none,
      copyStacks 2 1 (state false false false source [] (unary M) [] acc₁ []).stacks⟩ : Data) =
      state false false false source (unary M) (unary M) [] acc₁ [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [state, copyStacks]
  rw [hcopy] at h₂
  have h₃ : Eval emitToAcc (11 * M + 14)
      (state false false false source (unary M) (unary M) [] acc₁ [])
      (state false false false source [] (unary M) [] acc₂ []) := by
    simpa [unary, acc₂] using emitToAcc_eval (unary M) source (unary M) acc₁ false false false
  have h₄ := advance_eval source (unary M) acc₂
  have ht := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))
  convert ht using 1
  all_goals simp [ callbackCost, state, unary, pairBytes, acc₂, acc₁,
      List.reverse_append, List.append_assoc, List.replicate_succ]
  all_goals omega

abbrev baseState (M : ℕ) (acc : List Bool) : Data :=
  state false false false [] [] (unary M) [] acc []

theorem recordState_base (M : ℕ) (acc source payload : List Bool) (v p f : Bool) :
    RecordPrograms.state ports (baseState M acc) v p f source payload =
      state v p f source payload (unary M) [] acc [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [ ports, baseState, state]
  · funext i; fin_cases i <;> simp [ ports, baseState, state]

def indexRecords (remaining : List ℕ) : List (List Bool) := remaining.map unary

def loopCost (M : ℕ) : List ℕ → ℕ
  | [] => 1
  | n :: remaining =>
      (6 * n + 4) + (callbackCost M n + 2) + loopCost (M + 1) remaining + 1

/-- The actual framed-record loop preserves its growing counter and the raw
table accumulator in the exact input order. -/
theorem loop_eval (M : ℕ) (remaining : List ℕ) (suffix acc : List Bool) :
    Eval (RecordPrograms.loop ports callback) (loopCost M remaining)
      (RecordPrograms.afterTag ports (baseState M acc) (indexRecords remaining) suffix)
      (RecordPrograms.state ports
        (baseState (M + remaining.length) ((tableBytes M remaining).reverse ++ acc))
        false true false suffix []) := by
  induction remaining generalizing M acc with
  | nil =>
    simpa [loopCost, RecordPrograms.afterTag, indexRecords, tableBytes,
      ReadPlan.selectionTable, RecordPrograms.loop] using
      (Eval.while_false (test := ports.tag) (body := RecordPrograms.body ports callback)
        (a := RecordPrograms.state ports (baseState M acc) false true false suffix [])
        (by simp))
  | cons n remaining ih =>
    let tail := Encoding.encodeList id (indexRecords remaining) ++ suffix
    let nextAcc := (pairBytes n M).reverse ++ acc
    have hreader : Eval (RecordPrograms.reader ports) (6 * n + 4)
        (RecordPrograms.afterTag ports (baseState M acc) (indexRecords (n :: remaining)) suffix)
        (RecordPrograms.state ports (baseState M acc) false true false tail (unary n).reverse) := by
      simpa [RecordPrograms.afterTag, indexRecords, unary, tail] using
        RecordPrograms.reader_eval ports (baseState M acc) (unary n) tail [] true true false
    have hcallback : Eval callback (callbackCost M n)
        (RecordPrograms.state ports (baseState M acc) false true false tail (unary n).reverse)
        (RecordPrograms.state ports (baseState (M + 1) nextAcc) false true false tail []) := by
      simpa only [recordState_base] using callback_eval M n tail acc
    have hbranch : Eval
        (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
          (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
        (RecordPrograms.state ports (baseState (M + 1) nextAcc) false true false tail [])
        (RecordPrograms.afterTag ports (baseState (M + 1) nextAcc) (indexRecords remaining) suffix) := by
      apply Eval.ite_false (by simp)
      exact RecordPrograms.pop_list_eval ports (baseState (M + 1) nextAcc)
        (indexRecords remaining) suffix false true
    have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
    have hrest := ih (M + 1) nextAcc
    have hguard : (RecordPrograms.afterTag ports (baseState M acc)
        (indexRecords (n :: remaining)) suffix).regs ports.tag = true := by
      simp [RecordPrograms.afterTag, indexRecords]
    have ht := Eval.while_true hguard hbody hrest
    simpa [RecordPrograms.loop, RecordPrograms.body, loopCost, tableBytes_cons,
      List.length_cons, List.reverse_append, List.append_assoc, nextAcc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

abbrev inputState (M : ℕ) (remaining : List ℕ) : Data :=
  RecordPrograms.state ports (baseState M []) false false false
    (ProgramEncoding.encodeRecords (indexRecords remaining)) []

abbrev outputState (M : ℕ) (remaining : List ℕ) : Data :=
  state false false false [] [] (unary (M + remaining.length)) (tableBytes M remaining) [] []

def commandCost (M : ℕ) (remaining : List ℕ) : ℕ :=
  1 + (1 + loopCost M remaining) + (3 * (tableBytes M remaining).length + 3)

def traceCost (M : ℕ) (remaining : List ℕ) : ℕ := commandCost M remaining + 1

theorem command_eval (M : ℕ) (remaining : List ℕ) :
    Eval command (commandCost M remaining) (inputState M remaining) (outputState M remaining) := by
  have hinit := RecordPrograms.set_found_eval ports (baseState M []) false false false false
    (Encoding.encodeList id (indexRecords remaining) ++ []) []
  have hpop := RecordPrograms.pop_list_eval ports (baseState M []) (indexRecords remaining) [] false false
  have hloop := loop_eval M remaining [] []
  have hi := Eval.seq hinit (Eval.seq hpop hloop)
  let middle := state false true false [] [] (unary (M + remaining.length)) []
    (tableBytes M remaining).reverse []
  have hi' : Eval (RecordPrograms.iterate ports callback) (1 + (1 + loopCost M remaining))
      (inputState M remaining) middle := by
    simpa [RecordPrograms.iterate, inputState, ProgramEncoding.encodeRecords,
      recordState_base, middle] using hi
  have ht := transfer_eval (4 : Fin 6) 3 (by decide) middle.regs middle.stacks
  have hout : (⟨readRegs middle.regs 0 1 none, transferStacks 4 3 middle.stacks⟩ : Data) =
      outputState M remaining := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [middle, state, transferStacks]
  rw [hout] at ht
  simpa [command, commandCost, middle, state] using Eval.seq hi' ht

/-- Full halted trace of one fixed instruction table, with the table bytes
on output stack 3 and the incremented unary counter preserved on stack 2. -/
theorem program_trace (M : ℕ) (remaining : List ℕ) :
    Trace program (traceCost M remaining)
      ((inputState M remaining).withPC (some program.entry))
      ((outputState M remaining).withPC none) := by
  simpa [program, traceCost] using compiled_halt_trace (command_eval M remaining) 0 3

theorem primitive_run (M : ℕ) (remaining : List ℕ) :
    SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program * traceCost M remaining)
      (primitiveCfg program ((inputState M remaining).withPC (some program.entry)))
      (primitiveCfg program ((outputState M remaining).withPC none)) :=
  primitive_execution program ⟨_, le_rfl, program_trace M remaining⟩

@[simp] theorem pairBytes_length (key value : ℕ) :
    (pairBytes key value).length = 2 * key + 2 * value + 2 := by
  simp [pairBytes, unary]
  omega

theorem tableBytes_length_le (M : ℕ) (remaining : List ℕ) :
    (tableBytes M remaining).length ≤
      remaining.length * (2 * remaining.sum + 2 * (M + remaining.length) + 2) := by
  induction remaining generalizing M with
  | nil => simp
  | cons n remaining ih =>
    let B := 2 * (n + remaining.sum) + 2 * (M + (remaining.length + 1)) + 2
    have htail : (tableBytes (M + 1) remaining).length ≤ remaining.length * B :=
      (ih (M + 1)).trans (Nat.mul_le_mul_left _ (by dsimp [B]; omega))
    have hstep : 2 * n + 2 * M + 2 ≤ B := by dsimp [B]; omega
    simp only [tableBytes_cons, List.length_append, pairBytes_length,
      List.length_cons, List.sum_cons]
    calc
      _ ≤ B + remaining.length * B := Nat.add_le_add hstep htail
      _ = _ := by dsimp [B]; ring

theorem loopCost_le (M : ℕ) (remaining : List ℕ) :
    loopCost M remaining ≤
      1 + remaining.length * (17 * remaining.sum + 18 * (M + remaining.length) + 44) := by
  induction remaining generalizing M with
  | nil => simp [loopCost]
  | cons n remaining ih =>
    let B := 17 * (n + remaining.sum) + 18 * (M + (remaining.length + 1)) + 44
    have htail : loopCost (M + 1) remaining ≤ 1 + remaining.length * B :=
      (ih (M + 1)).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by dsimp [B]; omega)) _)
    have hstep : 17 * n + 18 * M + 44 ≤ B := by dsimp [B]; omega
    simp only [loopCost, callbackCost, List.length_cons, List.sum_cons]
    calc
      _ = (17 * n + 18 * M + 44) + loopCost (M + 1) remaining := by ring
      _ ≤ B + (1 + remaining.length * B) := Nat.add_le_add hstep htail
      _ = _ := by dsimp [B]; ring

/-- A fixed quadratic bound in the unary input size parameters. -/
theorem traceCost_quadratic (M : ℕ) (remaining : List ℕ) :
    traceCost M remaining ≤ 128 * (M + remaining.sum + remaining.length + 1) ^ 2 := by
  let t := M + remaining.sum + remaining.length + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hl : remaining.length ≤ t := by dsimp [t]; omega
  have hs : remaining.sum ≤ t := by dsimp [t]; omega
  have hm : M + remaining.length ≤ t := by dsimp [t]; omega
  have hloop : loopCost M remaining ≤ 1 + t * (17 * t + 18 * t + 44) :=
    (loopCost_le M remaining).trans (by gcongr)
  have htable : (tableBytes M remaining).length ≤ t * (2 * t + 2 * t + 2) :=
    (tableBytes_length_le M remaining).trans (by gcongr)
  dsimp [traceCost, commandCost]
  change _ ≤ 128 * t ^ 2
  have ht2 : t ≤ t ^ 2 := by nlinarith
  nlinarith

end SubexponentialSAT.Subexp.SelectionTableProgram

end OAI.Algorithms
