import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSunflowerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram
import OAI.Algorithms.SubexponentialSAT.FrontendProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.DyadicWidth

namespace OAI.Algorithms

/-!
# Deriving the clause count and index width from the current encoded formula

The fixed program preserves its source, counts its actual records, converts
the count to binary, computes its binary logarithm, and increments that value.
No supplied count or width is assumed. Temporary unary storage is bounded by
the number of source records. All other numeric storage is little-endian.
-/

namespace SubexponentialSAT.ExecNodeSizeProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple rippleCost)

abbrev Data := StructuredProgram.State 3 6
abbrev encode := Encoding.encodeList (id : List Bool → List Bool)

/-- Source, binary count, binary width, work source, unary count, scratch. -/
def data (v p z : Bool) (source count width work unary : List Bool) : Data :=
  ⟨CounterPrograms.counterRegs v p z, ![source, count, width, work, unary, []]⟩

abbrev zero := data false false false

private theorem call_io {r s l : ℕ} (p : Program r s l)
    (reg : Fin r → Fin 3) (stk : Fin s → Fin 6)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (a b : Data) (input output : List Bool) (n : ℕ)
    (ha : embedState reg stk a (StructuredProgram.ioState p.inputStack input) = a)
    (hb : embedState reg stk a (StructuredProgram.ioState p.outputStack output) = b)
    (h : Trace p n (initial p input) (terminal p output)) :
    Eval (.call (ProgramLinking.liftProgram p reg stk)) n a b := by
  have he := eval_call_lifted p reg stk a hr hs
    (a := StructuredProgram.ioState p.inputStack input)
    (b := StructuredProgram.ioState p.outputStack output) h
  simpa only [ha, hb] using he

abbrev initializeFlag : Cmd 3 6 := .base (.atom (.set 2 false))
abbrev copySource : Cmd 3 6 := .call (StackRoutines.copyProgram 0 3 5 0 1)
abbrev copyCount : Cmd 3 6 := .call (StackRoutines.copyProgram 1 2 5 0 1)

theorem initialize_eval (v p z : Bool) (source : List Bool) :
    Eval initializeFlag 1 (data v p z source [] [] [] []) (data v p false source [] [] [] []) := by
  have he := Eval.base (StructuredProgram.Eval.atom (.set (r := 3) (s := 6) 2 false)
    (data v p z source [] [] [] []))
  convert he using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;>
      simp [data, CounterPrograms.counterRegs,
        StructuredProgram.Atom.instr, execInstr]
  · rfl

theorem copySource_eval (v p : Bool) (source : List Bool) :
    Eval copySource (7 * source.length + 5) (data v p false source [] [] [] [])
      (zero source [] [] source []) := by
  let a := data v p false source [] [] [] []
  have he : Eval copySource (7 * source.length + 5) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 0 3 a.stacks⟩ :=
    Eval.call _ (by simpa [a, data] using
      (ListRegisterProgram.copy_run (r := 3) (s := 6) 0 3 5 0 1
        (by decide) (by decide) (by decide) (by decide) a.regs a.stacks rfl))
  convert he using 1
  apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
    simp [a, data, readRegs, StackRoutines.copyStacks, CounterPrograms.counterRegs]

theorem copyCount_eval (source count : List Bool) :
    Eval copyCount (7 * count.length + 5) (zero source count [] [] [])
      (zero source count count [] []) := by
  let a := zero source count [] [] []
  have he : Eval copyCount (7 * count.length + 5) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 1 2 a.stacks⟩ :=
    Eval.call _ (by simpa [a, data] using
      (ListRegisterProgram.copy_run (r := 3) (s := 6) 1 2 5 0 1
        (by decide) (by decide) (by decide) (by decide) a.regs a.stacks rfl))
  convert he using 1
  apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
    simp [a, data, readRegs, StackRoutines.copyStacks, CounterPrograms.counterRegs]

def countReg : Fin 2 → Fin 3 := ![0, 1]
def countStack : Fin 2 → Fin 6 := ![3, 4]
abbrev countRecords : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram SubexpSunflowerProgram.CountRecords.program countReg countStack)

theorem countReg_injective : Function.Injective countReg := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [countReg]
theorem countStack_injective : Function.Injective countStack := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [countStack]

theorem countRecords_eval (source : List Bool) (records : List (List Bool)) :
    Eval countRecords (SubexpSunflowerProgram.CountRecords.steps records)
      (zero source [] [] (encode records) [])
      (zero source [] [] [] (Encoding.encodeNat records.length)) := by
  apply call_io _ countReg countStack countReg_injective countStack_injective
    _ _ (encode records) (Encoding.encodeNat records.length)
  · apply embedState_eq_of_ports _ _ _ _ _ countReg_injective countStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  · apply embedState_eq_of_ports _ _ _ _ _ countReg_injective countStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;>
        simp_all [data, countStack, Fin.exists_fin_succ]
  · exact SubexpSunflowerProgram.CountRecords.complete_trace records

def binaryStack : Fin 4 → Fin 6 := ![4, 3, 1, 5]
abbrev binaryCount : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram FrontendProgram.initializeProgram id binaryStack)

theorem binaryStack_injective : Function.Injective binaryStack := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [binaryStack]

theorem binaryCount_eval (source : List Bool) (m : ℕ) :
    ∃ bits, value bits = m ∧ bits.length ≤ m ∧
      ∃ t ≤ FrontendProgram.initializeBound m,
        Eval binaryCount t (zero source [] [] [] (Encoding.encodeNat m))
          (zero source bits [] [] []) := by
  obtain ⟨bits, hv, hl, t, ht, hr⟩ := FrontendProgram.initialize_raw m []
  refine ⟨bits, hv, hl, t, ht, ?_⟩
  apply call_io _ id binaryStack Function.injective_id binaryStack_injective
    _ _ (Encoding.encodeNat m) bits
  · apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id binaryStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  · apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id binaryStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;>
        simp_all [data, binaryStack, Fin.exists_fin_succ]
  · have he : FrontendProgram.cfg none false false [] [] bits [] =
        terminal FrontendProgram.initializeProgram bits := by
      apply congrArg₂ (fun regs storage => (⟨none, regs, storage⟩ : Cfg 3 4 19))
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
    simpa only [List.append_nil, he] using hr

def logStack : Fin 3 → Fin 6 := ![2, 3, 5]
abbrev logarithm : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram SubexpParameterProgram.logProgram id logStack)

theorem logStack_injective : Function.Injective logStack := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [logStack]

theorem logarithm_eval (source count : List Bool) :
    ∃ bits, value bits = Nat.log2 (value count) ∧ bits.length ≤ count.length ∧
      ∃ t ≤ SubexpParameterProgram.logBound count.length,
        Eval logarithm t (zero source count count [] []) (zero source count bits [] []) := by
  obtain ⟨bits, hv, hl, t, ht, hr⟩ := SubexpParameterProgram.log_correct count
  refine ⟨bits, hv, hl, t, ht, ?_⟩
  apply call_io _ id logStack Function.injective_id logStack_injective _ _ count bits
  · apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id logStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  · apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id logStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;>
        simp_all [data, logStack, Fin.exists_fin_succ]
  · exact hr

def incrementStack : Fin 2 → Fin 6 := ![2, 5]
abbrev increment : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) id incrementStack)

theorem incrementStack_injective : Function.Injective incrementStack := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [incrementStack]

theorem increment_eval (source count bits : List Bool) :
    Eval increment (rippleCost true bits + 1)
      (zero source count bits [] []) (zero source count (ripple true bits) [] []) := by
  apply call_io _ id incrementStack Function.injective_id incrementStack_injective
    _ _ bits (ripple true bits)
  · apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  · apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;>
        simp_all [data, incrementStack, Fin.exists_fin_succ]
  · exact CounterPrograms.ripple_terminal_trace true bits

abbrev command : Cmd 3 6 :=
  .seq initializeFlag (.seq copySource (.seq countRecords
    (.seq binaryCount (.seq copyCount (.seq logarithm increment)))))

def program := compiled command 0 1

theorem command_eval (v p z : Bool) (records : List (List Bool)) :
    ∃ count width, value count = records.length ∧ value width = DyadicWidth.width records.length ∧
      count.length ≤ records.length ∧ width.length ≤ records.length + 1 ∧
      ∃ t, t + 1 ≤ 128 * ((encode records).length + 1) ^ 2 ∧
        Eval command t (data v p z (encode records) [] [] [] [])
          (zero (encode records) count width [] []) := by
  obtain ⟨count, hv, hlen, t₁, ht₁, hb⟩ := binaryCount_eval (encode records) records.length
  obtain ⟨log, hlv, hll, t₂, ht₂, hl⟩ := logarithm_eval (encode records) count
  have hi := increment_eval (encode records) count log
  have he := (initialize_eval v p z (encode records)).seq
    ((copySource_eval v p (encode records)).seq
      ((countRecords_eval (encode records) records).seq
        (hb.seq ((copyCount_eval (encode records) count).seq (hl.seq hi)))))
  refine ⟨count, ripple true log, hv, ?_, hlen, ?_, _, ?_, he⟩
  · rw [CounterPrograms.value_increment, hlv, hv, Nat.log2_eq_log_two]
    rfl
  · exact (CounterPrograms.ripple_length_le true log).trans (by omega)
  · have hc := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hr := CounterPrograms.rippleCost_le true log
    have hf := Encoding.length_encodeList_lower (id : List Bool → List Bool) records
    have hm : records.length ≤ (encode records).length := by simpa [encode] using Nat.le_of_succ_le hf
    have hbm := FrontendProgram.initializeBound_mono hm
    have hlm := SubexpParameterProgram.logBound_mono (hlen.trans hm)
    unfold FrontendProgram.initializeBound at ht₁ hbm
    unfold SubexpParameterProgram.logBound at ht₂ hlm
    change SubexpSunflowerProgram.CountRecords.steps records ≤ 3 * (encode records).length + 4 at hc
    nlinarith

theorem program_runs (v p z : Bool) (records : List (List Bool)) :
    ∃ count width, value count = records.length ∧ value width = DyadicWidth.width records.length ∧
      count.length ≤ records.length ∧ width.length ≤ records.length + 1 ∧
      RunsIn program (128 * ((encode records).length + 1) ^ 2)
        ((data v p z (encode records) [] [] [] []).withPC (some program.entry))
        ((zero (encode records) count width [] []).withPC none) := by
  obtain ⟨count, width, hcount, hwidth, hcl, hwl, t, ht, he⟩ := command_eval v p z records
  exact ⟨count, width, hcount, hwidth, hcl, hwl,
    t + 1, ht, compiled_halt_trace he 0 1⟩

/-- Generic fixed-port adapter, preserving every register and stack outside
the six assigned stack ports and three assigned registers. -/
theorem program_eval_at {R S : ℕ} (reg : Fin 3 → Fin R) (stk : Fin 6 → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : StructuredProgram.State R S) (v p z : Bool) (records : List (List Bool)) :
    ∃ count width, value count = records.length ∧ value width = DyadicWidth.width records.length ∧
      count.length ≤ records.length ∧ width.length ≤ records.length + 1 ∧
      ∃ t ≤ 128 * ((encode records).length + 1) ^ 2,
        Eval (.call (ProgramLinking.liftProgram program reg stk)) t
          (embedState reg stk frame (data v p z (encode records) [] [] [] []))
          (embedState reg stk frame (zero (encode records) count width [] [])) := by
  obtain ⟨count, width, hc, hw, hcl, hwl, t, ht, he⟩ := program_runs v p z records
  exact ⟨count, width, hc, hw, hcl, hwl, t, ht,
    eval_call_lifted program reg stk frame hr hs he⟩

def ambientReg : Fin 3 → Fin 32 := Fin.castAdd 29
def ambientStack : Fin 6 → Fin 32 := ![16, 19, 20, 0, 1, 2]

theorem ambientReg_injective : Function.Injective ambientReg := Fin.castAdd_injective 3 29
theorem ambientStack_injective : Function.Injective ambientStack := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [ambientStack]

def ambientProgram := ProgramLinking.liftProgram program ambientReg ambientStack

def result (d : StructuredProgram.State 32 32) (count width : List Bool) :
    StructuredProgram.State 32 32 :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    Function.update (Function.update d.stacks 19 count) 20 width⟩

/-- The concrete per-node ABI: derive ports 19 and 20 from the formula on 16,
using only initially empty ports 0, 1, and 2 as workspace. -/
theorem setup_eval (d : StructuredProgram.State 32 32) (records : List (List Bool))
    (hsource : d.stacks 16 = encode records)
    (hcount : d.stacks 19 = []) (hwidth : d.stacks 20 = [])
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = []) :
    ∃ count width, value count = records.length ∧ value width = DyadicWidth.width records.length ∧
      count.length ≤ records.length ∧ width.length ≤ records.length + 1 ∧
      ∃ t ≤ 128 * ((encode records).length + 1) ^ 2,
        Eval (.call ambientProgram) t d (result d count width) := by
  obtain ⟨count, width, hc, hw, hcl, hwl, t, ht, he⟩ := program_eval_at
    ambientReg ambientStack ambientReg_injective ambientStack_injective d
    (d.regs 0) (d.regs 1) (d.regs 2) records
  have ha : embedState ambientReg ambientStack d
      (data (d.regs 0) (d.regs 1) (d.regs 2) (encode records) [] [] [] []) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ ambientReg_injective ambientStack_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i
      · exact hsource
      · exact hcount
      · exact hwidth
      · exact h0
      · exact h1
      · exact h2
    · intro i hi; rfl
  have hb : embedState ambientReg ambientStack d (zero (encode records) count width [] []) =
      result d count width := by
    apply embedState_eq_of_ports _ _ _ _ _ ambientReg_injective ambientStack_injective
    · intro i; fin_cases i <;> simp [result, ambientReg, data, CounterPrograms.counterRegs]
    · intro i hi
      have hi0 : i ≠ 0 := by intro h; exact hi ⟨0, h.symm⟩
      have hi1 : i ≠ 1 := by intro h; exact hi ⟨1, h.symm⟩
      have hi2 : i ≠ 2 := by intro h; exact hi ⟨2, h.symm⟩
      simp [result, hi0, hi1, hi2]
    · intro i; fin_cases i <;> simp [result, ambientStack, data, hsource, h0, h1, h2]
    · intro i hi
      have hi19 : i ≠ 19 := by intro h; exact hi ⟨1, h.symm⟩
      have hi20 : i ≠ 20 := by intro h; exact hi ⟨2, h.symm⟩
      simp [result, hi19, hi20]
  rw [ha, hb] at he
  exact ⟨count, width, hc, hw, hcl, hwl, t, ht, he⟩

theorem encode_map {α : Type*} (enc : α → List Bool) (xs : List α) :
    encode (xs.map enc) = Encoding.encodeList enc xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, Encoding.encodeList, ih]

/-- This directly applies to nested clause encodings, without assuming any
supplied size word or index-width word. -/
theorem setup_encoded_eval {α : Type*} (enc : α → List Bool) (xs : List α)
    (d : StructuredProgram.State 32 32)
    (hsource : d.stacks 16 = Encoding.encodeList enc xs)
    (hcount : d.stacks 19 = []) (hwidth : d.stacks 20 = [])
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = []) :
    ∃ count width, value count = xs.length ∧ value width = DyadicWidth.width xs.length ∧
      count.length ≤ xs.length ∧ width.length ≤ xs.length + 1 ∧
      ∃ t ≤ 128 * ((Encoding.encodeList enc xs).length + 1) ^ 2,
        Eval (.call ambientProgram) t d (result d count width) := by
  simpa only [List.length_map, encode_map] using
    setup_eval d (xs.map enc) (by simpa only [encode_map] using hsource)
      hcount hwidth h0 h1 h2

theorem program_primitive (v p z : Bool) (records : List (List Bool)) :
    ∃ count width, value count = records.length ∧ value width = DyadicWidth.width records.length ∧
      count.length ≤ records.length ∧ width.length ≤ records.length + 1 ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * (128 * ((encode records).length + 1) ^ 2))
        (BitProgram.primitiveCfg program
          ((data v p z (encode records) [] [] [] []).withPC (some program.entry)))
        (BitProgram.primitiveCfg program
          ((zero (encode records) count width [] []).withPC none)) := by
  obtain ⟨count, width, hc, hw, hcl, hwl, t, ht, he⟩ := program_runs v p z records
  exact ⟨count, width, hc, hw, hcl, hwl,
    (BitProgram.primitive_trace program he).mono (Nat.mul_le_mul_left _ ht)⟩

end SubexponentialSAT.ExecNodeSizeProgram

end OAI.Algorithms
