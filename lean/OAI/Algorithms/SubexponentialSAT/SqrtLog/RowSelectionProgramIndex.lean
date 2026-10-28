import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Runtime, self-delimiting natural-index alphabet. The range control is the
existing unary loop, with one delimiter inserted in each emitted payload. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Index
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpIncidencePlanPrimitives
open SubexponentialSAT.SubexpUnaryRangeProgram (data unary testedRegs tested_active)

abbrev Data := StructuredProgram.State 10 10

def alphabet (s : ℕ) : List (List Bool) := (List.range s).reverse.map Encoding.encodeNat

def indexPrefix (js : List ℕ) : List Bool :=
  js.flatMap fun j => true :: Encoding.frame (Encoding.encodeNat j)

theorem indexPrefix_eq_records (js : List ℕ) :
    indexPrefix js ++ [false] = ProgramEncoding.encodeRecords (js.map Encoding.encodeNat) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simpa [indexPrefix, ProgramEncoding.encodeRecords, Encoding.encodeList,
      List.append_assoc] using congrArg (fun x => true :: Encoding.frame (Encoding.encodeNat j) ++ x) ih

abbrev emitCurrent : Cmd 10 10 :=
  .seq (copy 5 1 3)
    (.seq (Subexp.TupleProgram.pushConst 1 0 false)
      (.seq SubexpUnaryRangeProgram.setSelected (.seq emit (increment 5))))

theorem emitCurrent_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Eval emitCurrent (12*j+27) (data base regs j n out)
      (data base rf (j+1) n (true :: Encoding.frame (Encoding.encodeNat j) ++ out)) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = regs i) := by
  let a := data base regs j n out
  let b := copied 5 1 a
  let c := Subexp.TupleProgram.pushedState 1 0 false b
  let d := SubexpUnaryRangeProgram.selected c
  let e := emitted true (Encoding.encodeNat j) d
  let f := incremented 5 e
  have h1 := copy_eval 5 1 3 a (by decide) (by decide) (by decide) (by rfl)
  have h2 := Subexp.TupleProgram.pushConst_eval 1 0 false b
  have h3 : Eval SubexpUnaryRangeProgram.setSelected 1 c d := .base (.atom _ _)
  have h4 := emit_eval true (Encoding.encodeNat j) d
    (by simp [d, SubexpUnaryRangeProgram.selected, c,
      b, copied, StackRoutines.copyStacks, a, Encoding.encodeNat])
    (by simp [d, SubexpUnaryRangeProgram.selected])
  have h5 := increment_eval 5 e
  have hf : f = data base f.regs (j+1) n
      (true :: Encoding.frame (Encoding.encodeNat j) ++ out) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i
    fin_cases i <;> simp [ e, emitted, d, SubexpUnaryRangeProgram.selected,
      c, b, copied, StackRoutines.copyStacks, a,
      List.replicate_succ]
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  change Eval emitCurrent _ a f at h
  rw [hf] at h
  refine ⟨f.regs, ?_, ?_⟩
  · convert h using 1
    simp [a, SubexpNormalizeProgram.emitIfSelectedSteps]
    omega
  · intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    have h4 : i ≠ 4 := by intro h; subst i; change 7 ≤ 4 at hi; omega
    simp [f, incremented, e, emitted, d, SubexpUnaryRangeProgram.selected,
      c, b, copied, readRegs, a, h0, h1, h4]

abbrev loop : Cmd 10 10 := .while 9
  (.seq SubexpUnaryRangeProgram.pop (.seq emitCurrent SubexpUnaryRangeProgram.peek))
abbrev command : Cmd 10 10 := .seq SubexpUnaryRangeProgram.peek loop

def steps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | j, n+1 => 12*j+30 + steps (j+1) n

theorem loop_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool)
    (hg : regs 9 = decide (n ≠ 0)) :
    ∃ rf, Eval loop (steps j n) (data base regs j n out)
      (data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)) ∧ rf 9 = false := by
  induction n generalizing regs j out with
  | zero =>
      refine ⟨regs, ?_, by simpa using hg⟩
      simpa [steps, indexPrefix] using
        (Eval.while_false
          (body := .seq SubexpUnaryRangeProgram.pop (.seq emitCurrent SubexpUnaryRangeProgram.peek))
          (a := data base regs j 0 out) (show regs 9 = false by simpa using hg))
  | succ n ih =>
      obtain ⟨re, he, hr⟩ := emitCurrent_eval base (readRegs regs 7 9 (some true)) j n out
      have hp := SubexpUnaryRangeProgram.pop_eval base regs j n out
      have ht := SubexpUnaryRangeProgram.peek_eval base re (j+1) n
        (true :: Encoding.frame (Encoding.encodeNat j) ++ out)
      obtain ⟨rf, hf, hrf⟩ := ih (testedRegs re n) (j+1)
        (true :: Encoding.frame (Encoding.encodeNat j) ++ out) (tested_active re n)
      have h := Eval.while_true (show (data base regs j (n+1) out).regs 9 = true by simpa using hg)
        (hp.seq (he.seq ht)) hf
      refine ⟨rf, ?_, hrf⟩
      convert h using 1
      · simp only [steps]; omega
      · simp [indexPrefix, List.range'_succ, List.reverse_cons, List.flatMap_append,
          List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem command_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Eval command (1 + steps j n) (data base regs j n out)
      (data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)) ∧ rf 9 = false := by
  obtain ⟨rf, h, hr⟩ := loop_eval base (testedRegs regs n) j n out (tested_active regs n)
  exact ⟨rf, (SubexpUnaryRangeProgram.peek_eval base regs j n out).seq h, hr⟩

theorem steps_le (j n : ℕ) : 1 + steps j n ≤ n * (12*(j+n)+30) + 2 := by
  induction n generalizing j with
  | zero => simp [steps]
  | succ n ih =>
      have h := ih (j+1)
      simp only [steps]
      nlinarith

abbrev program : Program 10 10 (size command + 1) := compiled command 6 7

theorem alphabet_eval (base : Data) (regs : Fin 10 → Bool) (s : ℕ) :
    ∃ rf, Eval command (1 + steps 0 s) (data base regs 0 s [false])
      (data base rf s 0 (ProgramEncoding.encodeRecords (alphabet s))) ∧ rf 9 = false := by
  obtain ⟨rf, h, hr⟩ := command_eval base regs 0 s [false]
  refine ⟨rf, ?_, hr⟩
  simpa [alphabet, indexPrefix_eq_records, ← List.range_eq_range'] using h

theorem alphabet_runsIn (base : Data) (regs : Fin 10 → Bool) (s : ℕ) :
    ∃ rf, RunsIn program (s*(12*s+30)+3)
      ((data base regs 0 s [false]).withPC (some program.entry))
      ((data base rf s 0 (ProgramEncoding.encodeRecords (alphabet s))).withPC none) := by
  obtain ⟨rf, h, _⟩ := alphabet_eval base regs s
  refine ⟨rf, 1 + steps 0 s + 1, ?_, compiled_halt_trace h 6 7⟩
  have hb := steps_le 0 s
  simpa using Nat.add_le_add_right hb 1

@[simp] theorem alphabet_length (s : ℕ) : (alphabet s).length = s := by simp [alphabet]

theorem mem_alphabet (s j : ℕ) : Encoding.encodeNat j ∈ alphabet s ↔ j < s := by
  simp [alphabet, Encoding.encodeNat_injective.eq_iff]

theorem alphabet_nodup (s : ℕ) : (alphabet s).Nodup := by
  have hn : ((List.range s).reverse).Nodup := List.nodup_reverse.mpr List.nodup_range
  exact hn.map Encoding.encodeNat_injective

/-- A length-m function into Fin a, serialized as m self-delimiting natural fields. -/
def encodeTuple {a m : ℕ} (f : Fin m → Fin a) : List Bool :=
  (List.ofFn fun i => Encoding.encodeNat (f i).val).flatten

/-- The actual row order emitted by the fixed tuple generator. -/
def tupleRows (a m : ℕ) : List (List Bool) :=
  Subexp.TupleProgram.powerRows (alphabet a) m [[]]

@[simp] theorem tupleRows_length (a m : ℕ) : (tupleRows a m).length = a ^ m := by
  simp [tupleRows, Subexp.TupleProgram.generated_count]

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

end OAI.Algorithms
