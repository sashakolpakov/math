import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanPrimitives

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls SubexpIncidencePlanPrimitives

abbrev Data := StructuredProgram.State 10 10
abbrev unary (n : ℕ) := List.replicate n true

abbrev data (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) : Data :=
  ⟨regs, ![base.stacks 0, [], base.stacks 2, [], base.stacks 4,
    unary j, unary n, out, base.stacks 8, base.stacks 9]⟩

def indexPrefix (js : List ℕ) : List Bool := js.flatMap fun j => true :: Encoding.frame (unary j)

abbrev setSelected : Cmd 10 10 := .base (.atom (.set 4 true))
def selected (d : Data) : Data := ⟨Function.update d.regs 4 true, d.stacks⟩
abbrev emitCurrent : Cmd 10 10 := .seq (copy 5 1 3) (.seq setSelected (.seq emit (increment 5)))

theorem emitCurrent_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Eval emitCurrent (12*j+20) (data base regs j n out)
      (data base rf (j+1) n (true :: Encoding.frame (unary j) ++ out)) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = regs i) := by
  let a := data base regs j n out
  let b := copied 5 1 a
  let c := selected b
  let d := emitted true (unary j) c
  let e := incremented 5 d
  have h1 := copy_eval 5 1 3 a (by decide) (by decide) (by decide) (by rfl)
  have h2 : Eval setSelected 1 b c := .base (.atom _ _)
  have h3 := emit_eval true (unary j) c
    (by simp [c, selected, b, copied, StackRoutines.copyStacks, a ])
    (by simp [c, selected])
  have h4 := increment_eval 5 d
  have he : e = data base e.regs (j+1) n (true :: Encoding.frame (unary j) ++ out) := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [ d, emitted, c, selected, b, copied,
      StackRoutines.copyStacks, a, List.replicate_succ]
  have h := h1.seq (h2.seq (h3.seq h4))
  change Eval emitCurrent _ a e at h
  rw [he] at h
  refine ⟨e.regs, ?_, ?_⟩
  · convert h using 1
    simp [a, SubexpNormalizeProgram.emitIfSelectedSteps]
    omega
  · intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    have h4 : i ≠ 4 := by intro h; subst i; change 7 ≤ 4 at hi; omega
    simp [e, incremented, d, emitted, c, selected, b, copied, readRegs, a, h0, h1, h4]

abbrev peek : Cmd 10 10 := .base (.atom (.peek 6 7 9))
abbrev pop : Cmd 10 10 := .base (.atom (.pop 6 7 9))
abbrev loop : Cmd 10 10 := .while 9 (.seq pop (.seq emitCurrent peek))
abbrev command : Cmd 10 10 := .seq peek loop

abbrev testedRegs (regs : Fin 10 → Bool) (n : ℕ) : Fin 10 → Bool :=
  readRegs regs 7 9 (unary n).head?

theorem tested_active (regs : Fin 10 → Bool) (n : ℕ) :
    testedRegs regs n 9 = decide (n ≠ 0) := by
  cases n <;> simp [testedRegs, readRegs, List.replicate_succ]

theorem peek_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    Eval peek 1 (data base regs j n out) (data base (testedRegs regs n) j n out) := by
  exact .base (.atom _ _)

theorem pop_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    Eval pop 1 (data base regs j (n+1) out)
      (data base (readRegs regs 7 9 (some true)) j n out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (6 : Fin 10) 7 9)
    (data base regs j (n+1) out))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · simp [ StructuredProgram.Atom.instr, execInstr, List.replicate_succ]
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, List.replicate_succ]

def steps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | j, n+1 => 12*j+23 + steps (j+1) n

theorem loop_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool)
    (hg : regs 9 = decide (n ≠ 0)) :
    ∃ rf, Eval loop (steps j n) (data base regs j n out)
      (data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)) ∧ rf 9 = false := by
  induction n generalizing regs j out with
  | zero =>
      refine ⟨regs, ?_, by simpa using hg⟩
      simpa [steps, indexPrefix] using
        (Eval.while_false (body := .seq pop (.seq emitCurrent peek))
          (a := data base regs j 0 out) (show regs 9 = false by simpa using hg))
  | succ n ih =>
      obtain ⟨re, he, hr⟩ := emitCurrent_eval base (readRegs regs 7 9 (some true)) j n out
      have hp := pop_eval base regs j n out
      have ht := peek_eval base re (j+1) n (true :: Encoding.frame (unary j) ++ out)
      obtain ⟨rf, hf, hrf⟩ := ih (testedRegs re n) (j+1)
        (true :: Encoding.frame (unary j) ++ out) (tested_active re n)
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
  exact ⟨rf, (peek_eval base regs j n out).seq h, hr⟩

theorem steps_le (j n : ℕ) : 1 + steps j n ≤ n * (12*(j+n)+23) + 2 := by
  induction n generalizing j with
  | zero => simp [steps]
  | succ n ih =>
      have h := ih (j+1)
      simp only [steps]
      nlinarith

abbrev program : Program 10 10 (size command + 1) := compiled command 5 7

theorem program_trace (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Trace program (steps j n + 2)
      ((data base regs j n out).withPC (some program.entry))
      ((data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)).withPC none) := by
  obtain ⟨rf, h, _⟩ := command_eval base regs j n out
  refine ⟨rf, ?_⟩
  convert compiled_halt_trace h 5 7 using 1
  omega

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
