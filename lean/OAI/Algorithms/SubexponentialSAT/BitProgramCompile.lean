import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgram

namespace OAI.Algorithms

/-! The finite Boolean-stack language compiles instruction for instruction to
an actual finite TM2 machine. The verified stack compiler then supplies measured
primitive tape executions. No source instruction contains an unbounded function.
-/

namespace SubexponentialSAT.BitProgram

open SubexponentialSAT.Computation

def compileInstr {r s l : ℕ} (i : Instr r s l) :
    Turing.TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin r → Bool) :=
  match i with
  | .halt => .halt
  | .goto next => .goto (fun _ => next)
  | .set dst value next =>
      .load (fun regs => Function.update regs dst value) (.goto (fun _ => next))
  | .copy dst src next =>
      .load (fun regs => Function.update regs dst (regs src)) (.goto (fun _ => next))
  | .bnot dst src next =>
      .load (fun regs => Function.update regs dst (!(regs src))) (.goto (fun _ => next))
  | .band dst a b next =>
      .load (fun regs => Function.update regs dst (regs a && regs b)) (.goto (fun _ => next))
  | .bor dst a b next =>
      .load (fun regs => Function.update regs dst (regs a || regs b)) (.goto (fun _ => next))
  | .bxor dst a b next =>
      .load (fun regs => Function.update regs dst (regs a ^^ regs b)) (.goto (fun _ => next))
  | .branch test yes no =>
      .branch (fun regs => regs test) (.goto (fun _ => yes)) (.goto (fun _ => no))
  | .push stack src next => .push stack (fun regs => regs src) (.goto (fun _ => next))
  | .peek stack value present next =>
      .peek stack (fun regs top => readRegs regs value present top) (.goto (fun _ => next))
  | .pop stack value present next =>
      .pop stack (fun regs top => readRegs regs value present top) (.goto (fun _ => next))

/-- All three finite dimensions are determined by the fixed source program. -/
abbrev tm {r s l : ℕ} (p : Program r s l) : Turing.FinTM2 where
  K := Fin s
  k₀ := p.inputStack
  k₁ := p.outputStack
  Γ := fun _ => Bool
  Λ := Fin l
  main := p.entry
  σ := Fin r → Bool
  initialState := fun _ => false
  m := fun label => compileInstr (p.code label)

abbrev bitMachine {r s l : ℕ} (p : Program r s l) : BitMachine where
  tm := tm p
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  finiteAlphabet := fun _ => (inferInstance : Finite Bool)

@[simp] theorem bitMachine_inputAlphabet_symm_apply {r s l : ℕ}
    (p : Program r s l) (b : Bool) :
    (bitMachine p).inputAlphabet.symm b = b := rfl

@[simp] theorem bitMachine_outputAlphabet_symm_apply {r s l : ℕ}
    (p : Program r s l) (b : Bool) :
    (bitMachine p).outputAlphabet.symm b = b := rfl

@[simp] theorem bitMachine_input_map {r s l : ℕ}
    (p : Program r s l) (input : List Bool) :
    input.map (bitMachine p).inputAlphabet.symm = input := by
  induction input with
  | nil => rfl
  | cons b input ih =>
      rw [List.map_cons, bitMachine_inputAlphabet_symm_apply, ih]

@[simp] theorem bitMachine_output_map {r s l : ℕ}
    (p : Program r s l) (output : List Bool) :
    output.map (bitMachine p).outputAlphabet.symm = output := by
  induction output with
  | nil => rfl
  | cons b output ih =>
      rw [List.map_cons, bitMachine_outputAlphabet_symm_apply, ih]

abbrev tmCfg {r s l : ℕ} (p : Program r s l) (c : Cfg r s l) : (tm p).Cfg :=
  ⟨c.pc, c.regs, c.stacks⟩

theorem compileInstr_correct {r s l : ℕ} (p : Program r s l)
    (i : Instr r s l) (c : Cfg r s l) :
    Turing.TM2.stepAux (compileInstr i) c.regs c.stacks = tmCfg p (execInstr i c) := by
  cases i <;> simp [compileInstr, execInstr, tmCfg]
  all_goals first | rfl | (split <;> rfl)

/-- A source instruction is exactly one finite TM2 block execution. -/
theorem tm_step {r s l : ℕ} (p : Program r s l) (c : Cfg r s l) :
    (tm p).step (tmCfg p c) = (step p c).map (tmCfg p) := by
  rcases c with ⟨pc, regs, stk⟩
  cases pc with
  | none => rfl
  | some label =>
      change some (Turing.TM2.stepAux (compileInstr (p.code label)) regs stk) = _
      exact congrArg some (compileInstr_correct p (p.code label) ⟨some label, regs, stk⟩)

theorem tm_trace {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) :
    Computation.Trace (tm p).step n (tmCfg p a) (tmCfg p b) := by
  induction h with
  | refl a => exact .refl _
  | cons hs ht ih =>
      apply Computation.Trace.cons _ ih
      rw [tm_step, hs]
      rfl

theorem tm_runsIn {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : RunsIn p n a b) :
    Computation.RunsIn (tm p).step n (tmCfg p a) (tmCfg p b) := by
  obtain ⟨steps, hsteps, htrace⟩ := h
  exact ⟨steps, hsteps, tm_trace p htrace⟩

@[simp] theorem tm_initial {r s l : ℕ} (p : Program r s l) (input : List Bool) :
    tmCfg p (initial p input) = Turing.initList (tm p) input := by
  congr 1

@[simp] theorem tm_terminal {r s l : ℕ} (p : Program r s l) (output : List Bool) :
    tmCfg p (terminal p output) = Turing.haltList (tm p) output := by
  congr 1

theorem bitMachine_outputs {r s l : ℕ} (p : Program r s l)
    {input output : List Bool} {n : ℕ}
    (h : RunsIn p n (initial p input) (terminal p output)) :
    (bitMachine p).OutputsInTime input output n := by
  rw [BitMachine.outputsInTime_iff_runsIn]
  rw [bitMachine_input_map, bitMachine_output_map]
  change Computation.RunsIn (tm p).step n
    (Turing.initList (tm p) input) (Turing.haltList (tm p) output)
  simpa only [tm_initial, tm_terminal] using tm_runsIn p h

/-- The output is a fully specified primitive tape machine, obtained by the
previously verified finite-control and stack-block compilers. -/
noncomputable abbrev primitive {r s l : ℕ} (p : Program r s l) : PrimitiveMachine :=
  StackAdapter.compiledMachine (bitMachine p)

noncomputable abbrev primitiveCfg {r s l : ℕ} (p : Program r s l) (c : Cfg r s l) :
    (primitive p).Cfg := StackAdapter.compiledSourceCfg (bitMachine p) (tmCfg p c)

noncomputable abbrev primitiveOverhead {r s l : ℕ} (p : Program r s l) : ℕ :=
  StackAdapter.overhead (bitMachine p)

theorem primitiveOverhead_pos {r s l : ℕ} (p : Program r s l) :
    0 < primitiveOverhead p := StackAdapter.overhead_pos _

theorem primitive_execution {r s l : ℕ} (p : Program r s l)
    {a b : Cfg r s l} {n : ℕ} (h : RunsIn p n a b) :
    Computation.RunsIn (primitive p).step (primitiveOverhead p * n)
      (primitiveCfg p a) (primitiveCfg p b) :=
  StackAdapter.compiled_execution (bitMachine p) (tm_runsIn p h)

theorem primitive_trace {r s l : ℕ} (p : Program r s l)
    {a b : Cfg r s l} {n : ℕ} (h : Trace p n a b) :
    Computation.RunsIn (primitive p).step (primitiveOverhead p * n)
      (primitiveCfg p a) (primitiveCfg p b) :=
  primitive_execution p ⟨n, le_rfl, h⟩

@[simp] theorem primitive_initial {r s l : ℕ} (p : Program r s l) (input : List Bool) :
    primitiveCfg p (initial p input) = (primitive p).init input := by
  change StackAdapter.compiledSourceCfg (bitMachine p) (tmCfg p (initial p input)) =
    (StackAdapter.compiledMachine (bitMachine p)).init input
  rw [tm_initial]
  have h := StackAdapter.compiled_initial (bitMachine p) input
  rw [bitMachine_input_map] at h
  exact h

theorem primitive_terminal {r s l : ℕ} (p : Program r s l) (answer : Bool) :
    (primitiveCfg p (terminal p [answer])).state = .inl answer := by
  change (StackAdapter.compiledSourceCfg (bitMachine p)
    (tmCfg p (terminal p [answer]))).state = .inl answer
  rw [tm_terminal]
  have h := StackAdapter.compiled_terminal (bitMachine p) answer
  rw [bitMachine_output_map] at h
  exact h

theorem primitive_outputs {r s l : ℕ} (p : Program r s l)
    {input : List Bool} {answer : Bool} {n : ℕ}
    (h : RunsIn p n (initial p input) (terminal p [answer])) :
    (primitive p).OutputsInTime input answer (primitiveOverhead p * n) := by
  refine ⟨primitiveCfg p (terminal p [answer]), ?_, primitive_terminal p answer⟩
  simpa using primitive_execution p h

/-- Halting exposes the first output bit, without a cleanup precondition on
the remaining stacks or the finite Boolean registers. -/
theorem primitive_halted {r s l : ℕ} (p : Program r s l) (c : Cfg r s l)
    (halted : c.pc = none) :
    (primitiveCfg p c).state = .inl ((c.stacks p.outputStack).head?.getD false) := by
  rcases c with ⟨pc, regs, stk⟩
  simp only at halted
  subst pc
  change Sum.inl (StackAdapter.outputBit (bitMachine p) (stk p.outputStack).head?) = _
  cases (stk p.outputStack).head? <;> rfl

theorem primitive_outputs_of_halted {r s l : ℕ} (p : Program r s l)
    {input : List Bool} {answer : Bool} {n : ℕ} {final : Cfg r s l}
    (h : RunsIn p n (initial p input) final) (halted : final.pc = none)
    (output : (final.stacks p.outputStack).head? = some answer) :
    (primitive p).OutputsInTime input answer (primitiveOverhead p * n) := by
  refine ⟨primitiveCfg p final, ?_, ?_⟩
  · simpa using primitive_execution p h
  · rw [primitive_halted p final halted, output]
    rfl

end SubexponentialSAT.BitProgram

end OAI.Algorithms
