import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.PowerPrograms
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Source-preserving variable-power calls on fixed assigned ports. -/

namespace SubexponentialSAT.PowerCalls

open BitProgram StructuredCalls

structure Ports (S : ℕ) where
  base : Fin S
  exponent : Fin S
  out : Fin S
  work : Fin 7 ↪ Fin S
  out_ne_base : out ≠ base
  out_ne_exponent : out ≠ exponent
  work_ne_base : ∀ i, work i ≠ base
  work_ne_exponent : ∀ i, work i ≠ exponent
  work_ne_out : ∀ i, work i ≠ out

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

def Valid {S : ℕ} (p : Ports S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

@[simp] theorem base_ne_work {S : ℕ} (p : Ports S) (i : Fin 7) :
    p.base ≠ p.work i := (p.work_ne_base i).symm
@[simp] theorem exponent_ne_work {S : ℕ} (p : Ports S) (i : Fin 7) :
    p.exponent ≠ p.work i := (p.work_ne_exponent i).symm
@[simp] theorem out_ne_work {S : ℕ} (p : Ports S) (i : Fin 7) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

def powerPorts {S : ℕ} (p : Ports S) : Fin 9 → Fin S :=
  ![p.base, p.work 0, p.out, p.work 1, p.work 2, p.work 3,
    p.work 4, p.work 5, p.work 6]

theorem powerPorts_injective {S : ℕ} (p : Ports S) :
    Function.Injective (powerPorts p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [powerPorts, p.work.injective.eq_iff, p.work_ne_base,
      p.work_ne_out, p.out_ne_base, p.out_ne_base.symm]

abbrev rawPower {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram PowerPrograms.program id (powerPorts p))

abbrev clearCounter {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (StackRoutines.clearProgram (p.work 0) 0 1)

abbrev powerAt {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .seq (ArithmeticCalls.copyAt p.exponent (p.work 0) (p.work 4))
    (.seq (rawPower p) (clearCounter p))

def rawFinish {S : ℕ} (p : Ports S) (d : Data S) (f : PowerPrograms.Data) : Data S :=
  ⟨f.regs, Function.update (Function.update d.stacks (p.work 0) (f.stacks 1))
    p.out (f.stacks 2)⟩

theorem embed_start {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    embedState id (powerPorts p) d
      (PowerPrograms.state (ArithmeticCalls.afterCopy p.exponent (p.work 0) d).regs
        (d.stacks p.base) (d.stacks p.exponent) []) =
      ArithmeticCalls.afterCopy p.exponent (p.work 0) d := by
  apply embedState_eq_of_ports id (powerPorts p) d _ _
    Function.injective_id (powerPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [ArithmeticCalls.afterCopy, powerPorts, PowerPrograms.state, PowerPrograms.stackState,
        p.work.injective.eq_iff, hv.1, hv.2]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨1, h.symm⟩
    simp [ArithmeticCalls.afterCopy, h0]

theorem embed_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (f : PowerPrograms.Data) (hb : f.stacks 0 = d.stacks p.base)
    (hw : ∀ i : Fin 9, 3 ≤ i.val → f.stacks i = []) :
    embedState id (powerPorts p) d f = rawFinish p d f := by
  apply embedState_eq_of_ports id (powerPorts p) d _ _
    Function.injective_id (powerPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [rawFinish, powerPorts, p.work.injective.eq_iff, p.work_ne_out,
        p.out_ne_base.symm, hv.2, hb, hw]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨1, h.symm⟩
    have ho : i ≠ p.out := fun h => hi ⟨2, h.symm⟩
    simp [rawFinish, h0, ho]

theorem clear_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (f : PowerPrograms.Data) :
    Eval (clearCounter p) (2 * (f.stacks 1).length + 3) (rawFinish p d f)
      ⟨readRegs f.regs 0 1 none, Function.update d.stacks p.out (f.stacks 2)⟩ := by
  have h := ListRegisterProgram.clear_run (p.work 0) (0 : Fin 8) 1
    (rawFinish p d f).regs (rawFinish p d f).stacks
  have heq : StackRoutines.clearStacks (p.work 0) (rawFinish p d f).stacks =
      Function.update d.stacks p.out (f.stacks 2) := by
    funext i
    by_cases hi : i = p.work 0
    · subst i
      simp [StackRoutines.clearStacks, rawFinish, p.work_ne_out, hv.2]
    · simp [StackRoutines.clearStacks, rawFinish, Function.update_apply, hi]
  rw [heq] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, rawFinish,
    p.work_ne_out] using h

/-- Both source words are retained verbatim, and every work port is restored.
The exponent is represented by data, not by a parameter in the control table. -/
theorem powerAt_spec {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (powerAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.base) ^ BinaryArithmetic.toNat (d.stacks p.exponent) ∧
      word.length ≤ 1 + BinaryArithmetic.toNat (d.stacks p.exponent) * (d.stacks p.base).length ∧
      t ≤ PowerPrograms.runtimeBound (d.stacks p.base) (d.stacks p.exponent) +
        9 * (d.stacks p.exponent).length + 8 := by
  let ready := ArithmeticCalls.afterCopy p.exponent (p.work 0) d
  have hc := ArithmeticCalls.copyAt_eval p.exponent (p.work 0) (p.work 4) d
    (p.work_ne_exponent 0).symm (p.work_ne_exponent 4).symm
    (by intro h; exact (by decide : (4 : Fin 7) ≠ 0) (p.work.injective h))
    (hv.2 0) (hv.2 4)
  obtain ⟨f, hvalue, hlen, hb, hz, hwidth, hw, n, hn, ht⟩ :=
    PowerPrograms.run_value ready.regs (d.stacks p.base) (d.stacks p.exponent)
  have hp := eval_call_lifted PowerPrograms.program id (powerPorts p) d
    Function.injective_id (powerPorts_injective p) ht
  rw [embed_start p d hv, embed_finish p d hv f hb hw] at hp
  have hall := Eval.seq hc (Eval.seq hp (clear_finish p d hv f))
  refine ⟨_, readRegs f.regs 0 1 none, f.stacks 2, hall, hvalue, hlen, ?_⟩
  rw [hwidth]
  omega

end SubexponentialSAT.PowerCalls

end OAI.Algorithms
