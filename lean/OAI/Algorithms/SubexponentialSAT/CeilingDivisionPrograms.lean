import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ChunkPartition

namespace OAI.Algorithms

/-!
# Ceiling division by fixed finite bit programs

The rounding suffix tests the actual remainder word and increments the actual
quotient word precisely when that remainder is nonzero. Natural division is
used only in the semantic statement of the full routine.
-/

namespace SubexponentialSAT.CeilingDivisionPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms

abbrev Data := StructuredProgram.State 8 8

def registers : Fin 3 ↪ Fin 8 where
  toFun i := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

def remainderPorts : CounterForPrograms.Ports 8 8 :=
  ⟨registers, 0, 1, by decide⟩

def quotientPorts : CounterForPrograms.Ports 8 8 :=
  ⟨registers, 7, 1, by decide⟩

abbrev incrementCmd {R S : ℕ} (p : CounterForPrograms.Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram true) p.register
    (CounterForPrograms.stackPorts p))

noncomputable def incrementResult {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) : StructuredProgram.State R S :=
  CounterForPrograms.install p d false false (d.regs (p.register 2))
    (ripple true (d.stacks p.counter)) []

theorem increment_eval {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (incrementCmd p) (rippleCost true (d.stacks p.counter) + 1)
      d (incrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram true) p.register
    (CounterForPrograms.stackPorts p) d p.register.injective
    (CounterForPrograms.stackPorts p).injective
    (CounterForPrograms.ripple_local_trace true (d.regs (p.register 0))
      (d.regs (p.register 1)) (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (incrementCmd p) _
    (CounterForPrograms.install p d _ _ _ _ []) (incrementResult p d) at h
  rw [← hs, CounterForPrograms.install_self] at h
  exact h

theorem increment_counter {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) :
    (incrementResult p d).stacks p.counter = ripple true (d.stacks p.counter) :=
  CounterForPrograms.install_counter p d _ _ _ _ _

theorem increment_other {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) (hs : d.stacks p.scratch = [])
    (j : Fin S) (hc : j ≠ p.counter) :
    (incrementResult p d).stacks j = d.stacks j := by
  by_cases hj : j = p.scratch
  · subst j
    exact (CounterForPrograms.install_scratch p d _ _ _ _ _).trans hs.symm
  · exact CounterForPrograms.install_other_stack p d _ _ _ _ _ j hc hj

abbrev roundCmd : StructuredCalls.Cmd 8 8 :=
  .seq (CounterForPrograms.zeroCmd remainderPorts)
    (.ite 2 (.base .skip) (incrementCmd quotientPorts))

def roundProgram := StructuredCalls.compiled roundCmd (0 : Fin 8) 7

theorem roundCmd_size : StructuredCalls.size roundCmd = 22 := rfl

def RoundOutput (d e : Data) : Prop :=
  e.stacks 7 = (if value (d.stacks 0) = 0 then d.stacks 7 else ripple true (d.stacks 7)) ∧
  ∀ j : Fin 8, j ≠ 7 → e.stacks j = d.stacks j

def roundBound (d : Data) : ℕ := 8 * ((d.stacks 0).length + (d.stacks 7).length) + 15

theorem round_eval (d : Data) (hs : d.stacks 1 = []) :
    ∃ n e, StructuredCalls.Eval roundCmd n d e ∧ RoundOutput d e ∧ n ≤ roundBound d := by
  let z := CounterForPrograms.zeroResult remainderPorts d
  have hz : StructuredCalls.Eval (CounterForPrograms.zeroCmd remainderPorts)
      (8 * (d.stacks 0).length + 6) d z := CounterForPrograms.zero_eval remainderPorts d hs
  have hzstacks : z.stacks = d.stacks :=
    CounterForPrograms.install_stacks_self remainderPorts d _ _ _ hs
  have hzscratch : z.stacks 1 = [] := by rw [hzstacks]; exact hs
  have hzflag : z.regs 2 = isZero (d.stacks 0) :=
    CounterForPrograms.install_register remainderPorts d _ _ _ _ _ 2
  by_cases hv : value (d.stacks 0) = 0
  · have hf : z.regs 2 = true := hzflag.trans ((isZero_eq_true_iff _).mpr hv)
    refine ⟨(8 * (d.stacks 0).length + 6) + (0 + 1), z,
      .seq hz (.ite_true hf (.base (.skip z))), ?_, ?_⟩
    · constructor
      · simp only [hv, ite_eq_left, hzstacks]
      · intro j _; exact congrFun hzstacks j
    · dsimp [roundBound]; omega
  · have hf : z.regs 2 = false :=
      hzflag.trans ((isZero_eq_false_iff _).mpr (by omega))
    refine ⟨(8 * (d.stacks 0).length + 6) +
        ((rippleCost true (z.stacks 7) + 1) + 1), incrementResult quotientPorts z,
      .seq hz (.ite_false hf (increment_eval quotientPorts z hzscratch)), ?_, ?_⟩
    · constructor
      · simpa only [quotientPorts, hv, ite_false, hzstacks] using
          increment_counter quotientPorts z
      · intro j hj
        exact (increment_other quotientPorts z hzscratch j hj).trans (congrFun hzstacks j)
    · have hb := rippleCost_le true (z.stacks 7)
      rw [hzstacks] at hb ⊢
      dsimp [roundBound]
      omega

theorem round_value (d e : Data) (h : RoundOutput d e) :
    value (e.stacks 7) = value (d.stacks 7) + if value (d.stacks 0) = 0 then 0 else 1 := by
  rw [h.1]
  by_cases hz : value (d.stacks 0) = 0 <;> simp [hz, value_increment]

theorem round_length (d e : Data) (h : RoundOutput d e) :
    (e.stacks 7).length ≤ (d.stacks 7).length + 1 := by
  rw [h.1]
  split_ifs
  · omega
  · exact ripple_length_le true _

end SubexponentialSAT.CeilingDivisionPrograms

end OAI.Algorithms
