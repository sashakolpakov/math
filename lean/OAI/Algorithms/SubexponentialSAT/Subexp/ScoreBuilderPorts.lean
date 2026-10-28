import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-!
# The fixed global scorer stack layout

The preparation and candidate routines use the controller's 48 stacks through
explicit injective maps. The finalizer moves ordered score records to port 0
and clears the temporary selected-pair table, restoring the higher-stack
environment expected by the sequential controller.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 16 48

def candidatePorts : Fin 36 → Fin 48 :=
  ![0,1,2,10,3,4,5,6,7,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,
    35,36,8,37,19,38,39,40,41,42,43,44]

def preparationPorts : Fin 34 → Fin 48 :=
  ![0,1,2,3,4,5,6,7,20,21,22,23,24,25,26,27,28,29,31,32,33,35,36,37,
    38,41,42,43,44,40,46,45,47,19]

theorem candidatePorts_injective : Function.Injective candidatePorts := by decide
theorem preparationPorts_injective : Function.Injective preparationPorts := by decide

theorem candidatePorts_controller (i : Fin 36) :
    8 ≤ (candidatePorts i).val → (candidatePorts i).val < 20 →
      candidatePorts i = 8 ∨ candidatePorts i = 10 ∨ candidatePorts i = 19 := by
  exact (show ∀ i : Fin 36, 8 ≤ (candidatePorts i).val → (candidatePorts i).val < 20 →
    candidatePorts i = 8 ∨ candidatePorts i = 10 ∨ candidatePorts i = 19 by decide) i

theorem preparationPorts_controller (i : Fin 34) :
    8 ≤ (preparationPorts i).val → (preparationPorts i).val < 20 →
      preparationPorts i = 19 := by
  exact (show ∀ i : Fin 34, 8 ≤ (preparationPorts i).val → (preparationPorts i).val < 20 →
    preparationPorts i = 19 by decide) i

/-- A lifted actual subroutine that changes one local stack changes exactly
the corresponding caller stack. This proof does not execute an abstract map;
the premise is the concrete subroutine's instruction trace. -/
theorem call_lifted_update {r s S labels n : ℕ} (p : Program r s labels)
    (ports : Fin s → Fin S) (hinj : Function.Injective ports)
    (caller : State r S) (a b : State r s) (out : Fin s) (value : List Bool)
    (haRegs : a.regs = caller.regs)
    (haStacks : ∀ i, a.stacks i = caller.stacks (ports i))
    (hbStacks : b.stacks = Function.update a.stacks out value)
    (ht : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p id ports)) n caller
      ⟨b.regs, Function.update caller.stacks (ports out) value⟩ := by
  have hcall := eval_call_lifted p id ports caller Function.injective_id hinj ht
  have hstart : embedState id ports caller a = caller := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      exact (show (embedState id ports caller a).regs j = a.regs j by
        simpa only [id_eq] using embedState_register id ports caller a Function.injective_id j).trans
          (congrFun haRegs j)
    · funext j
      by_cases hj : ∃ i, ports i = j
      · obtain ⟨i, rfl⟩ := hj
        exact (embedState_stack id ports caller a hinj i).trans (haStacks i)
      · exact embedState_stack_frame id ports caller a j hj
  have hend : embedState id ports caller b =
      (⟨b.regs, Function.update caller.stacks (ports out) value⟩ : State r S) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      change (embedState id ports caller b).regs j = b.regs j
      exact embedState_register id ports caller b Function.injective_id j
    · funext j
      by_cases hj : ∃ i, ports i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [hinj.extend_apply, hbStacks]
        by_cases hi : i = out
        · subst i; simp
        · have hneq : ports i ≠ ports out := fun h => hi (hinj h)
          simp [hi, hneq, haStacks]
      · rw [Function.extend_apply' _ _ _ hj]
        have hneq : j ≠ ports out := fun h => hj ⟨out, h.symm⟩
        simp [hneq]
  simpa only [hstart, hend] using hcall

/-- Runtime tables are data on six fixed stack ports. All other high ports are
empty at a complete scorer-call boundary. -/
def environment (alphabet depth rawPairs seedIndices seedCount : List Bool) : Fin 48 → List Bool :=
  fun j => if j = 30 then alphabet else if j = 34 then depth
    else if j = 39 then alphabet else if j = 45 then rawPairs
    else if j = 46 then seedIndices else if j = 47 then seedCount else []

abbrev finish : Cmd 16 48 :=
  .seq (.call (transferProgram 41 42 0 1))
    (.seq (.call (transferProgram 42 0 0 1)) (.call (clearProgram 40 0 1)))

def finished (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update d.stacks
      0 (d.stacks 41)) 40 []) 41 []) 42 []⟩

/-- Two transfers restore the original byte order of the score records. The
selected-pair table is then cleared by actual pop instructions. -/
theorem finish_eval (d : Data) (hzero : d.stacks 0 = []) (htmp : d.stacks 42 = []) :
    Eval finish (6 * (d.stacks 41).length + 2 * (d.stacks 40).length + 9) d (finished d) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, transferStacks 41 42 d.stacks⟩
  let b : Data := ⟨readRegs a.regs 0 1 none, transferStacks 42 0 a.stacks⟩
  have h₁ := TupleProgram.transfer_eval (41 : Fin 48) 42 (0 : Fin 16) 1
    (by decide) (by decide) d
  have h₂ := TupleProgram.transfer_eval (42 : Fin 48) 0 (0 : Fin 16) 1
    (by decide) (by decide) a
  have h₃ := TupleProgram.clear_eval (40 : Fin 48) (0 : Fin 16) 1 b
  have he : (⟨readRegs b.regs 0 1 none, clearStacks 40 b.stacks⟩ : Data) = finished d := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [a, b, readRegs_reset]
    · funext j
      by_cases h0 : j = 0
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      by_cases h40 : j = 40
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      by_cases h41 : j = 41
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      by_cases h42 : j = 42
      · subst j; simp [a, b, clearStacks, transferStacks, hzero, htmp]
      · simp [a, b, clearStacks, transferStacks, hzero, htmp, h0, h40, h41, h42]
  rw [he] at h₃
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1 ; simp [ a, b, transferStacks, hzero, htmp] ; omega

theorem finished_output (d : Data) : (finished d).stacks 0 = d.stacks 41 := by
  simp [finished]

theorem finished_frame (d : Data) (j : Fin 48)
    (h0 : j ≠ 0) (h40 : j ≠ 40) (h41 : j ≠ 41) (h42 : j ≠ 42) :
    (finished d).stacks j = d.stacks j := by
  simp [finished, h0, h40, h41, h42]

theorem finished_controller_frame (d : Data) (j : Fin 48)
    (hj : j.val < 20) (h0 : j ≠ 0) :
    (finished d).stacks j = d.stacks j := by
  apply finished_frame d j h0 <;> intro h <;> subst j <;> omega

theorem finished_highState (d : Data)
    (alphabet depth rawPairs seedIndices seedCount : List Bool)
    (hframe : ∀ j : Fin 48, 20 ≤ j.val → j ≠ 40 → j ≠ 41 → j ≠ 42 →
      d.stacks j = environment alphabet depth rawPairs seedIndices seedCount j) :
    SequentialProgram.HighState (environment alphabet depth rawPairs seedIndices seedCount)
      (finished d).stacks := by
  intro j hj
  by_cases h40 : j = 40
  · subst j; simp [finished, environment]
  by_cases h41 : j = 41
  · subst j; simp [finished, environment]
  by_cases h42 : j = 42
  · subst j; simp [finished, environment]
  rw [finished_frame d j (by intro h; subst j; omega) h40 h41 h42]
  exact hframe j hj h40 h41 h42

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
