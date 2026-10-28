import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.PreserveHeadProgram

namespace OAI.Algorithms

/-!
# Local preparation for the encoded sparsifier node

The search block is shifted by five stacks so that pending formulas and
completed leaves are outside every search operation.  The accepted parent,
core and family are copied into the three child-controller inputs.  Actual
clear loops then empty the transient search block.  Neither the old pending
tail nor the old leaf stream occurs in the work bound.
-/

namespace SubexponentialSAT.ExecSparsifyNode

open BitProgram StructuredCalls

abbrev Data (k : ℕ) := State 32 (k + 39)
abbrev Code (k : ℕ) := Cmd 32 (k + 39)

def port (k : ℕ) (i : Fin 39) : Fin (k + 39) := ⟨i.val, by omega⟩

@[simp] theorem port_val (k : ℕ) (i : Fin 39) : (port k i).val = i.val := rfl

theorem port_injective (k : ℕ) : Function.Injective (port k) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (k + 39) => x.val) h

@[simp] theorem port_inj (k : ℕ) (i j : Fin 39) : port k i = port k j ↔ i = j :=
  (port_injective k).eq_iff

def headReg (i : Fin 2) : Fin 32 := Fin.castAdd 30 i
def headStack (k : ℕ) : Fin 5 → Fin (k + 39) :=
  ![port k 0, port k 21, port k 5, port k 6, port k 1]

theorem headReg_injective : Function.Injective headReg := Fin.castAdd_injective 2 30

theorem headStack_injective (k : ℕ) : Function.Injective (headStack k) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headStack]

/-- Extract only the leading tagged formula; preserve its original record. -/
def readHead (k : ℕ) : Code k :=
  .call (ProgramLinking.liftProgram PreserveHeadProgram.program headReg (headStack k))

def headLoaded {k : ℕ} (bits : List Bool) (a : Data k) : Data k :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks (port k 21) bits⟩

theorem readHead_eval {k : ℕ} (a : Data k) (bits tail : List Bool)
    (h0 : a.stacks (port k 0) = PreserveHeadProgram.pending bits tail)
    (h21 : a.stacks (port k 21) = [])
    (h5 : a.stacks (port k 5) = []) (h6 : a.stacks (port k 6) = []) :
    Eval (readHead k) (24 * bits.length + 29) a (headLoaded bits a) := by
  have he := PreserveHeadProgram.lifted_run headReg (headStack k)
    headReg_injective (headStack_injective k) a bits tail h0 h21 h5 h6
  have hend : PreserveHeadProgram.liftedResult headReg (headStack k) a bits tail =
      headLoaded bits a := by
    apply embedState_eq_of_ports headReg (headStack k) a (headLoaded bits a) _
      headReg_injective (headStack_injective k)
    · intro i
      fin_cases i <;> simp [headLoaded, headReg,
        ParserProgram.pair, readRegs]
    · intro i hi
      have hzero : i ≠ 0 := by intro h; exact hi ⟨0, h.symm⟩
      have hone : i ≠ 1 := by intro h; exact hi ⟨1, h.symm⟩
      exact StackRoutines.readRegs_frame a.regs 0 1 i none hzero hone
    · intro i
      fin_cases i <;> simp [headLoaded, headStack,
        h0, h5, h6]
    · intro i hi
      have hne : i ≠ port k 21 := by intro h; exact hi ⟨1, h.symm⟩
      simp [headLoaded, hne]
  simpa only [readHead, hend] using he

theorem headLoaded_stack_frame {k : ℕ} (a : Data k) (bits : List Bool)
    (i : Fin (k + 39)) (hi : i ≠ port k 21) :
    (headLoaded bits a).stacks i = a.stacks i := by
  simp [headLoaded, hi]

def copied {k : ℕ} (src dst : Fin (k + 39)) (a : Data k) : Data k :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks dst (a.stacks src)⟩

def copy {k : ℕ} (src dst tmp : Fin (k + 39)) : Code k :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

theorem copy_eval {k : ℕ} (src dst tmp : Fin (k + 39)) (a : Data k)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hd : a.stacks dst = []) (ht : a.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (a.stacks src).length + 5) a (copied src dst a) := by
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, copied, hd] using
    ListRegisterProgram.copy_run src dst tmp (0 : Fin 32) 1 hsd hst htd
      (by decide) a.regs a.stacks ht

/-- Only these fixed ports are cleared before the child controller runs. -/
def transientPorts (k : ℕ) : List (Fin (k + 39)) :=
  (List.finRange 30).map (fun i => port k ⟨7 + i.val, by omega⟩)

theorem transientPorts_nodup (k : ℕ) : (transientPorts k).Nodup := by
  apply (List.nodup_finRange 30).map
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 7 + i.val = 7 + j.val at hv
  omega

@[simp] theorem transientPorts_length (k : ℕ) : (transientPorts k).length = 30 := by
  simp [transientPorts]

@[simp] theorem mem_transientPorts (k : ℕ) (i : Fin (k + 39)) :
    i ∈ transientPorts k ↔ 7 ≤ i.val ∧ i.val < 37 := by
  simp only [transientPorts, List.mem_map]
  constructor
  · rintro ⟨j, _, rfl⟩
    change 7 ≤ 7 + j.val ∧ 7 + j.val < 37
    omega
  · intro hi
    refine ⟨⟨i.val - 7, by omega⟩, List.mem_finRange _, ?_⟩
    apply Fin.ext
    change 7 + (i.val - 7) = i.val
    omega

def transientBits {k : ℕ} (a : Data k) : ℕ :=
  ((transientPorts k).map (fun i => (a.stacks i).length)).sum

def load (k : ℕ) : Code k :=
  .seq (copy (port k 21) (port k 4) (port k 7))
    (.seq (copy (port k 13) (port k 5) (port k 7))
      (copy (port k 18) (port k 6) (port k 7)))

def loaded {k : ℕ} (a : Data k) : Data k :=
  copied (port k 18) (port k 6)
    (copied (port k 13) (port k 5) (copied (port k 21) (port k 4) a))

def loadCost {k : ℕ} (a : Data k) : ℕ :=
  7 * ((a.stacks (port k 21)).length + (a.stacks (port k 13)).length +
    (a.stacks (port k 18)).length) + 15

theorem load_eval {k : ℕ} (a : Data k)
    (h4 : a.stacks (port k 4) = []) (h5 : a.stacks (port k 5) = [])
    (h6 : a.stacks (port k 6) = []) (h7 : a.stacks (port k 7) = []) :
    Eval (load k) (loadCost a) a (loaded a) := by
  have h1 := copy_eval (port k 21) (port k 4) (port k 7) a
    (by simp) (by simp) (by simp) h4 h7
  have h2 := copy_eval (port k 13) (port k 5) (port k 7)
    (copied (port k 21) (port k 4) a)
    (by simp) (by simp) (by simp) (by simp [copied, h5]) (by simp [copied, h7])
  have h3 := copy_eval (port k 18) (port k 6) (port k 7)
    (copied (port k 13) (port k 5) (copied (port k 21) (port k 4) a))
    (by simp) (by simp) (by simp) (by simp [copied, h6]) (by simp [copied, h7])
  have h134 : port k 13 ≠ port k 4 := by
    intro h
    have := congrArg Fin.val h
    norm_num at this
  have h184 : port k 18 ≠ port k 4 := by
    intro h
    have := congrArg Fin.val h
    norm_num at this
  have h185 : port k 18 ≠ port k 5 := by
    intro h
    have := congrArg Fin.val h
    norm_num at this
  convert h1.seq (h2.seq h3) using 1
  all_goals simp [load, loadCost, loaded, copied, h134, h184, h185]
  all_goals omega

theorem loaded_stack {k : ℕ} (a : Data k) (i : Fin (k + 39)) :
    (loaded a).stacks i =
      if i = port k 6 then a.stacks (port k 18)
      else if i = port k 5 then a.stacks (port k 13)
      else if i = port k 4 then a.stacks (port k 21)
      else a.stacks i := by
  simp [loaded, copied, Function.update_apply]

theorem transientBits_loaded {k : ℕ} (a : Data k) :
    transientBits (loaded a) = transientBits a := by
  unfold transientBits
  congr 1

def prepare (k : ℕ) : Code k :=
  .seq (load k) (WorkspaceCleanupProgram.command 0 1 (transientPorts k))

def prepared {k : ℕ} (a : Data k) : Data k :=
  WorkspaceCleanupProgram.finish 0 1 (transientPorts k) (loaded a)

def prepareCost {k : ℕ} (a : Data k) : ℕ :=
  loadCost a + 2 * transientBits a + 90

/-- Three real copies followed by thirty real clear loops. -/
theorem prepare_eval {k : ℕ} (a : Data k)
    (h4 : a.stacks (port k 4) = []) (h5 : a.stacks (port k 5) = [])
    (h6 : a.stacks (port k 6) = []) (h7 : a.stacks (port k 7) = []) :
    Eval (prepare k) (prepareCost a) a (prepared a) := by
  have hc := WorkspaceCleanupProgram.command_eval (0 : Fin 32) 1
    (transientPorts k) (transientPorts_nodup k) (loaded a)
  have hcost : WorkspaceCleanupProgram.cost (transientPorts k) (loaded a) =
      2 * transientBits a + 90 := by
    change 2 * transientBits (loaded a) + 3 * (transientPorts k).length = _
    rw [transientBits_loaded, transientPorts_length]
  simpa only [prepare, prepared, prepareCost, hcost, Nat.add_assoc] using
    (load_eval a h4 h5 h6 h7).seq hc

theorem prepared_stack {k : ℕ} (a : Data k) (i : Fin (k + 39)) :
    (prepared a).stacks i =
      if 7 ≤ i.val ∧ i.val < 37 then []
      else if i = port k 6 then a.stacks (port k 18)
      else if i = port k 5 then a.stacks (port k 13)
      else if i = port k 4 then a.stacks (port k 21)
      else a.stacks i := by
  simp only [prepared, WorkspaceCleanupProgram.finish_stack,
    mem_transientPorts, loaded_stack]

@[simp] theorem prepared_parent {k : ℕ} (a : Data k) :
    (prepared a).stacks (port k 4) = a.stacks (port k 21) := by
  have hn : ¬ (7 ≤ (port k 4).val ∧ (port k 4).val < 37) := by
    change ¬ (7 ≤ 4 ∧ 4 < 37)
    decide
  rw [prepared_stack, ite_eq_right hn]
  simp
@[simp] theorem prepared_core {k : ℕ} (a : Data k) :
    (prepared a).stacks (port k 5) = a.stacks (port k 13) := by
  have hn : ¬ (7 ≤ (port k 5).val ∧ (port k 5).val < 37) := by
    change ¬ (7 ≤ 5 ∧ 5 < 37)
    decide
  rw [prepared_stack, ite_eq_right hn]
  simp
@[simp] theorem prepared_family {k : ℕ} (a : Data k) :
    (prepared a).stacks (port k 6) = a.stacks (port k 18) := by
  have hn : ¬ (7 ≤ (port k 6).val ∧ (port k 6).val < 37) := by
    change ¬ (7 ≤ 6 ∧ 6 < 37)
    decide
  rw [prepared_stack, ite_eq_right hn]
  simp

theorem prepared_transient {k : ℕ} (a : Data k) (i : Fin (k + 39))
    (hi : 7 ≤ i.val ∧ i.val < 37) : (prepared a).stacks i = [] := by
  simp [prepared_stack, hi]

/-- All persistent parameters and both unbounded worklist streams are framed. -/
theorem prepared_frame {k : ℕ} (a : Data k) (i : Fin (k + 39))
    (hi : i.val < 4 ∨ 37 ≤ i.val) : (prepared a).stacks i = a.stacks i := by
  have ht : ¬ (7 ≤ i.val ∧ i.val < 37) := by omega
  have h4 : i ≠ port k 4 := by
    intro h; subst i
    change 4 < 4 ∨ 37 ≤ 4 at hi
    omega
  have h5 : i ≠ port k 5 := by
    intro h; subst i
    change 5 < 4 ∨ 37 ≤ 5 at hi
    omega
  have h6 : i ≠ port k 6 := by
    intro h; subst i
    change 6 < 4 ∨ 37 ≤ 6 at hi
    omega
  simp [prepared_stack, ht, h4, h5, h6]

theorem prepared_register_frame {k : ℕ} (a : Data k) (i : Fin 32)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (prepared a).regs i = a.regs i := by
  rw [prepared, WorkspaceCleanupProgram.finish_register_frame _ _ _ _ _ h0 h1]
  simp only [loaded, copied]
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1,
    StackRoutines.readRegs_frame _ _ _ _ _ h0 h1,
    StackRoutines.readRegs_frame _ _ _ _ _ h0 h1]

def prepareProgram (k : ℕ) := compiled (prepare k) (port k 0) (port k 2)

theorem prepare_program_trace {k : ℕ} (a : Data k)
    (h4 : a.stacks (port k 4) = []) (h5 : a.stacks (port k 5) = [])
    (h6 : a.stacks (port k 6) = []) (h7 : a.stacks (port k 7) = []) :
    Trace (prepareProgram k) (prepareCost a + 1)
      (a.withPC (some (prepareProgram k).entry)) ((prepared a).withPC none) :=
  compiled_halt_trace (prepare_eval a h4 h5 h6 h7) (port k 0) (port k 2)

end SubexponentialSAT.ExecSparsifyNode

end OAI.Algorithms
