import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

abbrev Data (S : ℕ) := State 16 S
abbrev Command (S : ℕ) := Cmd 16 S

private theorem state_ext {S : ℕ} {a b : Data S}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

def copyState {S : ℕ} (src dst : Fin S) (a : Data S) : Data S :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

def copyCmd {S : ℕ} (src dst tmp : Fin S) : Command S :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

theorem copy_eval {S : ℕ} (src dst tmp : Fin S) (a : Data S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (ht : a.stacks tmp = []) :
    Eval (copyCmd src dst tmp) (7 * (a.stacks src).length + 5) a (copyState src dst a) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp (0 : Fin 16) 1
    hsd hst htd (by decide) a.regs a.stacks ht

@[simp] theorem copyState_stack {S : ℕ} (src dst : Fin S) (a : Data S) :
    (copyState src dst a).stacks = Function.update a.stacks dst (a.stacks src ++ a.stacks dst) := rfl

theorem copyState_frame {S : ℕ} (src dst i : Fin S) (a : Data S) (hi : i ≠ dst) :
    (copyState src dst a).stacks i = a.stacks i := by
  simp [copyState, StackRoutines.copyStacks, hi]

def copyMany {S : ℕ} (tmp : Fin S) : List (Fin S × Fin S) → Command S
  | [] => .base .skip
  | (src, dst) :: ps => .seq (copyCmd src dst tmp) (copyMany tmp ps)

def copyManyState {S : ℕ} : List (Fin S × Fin S) → Data S → Data S
  | [], a => a
  | (src, dst) :: ps, a => copyManyState ps (copyState src dst a)

def copyManyCost {S : ℕ} : List (Fin S × Fin S) → Data S → ℕ
  | [], _ => 0
  | (src, dst) :: ps, a => 7 * (a.stacks src).length + 5 +
      copyManyCost ps (copyState src dst a)

theorem copyMany_eval {S : ℕ} (tmp : Fin S) (ps : List (Fin S × Fin S)) (a : Data S)
    (hports : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (ht : a.stacks tmp = []) :
    Eval (copyMany tmp ps) (copyManyCost ps a) a (copyManyState ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih =>
    obtain ⟨src, dst⟩ := p
    have hp := hports (src, dst) (by simp)
    have hrest : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2 := by
      intro p hm
      exact hports p (by simp [hm])
    have ht' : (copyState src dst a).stacks tmp = [] :=
      (copyState_frame src dst tmp a hp.2.2).trans ht
    exact .seq (copy_eval src dst tmp a hp.1 hp.2.1 hp.2.2 ht)
      (ih (copyState src dst a) hrest ht')

theorem copyMany_frame {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hi : ∀ p ∈ ps, i ≠ p.2) : (copyManyState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨src, dst⟩ := p
    exact (ih (copyState src dst a) (fun p hp => hi p (by simp [hp]))).trans
      (copyState_frame src dst i a (hi (src, dst) (by simp)))

def clearState {S : ℕ} (port : Fin S) (a : Data S) : Data S :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks port []⟩

def clearCmd {S : ℕ} (port : Fin S) : Command S :=
  .call (StackRoutines.clearProgram port 0 1)

theorem clear_eval {S : ℕ} (port : Fin S) (a : Data S) :
    Eval (clearCmd port) (2 * (a.stacks port).length + 3) a (clearState port a) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run port (0 : Fin 16) 1 a.regs a.stacks

def clearMany {S : ℕ} : List (Fin S) → Command S
  | [] => .base .skip
  | p :: ps => .seq (clearCmd p) (clearMany ps)

def clearManyState {S : ℕ} : List (Fin S) → Data S → Data S
  | [], a => a
  | p :: ps, a => clearManyState ps (clearState p a)

def clearManyCost {S : ℕ} : List (Fin S) → Data S → ℕ
  | [], _ => 0
  | p :: ps, a => 2 * (a.stacks p).length + 3 + clearManyCost ps (clearState p a)

theorem clearMany_eval {S : ℕ} (ps : List (Fin S)) (a : Data S) :
    Eval (clearMany ps) (clearManyCost ps a) a (clearManyState ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih => exact .seq (clear_eval p a) (ih (clearState p a))

theorem clearMany_stacks {S : ℕ} (ps : List (Fin S)) (a : Data S) (i : Fin S) :
    (clearManyState ps a).stacks i = if i ∈ ps then [] else a.stacks i := by
  induction ps generalizing a with
  | nil => simp [clearManyState]
  | cons p ps ih =>
    rw [clearManyState, ih]
    by_cases hp : i = p <;> by_cases hs : i ∈ ps <;>
      simp [clearState, hp, hs]

def resetMany {S : ℕ} : List (Fin 16) → Command S
  | [] => .base .skip
  | r :: rs => .seq (.base (.atom (.set r false))) (resetMany rs)

def resetManyState {S : ℕ} : List (Fin 16) → Data S → Data S
  | [], a => a
  | r :: rs, a => resetManyState rs ((StructuredProgram.Atom.set r false).eval a)

theorem resetMany_eval {S : ℕ} (rs : List (Fin 16)) (a : Data S) :
    Eval (resetMany rs) rs.length a (resetManyState rs a) := by
  induction rs generalizing a with
  | nil => exact .base (.skip a)
  | cons r rs ih =>
    have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set r false) a))
      (ih ((StructuredProgram.Atom.set r false).eval a))
    simpa only [resetMany, resetManyState, List.length_cons, Nat.add_comm] using h

theorem resetMany_stacks {S : ℕ} (rs : List (Fin 16)) (a : Data S) :
    (resetManyState rs a).stacks = a.stacks := by
  induction rs generalizing a with
  | nil => rfl
  | cons r rs ih => exact ih ((StructuredProgram.Atom.set r false).eval a)

theorem resetMany_regs {S : ℕ} (rs : List (Fin 16)) (a : Data S) (i : Fin 16) :
    (resetManyState rs a).regs i = if i ∈ rs then false else a.regs i := by
  induction rs generalizing a with
  | nil => simp [resetManyState]
  | cons r rs ih =>
    rw [resetManyState, ih]
    by_cases hr : i = r <;> by_cases hs : i ∈ rs <;>
      simp [hr, hs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]

def workRegisters : List (Fin 16) := List.ofFn (fun i : Fin 9 => i.castLE (by decide))

def resetWork {S : ℕ} : Command S := resetMany workRegisters

theorem resetWork_eval {S : ℕ} (a : Data S) :
    Eval resetWork 9 a (resetManyState workRegisters a) := by
  simpa only [resetWork, workRegisters, List.length_ofFn] using resetMany_eval workRegisters a

theorem resetWork_reg {S : ℕ} (a : Data S) (i : Fin 9) :
    (resetManyState workRegisters a).regs (i.castLE (by decide)) = false := by
  rw [resetMany_regs]
  apply ite_eq_left
  rw [workRegisters, List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem resetWork_flag {S : ℕ} (a : Data S) :
    (resetManyState workRegisters a).regs 15 = a.regs 15 := by
  rw [resetMany_regs]
  have hnot : (15 : Fin 16) ∉ workRegisters := by
    simp only [workRegisters, List.mem_ofFn, not_exists]
    intro i hi
    have h := congrArg Fin.val hi
    have := i.isLt
    simp only [Fin.val_castLE] at h
    omega
  exact ite_eq_right hnot

def project {r s S : ℕ} (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (a : Data S) : State r s := ⟨a.regs ∘ register, a.stacks ∘ stack⟩

abbrev invoke {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S) : Command S :=
  .call (ProgramLinking.liftProgram p register stack)

theorem embed_project {r s S : ℕ} (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : Data S) :
    embedState register stack a (project register stack a) = a := by
  apply embedState_eq_of_ports register stack a a _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

/-- This rule consumes an actual subroutine trace. It does not postulate a
semantic-function instruction or an unproved runtime. -/
theorem invoke_eval {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (a : Data S) (out : State r s) {t : ℕ}
    (ht : Trace p t ((project register stack a).withPC (some p.entry)) (out.withPC none)) :
    Eval (invoke p register stack) t a (embedState register stack a out) := by
  have h := eval_call_lifted p register stack a hr hs ht
  simpa only [invoke, embed_project register stack hr hs a] using h

def prepare {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) : Command S :=
  .seq (clearMany [tmp]) (.seq (clearMany ports) (.seq resetWork (copyMany tmp inputs)))

def beforeCopies {S : ℕ} (tmp : Fin S) (ports : List (Fin S)) (a : Data S) : Data S :=
  resetManyState workRegisters (clearManyState ports (clearManyState [tmp] a))

def prepareState {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) : Data S :=
  copyManyState inputs (beforeCopies tmp ports a)

def prepareCost {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) : ℕ :=
  clearManyCost [tmp] a + (clearManyCost ports (clearManyState [tmp] a) +
    (9 + copyManyCost inputs (beforeCopies tmp ports a)))

theorem beforeCopies_temporary {S : ℕ} (tmp : Fin S) (ports : List (Fin S)) (a : Data S) :
    (beforeCopies tmp ports a).stacks tmp = [] := by
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks]
  simp

theorem prepare_eval {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S)
    (hp : ∀ p ∈ inputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2) :
    Eval (prepare tmp ports inputs) (prepareCost tmp ports inputs a) a
      (prepareState tmp ports inputs a) := by
  exact .seq (clearMany_eval [tmp] a)
    (.seq (clearMany_eval ports (clearManyState [tmp] a))
      (.seq (resetWork_eval (clearManyState ports (clearManyState [tmp] a)))
        (copyMany_eval tmp inputs (beforeCopies tmp ports a) hp
          (beforeCopies_temporary tmp ports a))))

theorem prepare_temporary {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S)
    (hp : ∀ p ∈ inputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2) :
    (prepareState tmp ports inputs a).stacks tmp = [] := by
  exact (copyMany_frame inputs (beforeCopies tmp ports a) tmp
    (fun p hm => (hp p hm).2.2)).trans (beforeCopies_temporary tmp ports a)

def finish {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) : Command S :=
  .seq (clearMany (outputs.map Prod.snd))
    (.seq (copyMany tmp outputs) (.seq (clearMany ports) resetWork))

def finishState {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) : Data S :=
  resetManyState workRegisters
    (clearManyState ports (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)))

def finishCost {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) : ℕ :=
  clearManyCost (outputs.map Prod.snd) a +
    (copyManyCost outputs (clearManyState (outputs.map Prod.snd) a) +
      (clearManyCost ports (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) + 9))

theorem finish_eval {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hp : ∀ p ∈ outputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (ht : a.stacks tmp = []) :
    Eval (finish tmp ports outputs) (finishCost ports outputs a) a
      (finishState ports outputs a) := by
  have ht' : (clearManyState (outputs.map Prod.snd) a).stacks tmp = [] := by
    rw [clearMany_stacks, ht]
    split <;> rfl
  exact .seq (clearMany_eval (outputs.map Prod.snd) a)
    (.seq (copyMany_eval tmp outputs (clearManyState (outputs.map Prod.snd) a) hp ht')
      (.seq (clearMany_eval ports (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)))
        (resetWork_eval _)))

abbrev isolated {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (tmp : Fin S) (ports : List (Fin S))
    (inputs outputs : List (Fin S × Fin S)) : Command S :=
  .seq (prepare tmp ports inputs)
    (.seq (invoke p register stack) (finish tmp ports outputs))

/-- Copy/clear overhead is derived from actual instructions around an actual
callee trace. No unproved semantic or timing callback is introduced. -/
theorem isolated_eval {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (tmp : Fin S) (ports : List (Fin S))
    (inputs outputs : List (Fin S × Fin S)) (a : Data S) (out : State r s) {t : ℕ}
    (hi : ∀ p ∈ inputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (ho : ∀ p ∈ outputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (hframe : ¬ ∃ j, stack j = tmp)
    (ht : Trace p t
      ((project register stack (prepareState tmp ports inputs a)).withPC (some p.entry))
      (out.withPC none)) :
    let middle := embedState register stack (prepareState tmp ports inputs a) out
    Eval (isolated p register stack tmp ports inputs outputs)
      (prepareCost tmp ports inputs a + (t + finishCost ports outputs middle)) a
      (finishState ports outputs middle) := by
  dsimp only
  have htmp :
      (embedState register stack (prepareState tmp ports inputs a) out).stacks tmp = [] :=
    (embedState_stack_frame register stack _ out tmp hframe).trans
      (prepare_temporary tmp ports inputs a hi)
  exact .seq (prepare_eval tmp ports inputs a hi)
    (.seq (invoke_eval p register stack hr hs _ out ht)
      (finish_eval tmp ports outputs _ ho htmp))

theorem finish_empty {S : ℕ} (ports : List (Fin S)) (outputs : List (Fin S × Fin S))
    (a : Data S) (i : Fin S) (hi : i ∈ ports) :
    (finishState ports outputs a).stacks i = [] := by
  rw [finishState, resetMany_stacks, clearMany_stacks, ite_eq_left hi]

theorem finish_workReg {S : ℕ} (ports : List (Fin S)) (outputs : List (Fin S × Fin S))
    (a : Data S) (i : Fin 9) :
    (finishState ports outputs a).regs (i.castLE (by decide)) = false :=
  resetWork_reg _ i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
