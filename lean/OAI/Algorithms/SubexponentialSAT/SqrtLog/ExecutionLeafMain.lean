import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionAllocation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionLeafIO

namespace OAI.Algorithms

/-! Concrete Main port allocation for the paid wide-leaf I/O wrapper. -/
namespace SubexponentialSAT.SqrtLog.Execution.LeafMain

open BitProgram StructuredCalls SubexpMainProgram
open SubexpSetupProgram (Config helperSize mainExtraStacks)

def external : Fin 4 → Fin 32 := ![9,2,24,10]

theorem external_injective : Function.Injective external := by decide

def stack (c : Config) (hc : 896 < helperSize c) :
    Fin 900 → Fin (totalStacks (mainExtraStacks c)) :=
  fun i => Fin.addCases (m := 896) (n := 4)
    (motive := fun _ => Fin (totalStacks (mainExtraStacks c)))
    (fun j => WideLeaf.stack c hc j)
    (fun j => persistent (mainExtraStacks c) (external j)) i

@[simp] theorem stack_work (c : Config) (hc : 896 < helperSize c) (i : Fin 896) :
    stack c hc (i.castAdd 4) = WideLeaf.stack c hc i := by
  simp only [stack,Fin.addCases_left]

@[simp] theorem stack_external (c : Config) (hc : 896 < helperSize c) (i : Fin 4) :
    stack c hc (i.natAdd 896) = persistent (mainExtraStacks c) (external i) :=
  by simp only [stack,Fin.addCases_right]

theorem stack_injective (c : Config) (hc : 896 < helperSize c) :
    Function.Injective (stack c hc) := by
  intro i j
  refine Fin.addCases (m := 896) (n := 4) (fun a => ?_) (fun a => ?_) i
  · refine Fin.addCases (m := 896) (n := 4) (fun b => ?_) (fun b => ?_) j
    · intro h
      rw [stack_work,stack_work] at h
      exact congrArg (Fin.castAdd 4) ((WideLeaf.stack c hc).injective h)
    · intro h
      rw [stack_work,stack_external] at h
      exact False.elim (WideLeaf.stack_ne_persistent c hc a (external b) h)
  · refine Fin.addCases (m := 896) (n := 4) (fun b => ?_) (fun b => ?_) j
    · intro h
      rw [stack_external,stack_work] at h
      exact False.elim (WideLeaf.stack_ne_persistent c hc b (external a) h.symm)
    · intro h
      rw [stack_external,stack_external] at h
      exact congrArg (Fin.natAdd 896)
        (external_injective ((persistent_injective (mainExtraStacks c)) h))

abbrev procedure (c : Config) (hc : 896 < helperSize c) (core : Cmd 40 896) :
    Procedure finalExtraRegisters (mainExtraStacks c) :=
  procedureOfCommand (LeafIO.command core) 896 899 WideLeaf.register
    ⟨stack c hc,stack_injective c hc⟩

abbrev Ready (c : Config) (hc : 896 < helperSize c) (core : Cmd 40 896)
    (a : MainState finalExtraRegisters (mainExtraStacks c)) : Prop :=
  LeafIO.Ready ((procedure c hc core).project a)

/-- Readiness follows from the actual blank helper prefix and empty answer
port. The formula and metadata words are read from persistent9/2/24. -/
theorem ready_of_blank (c : Config) (hc : 896 < helperSize c) (core : Cmd 40 896)
    (a : MainState finalExtraRegisters (mainExtraStacks c))
    (hwork : ∀ i : Fin 896, a.stacks (WideLeaf.stack c hc i) = [])
    (hanswer : a.stacks (persistent (mainExtraStacks c) 10) = []) :
    Ready c hc core a := by
  refine ⟨?_,?_⟩
  · intro i hi
    let j : Fin 896 := ⟨i.val,hi⟩
    have he : j.castAdd 4 = i := Fin.ext rfl
    change a.stacks (stack c hc i) = []
    rw [← he,stack_work]
    exact hwork j
  · exact hanswer

/-- All actual wrapper instructions and the return instruction are charged.
No correctness or running-time assumption is inferred for the core. -/
theorem procedure_eval (c : Config) (hc : 896 < helperSize c) (core : Cmd 40 896)
    (a : MainState finalExtraRegisters (mainExtraStacks c))
    (ha : Ready c hc core a) {t : ℕ} {b : State 40 896}
    (hb : Eval core t
      (projectState id LeafIO.work (LeafIO.prepared ((procedure c hc core).project a))) b) :
    let localInput := (procedure c hc core).project a
    let middle := embedState id LeafIO.work (LeafIO.prepared localInput) b
    Eval (procedure c hc core).invoke
      (LeafIO.prepareCost localInput+(t+1)+LeafIO.finishCost middle+1) a
      ((procedure c hc core).install a (LeafIO.finished middle)) := by
  dsimp only
  exact procedureOfCommand_eval (LeafIO.command core) 896 899 WideLeaf.register
    ⟨stack c hc,stack_injective c hc⟩ a (LeafIO.command_eval core _ ha hb)

/-- A complete run restores every local worker stack. -/
theorem install_finished_work (c : Config) (hc : 896 < helperSize c) (core : Cmd 40 896)
    (a : MainState finalExtraRegisters (mainExtraStacks c)) (middle : LeafIO.Data)
    (i : Fin 896) :
    ((procedure c hc core).install a (LeafIO.finished middle)).stacks
      (WideLeaf.stack c hc i) = [] := by
  have h := embedState_stack (procedure c hc core).registerMap (stack c hc) a
    (LeafIO.finished middle) (stack_injective c hc) (i.castAdd 4)
  rw [stack_work] at h
  exact h.trans (LeafIO.finished_work middle i)

/-- The actual copied answer is the core's answer word.  The external output
port is initially empty and cannot be touched by the isolated core. -/
theorem install_finished_answer (c : Config) (hc : 896 < helperSize c)
    (core : Cmd 40 896) (a : MainState finalExtraRegisters (mainExtraStacks c))
    (ha : Ready c hc core a) (b : State 40 896) :
    let middle := embedState id LeafIO.work
      (LeafIO.prepared ((procedure c hc core).project a)) b
    ((procedure c hc core).install a (LeafIO.finished middle)).stacks
      (persistent (mainExtraStacks c) 10) = b.stacks 787 := by
  dsimp only
  let input := (procedure c hc core).project a
  let middle := embedState id LeafIO.work (LeafIO.prepared input) b
  have outside : ¬ ∃ i : Fin 896, LeafIO.work i = (899 : Fin 900) := by
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change i.val = 899 at hv
    have := i.isLt
    omega
  have hempty : middle.stacks 899 = [] := by
    rw [show middle.stacks 899 = (LeafIO.prepared input).stacks 899 from
      embedState_stack_frame id LeafIO.work (LeafIO.prepared input) b 899 outside]
    exact (LeafIO.prepared_external input 899 (by decide)).trans ha.2
  have hanswer : middle.stacks 787 = b.stacks 787 :=
    embedState_stack id LeafIO.work (LeafIO.prepared input) b LeafIO.work_injective 787
  have h := embedState_stack (procedure c hc core).registerMap (stack c hc) a
    (LeafIO.finished middle) (stack_injective c hc) 899
  change _ = (LeafIO.finished middle).stacks 899 at h
  have hh := h.trans ((LeafIO.finished_answer middle hempty).trans hanswer)
  change ((embedState (procedure c hc core).registerMap (stack c hc) a
    (LeafIO.finished middle)).stacks (persistent (mainExtraStacks c) 10)) = b.stacks 787
  exact hh

/-- The input leaf and its two metadata words survive the wrapper literally. -/
theorem install_finished_sources (c : Config) (hc : 896 < helperSize c)
    (core : Cmd 40 896) (a : MainState finalExtraRegisters (mainExtraStacks c))
    (b : State 40 896) (j : Fin 3) :
    let middle := embedState id LeafIO.work
      (LeafIO.prepared ((procedure c hc core).project a)) b
    ((procedure c hc core).install a (LeafIO.finished middle)).stacks
      (persistent (mainExtraStacks c) (external (j.castAdd 1))) =
      a.stacks (persistent (mainExtraStacks c) (external (j.castAdd 1))) := by
  dsimp only
  let input := (procedure c hc core).project a
  let middle := embedState id LeafIO.work (LeafIO.prepared input) b
  let q : Fin 900 := (j.castAdd 1).natAdd 896
  have hlo : 896 ≤ q.val := by simp [q]
  have hhi : q.val < 899 := by simp [q]; omega
  have outside : ¬ ∃ i : Fin 896, LeafIO.work i = q := by
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change i.val = q.val at hv
    have := i.isLt
    omega
  have hm : middle.stacks q = input.stacks q :=
    (embedState_stack_frame id LeafIO.work (LeafIO.prepared input) b q outside).trans
      (LeafIO.prepared_external input q hlo)
  have h := embedState_stack (procedure c hc core).registerMap (stack c hc) a
    (LeafIO.finished middle) (stack_injective c hc) q
  have hs := (LeafIO.finished_source middle q hlo hhi).trans hm
  have hh : ((procedure c hc core).install a (LeafIO.finished middle)).stacks
      (stack c hc q) = a.stacks (stack c hc q) := h.trans hs
  simpa only [q,stack_external] using hh

/-- Main's unread leaf stream and all other unlisted persistent words are
outside the wrapper, including the threshold bank by the same separation. -/
theorem install_persistent_frame (c : Config) (hc : 896 < helperSize c)
    (core : Cmd 40 896) (a : MainState finalExtraRegisters (mainExtraStacks c))
    (out : LeafIO.Data) (j : Fin 32)
    (hj : ∀ i : Fin 4, external i ≠ j) :
    ((procedure c hc core).install a out).stacks (persistent (mainExtraStacks c) j) =
      a.stacks (persistent (mainExtraStacks c) j) := by
  apply procedure_install_stack_frame
  rintro ⟨i,hi⟩
  change stack c hc i = persistent (mainExtraStacks c) j at hi
  revert hi
  refine Fin.addCases (m := 896) (n := 4) (fun q => ?_) (fun q => ?_) i
  · intro h
    rw [stack_work] at h
    exact WideLeaf.stack_ne_persistent c hc q j h
  · intro h
    rw [stack_external] at h
    exact hj q ((persistent_injective (mainExtraStacks c)) h)

theorem install_threshold_frame (c : Config) (hc : 896 < helperSize c)
    (core : Cmd 40 896) (a : MainState finalExtraRegisters (mainExtraStacks c))
    (out : LeafIO.Data) (j : Fin (SubexpSetupProgram.thresholdCount c)) :
    ((procedure c hc core).install a out).stacks
        (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c j)) =
      a.stacks (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c j)) := by
  apply procedure_install_stack_frame
  rintro ⟨i,hi⟩
  change stack c hc i = _ at hi
  revert hi
  refine Fin.addCases (m := 896) (n := 4) (fun q => ?_) (fun q => ?_) i
  · intro h
    rw [stack_work] at h
    exact WideLeaf.stack_ne_threshold c hc q j h
  · intro h
    rw [stack_external] at h
    have hv := congrArg (fun z : Fin (totalStacks (mainExtraStacks c)) => z.val) h
    change workStacks (mainExtraStacks c)+(external q).val = helperSize c+j.val at hv
    have hj := j.isLt
    unfold workStacks SubexpSetupProgram.mainExtraStacks helperSize at hv
    omega

theorem install_unused_helper_frame (c : Config) (hc : 896 < helperSize c)
    (core : Cmd 40 896) (a : MainState finalExtraRegisters (mainExtraStacks c))
    (out : LeafIO.Data) (j : Fin (totalStacks (mainExtraStacks c)))
    (hlo : 896 ≤ j.val) (hhi : j.val < helperSize c) :
    ((procedure c hc core).install a out).stacks j = a.stacks j := by
  apply procedure_install_stack_frame
  rintro ⟨i,hi⟩
  change stack c hc i = j at hi
  revert hi
  refine Fin.addCases (m := 896) (n := 4) (fun q => ?_) (fun q => ?_) i
  · intro h
    rw [stack_work] at h
    have hv := congrArg (fun z : Fin (totalStacks (mainExtraStacks c)) => z.val) h
    change q.val = j.val at hv
    have hq := q.isLt
    omega
  · intro h
    rw [stack_external] at h
    have hv := congrArg (fun z : Fin (totalStacks (mainExtraStacks c)) => z.val) h
    change workStacks (mainExtraStacks c)+(external q).val = j.val at hv
    unfold workStacks SubexpSetupProgram.mainExtraStacks at hv
    unfold helperSize at hhi
    omega

end SubexponentialSAT.SqrtLog.Execution.LeafMain

end OAI.Algorithms
