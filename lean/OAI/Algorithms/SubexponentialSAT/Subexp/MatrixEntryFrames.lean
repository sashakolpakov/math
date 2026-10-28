import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryCore
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed-port execution rules used to assemble the concrete entry program.
The call rule consumes a trace of the supplied actual subprogram. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

def project {s : ℕ} (hs : s ≤ 37) (a : Data) : State 8 s :=
  ⟨fun j => a.regs (lowRegisters j), fun j => a.stacks (j.castLE hs)⟩

def install {s : ℕ} (a : Data) (b : State 8 s) : Data :=
  ⟨fun j => if h : j.val < 8 then b.regs ⟨j.val, h⟩ else a.regs j,
    fun j => if h : j.val < s then b.stacks ⟨j.val, h⟩ else a.stacks j⟩

theorem lowRegisters_injective : Function.Injective lowRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 9 => k.val) h

theorem lowStacks_injective {s : ℕ} (hs : s ≤ 37) :
    Function.Injective (Fin.castLE hs) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 37 => k.val) h

theorem embed_install {s : ℕ} (hs : s ≤ 37) (a : Data) (b : State 8 s) :
    embedState lowRegisters (Fin.castLE hs) a b = install a b := by
  apply embedState_eq_of_ports _ _ _ _ _ lowRegisters_injective (lowStacks_injective hs)
  · intro j
    simp [install, lowRegisters, j.isLt]
  · intro j hj
    have hn : ¬ j.val < 8 := by
      intro h
      exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]
  · intro j
    simp [install, j.isLt]
  · intro j hj
    have hn : ¬ j.val < s := by
      intro h
      exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]

theorem install_project {s : ℕ} (hs : s ≤ 37) (a : Data) :
    install a (project hs a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases h : j.val < 8 <;> simp [ project, lowRegisters, h]
  · funext j
    by_cases h : j.val < s <;> simp [ project, h]

theorem callLow_eval {s l : ℕ} (p : Program 8 s l) (hs : s ≤ 37)
    (a : Data) (b : State 8 s) {n : ℕ}
    (ht : Trace p n ((project hs a).withPC (some p.entry)) (b.withPC none)) :
    Eval (callLow p hs) n a (install a b) := by
  have he := eval_call_lifted p lowRegisters (Fin.castLE hs) a
    lowRegisters_injective (lowStacks_injective hs) ht
  rw [embed_install, embed_install, install_project] at he
  exact he

theorem callLow_runsIn {s l : ℕ} (p : Program 8 s l) (hs : s ≤ 37)
    (a : Data) (b : State 8 s) {bound : ℕ}
    (ht : RunsIn p bound ((project hs a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n ≤ bound, Eval (callLow p hs) n a (install a b) := by
  obtain ⟨n, hn, he⟩ := ht
  exact ⟨n, hn, callLow_eval p hs a b he⟩

@[simp] theorem install_stack_low {s : ℕ} (hs : s ≤ 37) (a : Data) (b : State 8 s) (j : Fin s) :
    (install a b).stacks (j.castLE hs) = b.stacks j := by simp [install, j.isLt]

theorem install_stack_high {s : ℕ} (a : Data) (b : State 8 s) (j : Fin 37) (hj : s ≤ j.val) :
    (install a b).stacks j = a.stacks j := by simp [install, Nat.not_lt.mpr hj]

@[simp] theorem install_reg8 {s : ℕ} (a : Data) (b : State 8 s) :
    (install a b).regs 8 = a.regs 8 := rfl

def copied (a : Data) (src dst : Fin 37) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

theorem copy_eval (a : Data) (src dst : Fin 37)
    (hsd : src ≠ dst) (hs9 : src ≠ 9) (h9d : (9 : Fin 37) ≠ dst) (h9 : a.stacks 9 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 9 (0 : Fin 9) 1 hsd hs9 h9d (by decide) a h9

def cleared (a : Data) (src : Fin 37) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

theorem clear_eval (a : Data) (src : Fin 37) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  TupleProgram.clear_eval src (0 : Fin 9) 1 a

def transferred (a : Data) (src dst : Fin 37) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks src dst a.stacks⟩

theorem transfer_eval (a : Data) (src dst : Fin 37) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferred a src dst) :=
  TupleProgram.transfer_eval src dst (0 : Fin 9) 1 hsd (by decide) a

def moved (a : Data) (src dst : Fin 37) : Data :=
  transferred (transferred a src 9) 9 dst

theorem move_eval (a : Data) (src dst : Fin 37) (hs9 : src ≠ 9) (h9d : (9 : Fin 37) ≠ dst)
    (h9 : a.stacks 9 = []) :
    Eval (move src dst) (6 * (a.stacks src).length + 6) a (moved a src dst) := by
  have he := (transfer_eval a src 9 hs9).seq (transfer_eval (transferred a src 9) 9 dst h9d)
  convert he using 1
  · rfl
  · simp [transferred, transferStacks, h9]
    omega
  · rfl

theorem series_cons_eval (c : Code) (cs : List Code) (a b d : Data) (n m : ℕ)
    (hc : Eval c n a b) (hcs : Eval (series cs) m b d) :
    Eval (series (c :: cs)) (n + m) a d := hc.seq hcs

def popped (a : Data) (src : Fin 37) : Data :=
  ⟨readRegs a.regs 0 1 (a.stacks src).head?, Function.update a.stacks src (a.stacks src).tail⟩

theorem pop_eval (a : Data) (src : Fin 37) :
    Eval (.base (.atom (.pop src 0 1))) 1 a (popped a src) := .base (.atom _ _)

def pushed (a : Data) (dst : Fin 37) : Data := TupleProgram.pushedState dst 0 true a

theorem push_eval (a : Data) (dst : Fin 37) : Eval (push dst) 2 a (pushed a dst) :=
  TupleProgram.pushConst_eval dst 0 true a

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
