import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram

namespace OAI.Algorithms

/-! Exact finite-port framing for the physical packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgramSupport

open BitProgram StructuredCalls

abbrev Data := State 16 48

def registers {r : ℕ} (h : r ≤ 16) : Fin r → Fin 16 := Fin.castLE h
def stackPorts {s : ℕ} (h : s ≤ 48) : Fin s → Fin 48 := Fin.castLE h

theorem registers_injective {r : ℕ} (h : r ≤ 16) : Function.Injective (registers h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) hij)

theorem stackPorts_injective {s : ℕ} (h : s ≤ 48) : Function.Injective (stackPorts h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin 48 => x.val) hij)

def project {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48) (a : Data) : State r s :=
  ⟨a.regs ∘ registers hr, a.stacks ∘ stackPorts hs⟩

/-- A computable description of the exact state after a low-port call. -/
def install {r s : ℕ} (_hr : r ≤ 16) (_hs : s ≤ 48) (a : Data) (b : State r s) : Data :=
  ⟨fun i => if h : i.val < r then b.regs ⟨i.val, h⟩ else a.regs i,
   fun i => if h : i.val < s then b.stacks ⟨i.val, h⟩ else a.stacks i⟩

theorem install_register {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin r) :
    (install hr hs a b).regs (registers hr i) = b.regs i := by
  simp [install, registers, i.isLt]

theorem install_stack {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin s) :
    (install hr hs a b).stacks (stackPorts hs i) = b.stacks i := by
  simp [install, stackPorts, i.isLt]

theorem install_register_frame {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin 16) (hi : r ≤ i.val) :
    (install hr hs a b).regs i = a.regs i := by
  simp [install, Nat.not_lt.mpr hi]

theorem install_stack_frame {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin 48) (hi : s ≤ i.val) :
    (install hr hs a b).stacks i = a.stacks i := by
  simp [install, Nat.not_lt.mpr hi]

theorem install_project {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48) (a : Data) :
    install hr hs a (project hr hs a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : i.val < r <;> simp [ project, registers, h]
  · funext i
    by_cases h : i.val < s <;> simp [ project, stackPorts, h]

theorem embed_eq_install {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) :
    embedState (registers hr) (stackPorts hs) a b = install hr hs a b := by
  apply SelectorMapProgram.embed_eq _ _ (registers_injective hr) (stackPorts_injective hs)
  · exact install_register hr hs a b
  · exact install_stack hr hs a b
  · intro i hi
    apply install_register_frame
    by_contra hn
    exact hi ⟨⟨i.val, Nat.lt_of_not_ge hn⟩, Fin.ext rfl⟩
  · intro i hi
    apply install_stack_frame
    by_contra hn
    exact hi ⟨⟨i.val, Nat.lt_of_not_ge hn⟩, Fin.ext rfl⟩

abbrev lowCall {r s l : ℕ} (p : Program r s l) (hr : r ≤ 16) (hs : s ≤ 48) : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram p (registers hr) (stackPorts hs))

/-- The premise is the actual trace of the invoked finite program. The theorem
does not replace any run by a semantic instruction or a callback oracle. -/
theorem lowCall_eval {r s l n : ℕ} (p : Program r s l)
    (hr : r ≤ 16) (hs : s ≤ 48) (a : Data) (b : State r s)
    (ht : Trace p n ((project hr hs a).withPC (some p.entry)) (b.withPC none)) :
    Eval (lowCall p hr hs) n a (install hr hs a b) := by
  have h := eval_call_lifted p (registers hr) (stackPorts hs) a
    (registers_injective hr) (stackPorts_injective hs) ht
  rw [embed_eq_install, install_project, embed_eq_install] at h
  exact h

abbrev copy (src dst tmp : Fin 48) : Cmd 16 48 :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

abbrev clear (src : Fin 48) : Cmd 16 48 :=
  .call (StackRoutines.clearProgram src 0 1)

abbrev transfer (src dst : Fin 48) : Cmd 16 48 :=
  .call (StackRoutines.transferProgram src dst 0 1)

abbrev sequence (cs : List (Cmd 16 48)) : Cmd 16 48 :=
  cs.foldr Cmd.seq (.base .skip)

end SubexponentialSAT.Subexp.PackingProgramSupport

end OAI.Algorithms
