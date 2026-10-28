import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed-control primitives for laying out a stored power table.  All indices,
dimensions, and scalar widths are data on unary tapes. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 2 18

structure Store where
  powers : List Bool
  degree : List Bool
  width : List Bool
  out : List Bool := []
  word : List Bool := []
  index : List Bool := []
  kc : List Bool := []
  ic : List Bool := []
  jc : List Bool := []
  ki : List Bool := []
  ii : List Bool := []
  ji : List Bool := []
  rev : List Bool := []

def tapes (s : Store) : Fin 18 → List Bool :=
  ![s.powers, s.degree, s.width, s.out, s.word, s.index,
    [], [], [], [], [], s.kc, s.ic, s.jc, s.ki, s.ii, s.ji, s.rev]

def state (regs : Fin 2 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

abbrev clear (dst : Fin 18) : Cmd 2 18 := .call (clearProgram dst 0 1)
abbrev copy (src dst : Fin 18) : Cmd 2 18 := .call (copyProgram src dst 10 0 1)
abbrev transfer (src dst : Fin 18) : Cmd 2 18 := .call (transferProgram src dst 0 1)

def afterClear (d : Data) (dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩
def afterTransfer (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem clear_eval (d : Data) (dst : Fin 18) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 0 1 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 18)
    (hsd : src ≠ dst) (hs : src ≠ 10) (hd : (10 : Fin 18) ≠ dst)
    (htmp : d.stacks 10 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 10 0 1 hsd hs hd
    (by decide) d.regs d.stacks htmp)

theorem transfer_eval (d : Data) (src dst : Fin 18) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

def readPorts : Fin 8 → Fin 18 := ![0, 4, 5, 2, 6, 7, 8, 9]
theorem readPorts_injective : Function.Injective readPorts := by decide

abbrev read : Cmd 2 18 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 2) 1) id readPorts)

def afterRead (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 5 []) 4 (word ++ d.stacks 4)⟩

theorem read_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 0 = earlier.flatten ++ (word ++ rest))
    (hi : (d.stacks 5).length = earlier.length)
    (hr : ∀ row ∈ earlier, row.length = (d.stacks 2).length)
    (hw : word.length = (d.stacks 2).length)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    Eval read
      (earlier.length * (14 * (d.stacks 2).length + 10) + 15 * (d.stacks 2).length + 16)
      d (afterRead d word) := by
  let a : State 2 8 := ⟨d.regs, d.stacks ∘ readPorts⟩
  let b : State 2 8 :=
    ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks word a.stacks⟩
  have ha : embedState id readPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id readPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; rfl
    · intro i hi; rfl
  have hb : embedState id readPorts d b = afterRead d word := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id readPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      fin_cases i <;> simp [b, a, afterRead, ArrayUpdatePrograms.readStacks, readPorts]
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨1, h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2, h.symm⟩
      simp [afterRead, h4, h5]
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 2) 1 (by decide)
    earlier word rest (d.stacks 2) (d.stacks 5) d.regs a.stacks
    hs rfl rfl hi hr hw h6 h7 h8 h9
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 2) 1)
    id readPorts d Function.injective_id readPorts_injective (a := a) (b := b) ht
  simpa only [ha, hb, read] using he

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
