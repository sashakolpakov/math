import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgramArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpGuardProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 9 14
abbrev Code := Cmd 9 14
def lowRegisters : Fin 8 → Fin 9 := Fin.castAdd 1
theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _
def prepare : Code := liftCommand arithmetic 0 3 lowRegisters id
def size (d : Data) : ℕ := inputLength (projectState lowRegisters id d)

theorem prepare_eval (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
    ∃ t ≤ 600 * (2 * size d + 4)^2 + 1, ∃ e : Data,
      Eval prepare t d e ∧
      BinaryArithmetic.toNat (e.stacks 3) = (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 4) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      BinaryArithmetic.toNat (e.stacks 5) = 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 6) = BinaryArithmetic.toNat (d.stacks 1) + 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 7) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) + BinaryArithmetic.toNat (d.stacks 1) ∧
      (∀ j : Fin 14, 3 ≤ j.val → j.val ≤ 7 → (e.stacks j).length ≤ 2 * size d + 4) ∧
      (∀ j : Fin 14, (j.val < 3 ∨ 7 < j.val) → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, b, he, hv3, hv4, hv5, hv6, hv7, hl, hf⟩ :=
    arithmetic_eval (projectState lowRegisters id d) hd
  let e := embedState lowRegisters id d b
  have hs (j : Fin 14) : e.stacks j = b.stacks j :=
    embedState_stack lowRegisters id d b Function.injective_id j
  refine ⟨t+1, Nat.add_le_add_right ht 1, e,
    eval_liftCommand_from_state arithmetic 0 3 lowRegisters id d
      lowRegisters_injective Function.injective_id he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; exact hv3
  · rw [hs]; exact hv4
  · rw [hs]; exact hv5
  · rw [hs]; exact hv6
  · rw [hs]; exact hv7
  · intro j hlo hhi; rw [hs]; exact hl j hlo hhi
  · intro j hj; rw [hs]; exact hf j hj

def checkStacks : Fin 6 → Fin 14 := ![6,4,7,5,8,9]
theorem checkStacks_injective : Function.Injective checkStacks := by decide
def pairPorts (j : Fin 2) (i : Fin 2) : Fin 14 :=
  checkStacks (SubexpGuardProgram.pairStack (Fin.castAdd 1 j) i)
def check (j : Fin 2) : Code :=
  liftCommand (SubexpGuardProgram.checkPair (Fin.castAdd 1 j)) 0 0 id checkStacks

theorem check_eval (j : Fin 2) (d : Data) :
    ∃ e : Data, Eval (check j)
      (10 * max (d.stacks (pairPorts j 0)).length (d.stacks (pairPorts j 1)).length + 9) d e ∧
      e.regs 8 = (d.regs 8 && decide
        (BinaryArithmetic.toNat (d.stacks (pairPorts j 1)) ≤ BinaryArithmetic.toNat (d.stacks (pairPorts j 0)))) ∧
      (∀ i, i ≠ pairPorts j 0 → i ≠ pairPorts j 1 → e.stacks i = d.stacks i) ∧
      (∀ i, e.stacks (pairPorts j i) = []) := by
  let a := projectState id checkStacks d
  obtain ⟨b, he, ho, hf, hz⟩ := SubexpGuardProgram.checkPair_eval (Fin.castAdd 1 j) a
  let e := embedState id checkStacks d b
  have hs (i : Fin 6) : e.stacks (checkStacks i) = b.stacks i :=
    embedState_stack id checkStacks d b checkStacks_injective i
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · have h := eval_liftCommand_from_state (SubexpGuardProgram.checkPair (Fin.castAdd 1 j))
      0 0 id checkStacks d Function.injective_id checkStacks_injective he
    simpa [check, SubexpGuardProgram.pairCost, a, projectState, pairPorts, Nat.add_assoc] using h
  · rw [show e.regs 8 = b.regs 8 from embedState_register id checkStacks d b Function.injective_id 8]
    exact ho
  · intro i hi0 hi1
    by_cases hm : ∃ k, checkStacks k = i
    · obtain ⟨k, rfl⟩ := hm
      rw [hs]
      apply hf
      rintro ⟨z, hz'⟩
      have heq := congrArg checkStacks hz'
      fin_cases z
      · exact hi0 heq.symm
      · exact hi1 heq.symm
    · exact embedState_stack_frame id checkStacks d b i hm
  · intro i; rw [show e.stacks (pairPorts j i) = b.stacks (SubexpGuardProgram.pairStack (Fin.castAdd 1 j) i) from hs _]
    exact hz i

def clearCount : Code := .call (StackRoutines.clearProgram 3 0 1)
def cleared (d : Data) : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks 3 []⟩
theorem clearCount_eval (d : Data) :
    Eval clearCount (2 * (d.stacks 3).length + 3) d (cleared d) :=
  .call _ (ListRegisterProgram.clear_run 3 0 1 d.regs d.stacks)

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
