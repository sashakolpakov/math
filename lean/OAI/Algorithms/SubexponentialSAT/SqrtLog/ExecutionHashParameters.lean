import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHash
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgramFinal

namespace OAI.Algorithms

/-! Relocation of the actual metadata arithmetic into a caller which also
holds the formula and ring context. Only binary n, m and B are supplied;
3m, the tuple depth and the number of hash rounds are computed by the fixed
parameter program. The empty-formula branch is handled by the leaf caller. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashParameters

open BitProgram StructuredCalls

structure Ports (R S : ℕ) where
  register : Fin 16 → Fin R
  stack : Fin 44 → Fin S
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

def Ports.hash {R S : ℕ} (p : Ports R S) : Hash.Ports R S where
  register := p.register ∘ HashParametersProgram.ABI.selectorRegisters
  stack := p.stack ∘ HashParametersProgram.ABI.selectorStacks
  register_injective := p.register_injective.comp (Fin.castAdd_injective _ _)
  stack_injective := p.stack_injective.comp (Fin.castAdd_injective _ _)

abbrev command {R S : ℕ} (p : Ports R S) : Cmd R S :=
  liftCommand HashParametersProgram.ABI.command 0 6 p.register p.stack

theorem command_eval {R S : ℕ} (p : Ports R S) (a : State R S) (L : ℕ)
    (hword : SubexpSetupStorage.WordBound L (projectState p.register p.stack a))
    (hready : HashInputs.Ready (projectState p.hash.register p.hash.stack a))
    (hm : BinaryArithmetic.toNat (a.stacks (p.stack 15)) ≠ 0) :
    ∃ t ≤ 10000000000*(L+1)^2+1, ∃ b : State R S,
      Eval (command p) t a b ∧
      HashInputs.Ready (projectState p.hash.register p.hash.stack b) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 0)) =
        3*BinaryArithmetic.toNat (a.stacks (p.stack 15)) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 5)) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks (p.stack 15)))
          (BinaryArithmetic.toNat (a.stacks (p.stack 16))) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 6)) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks (p.stack 14)))
          (BinaryArithmetic.toNat (a.stacks (p.stack 15))) ∧
      b.stacks (p.hash.stack 9) = a.stacks (p.hash.stack 9) ∧
      (∀ i, i ∉ HashParametersProgram.ABI.work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 →
        b.stacks (p.stack i) = a.stacks (p.stack i)) ∧
      (∀ i, (∀ j, p.stack j ≠ i) → b.stacks i = a.stacks i) ∧
      (∀ i, (∀ j, p.register j ≠ i) → b.regs i = a.regs i) := by
  obtain ⟨t,ht,c,hc,hr,h0,h5,h6,h9,hframe⟩ :=
    HashParametersProgram.ABI.command_ready_eval
      (projectState p.register p.stack a) L hword hready hm
  let b := embedState p.register p.stack a c
  have hs (i : Fin 44) : b.stacks (p.stack i) = c.stacks i :=
    embedState_stack p.register p.stack a c p.stack_injective i
  refine ⟨t+1,Nat.add_le_add_right ht 1,b,
    eval_liftCommand_from_state _ _ _ _ _ _ p.register_injective p.stack_injective hc,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi0 hi5 hi6 hi9
    change b.stacks (p.stack (HashParametersProgram.ABI.selectorStacks i)) = []
    rw [hs]
    exact hr i hi0 hi5 hi6 hi9
  · change BinaryArithmetic.toNat (b.stacks (p.stack 0)) = _
    rw [hs]
    exact h0
  · change BinaryArithmetic.toNat (b.stacks (p.stack 5)) = _
    rw [hs]
    exact h5
  · change BinaryArithmetic.toNat (b.stacks (p.stack 6)) = _
    rw [hs]
    exact h6
  · change b.stacks (p.stack 9) = a.stacks (p.stack 9)
    exact (hs 9).trans h9
  · intro i hi h39 h0 h5 h6
    exact (hs i).trans (hframe i hi h39 h0 h5 h6)
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i (by rintro ⟨j,hj⟩; exact hi j hj)
  · intro i hi
    exact embedState_register_frame _ _ _ _ i (by rintro ⟨j,hj⟩; exact hi j hj)

/-- This combined code still accepts the mass service as actual fixed code;
its execution contract is the one in Hash.command_eval. -/
abbrev withSelector {R S : ℕ} (p : Ports R S) (mass : Cmd R S) : Cmd R S :=
  .seq (command p) (Hash.command p.hash mass)

theorem withSelector_eval {R S : ℕ} (p : Ports R S) (mass : Cmd R S)
    {a b c : State R S} {t u : ℕ}
    (hp : Eval (command p) t a b) (hh : Eval (Hash.command p.hash mass) u b c) :
    Eval (withSelector p mass) (t+u) a c := hp.seq hh

end SubexponentialSAT.SqrtLog.Execution.HashParameters

end OAI.Algorithms
