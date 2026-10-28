import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHash

namespace OAI.Algorithms

/-! The existing fixed hash command with its full literal caller frame.
The extra conclusion is needed for the following accepted-count query. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram Execution Execution.Hash

theorem hash_eval_framed {R S : ℕ} (p : Execution.Hash.Ports R S) (mass : Cmd R S)
    (a : State R S) (initial : Records) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest : Records)
    (ready : HashInputs.Ready (projectState p.register p.stack a))
    (rows : a.stacks (p.stack 9) = candidateEncoding initial)
    (family : generatedPayloads
      (SubexpAlphabetProgram.alphabetWords (a.stacks (p.stack 0)))
      (CounterPrograms.value (a.stacks (p.stack 5))) = seed :: rest)
    (hmass : ∀ frame, ContextFrame p a frame → ∀ rows' state,
      rows'.length < initial.length + CounterPrograms.value (a.stacks (p.stack 6)) →
      rows' ⊆ (seed :: rest) ++ initial →
      ControllerReady p.controller frame (seed :: rest) rows' state →
      MassSpec mass p.controller.trial.core (afterCopyFamily p.controller.trial state)
        (score rows') (valid rows') B C cost)
    (hp : ∀ rows',
      rows'.length < initial.length + CounterPrograms.value (a.stacks (p.stack 6)) →
      rows' ⊆ (seed :: rest) ++ initial → ∀ bits ∈ seed :: rest,
        valid rows' bits ∧ bits.length ≤ C ∧ (score rows' bits).length = B) :
    ∃ t ≤ budget (a.stacks (p.stack 0)) (a.stacks (p.stack 5)) (a.stacks (p.stack 6)) B C cost,
      ∃ b : State R S, Eval (command p mass) t a b ∧
        b.stacks (p.stack 9) = candidateEncoding
          (iter (payloadNext score seed rest) (CounterPrograms.value (a.stacks (p.stack 6))) initial) ∧
        b.stacks (p.stack 13) = [] ∧ ContextFrame p a b := by
  obtain ⟨t1, ht1, prepared, hprepare, hready, hrounds, hstacks, hregs⟩ :=
    HashSetup.generate_eval p.register p.stack p.register_injective p.stack_injective
      initial a ready rows
  rw [family] at hready
  let rounds := List.replicate (CounterPrograms.value (a.stacks (p.stack 6))) true
  have hmass' : ∀ rows' state, rows'.length < initial.length + rounds.length →
      rows' ⊆ (seed :: rest) ++ initial →
      ControllerReady p.controller prepared (seed :: rest) rows' state →
      MassSpec mass p.controller.trial.core (afterCopyFamily p.controller.trial state)
        (score rows') (valid rows') B C cost := by
    simpa only [rounds, List.length_replicate] using hmass prepared ⟨hstacks, hregs⟩
  have hp' : ∀ rows', rows'.length < initial.length + rounds.length →
      rows' ⊆ (seed :: rest) ++ initial → ∀ bits ∈ seed :: rest,
        valid rows' bits ∧ bits.length ≤ C ∧ (score rows' bits).length = B := by
    simpa only [rounds, List.length_replicate] using hp
  obtain ⟨t2, ht2, b, hb, hk, _, he⟩ := controller_eval_bounded p.controller mass
    prepared score valid B C cost seed rest initial rounds prepared hmass' hp' hready hrounds
  refine ⟨t1+t2, ?_, b, hprepare.seq he, ?_, hk, ?_⟩
  · simp only [rounds, List.length_replicate] at ht2
    dsimp only [budget]
    rw [family, List.length_cons]
    omega
  · simpa only [rounds, List.length_replicate, Execution.Hash.Ports.controller,
      relocateController] using hb.2.2.1

  · constructor
    · intro i hi
      exact (hb.2.2.2.1 i (Ne.symm (hi 9)) (Ne.symm (hi 13))
        (fun j => hi (localController.trial.core.stack j))).trans (hstacks i hi)
    · intro i hi
      exact (hb.2.2.2.2 i (Ne.symm (hi 8)) (Ne.symm (hi 9))
        (fun j => hi (localController.trial.core.register j))).trans (hregs i hi)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
