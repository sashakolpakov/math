import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHash
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramHistory

namespace OAI.Algorithms

/-! The complete fixed hash command with exact execution history and literal
caller-frame preservation.  Alphabet generation and each mass evaluation
retain the same paid native implementation and budget. -/
namespace SubexponentialSAT.SqrtLog.Execution.Hash

open BitProgram StructuredCalls HashSelectProgram

/-- Mass correctness and its resource bound are needed only at actual greedy
history states.  No arbitrary repetition of initial rows is admitted by the
callback domain.  The conclusion preserves the full external context. -/
theorem command_eval_history {R S : ℕ} (p : Ports R S) (mass : Cmd R S)
    (a : State R S) (initial : Records) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest : Records)
    (ready : HashInputs.Ready (projectState p.register p.stack a))
    (rows : a.stacks (p.stack 9) = candidateEncoding initial)
    (family : generatedPayloads
      (SubexpAlphabetProgram.alphabetWords (a.stacks (p.stack 0)))
      (CounterPrograms.value (a.stacks (p.stack 5))) = seed :: rest)
    (hmass : ∀ frame, ContextFrame p a frame →
      ∀ q < CounterPrograms.value (a.stacks (p.stack 6)), ∀ state,
      ControllerReady p.controller frame (seed :: rest)
        (iter (payloadNext score seed rest) q initial) state →
      MassSpec mass p.controller.trial.core (afterCopyFamily p.controller.trial state)
        (score (iter (payloadNext score seed rest) q initial))
        (valid (iter (payloadNext score seed rest) q initial)) B C cost)
    (hp : ∀ q < CounterPrograms.value (a.stacks (p.stack 6)),
      ∀ bits ∈ seed :: rest,
      valid (iter (payloadNext score seed rest) q initial) bits ∧
        bits.length ≤ C ∧
        (score (iter (payloadNext score seed rest) q initial) bits).length = B) :
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
  have hmass' : ∀ q < rounds.length, ∀ state,
      ControllerReady p.controller prepared (seed :: rest)
        (iter (payloadNext score seed rest) q initial) state →
      MassSpec mass p.controller.trial.core (afterCopyFamily p.controller.trial state)
        (score (iter (payloadNext score seed rest) q initial))
        (valid (iter (payloadNext score seed rest) q initial)) B C cost := by
    simpa only [rounds, List.length_replicate] using hmass prepared ⟨hstacks, hregs⟩
  have hp' : ∀ q < rounds.length, ∀ bits ∈ seed :: rest,
      valid (iter (payloadNext score seed rest) q initial) bits ∧
        bits.length ≤ C ∧
        (score (iter (payloadNext score seed rest) q initial) bits).length = B := by
    simpa only [rounds, List.length_replicate] using hp
  obtain ⟨t2, ht2, b, hb, hk, _, he⟩ := controller_eval_history p.controller mass
    prepared score valid B C cost seed rest initial rounds prepared hmass' hp' hready hrounds
  refine ⟨t1+t2, ?_, b, hprepare.seq he, ?_, hk, ?_⟩
  · simp only [rounds, List.length_replicate] at ht2
    dsimp only [budget]
    rw [family, List.length_cons]
    omega
  · simpa only [rounds, List.length_replicate, Ports.controller,
      relocateController] using hb.2.2.1
  · constructor
    · intro i hi
      exact (hb.2.2.2.1 i (Ne.symm (hi 9)) (Ne.symm (hi 13))
        (fun j => hi (localController.trial.core.stack j))).trans (hstacks i hi)
    · intro i hi
      exact (hb.2.2.2.2 i (Ne.symm (hi 8)) (Ne.symm (hi 9))
        (fun j => hi (localController.trial.core.register j))).trans (hregs i hi)

end SubexponentialSAT.SqrtLog.Execution.Hash

end OAI.Algorithms
