import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideInitialization

namespace OAI.Algorithms

/-! Canonical node ranks computed by the actual search in the widened worker. -/

namespace SubexponentialSAT.SubexpNodeWideIndex

open BitProgram StructuredCalls

abbrev Data := State 16 288

def ports : Fin 256 → Fin 288 := Fin.castAdd 32
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _

def localState (d : Data) : SubexpNodeIndexProgram.Data := projectState id ports d

abbrev command : Cmd 16 288 :=
  .call (ProgramLinking.liftProgram SubexpNodeIndexProgram.program id ports)

theorem command_eval (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (i : Fin (p^4 - 1)) (d : Data)
    (hquery : d.stacks 78 = SubexpNodeIndexSemantics.thetaWord p D i)
    (hmaster : d.stacks 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (hclean : SubexpNodeIndexProgram.Clean (localState d)) :
    ∃ n ≤ SubexpNodeIndexProgram.budget (SubexpNodeIndexSemantics.thetaWord p D i)
        (SubexpNodeLiftData.liftedNodeWords p (D+1) M) + 1, ∃ out : Data,
      Eval command n d out ∧
      out.stacks = Function.update d.stacks 116 (List.replicate i.val true) ∧
      ∀ j : Fin 16, 5 ≤ j.val → out.regs j = d.regs j := by
  obtain ⟨e,⟨n,hn,ht⟩,hs,hr⟩ :=
    SubexpNodeIndexSemantics.program_run p M D i (localState d) hquery hmaster hclean
  let out := embedState id ports d e
  have he := eval_call_from_state SubexpNodeIndexProgram.program id ports d
    Function.injective_id ports_injective ht
  refine ⟨n,hn,out,he,?_,?_⟩
  · change Function.extend ports e.stacks d.stacks = _
    rw [hs, ProgramLinking.extend_update ports_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project id ports d Function.injective_id ports_injective)
    change Function.extend ports (localState d).stacks d.stacks = d.stacks at hb
    rw [hb]
    rfl
  · intro j hj
    exact (embedState_register id ports d e Function.injective_id j).trans (hr j hj)

/-- The outer iterator supplies a real table member. The search discovers
its canonical index; no index word is an input to this theorem. -/
theorem command_eval_of_mem (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (d : Data)
    (hquery : d.stacks 78 ∈ SubexpNodeLiftData.liftedNodeWords p (D+1) M)
    (hmaster : d.stacks 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (hclean : SubexpNodeIndexProgram.Clean (localState d)) :
    ∃ i : Fin (p^4 - 1), d.stacks 78 = SubexpNodeIndexSemantics.thetaWord p D i ∧
      ∃ n ≤ SubexpNodeIndexProgram.budget (d.stacks 78)
          (SubexpNodeLiftData.liftedNodeWords p (D+1) M) + 1, ∃ out : Data,
        Eval command n d out ∧
        out.stacks = Function.update d.stacks 116 (List.replicate i.val true) ∧
        ∀ j : Fin 16, 5 ≤ j.val → out.regs j = d.regs j := by
  obtain ⟨i,hi⟩ :=
    (SubexpNodeIndexSemantics.mem_liftedNodeWords_iff p (D+1) M (Nat.succ_pos D)
      (d.stacks 78)).mp hquery
  refine ⟨i,hi.symm,?_⟩
  simpa only [SubexpNodeIndexSemantics.thetaWord, hi] using
    command_eval p D M i d hi.symm hmaster hclean

/-- The search master is the actual one installed from the generated table
by the one-time widened initialization. -/
theorem initialized_master (d : SubexpNodeWideSetup.Data) (D : ℕ) :
    SubexpNodeWideInitialization.resultStacks d D 125 = d.stacks 332 := by
  simp [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, SubexpNodeWideInitialization.dimensionResult]

end SubexponentialSAT.SubexpNodeWideIndex

end OAI.Algorithms
