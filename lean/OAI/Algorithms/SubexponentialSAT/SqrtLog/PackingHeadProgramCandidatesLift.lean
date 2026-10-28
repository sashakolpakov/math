import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidatesBounds

namespace OAI.Algorithms

/-! Caller-state interface for the fixed all-candidate head score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp

abbrev lifted {R S : ℕ} (reg : Fin 8 → Fin R) (stack : Fin 12 → Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram program reg stack)

theorem final_stacks (rows candidates : List (List Bool)) :
    (baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).stacks =
    Function.update (Function.update (inputState rows candidates).stacks 8 []) 9
      (ProgramEncoding.encodeRecords (scoreRecords rows candidates)) := by
  funext i; fin_cases i <;> simp [baseState,inputState,RecordPrograms.state,ports]

theorem command_lifted {R S : ℕ} (reg : Fin 8 → Fin R) (stack : Fin 12 → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (d : State R S) (rows candidates : List (List Bool))
    (hr : ∀ i,d.regs (reg i)=false)
    (h1 : d.stacks (stack 1)=rows.flatten)
    (h5 : d.stacks (stack 5)=List.replicate rows.length true)
    (h8 : d.stacks (stack 8)=ProgramEncoding.encodeRecords candidates)
    (hc : ∀ i : Fin 12,i≠1 → i≠5 → i≠8 → d.stacks (stack i)=[])
    (hlen : ∀ candidate ∈ candidates,validPayload rows candidate) :
    ∃ n ≤ budget rows candidates, ∃ e : State R S,
      Eval (lifted reg stack) n d e ∧
      e.stacks = Function.update (Function.update d.stacks (stack 8) []) (stack 9)
        (ProgramEncoding.encodeRecords (scoreRecords rows candidates)) ∧
      (∀ i,e.regs (reg i)=decide (i=6)) ∧
      (∀ j,(¬∃ i,reg i=j) → e.regs j=d.regs j) := by
  let a := inputState rows candidates
  let b := baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))
  have ha : embedState reg stack d a=d := by
    apply embedState_eq_of_ports reg stack d d a hreg hstack
    · intro i; fin_cases i <;> simp [a,inputState,baseState,RecordPrograms.state,ports,hr]
    · intros; rfl
    · intro i
      fin_cases i <;> first
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using h1
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using h5
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using h8
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using hc _ (by decide) (by decide) (by decide)
    · intros; rfl
  let e := embedState reg stack d b
  obtain ⟨n,hn,ht⟩ := program_run rows candidates hlen
  have he := eval_call_lifted program reg stack d hreg hstack (a:=a) (b:=b) ht
  refine ⟨n,hn,e,?_,?_,?_,?_⟩
  · simpa only [ha,lifted] using he
  · change Function.extend stack b.stacks d.stacks = _
    have hf : Function.extend stack a.stacks d.stacks=d.stacks :=
      congrArg StructuredProgram.State.stacks ha
    change Function.extend stack
      (baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).stacks d.stacks = _
    rw [final_stacks,ProgramLinking.extend_update hstack,ProgramLinking.extend_update hstack]
    rw [hf]
  · intro i
    have h := embedState_register reg stack d b hreg i
    simpa [e,b,baseState] using h
  · intro j hj
    exact embedState_register_frame reg stack d b j hj

theorem command_lifted_words {R S r Q : ℕ}
    (reg : Fin 8 → Fin R) (stack : Fin 12 → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (d : State R S) (prior candidates : List (MulticolorTypes.Word r Q))
    (hr : ∀ i,d.regs (reg i)=false)
    (h1 : d.stacks (stack 1)=(prior.map ReadPlan.encodeWord).flatten)
    (h5 : d.stacks (stack 5)=List.replicate prior.length true)
    (h8 : d.stacks (stack 8)=ProgramEncoding.encodeRecords (candidates.map ReadPlan.encodeWord))
    (hc : ∀ i : Fin 12,i≠1 → i≠5 → i≠8 → d.stacks (stack i)=[]) :
    ∃ n ≤ candidates.length*(43*prior.length*(Q*r)+20*prior.length+17*(Q*r)+66)+22,
      ∃ e : State R S, Eval (lifted reg stack) n d e ∧
      e.stacks = Function.update (Function.update d.stacks (stack 8) []) (stack 9)
        (ProgramEncoding.encodeRecords
          (candidates.map (fun candidate => List.replicate (coordinateOverlap candidate prior) false))) ∧
      (∀ i,e.regs (reg i)=decide (i=6)) ∧
      (∀ j,(¬∃ i,reg i=j) → e.regs j=d.regs j) := by
  have hv : ∀ candidate ∈ candidates.map ReadPlan.encodeWord,
      validPayload (prior.map ReadPlan.encodeWord) candidate := by
    intro candidate hcan row hrow
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hcan
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hrow
    simp
  obtain ⟨n,hn,e,he,hes,her,hef⟩ := command_lifted reg stack hreg hstack d
    (prior.map ReadPlan.encodeWord) (candidates.map ReadPlan.encodeWord) hr h1
    (by simpa using h5) h8 hc hv
  have hb := budget_le (prior.map ReadPlan.encodeWord) (candidates.map ReadPlan.encodeWord) (Q*r) (by
    intro candidate hcan
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hcan
    simp [ReadPlan.wordWidth])
  rw [scoreRecords_words] at hes
  exact ⟨n,hn.trans (by simpa using hb),e,he,hes,her,hef⟩

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
