import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanProgram

namespace OAI.Algorithms

/-! The explicit record-reversal pass needed by the raw-pair frontend. -/
namespace SubexponentialSAT.SubexpIncidencePlanForward

open BitProgram StructuredCalls

abbrev Data := State 10 16
def registers : Fin 3 → Fin 10 := ![0,1,4]
def reverseStacks : Fin 4 → Fin 16 := ![7,3,0,4]
theorem registers_injective : Function.Injective registers := by decide
theorem stacks_injective : Function.Injective reverseStacks := by decide
abbrev reverseCall : Cmd 10 16 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram registers reverseStacks)
abbrev reverse : Cmd 10 16 := .seq (SubexpIncidencePlanFinish.pushFalse 0) reverseCall

def result (d : Data) (records : List (List Bool)) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 true) 4 false,
    Function.update (Function.update d.stacks 7 []) 0 (ProgramEncoding.encodeRecords records.reverse)⟩

theorem reverse_eval (d : Data) (records : List (List Bool))
    (h7 : d.stacks 7 = ProgramEncoding.encodeRecords records)
    (h0 : d.stacks 0 = []) (h4 : d.stacks 4 = []) :
    ∃ n, Eval reverse n d (result d records) ∧
      n ≤ 2+10*(ProgramEncoding.encodeRecords records).length := by
  let d1 := SubexpIncidencePlanFinish.pushedFalse 0 d
  let a := SubexpNormalizeProgram.filterState (d1.regs 0) (d1.regs 1) (d1.regs 4)
    (ProgramEncoding.encodeRecords records) (d.stacks 3) (ProgramEncoding.encodeRecords []) []
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 3)
    (ProgramEncoding.encodeRecords records.reverse) []
  obtain ⟨n,hn,ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] []
    (d.stacks 3) (d1.regs 0) (d1.regs 1) (d1.regs 4)
  have ha : embedState registers reverseStacks d1 a = d1 := by
    apply embedState_eq_of_ports registers reverseStacks d1 d1 a registers_injective stacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i
      fin_cases i <;> simp [a,SubexpNormalizeProgram.filterState,SubexpPostfixControl.quadruple,
        reverseStacks,d1,h0,h4,h7,ProgramEncoding.encodeRecords,
        Encoding.encodeList]
    · intros; rfl
  have hb : embedState registers reverseStacks d1 b = result d records := by
    apply embedState_eq_of_ports registers reverseStacks d1 (result d records) b
      registers_injective stacks_injective
    · intro i
      fin_cases i <;> simp [b,SubexpNormalizeProgram.filterState,SubexpPostfixControl.triple,
        registers,result]
    · intro i hi
      have h0' : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1' : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h4' : i ≠ 4 := fun h => hi ⟨2,h.symm⟩
      simp [result,d1,h0',h1',h4']
    · intro i
      fin_cases i <;> simp [b,SubexpNormalizeProgram.filterState,SubexpPostfixControl.quadruple,
        reverseStacks,result,h4]
    · intro i hi
      have h0' : i ≠ 0 := fun h => hi ⟨2,h.symm⟩
      have h7' : i ≠ 7 := fun h => hi ⟨0,h.symm⟩
      simp [result,d1,h0',h7']
  have htrace : Trace SubexpNormalizeProgram.reverseRecordsProgram n
      (a.withPC (some SubexpNormalizeProgram.reverseRecordsProgram.entry)) (b.withPC none) := by
    simpa [a,b,ProgramEncoding.encodeRecords] using ht
  have h := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram registers reverseStacks d1
    registers_injective stacks_injective htrace
  rw [ha,hb] at h
  change n ≤ 10*(ProgramEncoding.encodeRecords records).length at hn
  exact ⟨2+n,(SubexpIncidencePlanFinish.pushFalse_eval 0 d).seq h,by omega⟩

abbrev command : Cmd 10 16 := .seq SubexpIncidencePlanProgram.command reverse

def finalState (rf : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ)) : Data :=
  result (SubexpIncidencePlanFinish.state rf v scopes.length
    (Subexp.IncidencePlanSpec.degree scopes v) D Δ
    (ProgramEncoding.encodeRecords ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v).map
      SubexpIncidencePlanProgram.unary))
    (SubexpIncidencePlanProgram.unary (scopes.length+D+v*Δ+Δ))
    (SubexpIncidencePlanProgram.unary v))
    (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v))

theorem finalState_output (rf : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ)) :
    (finalState rf D Δ v scopes).stacks 0 = ProgramEncoding.encodeRecords
      (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.vertexPlan D Δ scopes v)) := by
  simp [finalState,result,Subexp.ReadPlan.unaryPlan,Subexp.IncidencePlanSpec.producedPlan]

theorem command_eval_exact (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool), Eval command n
      (SubexpIncidencePlanProgram.input regs D Δ v scopes) (finalState rf D Δ v scopes) ∧
      n ≤ SubexpIncidencePlanProgram.bound D Δ v scopes + 2 +
        10*(ProgramEncoding.encodeRecords
          (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v))).length := by
  obtain ⟨n,rf,h,hn⟩ := SubexpIncidencePlanProgram.command_eval regs D Δ v scopes hd
  let d := SubexpIncidencePlanFinish.state rf v scopes.length
    (Subexp.IncidencePlanSpec.degree scopes v) D Δ
    (ProgramEncoding.encodeRecords ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v).map
      SubexpIncidencePlanProgram.unary))
    (SubexpIncidencePlanProgram.unary (scopes.length+D+v*Δ+Δ)) (SubexpIncidencePlanProgram.unary v)
  obtain ⟨m,hr,hm⟩ := reverse_eval d
    (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v)) rfl rfl rfl
  exact ⟨n+m,rf,h.seq hr,by omega⟩

theorem command_eval (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ (n : ℕ) (e : Data), Eval command n (SubexpIncidencePlanProgram.input regs D Δ v scopes) e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords
        (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.vertexPlan D Δ scopes v)) ∧
      n ≤ SubexpIncidencePlanProgram.bound D Δ v scopes + 2 +
        10*(ProgramEncoding.encodeRecords
          (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v))).length := by
  obtain ⟨n,rf,h,hn⟩ := command_eval_exact regs D Δ v scopes hd
  exact ⟨n,finalState rf D Δ v scopes,h,finalState_output rf D Δ v scopes,hn⟩

abbrev program : Program 10 16 (size command+1) := compiled command 6 0

theorem program_trace (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ (n : ℕ) (e : Data),
      Trace program n ((SubexpIncidencePlanProgram.input regs D Δ v scopes).withPC (some program.entry))
        (e.withPC none) ∧
      e.stacks 0 = ProgramEncoding.encodeRecords
        (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.vertexPlan D Δ scopes v)) ∧
      n ≤ SubexpIncidencePlanProgram.bound D Δ v scopes + 3 +
        10*(ProgramEncoding.encodeRecords
          (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v))).length := by
  obtain ⟨n,e,h,he,hn⟩ := command_eval regs D Δ v scopes hd
  exact ⟨n+1,e,compiled_halt_trace h 6 0,he,by omega⟩

end SubexponentialSAT.SubexpIncidencePlanForward

end OAI.Algorithms
