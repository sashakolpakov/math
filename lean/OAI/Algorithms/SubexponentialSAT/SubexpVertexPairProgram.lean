import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreRefinement

namespace OAI.Algorithms

/-! Actual depth-two tuple generation produces the raw vertex-plan pairs. -/
namespace SubexponentialSAT.SubexpVertexPairProgram

open BitProgram StructuredCalls
open SubexpPlanAlphabetBase

abbrev Data := State 13 25
abbrev Code := Cmd 13 25

def tupleRegs : Fin 10 → Fin 13 := Fin.castAdd 3
def tupleStacks : Fin 9 → Fin 25 := ![0,24,1,2,3,4,5,6,7]
theorem tupleRegs_injective : Function.Injective tupleRegs := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)
theorem tupleStacks_injective : Function.Injective tupleStacks := by decide

def loadDepth : Code := .seq (Subexp.TupleProgram.pushConst 7 0 true)
  (Subexp.TupleProgram.pushConst 7 0 true)
def loaded (d : Data) : Data := Subexp.TupleProgram.pushedState 7 0 true
  (Subexp.TupleProgram.pushedState 7 0 true d)
theorem loadDepth_eval (d : Data) : Eval loadDepth 4 d (loaded d) :=
  (Subexp.TupleProgram.pushConst_eval 7 0 true d).seq
    (Subexp.TupleProgram.pushConst_eval 7 0 true _)

def tuples : Code := .call
  (ProgramLinking.liftProgram Subexp.TupleProgram.generateProgram tupleRegs tupleStacks)

def pairRows (D Δ : ℕ) (scopes : List (List ℕ)) : List (List Bool) :=
  Subexp.TupleProgram.powerRows (alphabet D Δ scopes) 2 [[]]

def PreservesMasters (D Δ : ℕ) (scopes : List (List ℕ)) (d : Data) : Prop :=
  d.stacks 16 = scopeBytes scopes ∧ d.stacks 17 = unary D ∧ d.stacks 18 = unary Δ

theorem tuples_eval_framed (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ)) :
    ∃ n e, Eval tuples n
      (loaded (data regs D Δ scopes (unary D) []
        (ProgramEncoding.encodeRecords (alphabet D Δ scopes)) [])) e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords (pairRows D Δ scopes) ∧
      e.stacks 24 = ProgramEncoding.encodeRecords (alphabet D Δ scopes) ∧
      PreservesMasters D Δ scopes e ∧
      n ≤ Subexp.TupleProgram.powerCost (alphabet D Δ scopes) 2 [[]]+9 := by
  let a := loaded (data regs D Δ scopes (unary D) []
    (ProgramEncoding.encodeRecords (alphabet D Δ scopes)) [])
  let localData : State 10 9 := ⟨a.regs ∘ tupleRegs,a.stacks ∘ tupleStacks⟩
  have ha : Subexp.TupleProgram.outerInvariant (alphabet D Δ scopes) [true,true]
      (localData.regs 9) localData := by
    simp [Subexp.TupleProgram.outerInvariant,localData,a,loaded,
      Subexp.TupleProgram.pushedState,data,tupleStacks]
  obtain ⟨b,hb,n,hn,ht⟩ := Subexp.TupleProgram.generateProgram_runsIn
    (alphabet D Δ scopes) [true,true] (localData.regs 9) localData ha rfl rfl rfl
  have he : embedState tupleRegs tupleStacks a localData = a := by
    apply embedState_eq_of_ports _ _ _ _ _ tupleRegs_injective tupleStacks_injective
    all_goals intros; rfl
  have h := eval_call_lifted Subexp.TupleProgram.generateProgram tupleRegs tupleStacks a
    tupleRegs_injective tupleStacks_injective ht
  rw [he] at h
  refine ⟨n,embedState tupleRegs tupleStacks a b,h,?_,?_,?_,?_⟩
  · have h0 := embedState_stack tupleRegs tupleStacks a b tupleStacks_injective (0 : Fin 9)
    simpa [tupleStacks,pairRows] using h0.trans hb.2.1
  · have h1 := embedState_stack tupleRegs tupleStacks a b tupleStacks_injective (1 : Fin 9)
    simpa [tupleStacks] using h1.trans hb.1.1
  · refine ⟨?_,?_,?_⟩
    · have hf := embedState_stack_frame tupleRegs tupleStacks a b 16 (by decide)
      simpa [a,loaded,Subexp.TupleProgram.pushedState,data] using hf
    · have hf := embedState_stack_frame tupleRegs tupleStacks a b 17 (by decide)
      simpa [a,loaded,Subexp.TupleProgram.pushedState,data] using hf
    · have hf := embedState_stack_frame tupleRegs tupleStacks a b 18 (by decide)
      simpa [a,loaded,Subexp.TupleProgram.pushedState,data] using hf
  · simpa only [List.length_cons,List.length_nil] using hn

theorem tuples_eval (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ)) :
    ∃ n e, Eval tuples n
      (loaded (data regs D Δ scopes (unary D) []
        (ProgramEncoding.encodeRecords (alphabet D Δ scopes)) [])) e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords (pairRows D Δ scopes) ∧
      e.stacks 24 = ProgramEncoding.encodeRecords (alphabet D Δ scopes) ∧
      n ≤ Subexp.TupleProgram.powerCost (alphabet D Δ scopes) 2 [[]]+9 := by
  obtain ⟨n,e,h,h0,h24,_,hn⟩ := tuples_eval_framed regs D Δ scopes
  exact ⟨n,e,h,h0,h24,hn⟩

def command : Code := .seq SubexpPlanAlphabetBase.command (.seq loadDepth tuples)
def bound (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  totalBound D Δ scopes + Subexp.TupleProgram.powerCost (alphabet D Δ scopes) 2 [[]]+13

theorem command_eval_framed (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ n e, Eval command n (data regs D Δ scopes [] [] [] []) e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords (pairRows D Δ scopes) ∧
      e.stacks 24 = ProgramEncoding.encodeRecords (alphabet D Δ scopes) ∧
      PreservesMasters D Δ scopes e ∧
      n ≤ bound D Δ scopes := by
  obtain ⟨n,rf,h,hn⟩ := SubexpPlanAlphabetBase.command_eval regs D Δ scopes hd
  obtain ⟨m,e,ht,h0,h24,hframe,hm⟩ := tuples_eval_framed rf D Δ scopes
  exact ⟨_,e,h.seq ((loadDepth_eval _).seq ht),h0,h24,hframe,by dsimp [bound]; omega⟩

theorem command_eval (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ n e, Eval command n (data regs D Δ scopes [] [] [] []) e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords (pairRows D Δ scopes) ∧
      e.stacks 24 = ProgramEncoding.encodeRecords (alphabet D Δ scopes) ∧
      n ≤ bound D Δ scopes := by
  obtain ⟨n,e,h,h0,h24,_,hn⟩ := command_eval_framed regs D Δ scopes hd
  exact ⟨n,e,h,h0,h24,hn⟩

theorem pairRows_length (D Δ : ℕ) (scopes : List (List ℕ)) :
    (pairRows D Δ scopes).length = D^2 := by
  unfold pairRows
  rw [Subexp.TupleProgram.powerRows_length]
  simp [alphabet]

theorem pairRows_perm (D Δ : ℕ) (scopes : List (List ℕ)) :
    (pairRows D Δ scopes).Perm
      (((List.range' 0 D).product (List.range' 0 D)).map (fun p =>
        Subexp.PairScoreProgram.pairBytes
          (Subexp.IncidencePlanSpec.vertexPlan D Δ scopes p.1,
           Subexp.IncidencePlanSpec.vertexPlan D Δ scopes p.2))) := by
  exact Subexp.CandidateScoreRefinement.generated_vertex_pair_payloads
    (List.range' 0 D) (Subexp.IncidencePlanSpec.vertexPlan D Δ scopes)

def canonicalPairs (D Δ : ℕ) (scopes : List (List ℕ)) :
    List Subexp.PairScoreProgram.PlanPair :=
  ((List.range' 0 D).product (List.range' 0 D)).map (fun p =>
    (Subexp.IncidencePlanSpec.vertexPlan D Δ scopes p.1,
     Subexp.IncidencePlanSpec.vertexPlan D Δ scopes p.2))

/-- A proof-level description of the actual emitted records. No decoder or
choice operation is installed in the machine. -/
theorem rawPlans_exists (D Δ : ℕ) (scopes : List (List ℕ)) :
    ∃ rawPlans : List Subexp.PairScoreProgram.PlanPair,
      pairRows D Δ scopes = rawPlans.map Subexp.PairScoreProgram.pairBytes ∧
      rawPlans.Perm (canonicalPairs D Δ scopes) := by
  have hp : (pairRows D Δ scopes).Perm
      ((canonicalPairs D Δ scopes).map Subexp.PairScoreProgram.pairBytes) := by
    simpa only [canonicalPairs,List.map_map,Function.comp_def] using pairRows_perm D Δ scopes
  have hr : Relation.Comp
      (fun bytes plans => bytes = plans.map Subexp.PairScoreProgram.pairBytes)
      List.Perm (pairRows D Δ scopes) (canonicalPairs D Δ scopes) := by
    rw [List.eq_map_comp_perm]
    exact hp
  exact hr

abbrev program : Program 13 25 (size command+1) := compiled command 16 0

theorem program_trace_framed (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ (n : ℕ) (e : Data), n ≤ bound D Δ scopes+1 ∧
      Trace program n ((data regs D Δ scopes [] [] [] []).withPC (some program.entry))
        (e.withPC none) ∧ e.stacks 0 = ProgramEncoding.encodeRecords (pairRows D Δ scopes) ∧
      e.stacks 24 = ProgramEncoding.encodeRecords (alphabet D Δ scopes) ∧
      PreservesMasters D Δ scopes e := by
  obtain ⟨n,e,h,h0,h24,hframe,hn⟩ := command_eval_framed regs D Δ scopes hd
  exact ⟨n+1,e,by omega,compiled_halt_trace h 16 0,h0,h24,hframe⟩

theorem program_trace (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ (n : ℕ) (e : Data), n ≤ bound D Δ scopes+1 ∧
      Trace program n ((data regs D Δ scopes [] [] [] []).withPC (some program.entry))
        (e.withPC none) ∧ e.stacks 0 = ProgramEncoding.encodeRecords (pairRows D Δ scopes) := by
  obtain ⟨n,e,h,h0,_,hn⟩ := command_eval regs D Δ scopes hd
  exact ⟨n+1,e,by omega,compiled_halt_trace h 16 0,h0⟩

theorem program_primitive (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ e : Data, e.stacks 0 = ProgramEncoding.encodeRecords (pairRows D Δ scopes) ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program*(bound D Δ scopes+1))
        (BitProgram.primitiveCfg program
          ((data regs D Δ scopes [] [] [] []).withPC (some program.entry)))
        (BitProgram.primitiveCfg program (e.withPC none)) := by
  obtain ⟨n,e,h,h0,_,hn⟩ := command_eval regs D Δ scopes hd
  exact ⟨e,h0,(StructuredCalls.primitive_execution h 16 0).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1))⟩

end SubexponentialSAT.SubexpVertexPairProgram

end OAI.Algorithms
