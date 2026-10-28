import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyIncidence

namespace OAI.Algorithms

/-! The incidence service used by the forty-register factor interpreter.
Only its assigned sixteen registers and output/factor stacks can change. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpSetupStorage
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

structure IncidenceReady {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a : OuterData)
    (width : List Bool) (frame : Fin 6 → List Bool) : Prop where
  caller : CallerInput p.t p.model p.modulus p.cache J p.R theta a n
  outputEmpty : a.stacks 62=[]
  temporary : a.stacks 684=[]
  wordBound : WordBound B (LeafProgram.Incidence.staged a)
  sourceSize : sourceCallWordBound B n (incidenceBitsBound n J (d*baseWidth 3 p.t)) ≤ S
  ambientSize : n ≤ S
  factorSize : f ≤ S
  plansSize : (LayoutOwnerFiberProgram.stream ps).length ≤ S
  sourceInput : ∀ j,j < n → ∀ acc,
    acc.length ≤ n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t)) →
    ((LeafProgram.Incidence.staged a).stacks 574).getD j false=false → ∀ regs,
    SourceCallInput p ps P (sourceCallData (LeafProgram.Incidence.staged a).stacks j acc regs)
      j n f S width frame

noncomputable def incidenceWideOutput (a : State 40 768) (rr : Fin 16 → Bool)
    (bits : List Bool) : State 40 768 :=
  embedState LeafProgram.Incidence.callerRegisters id a
    (⟨rr,incidenceOutput a.stacks bits⟩ : OuterData)

theorem incidenceWideOutput_stacks (a : State 40 768) (rr : Fin 16 → Bool)
    (bits : List Bool) :
    (incidenceWideOutput a rr bits).stacks=incidenceOutput a.stacks bits := by
  funext i
  exact embedState_stack _ _ _ _ Function.injective_id i

theorem incidenceWideOutput_registers (a : State 40 768) (rr : Fin 16 → Bool)
    (bits : List Bool) (i : Fin 40) (hi : 16 ≤ i.val) :
    (incidenceWideOutput a rr bits).regs i=a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv:=congrArg Fin.val hj
  change j.val=i.val at hv
  omega

theorem incidence_caller_from_source {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : State 40 768) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : IncidenceReady p ps P J n f S B theta
      (projectState LeafProgram.Incidence.callerRegisters id a) width frame) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ incidenceBitsBound n J (d*baseWidth 3 p.t) ∧
        payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
          (sourceRowProperty p ps P n f)
          (LeafProgram.Incidence.staged (projectState LeafProgram.Incidence.callerRegisters id a)).stacks
          j (payload j)) ∧
      k ≤ incidenceWorkBound p (projectState LeafProgram.Incidence.callerRegisters id a) n J S B+1 ∧
      Eval LeafProgram.Incidence.caller k a
        (incidenceWideOutput a rf (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries
            (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))) := by
  obtain ⟨payload,k,rf,hpayload,hk,he⟩ := incidence_command_from_source p ps P J n f S B theta
    (projectState LeafProgram.Incidence.callerRegisters id a) width frame
    h.caller h.outputEmpty h.temporary h.wordBound h.sourceSize h.ambientSize h.factorSize
    h.plansSize h.sourceInput
  have hl := eval_liftCommand_from_state LeafProgram.Incidence.command 556 62
    LeafProgram.Incidence.callerRegisters id a (Fin.castAdd_injective 16 24)
    Function.injective_id he
  exact ⟨payload,k+1,rf,hpayload,Nat.add_le_add_right hk 1,hl⟩

theorem incidence_program_of_eval (a b : OuterData) (k K : ℕ)
    (h : Eval LeafProgram.Incidence.command k a b) (hk : k ≤ K) :
    RunsIn LeafProgram.Incidence.program (K+1)
      (a.withPC (some LeafProgram.Incidence.program.entry)) (b.withPC none) :=
  ⟨k+1,Nat.add_le_add_right hk 1,compiled_halt_trace h 556 62⟩

theorem incidence_primitive_of_eval (a b : OuterData) (k K : ℕ)
    (h : Eval LeafProgram.Incidence.command k a b) (hk : k ≤ K) :
    Computation.RunsIn (primitive LeafProgram.Incidence.program).step
      (primitiveOverhead LeafProgram.Incidence.program*(K+1))
      (primitiveCfg LeafProgram.Incidence.program
        (a.withPC (some LeafProgram.Incidence.program.entry)))
      (primitiveCfg LeafProgram.Incidence.program (b.withPC none)) :=
  primitive_execution LeafProgram.Incidence.program (incidence_program_of_eval a b k K h hk)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
