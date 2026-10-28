import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeReferences
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativePrecision
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeExport

namespace OAI.Algorithms

/-! Fixed placement of the two measured setup programs in the outer worker.
The reference table is generated on320. The precision producer reads the
original binary parameters directly and leaves its unary result on212. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram

def referenceRegisters : Fin 10 → Fin 40 := Fin.castAdd 30
def referenceStacks : Fin 10 → Fin 896 := ![0,1,2,3,4,5,6,320,7,8]
abbrev references : Cmd 40 896 := .seq (route (782,0))
  (liftCommand References.command 0 7 referenceRegisters referenceStacks)

def ReferenceReady (a : FrameData) : Prop :=
  a.stacks 767=[] ∧ ∀ i : Fin 896, i.val < 9 ∨ i=320 → a.stacks i=[]

theorem references_eval (a : FrameData) (ha : ReferenceReady a) :
    ∃ t b, t ≤ routeCost (782,0) a+References.budget (a.stacks 782)+1 ∧
      Eval references t a b ∧ b.stacks=Function.update a.stacks 320
        (ProgramEncoding.encodeRecords (RowSelectionProgram.Index.alphabet
          (CounterPrograms.value (a.stacks 782)))) := by
  let c := routed (782,0) a
  let d := projectState referenceRegisters referenceStacks c
  have hd : d=References.input d.regs (a.stacks 782) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [d,c,projectState,referenceStacks,routed,References.input,
        ha.2 1 (by decide),ha.2 2 (by decide),ha.2 3 (by decide),ha.2 4 (by decide),
        ha.2 5 (by decide),ha.2 6 (by decide),ha.2 7 (by decide),ha.2 8 (by decide),
        ha.2 320 (by decide)]
  obtain ⟨t,rf,ht,he⟩ := References.command_eval d.regs (a.stacks 782)
  rw [←hd] at he
  let b := embedState referenceRegisters referenceStacks c
    (References.output rf (CounterPrograms.value (a.stacks 782)))
  have hl := eval_liftCommand_from_state References.command 0 7 referenceRegisters referenceStacks c
    (Fin.castAdd_injective 10 30) (by decide) he
  have hr := route_eval (782,0) (by unfold routeValid; decide) a ha.1
  refine ⟨routeCost (782,0) a+(t+1),b,by omega,hr.seq hl,?_⟩
  funext i
  by_cases hx : ∃ j, referenceStacks j=i
  · obtain ⟨j,rfl⟩ := hx
    rw [show b.stacks (referenceStacks j)=
      (References.output rf (CounterPrograms.value (a.stacks 782))).stacks j from
        embedState_stack _ _ _ _ (by decide) j]
    fin_cases j <;> simp [referenceStacks,References.output,
      ha.2 0 (by decide),ha.2 1 (by decide),ha.2 2 (by decide),ha.2 3 (by decide),
      ha.2 4 (by decide),ha.2 5 (by decide),ha.2 6 (by decide),ha.2 7 (by decide),ha.2 8 (by decide)]
  · have h0 : i≠0 := by intro hi; apply hx; exact ⟨0,hi.symm⟩
    have h320 : i≠320 := by intro hi; apply hx; exact ⟨7,hi.symm⟩
    rw [show b.stacks i=c.stacks i from embedState_stack_frame _ _ _ _ i hx]
    simp [c,routed,h0,h320]

def precisionRegisters : Fin 8 → Fin 40 := Fin.castAdd 32
def precisionStacks : Fin 10 → Fin 896 := ![785,782,0,1,2,3,4,5,212,6]
abbrev makePrecision : Cmd 40 896 :=
  liftCommand Precision.command 0 8 precisionRegisters precisionStacks

def PrecisionReady (a : FrameData) : Prop :=
  ∀ i : Fin 896, i.val < 7 ∨ i=212 → a.stacks i=[]

theorem makePrecision_eval (a : FrameData) (ha : PrecisionReady a)
    (hm : BinaryArithmetic.toNat (a.stacks 782)≠0) :
    ∃ t b, t ≤ Precision.budget (a.stacks 785) (a.stacks 782)+1 ∧
      Eval makePrecision t a b ∧ b.stacks=Function.update a.stacks 212
        (List.replicate (LeafParametersProgram.precision
          (BinaryArithmetic.toNat (a.stacks 785)) (BinaryArithmetic.toNat (a.stacks 782))) true) := by
  let d := projectState precisionRegisters precisionStacks a
  have hd : LeafParametersProgram.precisionReady d := by
    intro i hi
    fin_cases i <;> simp only [] at hi
    all_goals first
      | omega
      | exact ha _ (by decide)
  obtain ⟨t,e,ht,he,h0,h1,h8,hrest⟩ := Precision.command_eval d hd hm
  let b := embedState precisionRegisters precisionStacks a e
  have hl := eval_liftCommand_from_state Precision.command 0 8 precisionRegisters precisionStacks a
    (Fin.castAdd_injective 8 32) (by decide) he
  refine ⟨t+1,b,Nat.add_le_add_right ht 1,hl,?_⟩
  funext i
  by_cases hx : ∃ j, precisionStacks j=i
  · obtain ⟨j,rfl⟩ := hx
    rw [show b.stacks (precisionStacks j)=e.stacks j from
      embedState_stack _ _ _ _ (by decide) j]
    fin_cases j
    · exact h0
    · exact h1
    · simpa [precisionStacks,ha 0 (by decide)] using hrest 2 (by decide) (by decide) (by decide)
    · simpa [precisionStacks,ha 1 (by decide)] using hrest 3 (by decide) (by decide) (by decide)
    · simpa [precisionStacks,ha 2 (by decide)] using hrest 4 (by decide) (by decide) (by decide)
    · simpa [precisionStacks,ha 3 (by decide)] using hrest 5 (by decide) (by decide) (by decide)
    · simpa [precisionStacks,ha 4 (by decide)] using hrest 6 (by decide) (by decide) (by decide)
    · simpa [precisionStacks,ha 5 (by decide)] using hrest 7 (by decide) (by decide) (by decide)
    · exact h8
    · simpa [precisionStacks,ha 6 (by decide)] using hrest 9 (by decide) (by decide) (by decide)
  · have h212 : i≠212 := by intro hi; apply hx; exact ⟨8,hi.symm⟩
    rw [show b.stacks i=a.stacks i from embedState_stack_frame _ _ _ _ i hx]
    simp [h212]

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
