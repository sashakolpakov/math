import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopInputBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadySaved

namespace OAI.Algorithms

/-! Explicit bounded physical frame for one actual assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open IdempotentApplyProgram.Bounds
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {r Q n d : ℕ}

structure AssignmentFrame (q : Factor.Spec r Q n d) (degree : List Bool) (S A T F : ℕ)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d)
    (metadata702 metadata703 : List Bool) (high : Fin 768 → List Bool) : Prop where
  empty : ∀ i ∈ ([67,145,146,147,148,149,150,151,159,340,341,342,343,359] : List (Fin 768)),high i=[]
  headLength : (high 174).length=(high 178).length
  bucketLength : (high 174).length=(high 177).length
  supportLength : (high 174).length=(high 168).length
  ambientLength : (high 174).length ≤ n
  idsBytes : high 175=ProgramEncoding.encodeRecords (records (headIds (high 175)))
  idsBound : ∀ id ∈ headIds (high 175),id ≤ F
  idsLength : (high 175).length ≤ T
  oneBytes : high 69=Product.bytes q.one
  zeroBytes : high 190=RingProgram.flat zero
  coefficientOneBytes : high 207=RingProgram.flat one
  metadata702Bytes : high 702=metadata702
  metadata703Bytes : high 703=metadata703
  engine : FactorReady.Input q S A (preparedAssignment q degree high [] [])
  savedCapacity : byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ A

def assignmentReference (metadata702 metadata703 : List Bool)
    (c : AssignmentContext) (x : List Bool) : Fin 768 → List Bool :=
  Function.update (Function.update (Function.update (fun _=>[]) 145
    (LeafAssignmentMergeProgram.merge x c.headMask c.bucket)) 702 metadata702) 703 metadata703

def engineReady (q : Factor.Spec r Q n d) (S A : ℕ)
    (metadata702 metadata703 : List Bool) (c : AssignmentContext) (x : List Bool)
    (base : Fin 768 → List Bool) : Prop :=
  FactorReady.Input q S A base ∧
    base 145=LeafAssignmentMergeProgram.merge x c.headMask c.bucket ∧
    base 702=metadata702 ∧ base 703=metadata703

theorem preparedAssignment_regs (q : Factor.Spec r Q n d) (degree : List Bool)
    (high : Fin 768 → List Bool) (left seed : Raw n (baseWidth 3 q.p.t) d)
    (regs : Fin 40 → Bool) :
    (LeafAssignmentSetupProgram.prepared (assignmentMachine q degree high left seed regs)
      (fun _=>false) (fun _=>false)).stacks=preparedAssignment q degree high left seed := by
  simp only [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks]
  rfl

theorem AssignmentFrame.input (q : Factor.Spec r Q n d) (degree : List Bool) (S A T F : ℕ)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d)
    (metadata702 metadata703 : List Bool) (high : Fin 768 → List Bool)
    (hf : AssignmentFrame q degree S A T F headIds zero one metadata702 metadata703 high)
    (hAS : A ≤ S)
    (c : AssignmentContext) (x : List Bool) (hc : c.Matches high) (hx : high 174=x)
    (left seed : Raw n (baseWidth 3 q.p.t) d) (regs : Fin 40 → Bool)
    (hl : Good Finset.univ q.u q.J left) (hs : Good Finset.univ q.u q.J seed) :
    AssignmentReady q.u q.J (engineReady q S A metadata702 metadata703 c x)
      (fun id=>id ≤ F) T (headIds c.head) q.one (assignmentMachine q degree high left seed regs) := by
  rcases hc with ⟨h168,h178,h175,h177⟩
  have he (i : Fin 768) (hi : i ∈ ([67,145,146,147,148,149,150,151,159,340,341,342,343,359] : List (Fin 768))) := hf.empty i hi
  constructor
  · constructor
    · intro i hi
      have hh := he i (by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi ⊢; tauto)
      have hge : 56 ≤ i.val := by
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [assignmentMachine,machine,show ¬i.val < 56 by omega] using hh
    · exact ⟨by simpa [assignmentMachine,machine] using hf.headLength,
        by simpa [assignmentMachine,machine] using hf.bucketLength,
        by simpa [assignmentMachine,machine] using hf.supportLength⟩
  · rw [preparedAssignment_regs]
    have hleft : (Product.bytes left).length ≤ A :=
      (bytes_le_capacity Finset.univ q.u q.J left hl).trans hf.savedCapacity
    have hseed : (Product.bytes seed).length ≤ A :=
      (bytes_le_capacity Finset.univ q.u q.J seed hs).trans hf.savedCapacity
    have hengine : FactorReady.Input q S A (preparedAssignment q degree high left seed) := by
      rw [preparedAssignment_update]
      exact hf.engine.update_saved hAS hleft hseed
    refine ⟨hengine,?_,?_,?_⟩
    · simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine,hx,h178,h177]
    · simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine,hf.metadata702Bytes]
    · simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine,hf.metadata703Bytes]
  · simpa only [h175] using hf.idsBound
  · rw [←h175,←hf.idsBytes]
    exact hf.idsLength
  · simpa [assignmentMachine,machine,h175] using hf.idsBytes
  · simpa [assignmentMachine,machine] using hf.oneBytes
  · intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [assignmentMachine,machine,assignmentEnvironment,Product.working,Product.environment,
      Product.idle,Product.tapes,Normalize.bytes,
      Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary]
    all_goals exact hf.empty _ (by simp)
  · simpa [assignmentMachine,machine] using hf.ambientLength

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end

end OAI.Algorithms
