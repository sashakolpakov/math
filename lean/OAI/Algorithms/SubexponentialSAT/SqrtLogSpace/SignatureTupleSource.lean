import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- Native source data and the actual cache words produced by node bootstrap.
This record contains no evaluator, query service, or execution assumption. -/
structure ProducedSource where
  input : Native.Inputs
  source : Data
  ready : Native.Ready input source
  bound : ℕ
  bounded : WordBound bound source
  rows : input.rows.length=input.n+input.N
  owner : Fin input.D → Fin input.n
  plans : Fin input.D → ℕ × ℕ
  plans_eq : input.plans=List.ofFn plans
  owners_eq : ∀ i,(plans i).1=(owner i).val
  addressRegisters : Fin 3 → Bool
  dimensionRegisters : Fin 8 → Bool
  cacheRegisters : Fin 8 → Bool
  cacheWords : List (List Bool)
  cache : CacheCorrect input.height (unary input.R) input.width cacheWords

namespace ProducedSource

def base (s : ProducedSource) : ℕ := s.input.node.val*s.input.r

def headSize (s : ProducedSource) (depth : ℕ) : ℕ :=
  (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)).length

def key (s : ProducedSource) (depth : ℕ) : Fin (2^s.headSize depth) → Fin s.input.D → ℤ :=
  AttainedSignatures.integerKey (integerMatrix s.input s.owner (s.base+depth))

def masters (s : ProducedSource) : Data :=
  Native.start s.input s.source s.addressRegisters s.dimensionRegisters s.cacheRegisters s.cacheWords

theorem headSize_le (s : ProducedSource) (depth : ℕ) : s.headSize depth ≤ s.input.n :=
  Bounds.selectedHeads_length ..

theorem offset_value (s : ProducedSource) : BinaryArithmetic.toNat (s.source.stacks 141)=s.input.offset :=
  s.ready.offset

theorem source_offset (s : ProducedSource) (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    a.stacks 141=s.source.stacks 141 :=
  SignatureHeadLoader.native_offset_word s.input s.source s.addressRegisters s.dimensionRegisters
    s.cacheRegisters s.cacheWords _ hm

end ProducedSource


/-- The query snapshot contains every actual loader master. -/
theorem source_master_queryMaster (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i∈QueryTupleState.masterPorts := by
  simp only [SignatureHeadLoader.masters, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem source_frame_of_queryFrame (base : LeafHeadSetupProgram.Data)
    (a b : State 40 896)
    (ha : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : QueryTupleState.QueryMasterFrame a b) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  exact (hf.word (SignatureHeadLoader.lowStacks i) (source_master_queryMaster i hi)).trans
    (ha.stored i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
