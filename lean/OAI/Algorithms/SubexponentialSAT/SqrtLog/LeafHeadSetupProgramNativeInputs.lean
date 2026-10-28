import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramEntryFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramContract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramMagnitudeOffset

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

structure Inputs where
  n : ℕ
  N : ℕ
  r : ℕ
  Q : ℕ
  D : ℕ
  R : ℕ
  occurrence : ℕ
  packing : PackingData (Fin D) (UniversalType r Q 1)
  node : Fin Q
  plans : List (ℕ × ℕ)
  rows : List (List Bool)
  low : List Bool
  height : List Bool
  width : List Bool
  plans_length : plans.length=D
  rows_length : n+N ≤ rows.length
  rows_width : ∀ row∈rows,row.length=Q*r
  height_le : height.length ≤ Q
  width_boot : 1+2*height.length*R ≤ width.length
  width_node : Q+1 ≤ width.length
  fiber_degree : ∀ v < n,(LayoutOwnerFiberProgram.fiberIndices v 0 plans).length ≤ occurrence

def Inputs.records (s : Inputs) : List (List Bool) :=
  s.plans.map (fun p=>LayoutOwnerFiberProgram.pairPayload p.1 p.2)
def Inputs.metadata (s : Inputs) : List Bool :=
  SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords s.packing)
def Inputs.offset (s : Inputs) : ℕ := 2*s.occurrence*(8*s.Q)^(2*s.R)
def Inputs.power (s : Inputs) : WordPair := (LayoutProgram.IntegerCache.denominatorWord s.R,[])
def Inputs.size (s : Inputs) : ℕ :=
  s.n+s.D+s.metadata.length+(LayoutOwnerFiberProgram.stream s.plans).length+
    s.R*s.width.length+s.width.length+s.R+s.height.length+s.r+s.Q+s.Q*s.r+1

def Inputs.lookupTime (s : Inputs) : ℕ := 800*(s.metadata.length+s.D+1)^2+1
def Inputs.entryLength (s : Inputs) : ℕ := LayoutFiberSumProgram.nativeLength s.R s.width s.power
def Inputs.entryTime (s : Inputs) : ℕ :=
  LayoutFiberSumProgram.nativeTime s.r s.Q s.R s.width s.power s.height s.size s.lookupTime
def Inputs.columnLength (s : Inputs) : ℕ := s.D*(s.entryLength+2)
def Inputs.columnTime (s : Inputs) : ℕ :=
  1000*((LayoutOwnerFiberProgram.stream s.plans).length+s.n+1)^2+18*s.n+2*s.D+39+
    s.D*(s.entryTime+5*s.D+12+25000*((s.D+1)*(s.entryLength+2)+3)^2+9*(s.entryLength+2))
def Inputs.relation (s : Inputs) : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop :=
  BucketProgram.ProducedRank.FiberRel s.plans
    (BucketProgram.ProducedRank.entryNat s.packing s.height.length s.R s.node) s.offset

structure Ready (s : Inputs) (a : LeafHeadSetupProgram.Data) : Prop where
  ambient : a.stacks 128=unary s.n
  factors : a.stacks 129=unary s.N
  colors : a.stacks 130=unary s.r
  nodes : a.stacks 131=unary s.Q
  wordWidth : a.stacks 132=unary (s.Q*s.r)
  words : a.stacks 133=s.rows.flatten
  low : a.stacks 134=s.low
  metadata : a.stacks 135=s.metadata
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream s.plans
  order : a.stacks 138=unary s.R
  height : a.stacks 139=s.height
  width : a.stacks 140=s.width
  offset : BinaryArithmetic.toNat (a.stacks 141)=s.offset
  node : a.stacks 307=unary s.node.val
  tuples : a.stacks 660=[]
  marker : a.stacks 665=[]

@[simp] theorem Inputs.records_length (s : Inputs) : s.records.length=s.D := by
  simp [Inputs.records,s.plans_length]
theorem Inputs.records_bytes (s : Inputs) :
    SubexponentialSAT.Encoding.encodeList id s.records=LayoutOwnerFiberProgram.stream s.plans := by
  unfold Inputs.records LayoutOwnerFiberProgram.stream
  induction s.plans with
  | nil => rfl
  | cons p ps ih => simpa [SubexponentialSAT.Encoding.encodeList] using congrArg (fun x => true :: (SubexponentialSAT.Encoding.frame (LayoutOwnerFiberProgram.pairPayload p.1 p.2) ++ x)) ih

theorem Inputs.power_value (s : Inputs) : BinaryArithmetic.toNat s.power.1=2^(s.R-1) :=
  LayoutProgram.powerWord_value (s.R-1)
theorem Inputs.power_signed (s : Inputs) : pairValue s.power=(2:ℤ)^(s.R-1) := by
  simp [pairValue,RowSelectionProgram.signedValue,Inputs.power,LayoutProgram.IntegerCache.denominatorWord,
    LayoutProgram.powerWord_value]
theorem Inputs.power_total (s : Inputs) : LayoutProgramScalar.wordTotal s.power=2^(s.R-1) := by
  simpa [LayoutProgramScalar.wordTotal,pairTotal,Inputs.power,BinaryArithmetic.toNat] using s.power_value

theorem Inputs.metadata_bound (s : Inputs) (v : Fin s.D) :
    LayoutProgram.EntryBank.MetadataBound (PackingMetadata.value s.packing CollisionProgram.encodeType v) s.size := by
  have hinj : Function.Injective (fun v : Fin s.D=>List.replicate v.val true) := by
    intro x y h; apply Fin.ext; simpa using congrArg List.length h
  have hlookup := PackingMetadata.lookup_eq s.packing (fun v=>List.replicate v.val true)
    CollisionProgram.encodeType hinj v
  have hp := GlobalBasisMetadata.payload_length_le _ _ _ hlookup
  change (PackingMetadata.value s.packing CollisionProgram.encodeType v).encode.length ≤ s.metadata.length at hp
  have hs : s.metadata.length ≤ s.size := by unfold Inputs.size; omega
  have hf : ∀ m : GlobalBasisMetadata.Metadata,
      m.block.length ≤ m.encode.length ∧ m.typeCode.length ≤ m.encode.length ∧ m.rank.length ≤ m.encode.length := by
    intro m; cases m <;>
      simp [GlobalBasisMetadata.Metadata.block,GlobalBasisMetadata.Metadata.typeCode,
        GlobalBasisMetadata.Metadata.rank,GlobalBasisMetadata.Metadata.encode,SubexponentialSAT.Encoding.length_frame] <;> omega
  exact ⟨(hf _).1.trans (hp.trans hs),(hf _).2.1.trans (hp.trans hs),(hf _).2.2.trans (hp.trans hs)⟩

theorem Inputs.lookup_bound (s : Inputs) (row col : Fin s.D) :
    LayoutProgram.EntryBank.lookupBudget s.packing row col ≤ s.lookupTime := by
  have hr : row.val ≤ s.D := row.isLt.le
  have hc : col.val ≤ s.D := col.isLt.le
  unfold LayoutProgram.EntryBank.lookupBudget GlobalBasisMetadata.volume Inputs.lookupTime
  change 400*(s.metadata.length+(List.replicate row.val true).length+1)^2+
    400*(s.metadata.length+(List.replicate col.val true).length+1)^2+1 ≤ _
  simp only [List.length_replicate]
  have h1 := Nat.pow_le_pow_left (show s.metadata.length+row.val+1 ≤ s.metadata.length+s.D+1 by omega) 2
  have h2 := Nat.pow_le_pow_left (show s.metadata.length+col.val+1 ≤ s.metadata.length+s.D+1 by omega) 2
  omega

theorem Inputs.column_time_bound (s : Inputs) (v : ℕ) (hv : v < s.n) :
    LayoutFiberSumProgram.budget s.entryTime s.entryLength s.plans.length v s.plans ≤ s.columnTime := by
  have hf := LayoutOwnerFiberProgram.fiberIndices_length_le v 0 s.plans
  rw [s.plans_length] at hf
  have hq := LayoutOwnerFiberProgram.budget_polynomial v s.plans
  have hv' : v ≤ s.n := hv.le
  unfold LayoutFiberSumProgram.budget Inputs.columnTime
  dsimp only
  rw [s.plans_length]
  calc
    _ ≤ 1000*((LayoutOwnerFiberProgram.stream s.plans).length+v+1)^2+18*v+2*s.D+39+
        s.D*(s.entryTime+5*s.D+12+25000*((s.D+1)*(s.entryLength+2)+3)^2+9*(s.entryLength+2)) := by gcongr
    _ ≤ _ := by gcongr

theorem Inputs.column_length_bound (s : Inputs) (v : ℕ) :
    (LayoutOwnerFiberProgram.fiberIndices v 0 s.plans).length*(s.entryLength+2) ≤ s.columnLength := by
  unfold Inputs.columnLength
  apply Nat.mul_le_mul_right
  simpa only [s.plans_length] using LayoutOwnerFiberProgram.fiberIndices_length_le v 0 s.plans

theorem Inputs.column_mass_bound (s : Inputs) (v : ℕ) (hv : v < s.n) :
    (LayoutOwnerFiberProgram.fiberIndices v 0 s.plans).length*
      LayoutProgram.constraintMassBound s.Q s.R ≤ s.offset := by
  have hQ : 1 ≤ s.Q := by have := s.node.isLt; omega
  calc
    _ ≤ s.occurrence*(2*(8*s.Q)^(2*s.R)) :=
      Nat.mul_le_mul (s.fiber_degree v hv) (LayoutProgram.constraintMassBound_le _ _ hQ)
    _ = _ := by unfold Inputs.offset; ring

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
