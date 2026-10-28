import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramInterface
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankCost

namespace OAI.Algorithms

/-! Discharge the fiber loop's callback by the concrete integer-entry machine.
All remaining assumptions describe its actual caches and numerical bounds. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

theorem data_low_frame (base : Data) (regs : Fin 16 → Bool)
    (queue column : List Bool) (acc next : WordPair)
    (i : Fin 256) (hi : i.val < 212) :
    (data base regs queue column acc next).stacks i=base.stacks i := by
  have h212 : i≠212 := by
    intro h
    have he : i.val=212 := congrArg Fin.val h
    omega
  have h213 : i≠213 := by
    intro h
    have he : i.val=213 := congrArg Fin.val h
    omega
  have h214 : i≠214 := by
    intro h
    have he : i.val=214 := congrArg Fin.val h
    omega
  have h253 : i≠253 := by
    intro h
    have he : i.val=253 := congrArg Fin.val h
    omega
  have h254 : i≠254 := by
    intro h
    have he : i.val=254 := congrArg Fin.val h
    omega
  have h255 : i≠255 := by
    intro h
    have he : i.val=255 := congrArg Fin.val h
    omega
  simp [data,bank,h212,h213,h214,h253,h254,h255]

theorem data_cached {r Q : ℕ} (base : Data) (c : LayoutProgram.Numerator.Saved)
    (t : Fin Q) (hc : LayoutProgram.EntryBank.CacheWords (r:=r) base c t)
    (regs : Fin 16 → Bool) (queue column : List Bool) (acc next : WordPair) :
    LayoutProgram.EntryBank.CacheWords (r:=r) (data base regs queue column acc next) c t := by
  constructor
  · simpa [data,bank] using hc.hp
  · simpa [data,bank] using hc.hn
  · simpa [data,bank] using hc.hw
  · simpa [data,bank] using hc.hpos
  · exact hc.hneg
  · simpa [data,bank] using hc.hr
  · simpa [data,bank] using hc.ha
  · simpa [data,bank] using hc.colors
  · simpa [data,bank] using hc.nodes
  · simpa [data,bank] using hc.node
  · simpa [data,bank] using hc.typeWidth

theorem finish_data (base : Data) (hwork : ∀ i : Fin 256, i.val < 200 → base.stacks i=[])
    (regs rf : Fin 16 → Bool) (queue column : List Bool) (acc result : WordPair) :
    LayoutProgram.EntryBank.finish (data base regs queue column acc ([],[])) rf result=
      data base rf queue column acc result := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i.val < 200
    · have h212 : i ≠ 212 := by intro h; have := congrArg Fin.val h; omega
      have h213 : i ≠ 213 := by intro h; have := congrArg Fin.val h; omega
      have h214 : i ≠ 214 := by intro h; have := congrArg Fin.val h; omega
      have h253 : i ≠ 253 := by intro h; have := congrArg Fin.val h; omega
      have h254 : i ≠ 254 := by intro h; have := congrArg Fin.val h; omega
      have h255 : i ≠ 255 := by intro h; have := congrArg Fin.val h; omega
      simpa [LayoutProgram.EntryBank.finish,data,bank,hi,h212,h213,h214,h253,h254,h255]
        using hwork i hi
    · by_cases h254 : i=254
      · subst i; simp [bank]
      by_cases h255 : i=255
      · subst i; simp [bank]
      simp [data,bank,hi,h254,h255]

def incidenceValue {r Q D : ℕ} (P : PackingData (Fin D) (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (row : Fin D) (i : ℕ) : ℤ :=
  if h : i < D then LayoutProgram.localEntry P A R t row ⟨i,h⟩ else 0

def nativeLength (R : ℕ) (width : List Bool) (power : WordPair) : ℕ :=
  LayoutProgram.EntryBank.integerLength R width.length (pairLength power) power.1.length

def nativeTime (r Q R : ℕ) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (S U : ℕ) : ℕ :=
  U+LayoutProgram.EntryBank.integerBudget r Q aWord.length R width.length
    (pairLength power) power.1.length+550*S+450*nativeLength R width power+1200

/-- The concrete metadata lookup and universal integer-entry program fulfills
the native fiber callback, even with arbitrary accumulator/queue contents.
`U` bounds actual metadata lookup time; it is not a program-service premise. -/
theorem entryAt {r Q D : ℕ} (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
    (base : Data) (S U : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) base
      (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hwork : ∀ i : Fin 256, i.val < 200 → base.stacks i=[])
    (hmeta : base.stacks 200=SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
    (hrow : base.stacks 252=List.replicate row.val true)
    (hsize : ∀ i : Fin 256, i.val < 212 → (base.stacks i).length ≤ S)
    (hrs : row.val ≤ S) (hcs : col.val ≤ S)
    (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
      (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hlookup : LayoutProgram.EntryBank.lookupBudget P row col ≤ U) :
    EntryAt LayoutProgram.EntryBank.command base (incidenceValue P aWord.length R t row)
      (nativeTime r Q R width power aWord S U) (nativeLength R width power)
      (LayoutProgram.constraintMassBound Q R) col.val := by
  intro regs queue acc
  let a := data base regs queue (unary col.val) acc ([],[])
  have hready : LayoutProgram.EntryBank.BaseReady a := by
    refine ⟨?_,by simp [a,data,bank],by simp [a,data,bank]⟩
    intro i hi
    rw [data_low_frame base regs queue (unary col.val) acc ([],[]) i (by omega)]
    exact hwork i hi
  obtain ⟨n,hn,rf,result,he,hv,hm,hl⟩ := LayoutProgram.EntryBank.command_eval
    P Hwords width power aWord R t row col a S
    (LayoutProgram.EntryBank.integerBudget r Q aWord.length R width.length (pairLength power) power.1.length)
    (nativeLength R width power) hlen hwords hvalues hp hpt hpos hwidth hAQ hQ
    (data_cached base _ t hc regs queue (unary col.val) acc ([],[])) hready
    (by simpa [a,data,bank] using hmeta) (by simpa [a,data,bank] using hrow)
    (by simp [a,data,bank,unary])
    (by
      intro i hi
      rw [data_low_frame base regs queue (unary col.val) acc ([],[]) i hi]
      exact hsize i hi) hrs hcs hmetadata
    (fun u y => LayoutProgram.EntryBank.integerBudget_bound _ _ _ _ _ t u y)
    (fun u y => LayoutProgram.EntryBank.integerLength_bound _ _ _ _ u y)
    (LayoutProgram.EntryBank.integerLength_one _ _ _ _)
  have hf := finish_data base hwork regs rf queue (unary col.val) acc result
  change LayoutProgram.EntryBank.finish a rf result=_ at hf
  rw [hf] at he
  refine ⟨n,?_,rf,result,he,?_,hl,hm⟩
  · unfold nativeTime
    omega
  · simpa [incidenceValue] using hv

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
