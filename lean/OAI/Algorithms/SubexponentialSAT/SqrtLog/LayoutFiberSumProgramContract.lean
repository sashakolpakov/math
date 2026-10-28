import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankLiteral

namespace OAI.Algorithms

/-! The closed owner-fiber command realizes the literal matrix relation used
by the produced-head/rank join. Only actual cache data and numerical envelopes
remain as hypotheses; no per-entry machine contract is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

theorem matrix_cached {r Q : ℕ} (base : Fin 288 → List Bool)
    (c : LayoutProgram.Numerator.Saved) (t : Fin Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) (matrixBase base 0) c t)
    (j v : ℕ) :
    LayoutProgram.EntryBank.CacheWords (r:=r) (parked (matrixBase base j) v) c t := by
  constructor
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hp
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hn
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hw
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hpos
  · exact hc.hneg
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hr
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.ha
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.colors
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.nodes
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.node
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.typeWidth

theorem matrix_low_frame (base : Fin 288 → List Bool) (j v : ℕ)
    (i : Fin 256) (hi : i.val < 212) :
    (parked (matrixBase base j) v).stacks i=base (LayoutMatrixProgram.bankPort i) := by
  have h216 : i≠216 := by intro h; have hh : i.val=216 := congrArg Fin.val h; omega
  have h252 : i≠252 := by intro h; have hh : i.val=252 := congrArg Fin.val h; omega
  have h253 : i≠253 := by intro h; have hh : i.val=253 := congrArg Fin.val h; omega
  have h254 : i≠254 := by intro h; have hh : i.val=254 := congrArg Fin.val h; omega
  have h255 : i≠255 := by intro h; have hh : i.val=255 := congrArg Fin.val h; omega
  simp [parked,matrixBase,LayoutMatrixProgram.entryState,h216,h252,h253,h254,h255]

theorem nativeEntryContract {r Q D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q)
    (base : Fin 288 → List Bool) (ps : List (ℕ × ℕ))
    (Valid : ℕ → ℕ → Prop) (S U H Tout Bout : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) (matrixBase base 0)
      (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hready : ∀ j v, Valid j v → Ready (matrixBase base j))
    (hmeta : base (LayoutMatrixProgram.bankPort 200)=
      SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
    (hsource : base (LayoutMatrixProgram.bankPort 201)=LayoutOwnerFiberProgram.stream ps)
    (hsize : ∀ i : Fin 256, i.val < 212 → (base (LayoutMatrixProgram.bankPort i)).length ≤ S)
    (hps : ps.length=D) (hDS : D ≤ S)
    (hvalid : ∀ j v, Valid j v → j < D)
    (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
      (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hlookup : ∀ row col : Fin D, LayoutProgram.EntryBank.lookupBudget P row col ≤ U)
    (htime : ∀ j v, Valid j v →
      budget (nativeTime r Q R width power aWord S U) (nativeLength R width power)
        ps.length v ps ≤ Tout)
    (hlength : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*(nativeLength R width power+2) ≤ Bout)
    (hmass : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*LayoutProgram.constraintMassBound Q R ≤ H) :
    LayoutMatrixProgram.EntryContract (command LayoutProgram.EntryBank.command) base Valid
      (BucketProgram.ProducedRank.FiberRel ps
        (BucketProgram.ProducedRank.entryNat P aWord.length R t) H) Tout Bout := by
  apply entryContract LayoutProgram.EntryBank.command base Valid _ ps
    (BucketProgram.ProducedRank.entryNat P aWord.length R t)
    (nativeTime r Q R width power aWord S U) (nativeLength R width power)
    (LayoutProgram.constraintMassBound Q R) Tout Bout hready hsource
    ?_ htime hlength ?_
  · intro j v hv i hi
    have hj : j < D := hvalid j v hv
    have hiD : i < D := by simpa only [hps] using LayoutOwnerFiberProgram.mem_fiberIndices_lt v ps hi
    let row : Fin D := ⟨j,hj⟩
    let col : Fin D := ⟨i,hiD⟩
    let b := parked (matrixBase base j) v
    have hb := hready j v hv
    have hwork : ∀ x : Fin 256, x.val < 200 → b.stacks x=[] := by
      intro x hx
      have hn : x≠216 := by intro h; have he : x.val=216 := congrArg Fin.val h; omega
      simpa [b,parked,Function.update_of_ne hn] using hb.1 x hx
    have he := entryAt P Hwords width power aWord R t row col b S U
      hlen hwords hvalues hp hpt hpos hwidth hAQ hQ
      (matrix_cached base _ t hc j v) hwork
      (by simpa [b,parked,matrixBase,LayoutMatrixProgram.entryState] using hmeta)
      (by simp [b,parked,matrixBase,LayoutMatrixProgram.entryState,row,unary])
      (by
        intro x hx
        rw [matrix_low_frame base j v x hx]
        exact hsize x hx)
      (by dsimp [row]; omega) (by dsimp [col]; omega) hmetadata (hlookup row col)
    have heq : incidenceValue P aWord.length R t row=
        BucketProgram.ProducedRank.entryNat P aWord.length R t j := by
      funext z
      simp [incidenceValue,BucketProgram.ProducedRank.entryNat,row,hj]
    rw [heq] at he
    exact he
  · intro j v hv result hvalue htotal
    exact ⟨hvalue,htotal.trans (hmass j v hv)⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
