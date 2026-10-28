import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramPackedModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramStaging

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def stagedSourceBudget {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  nativeSourceBudget p S+12*S+12

theorem staged_native_relSourceSpec {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (h335 : base 335=[]) (h336 : base 336=[])
    (hready : SourceBank.Ready p (⟨fun _ => false,clearedSourceStore base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts,base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320,(base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    RelSourceSpec stagedPackedSource base
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (stagedSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  have hp := stagedSourceStore_projection base
  have heq (j : Fin 320) : stagedSourceStore base (sourcePorts j)=clearedSourceStore base (sourcePorts j) :=
    congrFun hp j
  have hc : ∀ j∈SourceBank.cleanupPorts,stagedSourceStore base (sourcePorts j)=[] := by
    intro j hj
    rw [heq]
    simp only [clearedSourceStore,Function.update_apply]
    split_ifs <;> first | rfl | exact hclean j hj
  have hz : ∀ j : Fin 320,(stagedSourceStore base (sourcePorts j)).length ≤ S := by
    intro j
    rw [heq]
    simp only [clearedSourceStore,Function.update_apply]
    split_ifs <;> first | exact Nat.zero_le _ | exact hsize j
  have raw := native_relSourceSpec p P row (stagedSourceStore base) I S hID hIS
    (hready.frame hp) hc
    (by simpa [stagedSourceStore,clearedSourceStore] using hmeta)
    (by simpa [stagedSourceStore,clearedSourceStore] using hrow)
    hz hmetadata hQ hR hW hRW
  intro i hi ids acc regs
  let st := Function.update (fiberState base ids acc) 305 (List.replicate i true)
  obtain ⟨e,n,rf,hr,hn,he⟩ := stagedPackedSource_eval _
    (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
      (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S) i)
    (nativeSourceBudget p S) st
    (by simp [st,fiberState,h335]) (by simp [st,fiberState,h336]) (by
      intro rr
      obtain ⟨e,k,rr',hr,_,hk,he⟩ := raw i hi ids acc rr
      exact ⟨e,k,rr',hr,hk,by simpa only [st,stagedSourceStore_fiber] using he⟩) regs
  refine ⟨e,n,rf,hr,hr.2,?_,he⟩
  have h5 : (st 5).length ≤ S := by simpa [st,fiberState,sourcePorts] using hsize 5
  have h10 : (st 10).length ≤ S := by simpa [st,fiberState,sourcePorts] using hsize 10
  unfold stagedSourceBudget
  omega

theorem cleared_rowState_source_projection (base : Store) (j : ℕ) (remaining acc : List Bool) :
    clearedSourceStore (rowState base j remaining acc) ∘ sourcePorts=
      clearedSourceStore base ∘ sourcePorts := by
  funext i
  have h := congrFun (rowState_source_projection base j remaining acc) i
  simp only [Function.comp_def,clearedSourceStore,Function.update_apply]
  split_ifs <;> first | rfl | exact h

theorem staged_native_row_relSourceSpec {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (h335 : base 335=[]) (h336 : base 336=[])
    (hready : SourceBank.Ready p (⟨fun _ => false,clearedSourceStore base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts,base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320,(base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
    (j : ℕ) (remaining acc : List Bool) :
    RelSourceSpec stagedPackedSource (rowState base j remaining acc)
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (stagedSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  have heq := rowState_source_projection base j remaining acc
  have he (i : Fin 320) : (rowState base j remaining acc) (sourcePorts i)=base (sourcePorts i) :=
    congrFun heq i
  exact staged_native_relSourceSpec p P row _ I S hID hIS
    (by simp [rowState,h335]) (by simp [rowState,h336])
    (hready.frame (cleared_rowState_source_projection base j remaining acc))
    (fun i hi => (he i).trans (hclean i hi))
    (by simpa [sourcePorts] using (he 306).trans hmeta)
    (by simpa [sourcePorts] using (he 304).trans hrow)
    (fun i => by rw [he]; exact hsize i) hmetadata hQ hR hW hRW

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
