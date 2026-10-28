import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramSourceMeaning
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramTyped
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankRun

namespace OAI.Algorithms

/-! Discharge of the source callback by the actual packed-source dispatcher.
All premises below are stored-byte and cache invariants. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def nativeSourceBudget {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  800*(2*S+1)^2+SourceBank.uniformBudget p S+200*S+302

theorem lookupBudget_le {r Q D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D) (S : ℕ)
    (hm : (SelectorProgram.rawRecords (SourceBank.metadataRecords P)).length ≤ S)
    (hr : row.val ≤ S) (hc : col.val ≤ S) :
    SourceBank.lookupBudget P row col ≤ 800*(2*S+1)^2+1 := by
  unfold SourceBank.lookupBudget GlobalBasisMetadata.volume
  simp only [List.length_replicate]
  calc
    _ ≤ 400*(2*S+1)^2+400*(2*S+1)^2+1 := by gcongr <;> omega
    _ = _ := by ring

theorem native_relSourceSpec {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (hready : SourceBank.Ready p (⟨fun _ => false,base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts, base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320, (base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    RelSourceSpec packedSource base
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (nativeSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  intro i hi ids acc regs
  let col : Fin D := ⟨i,by omega⟩
  let a : Data := ⟨regs,Function.update (fiberState base ids acc) 305 (List.replicate i true)⟩
  let small := projectState id sourcePorts a
  have hs : small.stacks=Function.update (base ∘ sourcePorts) 305 (List.replicate i true) :=
    source_fiber_projection base ids acc i
  have ha : SourceBank.Ready p small := sourceReady_index_frame p _ small hready (by
    intro j hj hk
    simp [hs,hk])
  have hc : ∀ j∈SourceBank.cleanupPorts,small.stacks j=[] := by
    intro j hj
    have hne : j≠305 := by
      intro h
      subst j
      simp [SourceBank.cleanupPorts] at hj
    simpa [hs,Function.update_apply,hne,Function.comp_def] using hclean j hj
  have hss : ∀ j,(small.stacks j).length ≤ S := by
    intro j
    by_cases hj : j=305
    · subst j; simp only [hs,Function.update_self,List.length_replicate]; omega
    · simpa [hs,Function.update_apply,hj,Function.comp_def] using hsize j
  obtain ⟨n,hn,b,bytes,he,hb,hgen⟩ := SourceBank.command_eval p P row col small ha S hc
    (by simpa [hs,sourcePorts] using hmeta) (by simpa [hs,sourcePorts] using hrow)
    (by simp [hs,col]) hss hmetadata hQ hR hW hRW
  obtain ⟨e,hbytes,hm,hd,hl⟩ := hgen
  have hb' : b=(⟨b.regs,Function.update (a.stacks ∘ sourcePorts) 287 bytes⟩ : SourceBank.Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hb
  rw [hb'] at he
  obtain ⟨out,hout,host⟩ := packedSource_transport a n b.regs bytes he
  have ho : out=(⟨out.regs,Function.update a.stacks 287 bytes⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact host
  rw [ho,hbytes] at hout
  refine ⟨e,n+1,out.regs,⟨?_,?_⟩,?_,?_,hout⟩
  · simpa [packedSourceValue,col,show i < D by omega] using hm
  · simpa only [hbytes] using hl
  · simpa only [hbytes] using hl
  · have hml : (SelectorProgram.rawRecords (SourceBank.metadataRecords P)).length ≤ S := by
      simpa [sourcePorts,hmeta] using hsize 306
    have hrl : row.val ≤ S := by simpa [sourcePorts,hrow] using hsize 304
    have hcl : col.val ≤ S := by dsimp [col]; omega
    have hbnd := lookupBudget_le P row col S hml hrl hcl
    unfold nativeSourceBudget
    omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
