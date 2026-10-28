import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramPacked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramFamily

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem rowState_source_projection (base : Store) (j : ℕ) (remaining acc : List Bool) :
    rowState base j remaining acc ∘ sourcePorts=base ∘ sourcePorts := by
  funext i
  have hp : (sourcePorts i).val < 320 := i.isLt
  have h320 : sourcePorts i≠320 := by intro he; rw [he] at hp; norm_num at hp
  have h331 : sourcePorts i≠331 := by intro he; rw [he] at hp; norm_num at hp
  have h332 : sourcePorts i≠332 := by intro he; rw [he] at hp; norm_num at hp
  simp [rowState,h320,h331,h332]

theorem native_row_relSourceSpec {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (hready : SourceBank.Ready p (⟨fun _ => false,base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts,base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320,(base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
    (j : ℕ) (remaining acc : List Bool) :
    RelSourceSpec packedSource (rowState base j remaining acc)
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (nativeSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  have heq := rowState_source_projection base j remaining acc
  have he (i : Fin 320) : (rowState base j remaining acc) (sourcePorts i)=base (sourcePorts i) :=
    congrFun heq i
  exact native_relSourceSpec p P row _ I S hID hIS
    (hready.frame heq) (fun i hi => (he i).trans (hclean i hi))
    (by simpa [sourcePorts] using (he 306).trans hmeta)
    (by simpa [sourcePorts] using (he 304).trans hrow)
    (fun i => by rw [he]; exact hsize i) hmetadata hQ hR hW hRW

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
