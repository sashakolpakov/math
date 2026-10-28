import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameInput

namespace OAI.Algorithms

/-! Concrete pre-state invariants for source dispatch. Metadata lookup and
whole-store comparisons preserve these low-bank arithmetic inputs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram

def lowStore (a : Data) : Fin 256 → List Bool :=
  (projectState id vectorPorts a).stacks

def InputFields {r Q : ℕ} (a : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) : Prop :=
  ∀ i : Fin 64, i≠23 → i≠24 →
    lowStore a (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i

theorem lowStore_metadata (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (rf : Fin 16 → Bool) : lowStore (⟨rf,metadataStacks a mr mc⟩ : Data)=lowStore a := by
  funext i
  have hb : (vectorPorts i).val < 256 := i.isLt
  have hn (j : Fin 320) (hj : 256 ≤ j.val) : vectorPorts i≠j := by
    intro h; have := congrArg Fin.val h; omega
  simp [lowStore,projectState,metadataStacks,
    hn 288 (by decide),hn 289 (by decide),hn 290 (by decide),
    hn 291 (by decide),hn 292 (by decide),hn 293 (by decide)]

theorem inputFields_frame {r Q : ℕ} (a b : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (h : InputFields a c start u y)
    (hf : lowStore b=lowStore a) : InputFields b c start u y := by
  intro i hi hj
  rw [hf]
  exact h i hi hj

theorem inputFields_metadata {r Q : ℕ} (a : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (mr mc : GlobalBasisMetadata.Metadata) (rf : Fin 16 → Bool)
    (h : InputFields a c start u y) :
    InputFields (⟨rf,metadataStacks a mr mc⟩ : Data) c start u y :=
  inputFields_frame a _ c start u y h (lowStore_metadata a mr mc rf)

theorem inputFields_store_frame {r Q : ℕ} (a b : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (h : InputFields a c start u y)
    (hf : b.stacks=a.stacks) : InputFields b c start u y :=
  inputFields_frame a b c start u y h (by simp [lowStore,projectState,hf])

theorem stageTypes_lowStore (a : Data) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (j : Fin 256) (hj23 : j≠23) (hj24 : j≠24) :
    lowStore (Staging.result 0 1 stageTypesOps a) j=lowStore a j := by
  have hn23 : vectorPorts j≠23 := by
    intro h; apply hj23; apply vectorPorts_inj; exact h
  have hn24 : vectorPorts j≠24 := by
    intro h; apply hj24; apply vectorPorts_inj; exact h
  simp [lowStore,projectState,stageTypes_stacks a h23 h24,hn23,hn24]

theorem inputFields_stage {r Q : ℕ} (a : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (h : InputFields a c start u y)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (hu : a.stacks 289=CollisionProgram.encodeType u)
    (hy : a.stacks 292=CollisionProgram.encodeType y) :
    ∀ i : Fin 64,
      lowStore (Staging.result 0 1 stageTypesOps a) (LayoutSourceValuesProgram.Native.numeratorPorts i)=
        (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i := by
  intro i
  by_cases hi23 : i=23
  · subst i
    simp [lowStore,projectState,stageTypes_stacks a h23 h24,vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,hu]
  by_cases hi24 : i=24
  · subst i
    simp [lowStore,projectState,stageTypes_stacks a h23 h24,vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,hy]
  have hn23 : LayoutSourceValuesProgram.Native.numeratorPorts i≠23 := by
    intro hh; apply hi23
    apply LayoutSourceValuesProgram.Native.numeratorPorts_injective
    exact hh
  have hn24 : LayoutSourceValuesProgram.Native.numeratorPorts i≠24 := by
    intro hh; apply hi24
    apply LayoutSourceValuesProgram.Native.numeratorPorts_injective
    exact hh
  rw [stageTypes_lowStore a h23 h24 _ hn23 hn24]
  exact h i hi23 hi24

theorem cachedReady_stage (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (a : Data)
    (h : CachedReady t model M cache zero one minusOne (lowStore a))
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    CachedReady t model M cache zero one minusOne (lowStore (Staging.result 0 1 stageTypesOps a)) := by
  apply LayoutSourceValuesProgram.Native.cachedReady_frame t model M cache zero one minusOne
    (lowStore a) _ h
  intro i hi _ _
  apply stageTypes_lowStore a h23 h24
  · intro he; subst i; norm_num at hi
  · intro he; subst i; norm_num at hi

theorem cachedReady_metadata (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (a : Data)
    (mr mc : GlobalBasisMetadata.Metadata) (rf : Fin 16 → Bool)
    (h : CachedReady t model M cache zero one minusOne (lowStore a)) :
    CachedReady t model M cache zero one minusOne (lowStore (⟨rf,metadataStacks a mr mc⟩ : Data)) := by
  rw [lowStore_metadata]
  exact h

theorem cachedReady_store_frame (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (a b : Data)
    (h : CachedReady t model M cache zero one minusOne (lowStore a))
    (hf : b.stacks=a.stacks) : CachedReady t model M cache zero one minusOne (lowStore b) := by
  simpa [lowStore,projectState,hf] using h

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
