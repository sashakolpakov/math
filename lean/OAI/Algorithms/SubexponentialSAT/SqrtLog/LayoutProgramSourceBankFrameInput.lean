import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrame

namespace OAI.Algorithms

/-! The actual scalar producer's numerator input already contains precisely
all low type-extractor inputs. No second pre-expanded input is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem numerator_mismatch_ready {r Q : ℕ} (a : Data) (c : Numerator.Saved)
    (start : Fin Q) (u y : UniversalType r Q 1) (bits : List Bool) (rf : Fin 16 → Bool)
    (hinput : ∀ i : Fin 64,
      (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
        (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i) :
    UniversalRowMismatchTypes.InputReady (0:Fin 1) u y
      (projectState lowRegs mismatchPorts (vectorState a rf bits)) := by
  intro j
  have hh := hinput (j.castAdd 35)
  fin_cases j <;>
    simpa [projectState,vectorPorts,LayoutSourceValuesProgram.Native.numeratorPorts,
      vectorState,mismatchPorts,UniversalRowMismatchTypes.inputStacks,
      Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,
      MatrixInputTypes.input,MatrixInputProgram.inputState] using hh

def nativePositions {r Q : ℕ} (u y : UniversalType r Q 1) : List ℕ :=
  MismatchPlanProgram.selectedPositions y.head (u.slot 0)

def nativeIndices {r Q : ℕ} (u y : UniversalType r Q 1) : List Bool :=
  ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords (nativePositions u y).reverse)

theorem nativeIndices_eq {r Q : ℕ} (u y : UniversalType r Q 1) :
    nativeIndices u y=UniversalRowTermProgram.indices (nativePositions u y) := by rfl

/-- Discharges the actual mismatch-trace premise of universal_cleanup_eval
from the same input invariant used by the native scalar-table program. -/
theorem native_mismatch_branch {r Q : ℕ} (a : Data) (c : Numerator.Saved)
    (start : Fin Q) (u y : UniversalType r Q 1) (bits : List Bool) (rf : Fin 16 → Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) (h71 : a.stacks 71=[])
    (hinput : ∀ i : Fin 64,
      (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
        (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i) :
    ∃ nm ≤ UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
        UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13,
      ∃ rm : Fin 16 → Bool, Eval mismatches nm (vectorState a rf bits)
        (branchState a rm bits (nativeIndices u y)) := by
  have hr := numerator_mismatch_ready a c start u y bits rf hinput
  have he : (vectorState a rf bits).stacks 71=[] := by
    simp [vectorState,stageTypes_stacks a h23 h24,h71]
  obtain ⟨nm,hnm,b,hb,hbs⟩ := mismatches_eval u y (vectorState a rf bits) hr he
  have heq : b=branchState a b.regs bits (nativeIndices u y) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [branchState,vectorState,nativeIndices,nativePositions] using hbs
  rw [heq] at hb
  exact ⟨nm,hnm,b.regs,hb⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
