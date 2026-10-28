import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNativePacking

namespace OAI.Algorithms

/-! Stage the actual selected words and owner plans for the native layout
suffix. The incidence dimension is converted from its actual binary master. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def dimensionPorts : Fin 14 ↪ Fin 64 :=
  ⟨![58,42,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩
def prepareCopies : List (Fin 64 × Fin 64) := [(61,25),(62,40),(53,41),(54,45)]
def prepareLiterals : Code := .seq (TupleProgram.pushConst 43 0 true)
  (TupleProgram.pushConst 44 0 false)
def prepareSuffix : Code := .seq (unaryCommand dimensionPorts)
  (.seq prepareLiterals (copyMany 52 prepareCopies))
def prepareBudget (outside : Store) :=
  LeafParametersProgram.Serialization.unaryCopyBound (outside 58)+1+4+
    7*((outside 61).length+(outside 62).length+(outside 53).length+(outside 54).length)+20

theorem prepareSuffix_eval (outside : Store) (regs : Fin 16 → Bool)
    (p : LayoutProgram.NativeFrontend.Params) (hdelta : p.Δ=1)
    (h52 : outside 52=[])
    (hD : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=p.D)
    (hwidth : outside 53=p.width)
    (halphabet : outside 54=ProgramEncoding.encodeRecords p.alphabet)
    (hplans : outside 61=p.planStream) (hwords : outside 62=p.rows.flatten) :
    ∃ t rf, t ≤ prepareBudget outside ∧ Eval prepareSuffix t
      (framed outside (⟨regs,fun _=>[]⟩ : Small))
      (framed outside (LayoutProgram.NativeFrontend.plansState p rf)) := by
  let a := framed outside (⟨regs,fun _=>[]⟩ : Small)
  obtain ⟨tu,ru,hu,htu⟩ := unaryCommand_eval dimensionPorts a
    (by simp [a,dimensionPorts,framed_stack])
    (by simp [a,dimensionPorts,framed_stack])
    (by simp [a,dimensionPorts,framed_stack])
    (by simp [a,dimensionPorts,framed_stack])
  let b : Local := ⟨ru,Function.update a.stacks 42 (List.replicate p.D true)⟩
  have hub : Eval (unaryCommand dimensionPorts) tu a b := by
    simpa [b,dimensionPorts,a,framed_stack,hD] using hu
  let c := TupleProgram.pushedState 44 0 false (TupleProgram.pushedState 43 0 true b)
  have hl : Eval prepareLiterals 4 b c :=
    (TupleProgram.pushConst_eval 43 0 true b).seq
      (TupleProgram.pushConst_eval 44 0 false (TupleProgram.pushedState 43 0 true b))
  have hc52 : c.stacks 52=[] := by
    simp [c,b,a,framed_stack,h52]
  have hp := copyMany_eval 52 prepareCopies c (by
    intro q hq; simp [prepareCopies] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> decide) hc52
  let e := copyManyState prepareCopies c
  have he : e=framed outside (LayoutProgram.NativeFrontend.plansState p e.regs) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [LayoutProgram.NativeFrontend.plansState]
    · funext i
      fin_cases i <;> simp [e,c,b,a,prepareCopies,copyManyState,copyState,StackRoutines.copyStacks,
        TupleProgram.pushedState,framed_stack,LayoutProgram.NativeFrontend.plansState,
        LayoutProgram.NativeFrontend.Params.input,LayoutProgram.NativeFrontend.Params.base,
        PackingFrontend.Params.input,PackingProgram.inputState,SubexpPlanAlphabetBase.scopeBytes,
        Encoding.encodeList,hdelta,hwidth,halphabet,hplans,hwords]
  have hcost : copyManyCost prepareCopies c =
      7*((outside 61).length+(outside 62).length+(outside 53).length+(outside 54).length)+20 := by
    simp [prepareCopies,copyManyCost,copyState,StackRoutines.copyStacks,c,b,a,
      TupleProgram.pushedState,framed_stack]
    omega
  have hall := hub.seq (hl.seq hp)
  change Eval prepareSuffix (tu+(4+copyManyCost prepareCopies c)) a e at hall
  rw [he] at hall
  refine ⟨tu+(4+copyManyCost prepareCopies c),e.regs,?_,hall⟩
  rw [hcost]
  have htu' : tu ≤ LeafParametersProgram.Serialization.unaryCopyBound (outside 58)+1 := by
    simpa [dimensionPorts,a,framed_stack] using htu
  dsimp [prepareBudget]
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
