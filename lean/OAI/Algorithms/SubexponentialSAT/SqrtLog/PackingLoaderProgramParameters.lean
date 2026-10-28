import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramFrame
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputState

namespace OAI.Algorithms

/-! Paid conversion of the actual binary radius and coordinate parameters. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def radiusPorts : Fin 14 ↪ Fin 64 :=
  ⟨![59,1,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩
def coordinatePorts : Fin 14 ↪ Fin 64 :=
  ⟨![55,2,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩
def parameters : Code := .seq (unaryCommand radiusPorts) (unaryCommand coordinatePorts)
def parameterBudget (outside : Store) :=
  LeafParametersProgram.Serialization.unaryCopyBound (outside 59)+1+
    (LeafParametersProgram.Serialization.unaryCopyBound (outside 55)+1)

theorem parameters_eval (outside : Store) (regs : Fin 16 → Bool)
    (n f : ℕ) (pairs : List Bool) :
    ∃ t rf, t ≤ parameterBudget outside ∧ Eval parameters t
      (framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState regs 0 0 0 n f pairs))
      (framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState rf
        (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
        (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) 0 n f pairs)) := by
  let a := framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState regs 0 0 0 n f pairs)
  obtain ⟨t1,r1,he1,ht1⟩ := unaryCommand_eval radiusPorts a
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
  let b := framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState r1
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 59)) 0 0 n f pairs)
  have hb : (⟨r1,Function.update a.stacks (radiusPorts 1)
      (List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (a.stacks (radiusPorts 0))) true)⟩ : Data)=b := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [b,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
    · funext i
      fin_cases i <;> simp [a,b,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
  rw [hb] at he1
  obtain ⟨t2,r2,he2,ht2⟩ := unaryCommand_eval coordinatePorts b
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
  let e := framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState r2
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) 0 n f pairs)
  have he : (⟨r2,Function.update b.stacks (coordinatePorts 1)
      (List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (b.stacks (coordinatePorts 0))) true)⟩ : Data)=e := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [e,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
    · funext i
      fin_cases i <;> simp [b,e,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
  rw [he] at he2
  refine ⟨t1+t2,r2,?_,he1.seq he2⟩
  simpa [parameterBudget,a,b,framed_stack,radiusPorts,coordinatePorts,
    SubexponentialSAT.Subexp.AssignmentInputProgram.inputState] using Nat.add_le_add ht1 ht2

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
