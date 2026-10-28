import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative

namespace OAI.Algorithms

/-! Paid binary metadata for the integer entry cache. The centered interval
start on port46 is produced by `SubexpIntervalStartProgram.program`; its
semantic identification is `SubexpIntervalStart.value_eq_intervalStart`.
This stage preserves that word and the parameter table while forming Qr and
the sufficient scalar width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Inputs r18, Q21, R29 and A46. Outputs Qr47 and cache width50;
48 and49 are paid temporary product words. -/
def code : List Instr := [
  .clear 47, .mul 21 18 47 (by decide) (by decide),
  .clear 48, .mul 46 29 48 (by decide) (by decide),
  .clear 49, .add 48 48 49 (by decide) (by decide),
  .clear 50, .add 49 21 50 (by decide) (by decide), .addConst 50 1]

abbrev command : Cmd 8 77 := Circuit.program code

theorem admissible (m : Model) : AdmissibleCode code m := by
  simp [code,AdmissibleCode,Admissible,next,output,lengthBound]

theorem values (m : Model) :
    (result code m).val 47=m.val 21*m.val 18 ∧
    (result code m).val 50=1+2*m.val 46*m.val 29+m.val 21 := by
  simp [code,result,next,value,output]
  ring

theorem frame (m : Model) (a : Fin 64)
    (h47 : a≠47) (h48 : a≠48) (h49 : a≠49) (h50 : a≠50) :
    (result code m).val a=m.val a := by
  simp [code,result,next,value,output,h47,h48,h49,h50]

theorem command_eval (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ t rf w', Eval command t (Bank.state r w) (Bank.state rf w') ∧
      Shape (result code m) w' ∧ t ≤ budget code m :=
  Circuit.program_eval code m w r hs (admissible m)

theorem sufficient_width (A R Q : ℕ) :
    max (1+2*A*R) (Q+1) ≤ 1+2*A*R+Q := by omega

theorem scaleBound (m : Model) : ScaleBound 2 code m := by
  simp [ScaleBound,code,scale]

/-- A polynomial in actual padded input lengths pays every operation here. -/
theorem budget_polynomial (m : Model) (B : ℕ) (hB : 2 ≤ B)
    (hl : ∀ a, m.len a ≤ B) :
    budget code m ≤
      (code.length*polynomialCoefficient code.length)*B^(6^code.length) := by
  have hm := (budget_majorant code m B hl
    (scaleBound_mono 2 B hB code m (scaleBound m))).2
  have hp := iterMajorant_polynomial code.length B (by omega)
  calc
    _ ≤ code.length*iterMajorant code.length B := hm
    _ ≤ code.length*(polynomialCoefficient code.length*B^(6^code.length)) :=
      Nat.mul_le_mul_left _ hp
    _ = _ := (Nat.mul_assoc _ _ _).symm

def program := compiled command (Bank.port 18) (Bank.port 50)

theorem program_runs (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ rf w', RunsIn program (budget code m+1)
      ((Bank.state r w).withPC (some program.entry))
      ((Bank.state rf w').withPC none) ∧ Shape (result code m) w' := by
  obtain ⟨t,rf,w',he,hshape,ht⟩ := command_eval m w r hs
  exact ⟨rf,w',⟨t+1,Nat.add_le_add_right ht 1,
    compiled_halt_trace he (Bank.port 18) (Bank.port 50)⟩,hshape⟩

theorem program_primitive (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ rf w', Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(budget code m+1))
      (primitiveCfg program ((Bank.state r w).withPC (some program.entry)))
      (primitiveCfg program ((Bank.state rf w').withPC none)) ∧
      Shape (result code m) w' := by
  obtain ⟨rf,w',he,hshape⟩ := program_runs m w r hs
  exact ⟨rf,w',primitive_execution program he,hshape⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

end OAI.Algorithms
