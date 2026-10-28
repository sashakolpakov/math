import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyMerge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgramNative

namespace OAI.Algorithms

/-! Actual native coefficient construction followed by stream weighting. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def weightPorts : Fin 13 → Fin 48 := ![20,21,22,23,15,16,1,2,3,4,5,6,7]
theorem weightPorts_injective : Function.Injective weightPorts := by decide

abbrev weights : Cmd 16 48 :=
  liftCommand PackingWeightProgram.command 0 4 mergeRegisters weightPorts

def WeightReady (d : Data) : Prop :=
  ∀ j : Fin 13, 4 ≤ j.val → d.stacks (weightPorts j)=[]

def dataLength (d : Data) : ℕ := PackingWeightProgram.inputLength
  (projectState mergeRegisters weightPorts d)

def nativeScore (d : Data) (ci ch : ℕ) : ℕ :=
  reducedScore (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 20))
    (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 21))
    (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 22))
    (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 23)) ci ch

theorem weights_eval (d : Data) (h : WeightReady d) :
    ∃ t ≤ 500*(2*dataLength d+4)^2+1, ∃ e : Data,
      Eval weights t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 15)=
        (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 20))^2 *
          (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 21))^2 ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 16)=
        8*(SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 22))^2 *
          (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 23))^2 ∧
      (e.stacks 15).length ≤ 2*(d.stacks 20).length+2*(d.stacks 21).length+3 ∧
      (e.stacks 16).length ≤ 2*(d.stacks 22).length+2*(d.stacks 23).length+6 ∧
      (∀ j,j≠15→j≠16→e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,e,he,hi,hh,hli,hlh,hf,_⟩ := PackingWeightProgram.command_lifted
    mergeRegisters weightPorts mergeRegisters_injective weightPorts_injective d h
  refine ⟨t,ht,e,he,?_,?_,hli,hlh,hf⟩
  · simpa [PackingWeightProgram.incidence,projectState,weightPorts,mul_pow] using hi
  · simpa [PackingWeightProgram.head,projectState,weightPorts,mul_pow,Nat.mul_assoc] using hh

def inputPairScores (d : Data) (ps : List (ℕ × ℕ)) : Prop :=
  d.stacks 0=ProgramEncoding.encodeRecords (Zip.firstScores ps) ∧
  d.stacks 12=ProgramEncoding.encodeRecords (Zip.secondScores ps) ∧
  (∀ j : Fin 48, j ∈ ({1,2,3,4,5,6,7,13,14,15,16,17} : Finset (Fin 48)) → d.stacks j=[])

theorem weights_mergeInput (d e : Data) (ps : List (ℕ × ℕ))
    (h : inputPairScores d ps) (hf : ∀ j,j≠15→j≠16→e.stacks j=d.stacks j) :
    MergeInput (e.stacks 15) (e.stacks 16) ps e := by
  intro i
  rw [Zip.input_stacks]
  fin_cases i <;> simp [mergePorts,hf,h.1,h.2.1,h.2.2]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
