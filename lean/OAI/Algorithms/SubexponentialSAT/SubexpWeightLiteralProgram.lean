import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWeightBitProgram
import OAI.Algorithms.SubexponentialSAT.SubexpWeightLiteralBase

namespace OAI.Algorithms

/-!
# Weight records to a raw constant-polynomial literal

The modulus supplied to this service is the lifted base-ring modulus, such as
`p^(D+1)`.  Coordinate addition in Fp and canonical lifting of its result occur
before its weight records are prepared.  This program executes multiplication,
quartic padding, key construction, and raw-record emission on actual words.
-/

namespace SubexponentialSAT.SubexpWeightLiteralProgram

open BitProgram StructuredCalls
open SubexpWeightBitProgram (WeightRecord)

def weightPorts : Fin 12 → Fin 24 := Fin.castAdd 12

theorem weightPorts_injective : Function.Injective weightPorts := Fin.castAdd_injective 12 12

def weight : Code :=
  .call (ProgramLinking.liftProgram SubexpWeightBitProgram.weightProgram id weightPorts)

def command : Code := .seq weight (.seq marshal (.seq prepare emit))
def program := StructuredCalls.compiled command 11 15

theorem weight_eval (rs : List WeightRecord) (r : Fin 8 → Bool)
    (initial modulus suffix shape : Word) (B D I : ℕ)
    (ha : initial.length = B) (hb : ∀ x ∈ rs, x.base.length = B)
    (hmLength : modulus.length ≤ B+1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2^B) :
    ∃ n rf output, n ≤ SubexpWeightBitProgram.scanSteps B rs + 2 ∧
      Eval weight n
        (state r initial modulus (SubexpWeightBitProgram.encodeRecords rs ++ suffix) shape D I [])
        (state rf output modulus suffix shape D I []) ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) *
          SubexpWeightBitProgram.recordsValue (BinaryArithmetic.toNat modulus) rs := by
  let a : SubexpWeightBitProgram.Data :=
    ⟨r,SubexpWeightBitProgram.weightStacks initial modulus [] []
      (SubexpWeightBitProgram.encodeRecords rs ++ suffix)⟩
  obtain ⟨b,output,⟨n,hn,ht⟩,hs,hbLength,hvalue⟩ :=
    SubexpWeightBitProgram.weight_execute rs a initial modulus suffix B rfl ha hb hmLength hm hcapacity
  have beq : b = ⟨b.regs,SubexpWeightBitProgram.weightStacks output modulus [] [] suffix⟩ := by
    cases b
    simp_all
  rw [beq] at ht
  let d := state r initial modulus (SubexpWeightBitProgram.encodeRecords rs ++ suffix) shape D I []
  have h := eval_call_lifted SubexpWeightBitProgram.weightProgram id weightPorts d
    Function.injective_id weightPorts_injective ht
  have hstart : embedState id weightPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id weightPorts_injective
    · intros; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hend : embedState id weightPorts d
      ⟨b.regs,SubexpWeightBitProgram.weightStacks output modulus [] [] suffix⟩ =
      state b.regs output modulus suffix shape D I [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id weightPorts_injective
    · intros; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h11 : i ≠ 11 := fun h => hi ⟨11,h.symm⟩
      fin_cases i <;> first | rfl | contradiction
  rw [hstart,hend] at h
  exact ⟨n,b.regs,output,hn,h,hbLength,hvalue⟩

theorem program_execute (rs : List WeightRecord) (r : Fin 8 → Bool)
    (initial modulus suffix shape : Word) (B D : ℕ)
    (ha : initial.length = B) (hshape : shape.length = B)
    (hb : ∀ x ∈ rs, x.base.length = B)
    (hmLength : modulus.length ≤ B+1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2^B) :
    ∃ rf output, RunsIn program
      (SubexpWeightBitProgram.scanSteps B rs + 2 + overhead D B)
      ((state r initial modulus (SubexpWeightBitProgram.encodeRecords rs ++ suffix)
        shape D (SubexpSymbolicCost.indexBits D) []).withPC (some program.entry))
      ((state rf [] modulus suffix shape D (SubexpSymbolicCost.indexBits D)
        (SubexpScalarLiteralProgram.rawLiteral D (SubexpQuarticMarshal.marshalBits output shape))).withPC none) ∧
      output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) *
          SubexpWeightBitProgram.recordsValue (BinaryArithmetic.toNat modulus) rs := by
  obtain ⟨n,r1,output,hn,hw,hlen,hvalue⟩ := weight_eval rs r initial modulus suffix shape B D
    (SubexpSymbolicCost.indexBits D) ha hb hmLength hm hcapacity
  obtain ⟨r2,hm⟩ := marshal_eval r1 output modulus suffix shape D (SubexpSymbolicCost.indexBits D)
  have hp := prepare_eval r2 (SubexpQuarticMarshal.marshalBits output shape) modulus suffix
    shape D (SubexpSymbolicCost.indexBits D)
  obtain ⟨r3,he⟩ := emit_eval r2 (SubexpQuarticMarshal.marshalBits output shape) modulus suffix shape D
  have h := Eval.seq hw (Eval.seq hm (Eval.seq hp he))
  have ht := StructuredCalls.compiled_halt_trace h 11 15
  refine ⟨r3,output,⟨_,?_,ht⟩,hlen,hvalue⟩
  simp only [SubexpRawArgumentService.cost,SubexpQuarticMarshal.marshalBits,
    List.length_append,List.length_replicate,hlen,hshape]
  unfold overhead
  omega

end SubexponentialSAT.SubexpWeightLiteralProgram

end OAI.Algorithms
