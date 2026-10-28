import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarInit

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms ModularArithmetic BinaryArithmetic

variable (t : ℕ)

def oneValue (shape : List Bool) (hs:shape.length=baseWidth 3 t) : Word (baseWidth 3 t) :=
  ⟨padTo shape [true],by simp [padTo_length,hs]⟩

def minusValue (M : SubexpPreparedQuartic.Modulus 3 t)
    (shape : List Bool) (hs:shape.length=baseWidth 3 t) : Word (baseWidth 3 t) :=
  ⟨padTo shape (CounterPrograms.ripple false M.bits),by simp [padTo_length,hs]⟩

def baseValues (M : SubexpPreparedQuartic.Modulus 3 t)
    (shape : List Bool) (hs:shape.length=baseWidth 3 t) : Values 3 t :=
  Function.update (Function.update (fun _=>zeroValue 3 t shape hs) 1 (oneValue t shape hs))
    9 (minusValue t M shape hs)

abbrev baseCommand : Cmd 8 41 :=
  .seq initializeAll (.seq (literal 18 [true]) (negativeOne 28))

theorem baseCommand_eval (M : SubexpPreparedQuartic.Modulus 3 t)
    (shape : List Bool) (hs:shape.length=baseWidth 3 t) (d:Data) (W:ℕ)
    (h:Rest d M.bits) (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W) :
    ∃ n e, Eval baseCommand n d e ∧ Encoded 3 t M (baseValues t M shape hs) e ∧
      Frame d e ∧ n ≤ 400*(baseWidth 3 t+W+1) := by
  obtain ⟨n0,d0,he0,hv0,h12',hf0,hn0⟩:=initializeAll_eval 3 t M shape hs d W h h12 hW hslots
  obtain ⟨n1,d1,he1,hes1,hn1⟩:=literal_eval d0 M.bits shape 18 [true] hv0.1 h12'
    (by decide) (by decide)
  have hu1:=encoded_update 3 t M (fun _=>zeroValue 3 t shape hs) d0 d1 1
    (oneValue t shape hs) hv0 hes1
  have h12'' : d1.stacks 12=shape := by rw [hes1]; simpa using h12'
  have hm : 0 < BinaryArithmetic.toNat M.bits := by rw [M.value]; positivity
  obtain ⟨n2,d2,he2,hes2,hn2⟩:=negativeOne_eval d1 M.bits shape 28 hu1.1.1 h12'' hm
    (by decide) (by decide)
  have hu2:=encoded_update 3 t M _ d1 d2 9 (minusValue t M shape hs) hu1.1 hes2
  refine ⟨n0+(n1+n2),d2,he0.seq (he1.seq he2),hu2.1,?_,?_⟩
  · intro j hj
    exact (hu2.2 j hj).trans ((hu1.2 j hj).trans (hf0 j hj))
  · have h18 : (d0.stacks 18).length=baseWidth 3 t := by
      have hh:=hv0.2 1
      simpa [port,zeroValue,padTo_length,hs] using congrArg List.length hh
    have h28 : (d1.stacks 28).length=baseWidth 3 t := by
      have hh:=hu1.1.2 9
      simpa [port,zeroValue,padTo_length,hs] using congrArg List.length hh
    have hm:=M.length_le
    simp only [List.length_cons,List.length_nil] at hn1
    rw [h18,hs] at hn1
    rw [h28,hs] at hn2
    rw [hs] at hn0
    omega

theorem zeroValue_nat (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    BinaryArithmetic.toNat (zeroValue 3 t shape hs).val=0 := by
  apply padTo_value_of_lt
  simp

theorem oneValue_nat (ht:0 < t) (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    BinaryArithmetic.toNat (oneValue t shape hs).val=1 := by
  have hb : 0 < shape.length := by rw [hs,RingProgram.ternary_baseWidth]; omega
  have hp : BinaryArithmetic.toNat [true] < 2^shape.length :=
    Nat.one_lt_pow (Nat.ne_of_gt hb) Nat.one_lt_two
  exact padTo_value_of_lt shape [true] hp

theorem minusValue_nat (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    BinaryArithmetic.toNat (minusValue t M shape hs).val=3^t-1 := by
  have hm:0 < CounterPrograms.value M.bits := by rw [CounterPrograms.value_eq_toNat,M.value]; positivity
  have hv : BinaryArithmetic.toNat (CounterPrograms.ripple false M.bits)=3^t-1 := by
    have hh:=CounterPrograms.value_decrement hm
    rw [CounterPrograms.value_eq_toNat,CounterPrograms.value_eq_toNat,M.value] at hh
    omega
  have hcap : BinaryArithmetic.toNat (CounterPrograms.ripple false M.bits) < 2^shape.length := by
    rw [hv,hs]
    have cap:=modulus_le_width 3 t
    have hp:0 < 3^t:=by positivity
    omega
  exact (padTo_value_of_lt shape _ hcap).trans hv

theorem baseValues_correct (ht:0 < t) (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    wordValue 3 t (baseValues t M shape hs 0)=0 ∧
    wordValue 3 t (baseValues t M shape hs 1)=1 ∧
    wordValue 3 t (baseValues t M shape hs 9) = -1 ∧
    (∀i,BinaryArithmetic.toNat (baseValues t M shape hs i).val < 3^t) := by
  have hz:=zeroValue_nat t shape hs
  have ho:=oneValue_nat t ht shape hs
  have hn:=minusValue_nat t M shape hs
  have hp:1 < 3^t:=by exact Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)
  have hm: ((3^t-1:ℕ):ZMod (3^t)) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3^t),Nat.cast_one,ZMod.natCast_self,zero_sub]
  constructor
  · simp [baseValues,wordValue,hz]
  constructor
  · simp [baseValues,wordValue,ho]
  constructor
  · simp [baseValues,wordValue,hn]
  · intro i
    by_cases h9:i=9
    · subst i; simp [baseValues,hn]
    · by_cases h1:i=1
      · subst i; simpa [baseValues,ho] using hp
      · simp [baseValues,h9,h1,hz]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
