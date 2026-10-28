import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpFactorProgram

namespace OAI.Algorithms

/-! Native integer-representative coefficient lifting. The only arithmetic
performed by the machine is the audited dynamic padding/clearing routine. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularRingPrograms

def constantVector (t d : ℕ) (c : ZMod 3) : RingProgram.Code (RingProgram.ScalarCode 3 t) (d+1) :=
  Fin.cases (RingProgram.liftCoefficientRun t c).1
    (fun _ => SubexponentialSAT.SubexpPreparedQuartic.zeroWord 3 t)

theorem flat_constantVector (t d : ℕ) (c : ZMod 3) :
    RingProgram.flat (constantVector t d c) =
      (RingProgram.liftCoefficientRun t c).1.val ++
        List.replicate (d*baseWidth 3 t) false := by
  simp [RingProgram.flat,constantVector,List.ofFn_succ,
    SubexponentialSAT.SubexpPreparedQuartic.zeroWord,List.flatten_replicate_replicate]

theorem zeros_value (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,bitVal,ih]

theorem constantVector_value (t d : ℕ) (ht : 0 < t) (c : ZMod 3) :
    BinaryArithmetic.toNat (RingProgram.flat (constantVector t d c)) = c.val := by
  rw [flat_constantVector,SubexponentialSAT.SubexpFactorProgram.toNat_append,zeros_value]
  simpa using RingProgram.liftCoefficientRun_value t ht c

theorem constantVector_decode (t d : ℕ) (ht : 0 < t) (a : RingModel.Data (d+1))
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (c : ZMod 3) :
    (RingProgram.modelRing t ht (Nat.succ_pos d) a M cache).decode
      (constantVector t d c) = LeafProgram.TernaryLift.coefficient a t c := by
  change (∑ i : Fin (d+1), SubexponentialSAT.LiftRing.of (a.F t)
    (wordValue 3 t (constantVector t d c i)) * RingBasis.basis (a.F t) i) = _
  rw [Fin.sum_univ_succ]
  simp [constantVector,RingProgram.liftCoefficientRun_correct t ht,
    SubexponentialSAT.SubexpPreparedQuartic.zeroWord_value,RingBasis.basis,
    LeafProgram.TernaryLift.coefficient]
  change (SubexponentialSAT.LiftRing.of (a.F t)) (c.val : ZMod (3^t)) = (c.val : a.O t)
  exact map_natCast _ _

theorem padTo_constantVector (t d : ℕ) (ht : 0 < t) (c : ZMod 3)
    (shape input : List Bool) (hshape : shape.length=(d+1)*baseWidth 3 t)
    (hinput : BinaryArithmetic.toNat input=c.val) :
    padTo shape input = RingProgram.flat (constantVector t d c) := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · simpa [hshape] using (padTo_length shape input)
  · rw [padTo_value_of_lt,constantVector_value t d ht c,hinput]
    rw [hinput,hshape]
    have hw : 2 ≤ baseWidth 3 t := by
      rw [RingProgram.ternary_baseWidth]
      omega
    have hW : 2 ≤ (d+1)*baseWidth 3 t := by nlinarith
    have hp := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hW
    have hc := c.val_lt
    norm_num at hp
    omega

/-- A single fixed program produces the whole flat extension-ring constant.
The runtime shape contains one bit per output bit, and is consumed. Long padded
input representations are cleared with their actual lengths charged. -/
theorem lift_runs (t d : ℕ) (ht : 0 < t) (c : ZMod 3)
    (shape input modulus : List Bool) (hshape : shape.length=(d+1)*baseWidth 3 t)
    (hinput : BinaryArithmetic.toNat input=c.val) (regs : Fin 8 → Bool) :
    ∃ finalRegs, RunsIn normalizeProgram (7*shape.length+2*input.length+9)
      ⟨some 0,regs,normalizationState input shape [] modulus⟩
      ⟨none,finalRegs,normalizationState
        (RingProgram.flat (constantVector t d c)) [] [] modulus⟩ := by
  obtain ⟨rf,hr⟩ := normalize_correct regs input shape modulus
  rw [padTo_constantVector t d ht c shape input hshape hinput] at hr
  exact ⟨rf,hr⟩

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
