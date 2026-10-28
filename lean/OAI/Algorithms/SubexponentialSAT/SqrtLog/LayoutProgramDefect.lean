import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramMagnitudeOffset

namespace OAI.Algorithms

/-! Physical clearing-defect entries from the actual signed numerator pair.
A diagonal entry is D−(P−N), an off-diagonal entry is −(P−N). The numerator
and cached denominator remain intact; the result is a fresh signed pair.
The diagonal flag is a runtime bit, supplied by the type equality scan. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Defect

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

abbrev Data := State 8 10

def addPorts : SubexponentialSAT.ArithmeticCalls.Ports 10 where
  left := 1
  right := 2
  out := 3
  work := ⟨![5,6,7,8,9], by decide⟩
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by decide
  work_ne_right := by decide
  work_ne_out := by decide

abbrev command : Cmd 8 10 :=
  .seq (SubexponentialSAT.ArithmeticCalls.copyAt 0 4 5)
    (.ite 7 (SubexponentialSAT.ArithmeticCalls.addAt addPorts) (SubexponentialSAT.ArithmeticCalls.copyAt 1 3 5))

def Ready (d : Data) : Prop := ∀ j : Fin 10, 3 ≤ j.val → d.stacks j = []
def output (d : Data) (positive negative : List Bool) : Fin 10 → List Bool :=
  Function.update (Function.update d.stacks 4 negative) 3 positive

def budget (d : Data) : ℕ :=
  7*(d.stacks 0).length + 100*((d.stacks 1).length+(d.stacks 2).length+1)^2+12

theorem command_eval (d : Data) (hd : Ready d) :
    ∃ t ≤ budget d, ∃ rf pos neg,
      Eval command t d ⟨rf,output d pos neg⟩ ∧
      (BinaryArithmetic.toNat pos : ℤ) - BinaryArithmetic.toNat neg =
        (if d.regs 7 then (BinaryArithmetic.toNat (d.stacks 2) : ℤ) else 0) -
          ((BinaryArithmetic.toNat (d.stacks 0) : ℤ)-BinaryArithmetic.toNat (d.stacks 1)) ∧
      BinaryArithmetic.toNat pos + BinaryArithmetic.toNat neg = BinaryArithmetic.toNat (d.stacks 0)+BinaryArithmetic.toNat (d.stacks 1)+
        (if d.regs 7 then BinaryArithmetic.toNat (d.stacks 2) else 0) ∧
      pos.length+neg.length ≤
        (d.stacks 0).length+(d.stacks 1).length+(d.stacks 2).length+1 := by
  let mid := SubexponentialSAT.ArithmeticCalls.afterCopy 0 4 d
  have hc := SubexponentialSAT.ArithmeticCalls.copyAt_eval 0 4 5 d
    (by decide) (by decide) (by decide) (hd 4 (by decide)) (hd 5 (by decide))
  have hm7 : mid.regs 7 = d.regs 7 := by simp [mid,SubexponentialSAT.ArithmeticCalls.afterCopy,readRegs]
  cases hg : d.regs 7 with
  | false =>
    have hp := SubexponentialSAT.ArithmeticCalls.copyAt_eval 1 3 5 mid
      (by decide) (by decide) (by decide)
      (by simpa [mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hd 3 (by decide))
      (by simpa [mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hd 5 (by decide))
    have he := hc.seq (Eval.ite_false (yes := SubexponentialSAT.ArithmeticCalls.addAt addPorts) (hm7.trans hg) hp)
    refine ⟨7*(d.stacks 0).length+5+(7*(mid.stacks 1).length+5+1),?_,
      (SubexponentialSAT.ArithmeticCalls.afterCopy 1 3 mid).regs,d.stacks 1,d.stacks 0,?_,?_,?_,?_⟩
    · simp only [mid,SubexponentialSAT.ArithmeticCalls.afterCopy,Function.update_of_ne (by decide : (1:Fin 10) ≠ 4),budget]
      nlinarith [Nat.zero_le (d.stacks 1).length, Nat.zero_le (d.stacks 2).length,
        sq_nonneg ((d.stacks 1).length+(d.stacks 2).length : ℤ)]
    · simpa [command,mid,SubexponentialSAT.ArithmeticCalls.afterCopy,output] using he
    · simp []
    · simp [Nat.add_comm]
    · omega
  | true =>
    have hv : SubexponentialSAT.ArithmeticCalls.Valid addPorts mid := by
      constructor
      · simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hd 3 (by decide)
      · intro j
        fin_cases j <;> simp [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] <;> apply hd <;> decide
    obtain ⟨ta,rf,pos,ha,hval,hlen,htime⟩ := SubexponentialSAT.ArithmeticCalls.addAt_eval addPorts mid hv
    have hval' : BinaryArithmetic.toNat pos = BinaryArithmetic.toNat (d.stacks 1)+BinaryArithmetic.toNat (d.stacks 2) := by
      simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hval
    have hlen' : pos.length ≤ (d.stacks 1).length+(d.stacks 2).length+1 := by
      simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hlen
    have ht' : ta ≤ 100*((d.stacks 1).length+(d.stacks 2).length+1)^2 := by
      simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using htime
    have he := hc.seq (Eval.ite_true (no := SubexponentialSAT.ArithmeticCalls.copyAt 1 3 5) (hm7.trans hg) ha)
    refine ⟨7*(d.stacks 0).length+5+(ta+1),by unfold budget; omega,
      rf,pos,d.stacks 0,?_,?_,?_,by omega⟩
    · simpa [command,mid,SubexponentialSAT.ArithmeticCalls.afterCopy,output,addPorts] using he
    · simp only [ite_true,hval',Nat.cast_add]
      ring
    · simp only [ite_true,hval']
      omega

/-- Noncanonical numerator components are bounded separately. The physical
transform only adds the denominator to that total on diagonal entries. -/
theorem result_mass_le (P N D p n Q R : ℕ)
    (hnum : P+N ≤ (8*Q)^(2*R)) (hden : D ≤ 2^(R-1)) (flag : Bool)
    (hresult : p+n = P+N+(if flag then D else 0)) :
    p+n ≤ constraintMassBound Q R := by
  cases flag <;> simp [constraintMassBound] at * <;> omega

end SubexponentialSAT.SqrtLog.LayoutProgram.Defect

end OAI.Algorithms
