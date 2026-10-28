import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram


/-- Native arithmetic produces actual words, with both value and physical
length guarantees. Internal powers are never supplied as advice. -/
theorem core_eval (regs : Regs) (B Q R : List Bool) :
    ∃ ticks rf a e p b out,
      Eval core ticks (bank regs (initial B Q R)) (bank rf (filled B Q R a e p b out)) ∧
      BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      out.length ≤ outputLength B Q R ∧
      (∀ i : Fin 15, i ∈ [3,4,5,6,7,8] →
        (filled B Q R a e p b out i).length ≤ width B Q R) ∧
      ticks ≤ coreBudget B Q R := by
  let w0 := initial B Q R
  obtain ⟨r1,h1⟩ := load_eval regs w0 3 two rfl
  let w1 := Function.update w0 3 two
  obtain ⟨r2,h2⟩ := load_eval r1 w1 4 eight (by simp [w1,w0,initial,inputWords])
  let w2 := Function.update w1 4 eight
  obtain ⟨t3,r3,a,h3,hva,hla,hta⟩ :=
    multiply_eval r2 w2 4 1 5 (by decide) (by decide) (by simp [w2,w1,w0,initial,inputWords])
  let w3 := Function.update w2 5 a
  obtain ⟨t4,r4,e,h4,hve,hle,hte⟩ :=
    multiply_eval r3 w3 3 2 6 (by decide) (by decide) (by simp [w3,w2,w1,w0,initial,inputWords])
  let w4 := Function.update w3 6 e
  obtain ⟨t5,r5,p,h5,hvp,hlp,htp⟩ :=
    power_eval r4 w4 5 6 7 (by decide) (by decide) (by simp [w4,w3,w2,w1,w0,initial,inputWords])
  let w5 := Function.update w4 7 p
  obtain ⟨t6,r6,b,h6,hvb,hlb,htb⟩ :=
    multiply_eval r5 w5 3 0 8 (by decide) (by decide) (by simp [w5,w4,w3,w2,w1,w0,initial,inputWords])
  let w6 := Function.update w5 8 b
  obtain ⟨t7,r7,out,h7,hvo,hlo,hto⟩ :=
    multiply_eval r6 w6 8 7 9 (by decide) (by decide) (by simp [w6,w5,w4,w3,w2,w1,w0,initial,inputWords])
  have hva' : BinaryArithmetic.toNat a=8*BinaryArithmetic.toNat Q := by simpa [w2,w1,w0,initial,inputWords] using hva
  have hve' : BinaryArithmetic.toNat e=2*BinaryArithmetic.toNat R := by simpa [w3,w2,w1,w0,initial,inputWords] using hve
  have hvp' : BinaryArithmetic.toNat p=(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) := by simpa [w4,w3,hva',hve'] using hvp
  have hvb' : BinaryArithmetic.toNat b=2*BinaryArithmetic.toNat B := by simpa [w5,w4,w3,w2,w1,w0,initial,inputWords] using hvb
  have hvo' : BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) := by
    simpa [w6,w5,hvb',hvp'] using hvo
  have hla' : a.length ≤ Q.length+5 := by
    have h : a.length ≤ 4+Q.length+1 := by simpa [w2,w1,w0,initial,inputWords] using hla
    omega
  have hle' : e.length ≤ R.length+3 := by
    have h : e.length ≤ 2+R.length+1 := by simpa [w3,w2,w1,w0,initial,inputWords] using hle
    omega
  have hlp' : p.length ≤ 1+2*BinaryArithmetic.toNat R*a.length := by simpa [w4,w3,hve'] using hlp
  have hlb' : b.length ≤ B.length+3 := by
    have h : b.length ≤ 2+B.length+1 := by simpa [w5,w4,w3,w2,w1,w0,initial,inputWords] using hlb
    omega
  have hlo' : out.length ≤ b.length+p.length+1 := by simpa [w6,w5] using hlo
  have hlpQ : p.length ≤ 1+2*BinaryArithmetic.toNat R*(Q.length+5) :=
    hlp'.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hla') 1)
  have hlout : out.length ≤ outputLength B Q R := by unfold outputLength; omega
  let L := sourceWidth B Q R
  let E := 2*BinaryArithmetic.toNat R
  let H := width B Q R
  have hH : 1 ≤ H := width_pos B Q R
  have hLH : L+1 ≤ H := sourceWidth_le_width B Q R
  have hL : 10 ≤ L := by dsimp [L,sourceWidth]; omega
  have haL : a.length ≤ L := by dsimp [L,sourceWidth]; omega
  have heL : e.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hbL : b.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hQL : Q.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hRL : R.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hBL : B.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hpH : p.length ≤ H := by
    calc
      _ ≤ 1+E*L := hlp'.trans (Nat.add_le_add_left (Nat.mul_le_mul_left E haL) 1)
      _ ≤ H := by
        change 1+E*L ≤ (E+1)*(L+1)
        simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
        omega
  have haH : a.length ≤ H := by omega
  have heH : e.length ≤ H := by omega
  have hbH : b.length ≤ H := by omega
  have ta : t3 ≤ 900*H^2 := hta.trans (arithmetic_cost_le _ _ H
    (by simp [w2,w1]; omega) (by simp [w2,w1,w0,initial,inputWords]; omega) hH)
  have te : t4 ≤ 900*H^2 := hte.trans (arithmetic_cost_le _ _ H
    (by simp [w3,w2,w1]; omega) (by simp [w3,w2,w1,w0,initial,inputWords]; omega) hH)
  have tb : t6 ≤ 900*H^2 := htb.trans (arithmetic_cost_le _ _ H
    (by simp [w5,w4,w3,w2,w1]; omega) (by simp [w5,w4,w3,w2,w1,w0,initial,inputWords]; omega) hH)
  have tout : t7 ≤ 900*H^2 := hto.trans (arithmetic_cost_le _ _ H
    (by simpa [w6] using hbH) (by simpa [w6,w5] using hpH) hH)
  have tp : t5 ≤ 200*H^2 := by
    have ht : t5 ≤ PowerPrograms.runtimeBound a e+9*e.length+8 := by simpa [w4,w3] using htp
    exact ht.trans (power_cost_le a e L E haL heL hve')
  have hall := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  refine ⟨_,r7,a,e,p,b,out,hall,hvo',hlout,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [filled,loaded] <;> omega
  · have hs : 1 ≤ H^2 := by nlinarith only [hH]
    change 2*two.length+(2*eight.length+(t3+(t4+(t5+(t6+t7))))) ≤ 4000*H^2
    simp only [two_length,eight_length]
    omega

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
