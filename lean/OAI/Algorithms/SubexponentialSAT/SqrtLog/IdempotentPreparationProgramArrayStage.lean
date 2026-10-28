import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramArrays

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

abbrev arrayStage : Cmd 8 41 := .seq initialArray (.seq cloneInitial negativeOneArray)

def arrayStacks (s : Fin 41 → List Bool) (t : ℕ) : Fin 41 → List Bool :=
  let v := s 30 ++ s 31 ++ s 27 ++ Subexp.BlockCopyProgram.copies (3*t-3) (s 17)
  let m := s 28 ++ Subexp.BlockCopyProgram.copies (3*t-1) (s 17)
  Function.update (Function.update (Function.update (Function.update (Function.update s
    32 v) 33 v) 34 v) 35 v) 36 m

theorem arrayStage_eval (d : Data) (t B : ℕ) (ht : 0 < t)
    (hd : d.stacks 37 = List.replicate (3*t) true)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (h32 : d.stacks 32 = []) (h33 : d.stacks 33 = [])
    (h34 : d.stacks 34 = []) (h35 : d.stacks 35 = []) (h36 : d.stacks 36 = [])
    (hz : (d.stacks 17).length=B) (hu : (d.stacks 27).length=B)
    (hm : (d.stacks 28).length=B) (hx : (d.stacks 30).length=B)
    (hy : (d.stacks 31).length=B) :
    ∃ cost rf, cost ≤ 500*(3*t+1)*(B+1) ∧
      Eval arrayStage cost d ⟨rf,arrayStacks d.stacks t⟩ := by
  have hd3 : 3*t-3+3=3*t := by omega
  have hd1 : 3*t-1+1=3*t := by omega
  obtain ⟨na,ra,hna,ha⟩ := initialArray_eval d (3*t-3) (by simpa only [hd3] using hd) h1 h2 h32
  let a : Data := ⟨ra,Function.update d.stacks 32 (initialBits d (3*t-3))⟩
  obtain ⟨rb,hb⟩ := cloneInitial_eval a (by simp [a,h2]) (by simp [a,h33])
    (by simp [a,h34]) (by simp [a,h35])
  let b : Data := ⟨rb,Function.update (Function.update (Function.update a.stacks
    33 (a.stacks 32)) 34 (a.stacks 32)) 35 (a.stacks 32)⟩
  obtain ⟨rc,hc⟩ := negativeOneArray_eval b (3*t-1)
    (by simpa [b,a,hd1] using hd) (by simp [b,a,h1]) (by simp [b,a,h2]) (by simp [b,a,h36])
  have he := ha.seq (hb.seq hc)
  have hlen : (a.stacks 32).length = 3*t*B := by
    simp only [a,Function.update_same,initialBits,List.length_append,
      Subexp.BlockCopyProgram.copies_length,hx,hy,hu,hz]
    calc
      _ = ((3*t-3)+3)*B := by ring
      _ = _ := by rw [hd3]
  refine ⟨na+((21*(a.stacks 32).length+15)+
    (7*(3*t-1+1)+5+1+((3*t-1)*(7*(b.stacks 17).length+7)+6)+
      (7*(b.stacks 28).length+5))),rc,?_,?_⟩
  · rw [hna,hlen]
    simp only [b,a,Function.update_of_ne (by decide : (17:Fin 41)≠35),
      Function.update_of_ne (by decide : (17:Fin 41)≠34),
      Function.update_of_ne (by decide : (17:Fin 41)≠33),
      Function.update_of_ne (by decide : (17:Fin 41)≠32),
      Function.update_of_ne (by decide : (28:Fin 41)≠35),
      Function.update_of_ne (by decide : (28:Fin 41)≠34),
      Function.update_of_ne (by decide : (28:Fin 41)≠33),
      Function.update_of_ne (by decide : (28:Fin 41)≠32),hz,hu,hm,hx,hy,hd1,hd3]
    nlinarith [Nat.mul_le_mul_right (7*B+7) (Nat.sub_le (3*t) 3),
      Nat.mul_le_mul_right (7*B+7) (Nat.sub_le (3*t) 1)]
  · simpa [arrayStage,arrayStacks,b,a,initialBits] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
