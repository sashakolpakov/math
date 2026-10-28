import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramPrecision
import OAI.Algorithms.SubexponentialSAT.CounterConversions

namespace OAI.Algorithms

/-! A fixed native producer for the score width. The binary ambient and modulus
are read and preserved; their computed precision is expanded to a unary word.
No precision-sized input word is supplied for free. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative.Precision
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

abbrev Data := State 8 10
def registers : Fin 3 → Fin 8 := Fin.castAdd 5
def stackMap : Fin 3 → Fin 10 := ![2,8,9]
abbrev expand : Cmd 8 10 := liftCommand CounterConversions.unaryCmd 0 1 registers stackMap

abbrev command : Cmd 8 10 := .seq precisionCommand expand

def budget (ambient modulus : List Bool) : ℕ :=
  let L := ambient.length+modulus.length+3
  let p := precision (BinaryArithmetic.toNat ambient) (BinaryArithmetic.toNat modulus)
  1000*L^2+2*p+(p+1)*(16*L+16)+2*L+7

theorem expand_eval (a : Data) (h8 : a.stacks 8=[]) (h9 : a.stacks 9=[]) :
    ∃ t b, t ≤ CounterConversions.coreBound (a.stacks 2)+1 ∧ Eval expand t a b ∧
      b.stacks 2=[] ∧ b.stacks 8=List.replicate (CounterPrograms.value (a.stacks 2)) true ∧
      b.stacks 9=[] ∧
      (∀ i : Fin 10, i≠2 → i≠8 → i≠9 → b.stacks i=a.stacks i) := by
  let d := projectState registers stackMap a
  obtain ⟨t,he,ht⟩ := CounterConversions.unary_correct d h9
  let z := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks 2)) true)
  have he' : Eval CounterConversions.unaryCmd t d z := by
    simpa only [d,z,projectState,Function.comp_apply,stackMap,Matrix.cons_val_zero,
      Matrix.cons_val_one,h8,List.append_nil] using he
  let b := embedState registers stackMap a z
  refine ⟨t+1,b,Nat.add_le_add_right ht 1,
    eval_liftCommand_from_state _ _ _ _ _ _ (Fin.castAdd_injective 3 5) (by decide) he',
    ?_,?_,?_,?_⟩
  · exact embedState_stack _ _ _ _ (by decide) 0
  · exact embedState_stack _ _ _ _ (by decide) 1
  · exact embedState_stack _ _ _ _ (by decide) 2
  · intro i h2 h8 h9
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    fin_cases j
    · exact h2 hj.symm
    · exact h8 hj.symm
    · exact h9 hj.symm

theorem command_eval (a : Data) (ha : precisionReady a)
    (hm : BinaryArithmetic.toNat (a.stacks 1)≠0) :
    ∃ t b, t ≤ budget (a.stacks 0) (a.stacks 1) ∧ Eval command t a b ∧
      b.stacks 0=a.stacks 0 ∧ b.stacks 1=a.stacks 1 ∧
      b.stacks 8=List.replicate (precision (BinaryArithmetic.toNat (a.stacks 0))
        (BinaryArithmetic.toNat (a.stacks 1))) true ∧
      (∀ i : Fin 10, i≠0 → i≠1 → i≠8 → b.stacks i=[]) := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := precisionCommand_eval a ha hm
  let c : Data := ⟨rf,Function.update a.stacks 2 word⟩
  have hc8 : c.stacks 8=[] := by simp [c,ha 8 (by decide)]
  have hc9 : c.stacks 9=[] := by simp [c,ha 9 (by decide)]
  obtain ⟨u,b,hu,heu,h2,h8,h9,hframe⟩ := expand_eval c hc8 hc9
  have hu' : u ≤ CounterConversions.coreBound word+1 := by simpa [c] using hu
  refine ⟨t+u,b,?_,he.seq heu,?_,?_,?_,?_⟩
  · unfold budget CounterConversions.coreBound at *
    rw [CounterPrograms.value_eq_toNat,hv] at hu'
    have hmul := Nat.mul_le_mul_left
      (precision (BinaryArithmetic.toNat (a.stacks 0)) (BinaryArithmetic.toNat (a.stacks 1))+1)
      (show 16*word.length+16 ≤ 16*((a.stacks 0).length+(a.stacks 1).length+3)+16 by omega)
    dsimp only
    omega
  · simpa [c] using hframe 0 (by decide) (by decide) (by decide)
  · simpa [c] using hframe 1 (by decide) (by decide) (by decide)
  · simpa [c,CounterPrograms.value_eq_toNat,hv] using h8
  · intro i h0 h1 h8'
    by_cases hi2 : i=2
    · subst i; exact h2
    by_cases hi9 : i=9
    · subst i; exact h9
    rw [hframe i hi2 h8' hi9]
    simp only [c,Function.update_of_ne hi2]
    exact ha i (by have := i.isLt; have := Fin.val_ne_of_ne h0; have := Fin.val_ne_of_ne h1; omega)

end SubexponentialSAT.SqrtLog.LeafOuterNative.Precision

end OAI.Algorithms
