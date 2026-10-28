import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmeticSearch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupCleanup

namespace OAI.Algorithms

/-! Actual finite square-root calls. Search is bounded by the runtime input
value, which is charged explicitly; arbitrary padding is charged separately. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open CounterPrograms (value)

abbrev SqrtData := StructuredProgram.State 8 15

abbrev sqrtLocal : Cmd 8 15 :=
  .seq (ArithmeticExpressionSupport.pushWord 1 [true])
    (.seq (ArithmeticCalls.copyAt 2 13 11)
      (.seq Setup.Search.command (Setup.Cleanup.clearMany [0,1,13])))

def SqrtLocalReady (d : SqrtData) : Prop :=
  ∀ i : Fin 15, i ≠ 2 → d.stacks i = []

theorem sqrtLocal_eval (d : SqrtData) (hd : SqrtLocalReady d) :
    ∃ t rf word,
      Eval sqrtLocal t d ⟨rf,Function.update d.stacks 12 word⟩ ∧
      value word = Nat.sqrt (value (d.stacks 2)) ∧
      word.length ≤ value (d.stacks 2) ∧
      t ≤ 200000*(value (d.stacks 2)+(d.stacks 2).length+2)^3 := by
  obtain ⟨r1,hpush⟩ := ArithmeticExpressionSupport.pushWord_eval (1 : Fin 15) [true] d
  let a : SqrtData := ⟨r1,Function.update d.stacks 1 [true]⟩
  have h1 : Eval (ArithmeticExpressionSupport.pushWord 1 [true]) 2 d a := by
    simpa [a,hd 1 (by decide)] using hpush
  have hcopy := ArithmeticCalls.copyAt_eval (2 : Fin 15) 13 11 a
    (by decide) (by decide) (by decide)
    (by simp [a,hd 13 (by decide)]) (by simp [a,hd 11 (by decide)])
  let b := ArithmeticCalls.afterCopy 2 13 a
  have hbs : b.stacks =
      Function.update (Function.update d.stacks 1 [true]) 13 (d.stacks 2) := by
    simp [b,ArithmeticCalls.afterCopy,a]
  have h2 : Eval (ArithmeticCalls.copyAt 2 13 11) (7*(d.stacks 2).length+5) a b := by
    simpa [a] using hcopy
  obtain ⟨ts,e,hs,hv,hl0,hl12,hl13,he14,hframe,hts⟩ := Search.command_eval b
    (by simp [hbs,CounterPrograms.value])
    (by simpa [hbs,Search.root,CounterPrograms.value] using Nat.sqrt_le_self (value (d.stacks 2)))
    (by simp [hbs,hd 0 (by decide)])
    (by simp [hbs,hd 12 (by decide)])
    (by simp [hbs,hd 14 (by decide)])
    (by
      intro i hi
      have h0 : Setup.Search.guardPorts i ≠ (1 : Fin 15) := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 1 at hv
        omega
      have h2 : Setup.Search.guardPorts i ≠ (2 : Fin 15) := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 2 at hv
        omega
      have h13 : Setup.Search.guardPorts i ≠ (13 : Fin 15) := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 13 at hv
        omega
      simp [hbs,h0,h13,hd _ h2])
  simp only [hbs,Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 15) ≠ 13),
    Function.update_of_ne (by decide : (2 : Fin 15) ≠ 13),
    Function.update_of_ne (by decide : (2 : Fin 15) ≠ 1)] at hv hl0 hl12 hl13 hts
  have he1 : e.stacks 1 = [true] := by
    rw [hframe 1 (by decide) (by decide) (by decide) (by decide)]
    simp [hbs]
  have he2 : e.stacks 2 = d.stacks 2 := by
    rw [hframe 2 (by decide) (by decide) (by decide) (by decide)]
    simp [hbs]
  let B := value (d.stacks 2)+(d.stacks 2).length+1
  have heB : ∀ i, (e.stacks i).length ≤ B := by
    intro i
    by_cases h0 : i=0
    · subst i; dsimp [B]; omega
    by_cases h12 : i=12
    · subst i; dsimp [B]; omega
    by_cases h13 : i=13
    · subst i; dsimp [B]; omega
    by_cases h14 : i=14
    · subst i; simp [he14,B]
    rw [hframe i h0 h12 h13 h14]
    by_cases h1 : i=1
    · subst i; simp [hbs,B]
    by_cases h2 : i=2
    · subst i
      simp [hbs,B]
      omega
    simp [hbs,h1,h13,hd i h2,B]
  obtain ⟨tc,f,hclean,hfs,htc⟩ := Setup.Cleanup.clearMany_eval [0,1,13] e B heB
  have hfinal : f.stacks = Function.update d.stacks 12 (e.stacks 12) := by
    funext i
    rw [hfs]
    by_cases h12 : i=12
    · subst i; simp
    by_cases hclear : i ∈ ([0,1,13] : List (Fin 15))
    · rw [ite_eq_left hclear,Function.update_of_ne h12]
      have hi2 : i ≠ 2 := by intro h; subst i; simp at hclear
      exact (hd i hi2).symm
    · rw [ite_eq_right hclear,Function.update_of_ne h12]
      by_cases h14 : i=14
      · subst i; rw [he14,hd 14 (by decide)]
      have h0 : i ≠ 0 := by intro h; subst i; simp at hclear
      have h1 : i ≠ 1 := by intro h; subst i; simp at hclear
      have h13 : i ≠ 13 := by intro h; subst i; simp at hclear
      rw [hframe i h0 h12 h13 h14]
      simp [hbs,h1,h13]
  have hf : f = (⟨f.regs,Function.update d.stacks 12 (e.stacks 12)⟩ : SqrtData) :=
    CounterForPrograms.data_ext rfl hfinal
  refine ⟨2+((7*(d.stacks 2).length+5)+(ts+tc)),f.regs,e.stacks 12,?_,?_,hl12,?_⟩
  · rw [← hf]
    exact h1.seq (h2.seq (hs.seq hclean))
  · simpa [Search.root,CounterPrograms.value] using hv
  · simp only [Setup.Search.iterationBound,hbs,Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 15) ≠ 13),
      Function.update_of_ne (by decide : (2 : Fin 15) ≠ 13),
      Function.update_of_ne (by decide : (2 : Fin 15) ≠ 1),List.length_cons,List.length_nil] at hts
    simp only [List.length_cons,List.length_nil] at htc
    let X := value (d.stacks 2)+(d.stacks 2).length+2
    have hx : 1 ≤ X := by dsimp [X]; omega
    have ha : value (d.stacks 2) ≤ X := by dsimp [X]; omega
    have hb : value (d.stacks 2)+1+(d.stacks 2).length+value (d.stacks 2)+2 ≤ 2*X := by
      dsimp [X]; omega
    have hc : value (d.stacks 2)+1 ≤ X := by dsimp [X]; omega
    have he : 16*(d.stacks 2).length+16 ≤ 16*X := by dsimp [X]; omega
    have hsq := Nat.pow_le_pow_left hb 2
    have hmul := Nat.mul_le_mul ha (Nat.mul_le_mul_left 20000 hsq)
    have hmul2 := Nat.mul_le_mul hc he
    have hx2 : X^2 ≤ X^3 := by
      calc
        X^2 = X^2*1 := by simp
        _ ≤ X^2*X := Nat.mul_le_mul_left _ hx
        _ = X^3 := by ring
    change _ ≤ 200000*X^3
    dsimp [B] at htc
    nlinarith

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
