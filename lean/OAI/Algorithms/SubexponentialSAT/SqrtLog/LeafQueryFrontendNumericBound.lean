import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendNumericRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendGrowth

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def numericCost (ambient clauses : List Bool) (k free occ arity factors mass : ℕ) : ℕ :=
  7*ambient.length+5+7*clauses.length+5+2*k.bits.length+1+
    conversionCost free+conversionCost occ+conversionCost arity+conversionCost factors+conversionCost mass

/-- The concrete input bank admits an input-only uniform word-length model. -/
theorem numericStage_eval_bounded (a : Data) (ambient clauses : List Bool)
    (k free occ arity factors mass : ℕ)
    (ha : a.stacks 709=ambient) (hm : a.stacks 707=clauses)
    (hz : emptyRange a 340 417) (ht : a.stacks 679=[]) (ht' : a.stacks 647=[])
    (hfree : a.stacks 626=List.replicate free true)
    (hocc : a.stacks 627=List.replicate occ true)
    (harity : a.stacks 642=List.replicate arity true)
    (hfactors : a.stacks 613=List.replicate factors true)
    (hmass : a.stacks 628=List.replicate mass true) :
    ∃ n b l w, Eval (numericStage k) n a b ∧
      projectState r9 bank b=Execute.state (b.regs ∘ r9) w ∧
      Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w ∧
      n ≤ numericCost ambient clauses k free occ arity factors mass ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 417 ≤ i.val) →
        i≠626 → i≠627 → i≠642 → i≠613 → i≠628 → i≠647 → b.stacks i=a.stacks i) ∧
      l=(fun _ => numericCost ambient clauses k free occ arity factors mass) := by
  obtain ⟨n,b,l,w,he,hp,hs,hn,hf⟩ := numericStage_eval a ambient clauses k free occ arity factors mass
    ha hm hz ht ht' hfree hocc harity hfactors hmass
  refine ⟨n,b,fun _ => numericCost ambient clauses k free occ arity factors mass,w,he,hp,⟨hs.1,?_⟩,hn,hf,rfl⟩
  intro i
  by_cases hi : i.val < 8
  · have hv : b.stacks (bank (Bank.port i))=w i := by
      have h := congrFun (congrArg StructuredProgram.State.stacks hp) (Bank.port i)
      simpa [projectState,Execute.state,Bank.state,Bank.port] using h
    have hg := eval_length_le he (bank (Bank.port i))
    have hz' := hz (bank (Bank.port i)) (by dsimp [bank,block,Bank.port]; omega)
      (by dsimp [bank,block,Bank.port]; omega)
    rw [hz',List.length_nil,zero_add,hv] at hg
    simpa [numericCost, Layout.initialModel, hi, Nat.add_assoc] using hg.trans hn
  · simpa [Layout.initialModel,hi] using hs.2 i

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
