import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceProduced

namespace OAI.Algorithms

/-! The ordinary cap dominates actual setup words and products of the produced
scalar parameters. Counts of high branches remain charged to assembled work. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram ProducedQueryResources

 theorem product_three_le (I V a b c : ℕ) (ha : a ≤ V) (hb : b ≤ V) (hc : c ≤ V) :
    a*b*c ≤ 100*(I+V+2)^4 := by
  have hV : V ≤ I+V+2 := by omega
  calc
    _ ≤ (I+V+2)*(I+V+2)*(I+V+2) := Nat.mul_le_mul (Nat.mul_le_mul (ha.trans hV) (hb.trans hV)) (hc.trans hV)
    _ = (I+V+2)^3 := by ring
    _ ≤ (I+V+2)^4 := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := by omega

 variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ}

 theorem produced_maxJet_le (p : Preparation q k a hg W V L) (occurrence qi : ℕ)
    (hn : 2 ≤ ambient q) (hs : SmallInputs q k (ambient q)) :
    (produce (q.input k)).J*((produce (q.input k)).d*
      SubexpLiftRing.baseWidth 3 (produce (q.input k)).t) ≤ ordinaryCap p occurrence qi := by
  obtain ⟨hambient,hB,hd,ht,hJ⟩ := FactorResource.produced_dimensions_le q k occurrence qi hg
    p.firstWord p.remainingWords hn hs
  simpa only [ordinaryCap,Nat.mul_assoc] using
    product_three_le (Width.incomingWidth p) _ _ _ _ hJ hd hB

 theorem output_width_le (p : Preparation q k a hg W V L) (occurrence qi : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,(p.out.stacks i).length ≤ ordinaryCap p occurrence qi := by
  intro i
  exact (p.output_width hw i).trans (by have := setup_le_ordinary p occurrence qi; omega)

 theorem prepared_width_le (p : Preparation q k a hg W V L) (occurrence qi : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,((prepared p.out).stacks i).length ≤ ordinaryCap p occurrence qi := by
  intro i
  have hi := eval_width (prepare_eval p.out)
    (W+p.frontSteps+p.packingSteps+p.arithmeticSteps) (p.output_width hw) i
  exact hi.trans (setup_le_ordinary p occurrence qi)

 theorem branches_le_assembled (p : Preparation q k a hg W V L) (occurrence qi : ℕ) :
    2^HighIncidenceProgram.Branches.trueCount (p.out.stacks 338) ≤
      CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords) := by
  rw [Width.output_mask]
  change 2^(resources q k occurrence qi hg p.firstWord p.remainingWords).branchVars ≤ _
  apply branches_le_work
  · change 0 < 2*ambient q*matrixHeight q k+1
    omega
  · exact make_heads_pos _ _ _ _ _ _ _ _ _
  · exact make_bits_pos _ _ _ _ _ _ _ _ _

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
