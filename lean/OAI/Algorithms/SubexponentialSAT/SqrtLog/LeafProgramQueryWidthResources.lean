import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthStages
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceProduced

namespace OAI.Algorithms

/-! The actual finite maxima produced by Query.construct discharge all
intermediate setup caps. The bound keeps the original masked input W explicit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram CostAssembly.Polynomial
open ProducedQueryResources

 def upgradeScale (C d U : ℕ) := U+8*(U+1)+C*(8*(U+1)+1)^d+1
 theorem upgradeScale_ordinary (C d : ℕ) : Ordinary (upgradeScale C d) := by
  have h := ordinary_id
  have h8 := ordinary_mul (ordinary_const 8) (ordinary_add h (ordinary_const 1))
  unfold upgradeScale
  exact ordinary_add (ordinary_add (ordinary_add h h8)
    (ordinary_mul (ordinary_const C) (ordinary_pow (ordinary_add h8 (ordinary_const 1)) d))) (ordinary_const 1)

 theorem incoming_width_resources : ∃ C d : ℕ, ∀ (q : LeafQueryFrontend.Query)
    (k occurrence qi : ℕ) (a : Data) (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k a hg W V L), q.Valid → q.Ready a →
    (∀i,(a.stacks i).length ≤ W) → 2 ≤ ambient q → SmallInputs q k (ambient q) →
    V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    incomingWidth p ≤ C*(W+(resources q k occurrence qi hg p.firstWord p.remainingWords).bits+k+2)^d := by
  obtain ⟨cl,dl,hcl⟩ := model_lengths_polynomial
  obtain ⟨ca,da,hca⟩ := incoming_width_diagonal
  have hpoly : Ordinary (fun U=>ca*(upgradeScale cl dl U+1)^da) :=
    ordinary_mul (ordinary_const ca) (ordinary_pow
      (ordinary_add (upgradeScale_ordinary cl dl) (ordinary_const 1)) da)
  obtain ⟨C,d,hd⟩ := hpoly
  refine ⟨C,d,?_⟩
  intro q k occurrence qi a hg W V L p hv hr hw hn hsmall hV hL
  let res := resources q k occurrence qi hg p.firstWord p.remainingWords
  let U := W+res.bits+k+1
  let Z := upgradeScale cl dl U
  have hvalues : ∀i,(Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)).val i ≤ res.bits :=
    values_le_resources q k occurrence qi (ambient q) hn rfl hsmall hg p.firstWord p.remainingWords p.lengths
  have hVbits : V ≤ res.bits := by rw [hV]; exact modelValueCap_le _ _ hvalues
  have hm := model_values_le (q.input k) p.lengths res.bits hvalues
  have hnBits : ambient q ≤ res.bits :=
    (FactorResource.produced_dimensions_le q k occurrence qi hg p.firstWord p.remainingWords hn hsmall).1
  have hcap := capacity_le q k W a hr hw
  have hcapU : LeafScopeInputBounds.capacity q k ≤ 8*(U+1) := by dsimp [U]; omega
  have hlen := hcl q k hv p.lengths p.frontOutput.canonicalLengths
  have hLZ : L ≤ Z := by
    rw [hL]
    exact hlen.trans ((Nat.mul_le_mul_left cl (Nat.pow_le_pow_left (Nat.add_le_add_right hcapU 1) dl)).trans
      (by unfold Z upgradeScale; omega))
  have hUZ : U ≤ Z := by unfold Z upgradeScale; omega
  have hVZ : res.bits ≤ Z := (show res.bits ≤ U by dsimp [U]; omega).trans hUZ
  have hWZ : W ≤ Z := (show W ≤ U by dsimp [U]; omega).trans hUZ
  have hcZ : LeafScopeInputBounds.capacity q k ≤ Z := hcapU.trans (by unfold Z upgradeScale; omega)
  have hl := model_before_lengths_le (q.input k) p.lengths Z (by rw [←hL]; exact hLZ)
  have hbound := hca q k a hg W V L p Z hv hw hWZ (hVbits.trans hVZ) hLZ hcZ
    (fun i=>(hm i).trans hVZ) hl
  apply hbound.trans
  simpa only [Z,U,res,Nat.add_assoc,Nat.reduceAdd] using hd U

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
