import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthResources

namespace OAI.Algorithms

/-! The complete produced setup-width bound, with original masked input
padding separate from the ordinary resource dimension. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram ProducedQueryResources

 theorem sum_le_product (W V k : ℕ) : W+V+k+2 ≤ (k+2)*(W+1)*(V+1) := by
  nlinarith [Nat.zero_le (W*V),Nat.zero_le (k*W),Nat.zero_le (k*V),Nat.zero_le (k*W*V)]

 theorem incoming_width_fixed (k : ℕ) : ∃ C d : ℕ, ∀ (q : LeafQueryFrontend.Query)
    (occurrence qi : ℕ) (a : Data) (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k a hg W V L), q.Valid → q.Ready a →
    (∀i,(a.stacks i).length ≤ W) → 2 ≤ ambient q → SmallInputs q k (ambient q) →
    V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    incomingWidth p ≤ C*(W+1)^d*((resources q k occurrence qi hg p.firstWord p.remainingWords).bits+1)^d := by
  obtain ⟨C,d,h⟩ := incoming_width_resources
  refine ⟨C*(k+2)^d,d,?_⟩
  intro q occurrence qi a hg W V L p hv hr hw hn hs hV hL
  apply (h q k occurrence qi a hg W V L p hv hr hw hn hs hV hL).trans
  calc
    _ ≤ C*((k+2)*(W+1)*((resources q k occurrence qi hg p.firstWord p.remainingWords).bits+1))^d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (sum_le_product W _ k) _)
    _ = _ := by simp only [mul_pow]; ring

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
