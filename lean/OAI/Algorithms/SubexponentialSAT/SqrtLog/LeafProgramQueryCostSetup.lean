import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidth
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostPadding

namespace OAI.Algorithms

/-! A produced ordinary cap pays for all setup words and products of ordinary
parameters. Its polynomial constants are fixed before the raw query. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram ProducedQueryResources

 noncomputable def ordinaryCap {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (occurrence qi : ℕ) : ℕ :=
  100*(Width.incomingWidth p+(resources q k occurrence qi hg p.firstWord p.remainingWords).bits+2)^4

 theorem enlarged_bound (I W V C d : ℕ)
    (hi : I ≤ C*(W+1)^d*(V+1)^d) :
    100*(I+V+2)^4 ≤ 100*(C+2)^4*(W+1)^(4*(d+1))*(V+1)^(4*(d+1)) := by
  have hw : 1 ≤ (W+1)^(d+1) := Nat.one_le_pow _ _ (by omega)
  have hv : V+1 ≤ (V+1)^(d+1) := Nat.le_self_pow (by omega) _
  have hwd : (W+1)^d ≤ (W+1)^(d+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hvd : (V+1)^d ≤ (V+1)^(d+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hi' := hi.trans (Nat.mul_le_mul (Nat.mul_le_mul_left C hwd) hvd)
  have hV : V+1 ≤ (W+1)^(d+1)*(V+1)^(d+1) := by
    exact hv.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((V+1)^(d+1)) hw)
  have hs : I+V+2 ≤ (C+2)*(W+1)^(d+1)*(V+1)^(d+1) := by nlinarith
  calc
    _ ≤ 100*((C+2)*(W+1)^(d+1)*(V+1)^(d+1))^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4)
    _ = _ := by simp only [mul_pow,←pow_mul]; ring

 theorem ordinaryCap_fixed (k : ℕ) : ∃ C d : ℕ, ∀ (q : LeafQueryFrontend.Query)
    (occurrence qi : ℕ) (a : Data) (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k a hg W V L), q.Valid → q.Ready a →
    (∀i,(a.stacks i).length ≤ W) → 2 ≤ ambient q → SmallInputs q k (ambient q) →
    V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    ordinaryCap p occurrence qi ≤ C*(W+1)^d*
      ((resources q k occurrence qi hg p.firstWord p.remainingWords).bits+1)^d := by
  obtain ⟨C,d,h⟩ := Width.incoming_width_fixed k
  refine ⟨100*(C+2)^4,4*(d+1),?_⟩
  intro q occurrence qi a hg W V L p hv hr hw hn hs hV hL
  exact enlarged_bound _ W _ C d (h q occurrence qi a hg W V L p hv hr hw hn hs hV hL)

 theorem incoming_le_ordinary {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (occurrence qi : ℕ) : Width.incomingWidth p ≤ ordinaryCap p occurrence qi := by
  unfold ordinaryCap
  have hp := Nat.le_self_pow (by decide : 4≠0) (Width.incomingWidth p+
    (resources q k occurrence qi hg p.firstWord p.remainingWords).bits+2)
  omega

 theorem setup_le_ordinary {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (occurrence qi : ℕ) :
    W+p.frontSteps+p.packingSteps+p.arithmeticSteps+prepareCost p.out ≤ ordinaryCap p occurrence qi := by
  apply le_trans _ (incoming_le_ordinary p occurrence qi)
  unfold Width.incomingWidth
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
