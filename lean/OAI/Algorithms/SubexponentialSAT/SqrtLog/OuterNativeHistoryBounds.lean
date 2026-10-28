import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQuerySize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeAcceptedLocalBounds

namespace OAI.Algorithms

/-! Literal selected-table growth along every exact greedy history. The
incumbent, queue, and untouched frame need no size hypothesis. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram LeafOuterProgram
open SubexpSetupStorage

 theorem iter_encoding_length_le (score : Records → List Bool → List Bool)
    (seed : List Bool) (rest initial : Records) (P t : ℕ)
    (hp : ∀ bits∈seed::rest,bits.length ≤ P) :
    (candidateEncoding (iter (payloadNext score seed rest) t initial)).length ≤
      (candidateEncoding initial).length+t*(2*P+2) := by
  induction t with
  | zero => simp [iter]
  | succ t ih =>
    rw [iter_succ_apply]
    have hb := hp _ (HashSelect.best_mem
      (fun bits => BinaryArithmetic.toNat
        (score (iter (payloadNext score seed rest) t initial) bits)) seed rest)
    simp only [payloadNext,candidateEncoding,List.length_cons,List.length_append,
      Encoding.length_frame,List.length_reverse]
    nlinarith

 theorem massInput_score_empty (current : Data) (regs : Fin 8 → Bool)
    (bits : List Bool) (best : Entry) (queue : List Bool) :
    (OuterQuery.massInput current regs bits best queue).stacks 769=[] := by
  exact state_stack selector.controller.trial.core _ regs ⟨bits,[]⟩ best queue 1

 theorem massInput_sources_le {a frame current : Data} {seed : List Bool}
    {rest initial : Records} {score : Records → List Bool → List Bool}
    {P K t W : ℕ} (ha : WordBound W a)
    (hi : a.stacks 777=candidateEncoding initial)
    (hf : Execution.Hash.ContextFrame selector a frame)
    (hr : ControllerReady selector.controller frame (seed::rest)
      (iter (payloadNext score seed rest) t initial) current)
    (ht : t ≤ K) (hp : ∀ bits∈seed::rest,bits.length ≤ P)
    (regs : Fin 8 → Bool) (bits : List Bool) (best : Entry) (queue : List Bool)
    (hb : bits∈seed::rest) :
    ∀ i, LeafOuterNative.MassSource i →
      ((OuterQuery.massInput current regs bits best queue).stacks i).length ≤
        W+K*(2*P+2)+P := by
  intro i his
  rcases his with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [OuterQuery.massInput_payload]
    exact (hp bits hb).trans (by omega)
  · rw [massInput_score_empty]
    simp
  · rw [OuterQuery.massInput_rows hr]
    have hg := iter_encoding_length_le score seed rest initial P t hp
    have h0 : (candidateEncoding initial).length ≤ W := hi ▸ ha 777
    have hm := Nat.mul_le_mul_right (2*P+2) ht
    omega
  all_goals
    rw [OuterQuery.massInput_outer hf hr regs bits best queue _ (Or.inr (by decide))]
    exact (ha _).trans (by omega)

 theorem final_sources_le {a b : Data} {seed : List Bool}
    {rest initial : Records} {score : Records → List Bool → List Bool}
    {P K W : ℕ} (ha : WordBound W a)
    (hi : a.stacks 777=candidateEncoding initial)
    (hf : Execution.Hash.ContextFrame selector a b)
    (hr : b.stacks 777=candidateEncoding (iter (payloadNext score seed rest) K initial))
    (hp : ∀ bits∈seed::rest,bits.length ≤ P) :
    ∀ i, LeafOuterNative.AcceptedSource i → (b.stacks i).length ≤ W+K*(2*P+2) := by
  intro i his
  rcases his with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [hr]
    have hg := iter_encoding_length_le score seed rest initial P K hp
    have h0 : (candidateEncoding initial).length ≤ W := hi ▸ ha 777
    omega
  all_goals
    rw [selected_outer_frame hf _ (by decide)]
    exact (ha _).trans (by omega)

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
