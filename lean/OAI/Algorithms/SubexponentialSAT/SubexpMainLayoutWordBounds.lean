import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

namespace OAI.Algorithms

/-!
# Selected word bounds for the complete layout program

Only ordinary layout storage and the persistent parameters, caches and
current leaf are selected. The pending leaf stream is not selected. Bounds
after a stage follow from its actual instruction trace.
-/

namespace SubexponentialSAT.SubexpMainLayoutWordBounds

open BitProgram StructuredCalls SubexpMainProgram SubexpMainInvariant
open scoped BigOperators

def RelevantPort (es : ℕ) (i : Fin (totalStacks es)) : Prop :=
  i.val < 672 ∨ ∃ j : Fin 32, i = persistent es j ∧
    (ParameterPort j ∨ CachePort j ∨ j = 9)

def RelevantWordBound {er es : ℕ} (W : ℕ) (a : MainState er es) : Prop :=
  ∀ i, RelevantPort es i → (a.stacks i).length ≤ W

theorem ordinary {er es W : ℕ} {a : MainState er es} (h : RelevantWordBound W a)
    (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 672) :
    (a.stacks (SubexpLayoutPorts.ordinary alloc i)).length ≤ W :=
  h _ (Or.inl i.isLt)

theorem parameter {er es W : ℕ} {a : MainState er es} (h : RelevantWordBound W a)
    (i : Fin 32) (hi : ParameterPort i) : (a.stacks (persistent es i)).length ≤ W :=
  h _ (Or.inr ⟨i, rfl, Or.inl hi⟩)

theorem cache {er es W : ℕ} {a : MainState er es} (h : RelevantWordBound W a)
    (i : Fin 32) (hi : CachePort i) : (a.stacks (persistent es i)).length ≤ W :=
  h _ (Or.inr ⟨i, rfl, Or.inr (Or.inl hi)⟩)

theorem leaf {er es W : ℕ} {a : MainState er es} (h : RelevantWordBound W a) :
    (a.stacks (persistent es 9)).length ≤ W :=
  h _ (Or.inr ⟨9, rfl, Or.inr (Or.inr rfl)⟩)

theorem mono {er es W V : ℕ} {a : MainState er es}
    (h : RelevantWordBound W a) (hWV : W ≤ V) : RelevantWordBound V a :=
  fun i hi => (h i hi).trans hWV

theorem after_eval {er es W t : ℕ} {a b : MainState er es} {cmd : MainCmd er es}
    (h : RelevantWordBound W a) (he : Eval cmd t a b) : RelevantWordBound (W + t) b := by
  intro i hi
  have hg := trace_selectedStackBits (compiled cmd i i) {i} (compiled_trace he i i)
  have hx : (b.stacks i).length ≤ (a.stacks i).length + t := by
    simpa only [selectedStackBits, Finset.sum_singleton, StructuredProgram.State.withPC] using hg
  exact hx.trans (Nat.add_le_add_right (h i hi) t)

theorem after_run {er es W T : ℕ} {a b : MainState er es} {cmd : MainCmd er es}
    (h : RelevantWordBound W a) (he : ∃ t ≤ T, Eval cmd t a b) : RelevantWordBound (W + T) b := by
  obtain ⟨t, ht, he⟩ := he
  exact mono (after_eval h he) (Nat.add_le_add_left ht W)

theorem sum_lengths {er es W s : ℕ} {a : MainState er es} (h : RelevantWordBound W a)
    (ports : Fin s → Fin (totalStacks es)) (hp : ∀ i, RelevantPort es (ports i)) :
    (∑ i, (a.stacks (ports i)).length) ≤ s * W := by
  calc
    _ ≤ ∑ _i : Fin s, W := Finset.sum_le_sum (fun i _ => h _ (hp i))
    _ = s * W := by simp

theorem list_lengths {er es W : ℕ} {a : MainState er es} (h : RelevantWordBound W a)
    (ports : List (Fin (totalStacks es))) (hp : ∀ i ∈ ports, RelevantPort es i) :
    (ports.map (fun i => (a.stacks i).length)).sum ≤ ports.length * W := by
  induction ports with
  | nil => simp
  | cons i is ih =>
      have hi := h i (hp i (by simp))
      have hs := ih (fun j hj => hp j (by simp [hj]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith only [hi, hs]

end SubexponentialSAT.SubexpMainLayoutWordBounds

end OAI.Algorithms
