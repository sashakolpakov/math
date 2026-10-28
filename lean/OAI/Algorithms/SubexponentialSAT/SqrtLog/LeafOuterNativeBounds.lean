import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMassFrame

namespace OAI.Algorithms

/-! A polynomial outer envelope with a linear sum of native query runtimes.
In particular the expensive query time is never raised to a power. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram SubexpSetupStorage LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def overhead (L m p W : ℕ) : ℕ :=
  (68*L+66)+
  (32*(m+1)*(L+1)+m*(12*m+32)+9)+
  (4+m*(22*(m*(m+W+1))+26))+
  (1000*(2*L+3)^2+2*p+(p+1)*(16*(2*L+3)+16)+2*(2*L+3)+8)+
  (14*p+2*(m*(W+1))+15)+
  (2*L+7*p+8+1536*(3*L+p+2)+2348)

private theorem sum_map_le {α : Type*} (xs : List α) (f : α → ℕ) (M : ℕ)
    (h : ∀ x∈xs, f x ≤ M) : (xs.map f).sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hh := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

theorem trial_wordBound (a : Data) (L : ℕ) (ha : WordBound L a) :
    WordBound (3*L+2) (trialStaged a) := by
  have hf := routes_wordBound masterRoutes a L ha
  change WordBound L (finalStaged a) at hf
  intro i
  by_cases h1 : i=701
  · subst i
    rw [trialStaged,prefixed_rows]
    have hsrc := hf 768
    have hdst := hf 701
    simp only [List.length_cons,List.length_append,Encoding.length_frame,List.length_reverse]
    omega
  by_cases h2 : i=702
  · subst i
    simp only [trialStaged,prefixed_scratch,List.length_nil]
    omega
  rw [trialStaged,prefixed_frame _ _ h1 h2]
  exact (hf i).trans (by omega)

theorem stage_cost_le (a : Data) (L : ℕ) (ha : WordBound L a) :
    stageTrialCost a+routeCost (782,0) (trialStaged a) ≤ 68*L+66 := by
  have hf := routes_wordBound masterRoutes a L ha
  have hr := routes_cost_bound masterRoutes a L ha
  have h768 := hf 768
  have h702 := hf 702
  have h782 := ha 782
  have h0 := ha 0
  have hs782 := trialStaged_frame a 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs0 := trialStaged_frame a 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change routesCost masterRoutes a ≤ 5*(9*L+8)+3 at hr
  simp only [stageTrialCost,stageFinalCost,prefixCost,routeCost,hs782,hs0]
  change ((finalStaged a).stacks 768).length ≤ L at h768
  change ((finalStaged a).stacks 702).length ≤ L at h702
  omega

theorem references_budget_le (bits : List Bool) (L : ℕ) (hl : bits.length ≤ L) :
    References.budget bits ≤ 32*(CounterPrograms.value bits+1)*(L+1)+
      CounterPrograms.value bits*(12*CounterPrograms.value bits+32)+8 := by
  have h := CounterConversions.coreBound_le bits
  have hm := Nat.mul_le_mul_left (32*(CounterPrograms.value bits+1))
    (Nat.add_le_add_right hl 1)
  unfold CounterConversions.runtimeBound at h
  unfold References.budget
  omega

theorem reference_length_le (m : ℕ) (bits : List Bool)
    (h : bits∈RowSelectionProgram.Index.alphabet m) : bits.length ≤ m := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  have hi' : i < m := by simpa using hi
  simp [Encoding.encodeNat]
  omega

theorem collector_budget_le (m Q W : ℕ) (queryCost width : List Bool → ℕ)
    (hQ : ∀ bits∈RowSelectionProgram.Index.alphabet m, queryCost bits ≤ Q)
    (hW : ∀ bits∈RowSelectionProgram.Index.alphabet m, width bits ≤ W) :
    Marked.Wide.valueBudget queryCost width (RowSelectionProgram.Index.alphabet m) [] ≤
      m*Q+4+m*(22*(m*(m+W+1))+26) := by
  have hq := sum_map_le _ queryCost Q hQ
  have hs := sum_map_le (RowSelectionProgram.Index.alphabet m)
    (fun bits => bits.length+width bits+1) (m+W+1) (by
      intro bits hb
      have := reference_length_le m bits hb
      have := hW bits hb
      omega)
  simp only [RowSelectionProgram.Index.alphabet_length] at hq hs
  unfold Marked.Wide.valueBudget Marked.Wide.valueInputSize
  simp only [RowSelectionProgram.Index.alphabet_length,List.length_nil,zero_add]
  have hh := Nat.mul_le_mul_left m (Nat.add_le_add_right (Nat.mul_le_mul_left 22 hs) 26)
  omega

theorem precision_budget_le (a : Data) (L : ℕ) (ha : WordBound L a) :
    Precision.budget (a.stacks 785) (a.stacks 782)+1 ≤
      1000*(2*L+3)^2+2*massPrecision a+(massPrecision a+1)*(16*(2*L+3)+16)+2*(2*L+3)+8 := by
  have hlen : (a.stacks 785).length+(a.stacks 782).length+3 ≤ 2*L+3 := by
    have := ha 785; have := ha 782; omega
  have hp := Nat.pow_le_pow_left hlen 2
  have hm := Nat.mul_le_mul_left (massPrecision a+1)
    (show 16*((a.stacks 785).length+(a.stacks 782).length+3)+16 ≤ 16*(2*L+3)+16 by omega)
  dsimp only [Precision.budget]
  change 1000*((a.stacks 785).length+(a.stacks 782).length+3)^2+2*massPrecision a+
    (massPrecision a+1)*(16*((a.stacks 785).length+(a.stacks 782).length+3)+16)+
    2*((a.stacks 785).length+(a.stacks 782).length+3)+7+1 ≤ _
  omega

theorem export_budget_le (a : Data) (L z : ℕ) (ha : WordBound L a) :
    exportCost 322 769 (scoredState a z) ≤
      2*L+7*massPrecision a+8+1536*(3*L+massPrecision a+2)+2348 := by
  have hs := trial_wordBound a L ha
  have hword : WordBound (3*L+massPrecision a+2) (scoredState a z) := by
    intro i
    by_cases h322 : i=322
    · subst i; simp [scoredState,SubexpLiftRing.fixedBits_length]; omega
    by_cases h212 : i=212
    · subst i; simp [scoredState,List.length_replicate]; omega
    simp only [scoredState,Function.update_of_ne h322,Function.update_of_ne h212]
    exact (hs i).trans (by omega)
  have hrouted : WordBound (3*L+massPrecision a+2)
      (routed (workerStack 322,769) (scoredState a z)) := by
    intro i
    by_cases hi : i=769
    · subst i; simpa [routed] using hword (workerStack 322)
    · simpa [routed,hi] using hword i
  have hc := cleanup_budget_le _ _ hrouted
  have h769 : (scoredState a z).stacks 769=a.stacks 769 := by
    simp [scoredState,trialStaged_frame]
  have h322 : ((scoredState a z).stacks (workerStack 322)).length=massPrecision a := by
    simp [scoredState,workerStack,SubexpLiftRing.fixedBits_length]
  have hl := ha 769
  unfold exportCost routeCost
  rw [h769,h322]
  omega

theorem massBodyBudget_le (a : Data) (L Q W z : ℕ) (ha : WordBound L a)
    (queryCost width : List Bool → ℕ)
    (hQ : ∀ bits∈massRecords a, queryCost bits ≤ Q)
    (hW : ∀ bits∈massRecords a, width bits ≤ W) :
    massBodyBudget a queryCost width z ≤
      CounterPrograms.value (a.stacks 782)*Q+
        overhead L (CounterPrograms.value (a.stacks 782)) (massPrecision a) W := by
  have hs := stage_cost_le a L ha
  have hr := references_budget_le (a.stacks 782) L (ha 782)
  have hc := collector_budget_le (CounterPrograms.value (a.stacks 782)) Q W queryCost width hQ hW
  have hp := precision_budget_le a L ha
  have he := export_budget_le a L z ha
  have hg := Marked.Wide.outputGrowth_le width (massRecords a) W hW
  simp only [massRecords,RowSelectionProgram.Index.alphabet_length] at hg
  unfold massBodyBudget overhead
  simp only [massRecords] at *
  omega


theorem saved_wordBound (a : Data) (L : ℕ) (ha : WordBound L a) :
    WordBound (L+32) (savedRegisters callerRegisters a) := by
  intro i
  rw [savedRegisters_eq]
  by_cases hi : i=895
  · subst i
    simp only [Function.update_self,List.length_append,List.length_reverse,List.length_map,
      callerRegisters_length]
    have := ha 895
    omega
  · simp only [Function.update_of_ne hi]
    exact (ha i).trans (by omega)

theorem massBudget_le (a : Data) (L Q W z : ℕ) (ha : WordBound L a)
    (queryCost width : List Bool → ℕ)
    (hQ : ∀ bits∈massRecords a, queryCost bits ≤ Q)
    (hW : ∀ bits∈massRecords a, width bits ≤ W) :
    massBudget a queryCost width z ≤
      CounterPrograms.value (a.stacks 782)*Q+
        overhead (L+32) (CounterPrograms.value (a.stacks 782)) (massPrecision a) W+64 := by
  have h := massBodyBudget_le (savedRegisters callerRegisters a) (L+32) Q W z
    (saved_wordBound a L ha) queryCost width (by simpa using hQ) (by simpa using hW)
  have hh := Nat.add_le_add_right h 64
  simpa [massBudget,savedRegisters_eq,massPrecision] using hh

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
