import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeBounds

namespace OAI.Algorithms

/-! The mass budget depends only on its physical sources and worker bank.
The selector incumbent, remaining candidate queue, and register-save tail are
not traversed and therefore do not occur in the size hypothesis. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram SubexpSetupStorage LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def MassSource (i : Fin 896) : Prop :=
  i=768 ∨ i=769 ∨ i=777 ∨ i=782 ∨ i=783 ∨ i=784 ∨ i=785

def MassPort (i : Fin 896) : Prop := i.val < 768 ∨ MassSource i

instance (i : Fin 896) : Decidable (MassSource i) := inferInstanceAs
  (Decidable (i=768 ∨ i=769 ∨ i=777 ∨ i=782 ∨ i=783 ∨ i=784 ∨ i=785))
instance (i : Fin 896) : Decidable (MassPort i) := inferInstanceAs
  (Decidable (i.val < 768 ∨ MassSource i))

def massRestricted (a : Data) : Data :=
  ⟨a.regs,fun i => if MassPort i then a.stacks i else []⟩

theorem massRestricted_wordBound (a : Data) (L : ℕ) (hw : WorkerEmpty a)
    (hs : ∀ i, MassSource i → (a.stacks i).length ≤ L) :
    WordBound L (massRestricted a) := by
  intro i
  by_cases hp : MassPort i
  · simp only [massRestricted,ite_eq_left hp]
    rcases hp with hi|hi
    · let j : Fin 768 := ⟨i.val,hi⟩
      have hj : workerStack j=i := rfl
      have he := hw j
      rw [hj] at he
      simp [he]
    · exact hs i hi
  · simp [massRestricted,hp]

theorem trialStaged_congr_massPort (a b : Data)
    (h : ∀ i, MassPort i → a.stacks i=b.stacks i) :
    ∀ i, MassPort i → (trialStaged a).stacks i=(trialStaged b).stacks i := by
  intro i hi
  by_cases h0 : i=700
  · subst i; rw [(trialStaged_sources a).1,(trialStaged_sources b).1]
    exact h 784 (by decide)
  by_cases h1 : i=701
  · subst i; rw [(trialStaged_sources a).2.1,(trialStaged_sources b).2.1,
      h 768 (by decide),h 777 (by decide)]
  by_cases h2 : i=702
  · subst i; simp only [trialStaged,prefixed_scratch]
  by_cases h7 : i=707
  · subst i; rw [(trialStaged_sources a).2.2.1,(trialStaged_sources b).2.2.1]
    exact h 782 (by decide)
  by_cases h8 : i=708
  · subst i; rw [(trialStaged_sources a).2.2.2.1,(trialStaged_sources b).2.2.2.1]
    exact h 783 (by decide)
  by_cases h9 : i=709
  · subst i; rw [(trialStaged_sources a).2.2.2.2,(trialStaged_sources b).2.2.2.2]
    exact h 785 (by decide)
  rw [trialStaged_frame a i h0 h1 h2 h7 h8 h9,
    trialStaged_frame b i h0 h1 h2 h7 h8 h9]
  exact h i hi

theorem massBodyBudget_congr (a b : Data)
    (h : ∀ i, MassPort i → a.stacks i=b.stacks i)
    (queryCost width : List Bool → ℕ) (z : ℕ) :
    massBodyBudget a queryCost width z=massBodyBudget b queryCost width z := by
  have hp : massPrecision a=massPrecision b := by
    simp only [massPrecision,h 785 (by decide),h 782 (by decide)]
  have hs : stageTrialCost a=stageTrialCost b := by
    simp only [stageTrialCost,stageFinalCost,prefixCost,masterRoutes,routesCost,
      routesState,routed,routeCost,finalStaged]
    simp [h 700 (by decide),h 701 (by decide),h 702 (by decide),h 707 (by decide),
      h 708 (by decide),h 709 (by decide),h 768 (by decide),h 777 (by decide),
      h 782 (by decide),h 783 (by decide),h 784 (by decide),h 785 (by decide)]
  have ht := trialStaged_congr_massPort a b h
  have hf (i : Fin 896) (hi : MassPort i) :
      (scoredState a z).stacks i=(scoredState b z).stacks i := by
    by_cases h322 : i=322
    · subst i; simp [scoredState,hp]
    by_cases h212 : i=212
    · subst i; simp [scoredState,hp]
    simp only [scoredState,Function.update_of_ne h322,Function.update_of_ne h212]
    exact ht i hi
  have he : exportCost 322 769 (scoredState a z)=exportCost 322 769 (scoredState b z) := by
    have hc : Cleanup.Wide.bytes (projectState id workerStack
        (routed (workerStack 322,769) (scoredState a z)))=
        Cleanup.Wide.bytes (projectState id workerStack
        (routed (workerStack 322,769) (scoredState b z))) := by
      unfold Cleanup.Wide.bytes
      apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      have hne : workerStack i≠769 := by
        intro heq
        have hv := congrArg (fun x : Fin 896 => x.val) heq
        simp only [workerStack,Fin.val_castAdd] at hv
        have := i.isLt
        omega
      simp only [projectState,routed,Function.comp_apply,Function.update_of_ne hne]
      rw [hf (workerStack i) (Or.inl i.isLt)]
    simp only [exportCost,routeCost,Cleanup.Wide.budget,hc,
      hf 769 (by decide),hf (workerStack 322) (by decide)]
  simp only [massBodyBudget,hs,routeCost,ht 0 (by decide),ht 782 (by decide),
    h 782 (by decide),h 785 (by decide),massRecords,hp,he]

theorem massBudget_eq_body_add (a : Data) (queryCost width : List Bool → ℕ) (z : ℕ) :
    massBudget a queryCost width z=massBodyBudget a queryCost width z+64 := by
  unfold massBudget
  apply congrArg (fun n : ℕ => n+64)
  apply massBodyBudget_congr
  intro i hi
  have hn : i≠895 := by
    intro heq
    subst i
    rcases hi with hi|hi
    · simp at hi
    · rcases hi with hi|hi|hi|hi|hi|hi|hi <;> cases hi
  simp [savedRegisters_eq,hn]

theorem massBudget_le_sources (a : Data) (L Q W z : ℕ) (hw : WorkerEmpty a)
    (hs : ∀ i, MassSource i → (a.stacks i).length ≤ L)
    (queryCost width : List Bool → ℕ)
    (hQ : ∀ bits∈massRecords a, queryCost bits ≤ Q)
    (hW : ∀ bits∈massRecords a, width bits ≤ W) :
    massBudget a queryCost width z ≤
      CounterPrograms.value (a.stacks 782)*Q+
        overhead L (CounterPrograms.value (a.stacks 782)) (massPrecision a) W+64 := by
  have hr (i : Fin 896) (hi : MassPort i) :
      a.stacks i=(massRestricted a).stacks i := by simp [massRestricted,hi]
  have hm : massRecords (massRestricted a)=massRecords a := by
    simp [massRecords,massRestricted,MassPort,MassSource]
  have hb := massBodyBudget_le (massRestricted a) L Q W z
    (massRestricted_wordBound a L hw hs) queryCost width
    (by simpa only [hm] using hQ) (by simpa only [hm] using hW)
  rw [massBudget_eq_body_add,massBodyBudget_congr a (massRestricted a) hr]
  have hh := Nat.add_le_add_right hb 64
  simpa [massRestricted,MassPort,MassSource,massPrecision] using hh

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
