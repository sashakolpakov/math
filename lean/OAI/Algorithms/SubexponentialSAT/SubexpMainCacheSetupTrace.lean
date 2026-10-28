import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheSetup

namespace OAI.Algorithms

/-!
# Actual intermediate traces for Main cache setup

The states occurring in the cache setup cost are the outputs of the actual
preceding calls.  This additive API retains those traces and stage results;
it does not change the fixed procedure or its published semantic record.
-/

namespace SubexponentialSAT.SubexpMainCacheSetupTrace

open BitProgram StructuredCalls SubexpMainProgram
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open SubexpMainCacheSetup

def Run {er es : ℕ} (proc : Procedure er es) (budget : ℕ)
    (a b : MainState er es) : Prop :=
  ∃ steps ≤ budget, Eval proc.invoke steps a b

structure StageTrace {er es : ℕ} (alloc : Allocation es)
    (a b c e : MainState er es) (p D : ℕ) [Fact p.Prime] : Prop where
  selectorReady : SubexpQuarticSelectorAdapter.WorkspaceReady a
  selectorRun : Run (SubexpQuarticSelectorAdapter.procedure er es)
    (SubexpQuarticSelectorAdapter.bound p
      (a.stacks (persistent es 6)).length (a.stacks (persistent es 15)).length)
    a (SubexpQuarticSelectorAdapter.result a p)
  ringsRun : Run (SubexpMainPreparedRings.procedure er (ringAllocation alloc))
    (SubexpMainPreparedRings.runtimeBound (ringAllocation alloc)
      (SubexpQuarticSelectorAdapter.result a p) p D)
    (SubexpQuarticSelectorAdapter.result a p) b
  ringsResult : SubexpMainPreparedRings.SelectedResult (ringAllocation alloc)
    (SubexpQuarticSelectorAdapter.result a p) b p D
  nodesRun : Run (SubexpMainFieldNodes.procedure er (nodeAllocation alloc))
    (SubexpMainFieldNodes.runtimeBound (nodeAllocation alloc) b p (D + 1)) b c
  nodesResult : SubexpMainFieldNodes.Result (nodeAllocation alloc) b c p (D + 1)
    (SubexpPreparedQuarticSetup.modulus p 1)
  cacheRun : Run (SubexpMainFieldCache.procedure er (cacheAllocation alloc))
    (SubexpMainFieldCache.runtimeBound (cacheAllocation alloc) c p) c e
  cacheResult : SubexpMainFieldCache.Result (cacheAllocation alloc) c e p D

theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (ha : WorkspaceReady alloc a)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    ∃ b c, ∃ n ≤ runtimeBound alloc a b c p D, ∃ e,
      Eval (procedure er alloc).invoke n a e ∧ Result alloc a e p D ∧
      StageTrace alloc a b c e p D := by
  have has := selector_ready alloc a ha
  let selected := SubexpQuarticSelectorAdapter.result a p
  obtain ⟨ns, hns, hes⟩ := SubexpQuarticSelectorAdapter.execution a p has hp
  have hps : BinaryArithmetic.toNat (selected.stacks (persistent es 6)) = p := by
    rw [selector_persistent_frame a p has 6 (by decide)]
    exact hp
  have hms : BinaryArithmetic.toNat (selected.stacks (persistent es 22)) = D + 1 := by
    rw [selector_persistent_frame a p has 22 (by decide)]
    exact hprecision
  have hxs : BinaryArithmetic.toNat (selected.stacks (persistent es 29)) = p^4 - 2 := by
    rw [selector_persistent_frame a p has 29 (by decide)]
    exact hexp
  obtain ⟨nr, hnr, b, her, hr⟩ := SubexpMainPreparedRings.selected_execution
    (ringAllocation alloc) selected p D hps hms
    (SubexpQuarticSelectorAdapter.result_selected a p has)
  obtain ⟨nn, hnn, c, hen, hn⟩ := SubexpMainFieldNodes.after_prepared
    (nodeAllocation alloc) selected b p D
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) hr hps
  have hce : ∀ i, SubexpMainFieldCache.initiallyEmpty i →
      selected.stacks (SubexpMainFieldCache.ordinary (cacheAllocation alloc) i) = [] := by
    intro i hi
    apply selector_workspace alloc a p ha ⟨i.val, by omega⟩
    rcases hi with ⟨_, hi⟩ | hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (congrArg (fun j : Fin 301 => j.val) hi))
  obtain ⟨nc, hnc, e, hec, hc⟩ := SubexpMainFieldCache.execution
    (cacheAllocation alloc) selected b c p D
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) hr hn hce hxs
  refine ⟨b, c, ns + (nr + (nn + nc + 1) + 1) + 1, ?_, e, ?_, ?_, ?_⟩
  · unfold runtimeBound
    dsimp only [selected] at hnr
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hes
      (SubexpProcedureCompose.sequence_invoke _ _ her
        (SubexpProcedureCompose.sequence_invoke _ _ hen hec))
  · exact result_of_stages alloc a b c e p D has hr hn hc
  · exact {
      selectorReady := has
      selectorRun := ⟨ns, hns, hes⟩
      ringsRun := ⟨nr, hnr, her⟩
      ringsResult := hr
      nodesRun := ⟨nn, hnn, hen⟩
      nodesResult := hn
      cacheRun := ⟨nc, hnc, hec⟩
      cacheResult := hc }

end SubexponentialSAT.SubexpMainCacheSetupTrace

end OAI.Algorithms
