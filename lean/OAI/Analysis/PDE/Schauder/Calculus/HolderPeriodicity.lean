import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

open Set Module
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
  {α : ℝ} {r : E → ℝ}

omit [Fintype ι] in
theorem holder_value_eq_of_periodic
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value T)))
    (x y : {x | r x ≤ 0}) (l : Submodule.span ℤ (Set.range b))
    (hy : (y : E) = e.symm ((e (x:E)).1+(l:P),(e (x:E)).2)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value T y = OAI.Analysis.Normed.Function.Holder.HolderMap.value T x := by
  have h := hT x l
  rw [← hy,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ y.property,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] at h
  exact h

omit [Fintype ι] in
theorem holder_periodic_of_value_eq
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : ∀ (x y : {x | r x ≤ 0}) (l : Submodule.span ℤ (Set.range b)),
      (y : E) = e.symm ((e (x:E)).1+(l:P),(e (x:E)).2) →
      OAI.Analysis.Normed.Function.Holder.HolderMap.value T y = OAI.Analysis.Normed.Function.Holder.HolderMap.value T x) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value T)) := by
  intro x l
  by_cases hx : r x ≤ 0
  · have hy : r (e.symm ((e x).1+(l:P),(e x).2)) ≤ 0 := by rw [hr x l]; exact hx
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.HolderMap.value T)
      (show e.symm ((e x).1+(l:P),(e x).2) ∈ {x | r x ≤ 0} from hy),
      OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.HolderMap.value T) (show x ∈ {x | r x ≤ 0} from hx)]
    exact hT ⟨x,hx⟩ ⟨_,hy⟩ l rfl
  · have hy : ¬ r (e.symm ((e x).1+(l:P),(e x).2)) ≤ 0 := by rw [hr x l]; exact hx
    simp only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension,OAI.Analysis.PDE.Dirichlet.zeroExtend,Set.mem_ofPred_eq,dite_eq_right hx,dite_eq_right hy]

omit [Fintype ι] in
theorem holder_periodic_of_actual
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α) (f : E → F) (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    (hT : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = f x) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value T)) := by
  apply holder_periodic_of_value_eq e b hr T
  intro x y l hy
  rw [hT,hT,hy]
  exact hf x l

end OAI.Analysis.PDE.Schauder
