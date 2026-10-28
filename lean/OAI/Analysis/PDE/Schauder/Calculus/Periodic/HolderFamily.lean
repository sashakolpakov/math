import OAI.Analysis.PDE.Schauder.Calculus.Periodic.HolderContinuity
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Derivative

open Set Filter Metric Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V F I : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]

theorem exists_periodic_holder_family
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {U : Set ℝ} (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x))) :
    ∃ T : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α,
      ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x) := by
  classical
  have he t (ht : t ∈ U) := OAI.Analysis.PDE.Dirichlet.exists_periodic_holder_field e b hK hr hrp hbounded
    (fun x => f (t,x)) ((contDiff_parameter_space_slice hf ht).of_le (by simp))
    (hp t ht) hα hα1
  let T (t : ℝ) : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α :=
    if ht : t ∈ U then (he t ht).choose else 0
  refine ⟨T,?_⟩
  intro t ht x
  simpa only [T,dite_eq_left ht] using (he t ht).choose_spec x

theorem continuousOn_periodic_holder_family
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set ℝ} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    (T : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x)) : ContinuousOn T U := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_periodic_holder_family e b hK hr hrp hbounded hα hα1
    (fun t : U => fun x => f (t,x)) (fun t : U => T t)
  · exact hf.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun p => p.1.property)
  · exact (OAI.Analysis.PDE.Dirichlet.contDiffOn_slice_fderiv hU hf).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun p => p.1.property)
  · intro t x
    exact (contDiff_parameter_space_slice hf t.property).differentiable (by simp) x
  · intro t
    exact hp t t.property
  · intro t x
    exact hT t t.property x

omit [ProperSpace E] [Fintype I] in
theorem parameterDerivative_latticePeriodic
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ × E → F} (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    {t : ℝ} (ht : t ∈ U) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => parameterDerivative f (t,x)) := by
  intro x l
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds ht] with s hs
  exact hp s hs x l

end OAI.Analysis.PDE.Schauder
