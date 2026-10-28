import OAI.Analysis.PDE.Schauder.Calculus.Periodic.HolderContinuity
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.FDerivative
import OAI.Analysis.PDE.Schauder.Calculus.HolderFDeriv
import OAI.Analysis.PDE.Schauder.Calculus.HolderTranspose

open Set Filter Metric Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {Z E P V F ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

theorem exists_periodic_parameter_family
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {U : Set Z} (f : Z × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x))) :
    ∃ T : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α,
      ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x) := by
  classical
  have he t (ht : t ∈ U) := OAI.Analysis.PDE.Dirichlet.exists_periodic_holder_field e b hK hr hrp hbounded
    (fun x => f (t,x)) ((contDiff_fixed_parameter_slice hf ht).of_le (by simp))
    (hp t ht) hα hα1
  let T (t : Z) : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α :=
    if ht : t ∈ U then (he t ht).choose else 0
  refine ⟨T,?_⟩
  intro t ht x
  simpa only [T,dite_eq_left ht] using (he t ht).choose_spec x

theorem continuousOn_periodic_parameter_family
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set Z} (hU : IsOpen U)
    (f : Z × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    (T : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x)) : ContinuousOn T U := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_periodic_holder_family e b hK hr hrp hbounded hα hα1
    (fun t : U => fun x => f (t,x)) (fun t : U => T t)
  · exact hf.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun p => p.1.property)
  · exact (contDiffOn_space_fderiv hU hf).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun p => p.1.property)
  · intro t x
    exact (contDiff_fixed_parameter_slice hf t.property).differentiable (by simp) x
  · intro t
    exact hp t t.property
  · intro t x
    exact hT t t.property x

omit [ProperSpace E] [Fintype ι] in
theorem parameterFDerivative_latticePeriodic
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {U : Set Z} (hU : IsOpen U)
    {f : Z × E → F} (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    {t : Z} (ht : t ∈ U) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => parameterFDerivative f (t,x)) := by
  intro x l
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hU.mem_nhds ht] with s hs
  exact hp s hs x l

theorem hasFDerivAt_periodic_parameter_family
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set Z} (hU : IsOpen U)
    (f : Z × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    (T : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (S : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Z →L[ℝ] F) α)
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x))
    (hS : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (S t) x = parameterFDerivative f (t,x))
    {a : Z} (ha : a ∈ U) : HasFDerivAt T (holderTranspose (S a)) a := by
  have hpD : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => parameterFDerivative f (t,x)) :=
    fun t ht => parameterFDerivative_latticePeriodic e b hU hp ht
  have hcS := continuousOn_periodic_parameter_family e b hK hr hrp hbounded hα hα1 hU
    (parameterFDerivative f) (contDiffOn_parameterFDerivative hU hf) hpD S hS
  apply hasFDerivAt_holder_of_pointwise hU ha
    (holderTransposeCLM.continuous.continuousAt.comp (hcS.continuousAt (hU.mem_nhds ha)))
  intro t ht x
  have hdiff : DifferentiableAt ℝ f (t,(x : E)) :=
    ((hf (t,x) ht).contDiffAt ((hU.preimage continuous_fst).mem_nhds ht)).differentiableAt (by simp)
  have hd := hasFDerivAt_parameter_slice hdiff
  rw [← parameterFDerivative_eq hdiff,← hS t ht x] at hd
  have hd' : HasFDerivAt (fun s => OAI.Analysis.Normed.Function.Holder.HolderMap.value (T s) x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value (S t) x) t := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds ht] with s hs
    exact hT s hs x
  convert hd' using 1
  ext z
  rfl

end OAI.Analysis.PDE.Schauder
