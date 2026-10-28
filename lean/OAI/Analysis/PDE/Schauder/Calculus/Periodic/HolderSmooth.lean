import OAI.Analysis.PDE.Schauder.Calculus.Periodic.HolderFamily
import OAI.Analysis.PDE.Schauder.Calculus.HolderDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Filter Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V F I : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]

theorem hasDerivAt_periodic_holder_family
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set ℝ} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    (T S : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x))
    (hS : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (S t) x = parameterDerivative f (t,x))
    {a : ℝ} (ha : a ∈ U) : HasDerivAt T (S a) a := by
  have hpD : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => parameterDerivative f (t,x)) :=
    fun t ht => parameterDerivative_latticePeriodic e b hU hp ht
  have hcS := continuousOn_periodic_holder_family e b hK hr hrp hbounded hα hα1 hU
    (parameterDerivative f) (contDiffOn_parameterDerivative hU hf) hpD S hS
  apply hasDerivAt_holder_of_pointwise hU ha (hcS.continuousAt (hU.mem_nhds ha))
  intro t ht x
  have hdiff : DifferentiableAt ℝ f (t,(x : E)) :=
    ((hf (t,x) ht).contDiffAt ((hU.preimage continuous_fst).mem_nhds ht)).differentiableAt (by simp)
  have hd := hasDerivAt_parameter_slice hdiff
  rw [← parameterDerivative_eq hdiff,← hS t ht x] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds ht] with s hs
  exact hT s hs x

/-- Every jointly smooth periodic family is smooth with values in C^α,
without assuming smooth dependence in that Banach norm. -/
theorem contDiffOn_periodic_holder_family
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set ℝ} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    (T : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x)) :
    ContDiffOn ℝ ∞ T U := by
  rw [contDiffOn_infty]
  intro q
  induction q generalizing f T with
  | zero =>
      exact contDiffOn_zero.mpr (continuousOn_periodic_holder_family
        e b hK hr hrp hbounded hα hα1 hU f hf hp T hT)
  | succ q ih =>
      have hfD := contDiffOn_parameterDerivative hU hf
      have hpD : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => parameterDerivative f (t,x)) :=
        fun t ht => parameterDerivative_latticePeriodic e b hU hp ht
      obtain ⟨S,hS⟩ := exists_periodic_holder_family e b hK hr hrp hbounded hα hα1
        (parameterDerivative f) hfD hpD
      have hd t (ht : t ∈ U) : HasDerivAt T (S t) t :=
        hasDerivAt_periodic_holder_family e b hK hr hrp hbounded hα hα1 hU
          f hf hp T S hT hS ht
      rw [show (↑(q+1) : ℕ∞ω) = (q : ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt,?_,?_⟩
      · intro hq
        exact (by simp at hq)
      · exact (ih (parameterDerivative f) hfD hpD S hS).congr
          (fun t ht => (hd t ht).deriv)

theorem exists_smooth_periodic_holder_family
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set ℝ} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x))) :
    ∃ T : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α, ContDiffOn ℝ ∞ T U ∧
      ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x) := by
  obtain ⟨T,hT⟩ := exists_periodic_holder_family e b hK hr hrp hbounded hα hα1 f hf hp
  exact ⟨T,contDiffOn_periodic_holder_family e b hK hr hrp hbounded hα hα1 hU f hf hp T hT,hT⟩

end OAI.Analysis.PDE.Schauder
