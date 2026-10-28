import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support

/-! # Locally Finite Sum -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Locally finite sums of smooth differential forms

All sums are the actual pointwise `finsum`. Local finiteness supplies a finite
sum that agrees on a neighborhood, proving smoothness and differentiation
without any convergence hypothesis or interchange assumption.
-/

open Function Set Filter
open scoped _root_.Topology ContDiff

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {r : WithTop ℕ∞} {x : E} {s : Finset ι} {f : ι → E → F}

/-- A locally uniform finite support turns the pointwise sum into a smooth
finite sum near the specified point. -/
theorem LocallyFiniteSum.contDiffAt_finsum_of_eventually_support_subset
    (hf : ∀ i, ContDiffAt ℝ r (f i) x)
    (hs : ∀ᶠ y in 𝓝 x, support (fun i => f i y) ⊆ s) :
    ContDiffAt ℝ r (fun y => ∑ᶠ i, f i y) x := by
  have heq : (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ s, f i y) :=
    hs.mono fun y hy => finsum_eq_sum_of_support_subset _ hy
  exact (ContDiffAt.sum (fun i _ => hf i)).congr_of_eventuallyEq heq

/-- Smoothness of an actual sum with locally finite supports. -/
theorem LocallyFiniteSum.contDiff_finsum_of_locallyFinite (hf : ∀ i, ContDiff ℝ r (f i))
    (hlf : LocallyFinite (fun i => support (f i))) :
    ContDiff ℝ r (fun y => ∑ᶠ i, f i y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨s, hs⟩ := hlf.exists_finset_support x
  exact LocallyFiniteSum.contDiffAt_finsum_of_eventually_support_subset (fun i => (hf i).contDiffAt) hs

/-- Terms outside a local finite support have zero derivative at the point. -/
theorem LocallyFiniteSum.fderiv_eq_zero_of_notMem_eventually_support
    (hs : ∀ᶠ y in 𝓝 x, support (fun i => f i y) ⊆ s) {i : ι} (hi : i ∉ s) :
    fderiv ℝ (f i) x = 0 := by
  have heq : f i =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
    filter_upwards [hs] with y hy
    by_contra hne
    exact hi (hy hne)
  simpa only [fderiv_const_apply] using heq.fderiv_eq

/-- The derivatives have finite support at a point whenever the original
family has one uniform finite support on a neighborhood. -/
theorem LocallyFiniteSum.support_fderiv_subset_of_eventually_support
    (hs : ∀ᶠ y in 𝓝 x, support (fun i => f i y) ⊆ s) :
    support (fun i => fderiv ℝ (f i) x) ⊆ s := by
  intro i hi
  by_contra his
  exact hi (LocallyFiniteSum.fderiv_eq_zero_of_notMem_eventually_support hs his)

/-- Differentiation commutes with a sum that is locally a fixed finite sum. -/
theorem LocallyFiniteSum.fderiv_finsum_of_eventually_support_subset
    (hf : ∀ i, DifferentiableAt ℝ (f i) x)
    (hs : ∀ᶠ y in 𝓝 x, support (fun i => f i y) ⊆ s) :
    fderiv ℝ (fun y => ∑ᶠ i, f i y) x = ∑ᶠ i, fderiv ℝ (f i) x := by
  have heq : (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ s, f i y) :=
    hs.mono fun y hy => finsum_eq_sum_of_support_subset _ hy
  rw [heq.fderiv_eq, fderiv_fun_sum (fun i _ => hf i)]
  exact (finsum_eq_sum_of_support_subset _
    (LocallyFiniteSum.support_fderiv_subset_of_eventually_support hs)).symm

variable {n : ℕ}

/-- Exterior differentiation commutes with a locally finite sum at each point. -/
theorem LocallyFiniteSum.extDeriv_finsum_of_eventually_support_subset {form : ι → Basic.RawForm E n}
    (hf : ∀ i, DifferentiableAt ℝ (form i) x)
    (hs : ∀ᶠ y in 𝓝 x, support (fun i => form i y) ⊆ s) :
    extDeriv (fun y => ∑ᶠ i, form i y) x = ∑ᶠ i, extDeriv (form i) x := by
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
    (fderiv ℝ (fun y => ∑ᶠ i, form i y) x) = _
  rw [LocallyFiniteSum.fderiv_finsum_of_eventually_support_subset hf hs]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).toLinearMap.toAddMonoidHom.map_finsum
    (s.finite_toSet.subset (LocallyFiniteSum.support_fderiv_subset_of_eventually_support hs))

/-- Exterior differentiation cannot enlarge topological support. -/
theorem LocallyFiniteSum.support_extDeriv_subset_tsupport (form : Basic.RawForm E n) :
    support (extDeriv form) ⊆ tsupport form := by
  intro x hx
  by_contra hnot
  apply hx
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
    (fderiv ℝ form x) = 0
  rw [fderiv_of_notMem_tsupport ℝ hnot, map_zero]

/-- The actual pointwise sum of a locally finite family of smooth forms. -/
def Basic.SmoothForm.locallyFiniteSum (form : ι → Basic.SmoothForm E n)
    (hlf : LocallyFinite (fun i => support (form i : Basic.RawForm E n))) : Basic.SmoothForm E n :=
  ⟨fun x => ∑ᶠ i, form i x,
    LocallyFiniteSum.contDiff_finsum_of_locallyFinite (fun i => (form i).smooth) hlf⟩

@[simp] theorem Basic.SmoothForm.locallyFiniteSum_apply (form : ι → Basic.SmoothForm E n)
    (hlf : LocallyFinite (fun i => support (form i : Basic.RawForm E n))) (x : E) :
    Basic.SmoothForm.locallyFiniteSum form hlf x = ∑ᶠ i, form i x := rfl

/-- The derivative family remains locally finite, by the support theorem. -/
theorem Basic.SmoothForm.locallyFinite_d (form : ι → Basic.SmoothForm E n)
    (hlf : LocallyFinite (fun i => support (form i : Basic.RawForm E n))) :
    LocallyFinite (fun i => support (Basic.SmoothForm.d (form i) : Basic.RawForm E (n + 1))) :=
  hlf.closure.subset fun i => LocallyFiniteSum.support_extDeriv_subset_tsupport (form i : Basic.RawForm E n)

/-- The exterior differential of the locally finite sum is the actual sum of
the differentials. -/
theorem Basic.SmoothForm.d_locallyFiniteSum (form : ι → Basic.SmoothForm E n)
    (hlf : LocallyFinite (fun i => support (form i : Basic.RawForm E n))) :
    Basic.SmoothForm.d (Basic.SmoothForm.locallyFiniteSum form hlf) =
      Basic.SmoothForm.locallyFiniteSum (fun i => Basic.SmoothForm.d (form i)) (Basic.SmoothForm.locallyFinite_d form hlf) := by
  apply Basic.SmoothForm.ext
  intro x
  obtain ⟨s, hs⟩ := hlf.exists_finset_support x
  exact LocallyFiniteSum.extDeriv_finsum_of_eventually_support_subset
    (fun i => ((form i).smooth.differentiable (by simp)).differentiableAt) hs

/-- In the finite case the construction is the usual sum of bundled forms. -/
theorem Basic.SmoothForm.locallyFiniteSum_eq_sum [Fintype ι] (form : ι → Basic.SmoothForm E n)
    (hlf : LocallyFinite (fun i => support (form i : Basic.RawForm E n))) :
    Basic.SmoothForm.locallyFiniteSum form hlf = ∑ i, form i := by
  apply Basic.SmoothForm.ext
  intro x
  change (∑ᶠ i, form i x) = Basic.SmoothForm.eval x (∑ i, form i)
  rw [map_sum, finsum_eq_sum_of_fintype]
  rfl

end

end OAI.Analysis.DifferentialForms.Manifold
