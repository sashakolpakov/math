import OAI.Analysis.PDE.Dirichlet.Boundary.Normal
import OAI.Analysis.PDE.Dirichlet.DataGradient
import OAI.Analysis.PDE.Dirichlet.PositiveDeterminant
import OAI.Analysis.PDE.Dirichlet.NormalBounded

open Set Filter
open scoped Topology ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem mem_interior_sublevel_of_neg {E : Type*} [TopologicalSpace E]
    {r : E → ℝ} (hr : Continuous r) {x : E} (hx : r x < 0) :
    x ∈ interior {y | r y ≤ 0} := by
  apply mem_interior.mpr
  exact ⟨{y | r y < 0}, fun y (hy : r y < 0) ↦ hy.le, isOpen_lt hr continuous_const, hx⟩

theorem sublevel_subset_closure_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : E → ℝ} (hr : ContDiff ℝ 1 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) :
    {x | r x ≤ 0} ⊆ closure (interior {x | r x ≤ 0}) := by
  intro x hx
  by_cases hz : r x = 0
  · obtain ⟨v, hv⟩ := linear_form_exists_negative (fderiv ℝ r x) (hreg x hz)
    have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
    have hr' : DifferentiableAt ℝ r (x + (0 : ℝ) • v) := by
      simpa using hr.differentiable (by norm_num) x
    have hslope : Tendsto (fun t : ℝ ↦ r (x + t • v) / t) (𝓝[>] 0)
        (𝓝 (fderiv ℝ r x v)) := by
      simpa [hz, div_eq_inv_mul] using
        (hr'.hasFDerivAt.comp_hasDerivAt 0 hline).tendsto_slope_zero_right
    have hpoint : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
      simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ interior {x | r x ≤ 0} := by
      filter_upwards [hslope.eventually (eventually_lt_nhds hv), self_mem_nhdsWithin] with t ht htp
      apply mem_interior_sublevel_of_neg hr.continuous
      simpa using (div_lt_iff₀ (show 0 < t from htp)).mp ht
    exact mem_closure_of_tendsto hpoint hnear
  · exact subset_closure (mem_interior_sublevel_of_neg hr.continuous (lt_of_le_of_ne hx hz))

theorem equality_on_regular_sublevel_of_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r f g : E → ℝ}
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ x ∈ interior {x | r x ≤ 0}, f x = g x) :
    ∀ x, r x ≤ 0 → f x = g x := by
  intro x hx
  exact closure_minimal heq (isClosed_eq hf hg) (sublevel_subset_closure_interior hr hreg hx)

theorem quaternionHessian_posSemidef_on_regular_sublevel {n : ℕ}
    {r ψ : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 1 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) (hψ : ContDiff ℝ 2 ψ)
    (hpos : ∀ x ∈ interior {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) :
    ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosSemidef := by
  intro x hx
  apply (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt)).mpr
  intro z
  have hc : Continuous (fun y ↦ (quaternionForm (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) z).re) :=
    continuous_quaternionForm_re (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ) continuous_const
  have hsub : interior {y | r y ≤ 0} ⊆
      {y | 0 ≤ (quaternionForm (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) z).re} := by
    intro y hy
    exact (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt)).mp
      (hpos y hy).posSemidef z
  exact closure_minimal hsub (isClosed_le continuous_const hc)
    (sublevel_subset_closure_interior hr hreg hx)

end OAI.Analysis.PDE.Dirichlet
