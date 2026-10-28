import OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree
import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts
import OAI.Analysis.DifferentialForms.Manifold.Transition
import OAI.AlgebraicTopology.DeRham.Comparison.BidegreeRestriction
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Bidegree Invariant -/

namespace OAI.Analysis.DifferentialForms.Manifold

/-! Pure bidegree is invariant under the actual holomorphic chart transitions. -/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {p q : ℕ}

section

/-- A pure chart value remains pure after the genuine holomorphic change of chart. -/
theorem Algebra.RawManifoldForm.hasBidegree_inChart_of_transition (form : Algebra.RawManifoldForm E M (p + q))
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {y : E} (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source)
    (hform : Bidegree.HasBidegree E p q (form.inChart f (f (e.symm y)))) :
    Bidegree.HasBidegree E p q (form.inChart e y) := by
  let : IsManifold 𝓘(ℝ, E) ∞ M := ComplexCharts.complexManifold_isRealSmooth
  rw [form.inChart_transition e f he hf hy hfy]
  have hhol : DifferentiableAt ℂ (f ∘ e.symm) y :=
    (ComplexCharts.complexContDiffAt_chart_transition e f he hf hy hfy).differentiableAt (by simp)
  rw [hhol.fderiv_restrictScalars ℝ]
  exact AlgebraicTopology.DeRham.Comparison.BidegreeRestriction.hasBidegree_pullback hform (fderiv ℂ (f ∘ e.symm) y)

/-- Purity at a manifold point is independent of the atlas chart used there. -/
theorem Algebra.RawManifoldForm.hasBidegree_inChart_iff (form : Algebra.RawManifoldForm E M (p + q))
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {x : M} (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    Bidegree.HasBidegree E p q (form.inChart e (e x)) ↔
      Bidegree.HasBidegree E p q (form.inChart f (f x)) := by
  constructor
  · intro hform
    apply form.hasBidegree_inChart_of_transition f e hf he (f.map_source hfx)
      (by simpa only [f.left_inv hfx] using hex)
    simpa only [f.left_inv hfx] using hform
  · intro hform
    apply form.hasBidegree_inChart_of_transition e f he hf (e.map_source hex)
      (by simpa only [e.left_inv hex] using hfx)
    simpa only [e.left_inv hex] using hform

end

/-- Testing all chart expressions is equivalent to testing one genuine chart
at each point; no extra purity assumption arises from the chosen atlas. -/
theorem BidegreeInvariant.hasManifoldBidegree_iff_chartAt (form : Algebra.RawManifoldForm E M (p + q)) :
    ManifoldBidegree.HasManifoldBidegree E M p q form ↔
      ∀ x : M, Bidegree.HasBidegree E p q (form.inChart (chartAt E x) (chartAt E x x)) := by
  constructor
  · intro hform x
    exact hform (chartAt E x) (chart_mem_atlas E x) (chartAt E x x)
      ((chartAt E x).map_source (mem_chart_source E x))
  · intro hform e he y hy
    exact form.hasBidegree_inChart_of_transition e (chartAt E (e.symm y)) he
      (chart_mem_atlas E (e.symm y)) hy (mem_chart_source E (e.symm y)) (hform (e.symm y))

end OAI.Analysis.DifferentialForms.Manifold
