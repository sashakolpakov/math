import OAI.Analysis.DifferentialForms.Manifold.PurePullback
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence

/-! # Local Holomorphic Purity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicPurity

noncomputable section

/-! Pure type under a holomorphic map needs only the actual derivative at the point. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N] {p q : ℕ}

theorem pure_pullback_inChart_at (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N (p + q)) (g : M → N)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ atlas E M) (hf : f ∈ atlas F N) {y : E}
    (hy : y ∈ e.target) (hfy : g (e.symm y) ∈ f.source)
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g (e.symm y))
    (hform : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F p q (form.inChart f (f (g (e.symm y))))) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q ((form.pullback (E := E) g).inChart e y) := by
  rw [form.pullback_inChart g e f he hf hy hfy
    ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex hg).mdifferentiableAt (by simp))]
  have hhol := (Analysis.DifferentialForms.Manifold.Holomorphic.complexContDiffAt_manifoldMap_inChart g e f he hf hy hfy hg).differentiableAt
    (by simp)
  rw [hhol.fderiv_restrictScalars ℝ]
  exact AlgebraicTopology.DeRham.Comparison.BidegreeRestriction.hasBidegree_pullback hform (fderiv ℂ (f ∘ g ∘ e.symm) y)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem complexOpenInverse_contMDiffAt {U : Opens M} (hs : Nonempty U) {x : M} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (U.openPartialHomeomorphSubtypeCoe hs).symm x := by
  rw [← ContMDiffAt.subtypeVal_comp_iff]
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact (U.openPartialHomeomorphSubtypeCoe hs).right_inv
    (by simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy)

end

end OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicPurity
