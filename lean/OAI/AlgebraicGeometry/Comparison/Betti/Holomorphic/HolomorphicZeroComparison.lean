import OAI.AlgebraicGeometry.Comparison.Betti.CochainZeroCriterion
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.PresheafInclusion
import Mathlib.Algebra.Homology.Functor

/-! # Holomorphic Zero Comparison -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicZeroComparison

noncomputable section

/-! The actual holomorphic inclusion induces an isomorphism in degree zero. -/

open _root_.CategoryTheory _root_.HomologicalComplex _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem inclusionCochainMap_quasiIsoAt_zero : QuasiIsoAt (DeRhamComplex.inclusionCochainMap E M) 0 := by
  apply CochainZeroCriterion.Homology.quasiIsoAt_zero_of_closed_lift
  · exact HolomorphicPullback.inclusion_injective 0
  · intro a ha
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 at a
    rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d] at ha
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 at ha
    let apure : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 0 :=
      ⟨a, fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero (E := E) _⟩
    have hh : apure ∈ DeRhamComplex.forms E M 0 := by
      apply (DeRhamComplex.mem_forms_iff_derivative_pure 0 apure).mpr
      change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val
      rw [ha]
      exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.zero
    let b : DeRhamComplex.forms E M 0 := ⟨apure, hh⟩
    refine ⟨b, ?_, rfl⟩
    rw [DeRhamComplex.complex_d]
    change DeRhamComplex.differential E M 0 b = 0
    apply HolomorphicPullback.inclusion_injective 1
    rw [DeRhamComplex.inclusion_differential, map_zero]
    exact ha

theorem inclusionPresheafCochainMap_quasiIsoAt_zero :
    QuasiIsoAt (PresheafInclusion.inclusionPresheafCochainMap E M) 0 := by
  apply (quasiIsoAt_iff_evaluation _ 0).mpr
  intro U
  apply CochainZeroCriterion.Homology.quasiIsoAt_zero_of_closed_lift
  · exact (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U.unop 0).symm.injective.comp (HolomorphicPullback.inclusion_injective 0)
  · intro a ha
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U.unop 0 at a
    change (Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E U.unop).d 0 1 a = 0 at ha
    rw [Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex_d] at ha
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0 at ha
    let α := Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U.unop 0 a
    have hα : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d α = 0 := by
      rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, ha, map_zero]
    let apure : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E U.unop 0 0 :=
      ⟨α, fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero (E := E) _⟩
    have hh : apure ∈ DeRhamComplex.forms E U.unop 0 := by
      apply (DeRhamComplex.mem_forms_iff_derivative_pure 0 apure).mpr
      change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U.unop 1 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d α).val
      rw [hα]
      exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.zero
    let b : DeRhamComplex.forms E U.unop 0 := ⟨apure, hh⟩
    refine ⟨b, ?_, ?_⟩
    · change (DeRhamComplex.complex E U.unop).d 0 1 b = 0
      rw [DeRhamComplex.complex_d]
      change DeRhamComplex.differential E U.unop 0 b = 0
      apply HolomorphicPullback.inclusion_injective 1
      rw [DeRhamComplex.inclusion_differential, map_zero]
      exact hα
    · exact (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U.unop 0).symm_apply_apply a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicZeroComparison
