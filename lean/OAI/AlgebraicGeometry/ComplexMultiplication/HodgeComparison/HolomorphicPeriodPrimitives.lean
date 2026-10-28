import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalRealOneForms
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegralPrimitiveCover

/-! # Holomorphic Period Primitives -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPeriodPrimitives.CM.Construction

noncomputable section

/-! Holomorphic combinations of rational H¹ classes produce actual
holomorphic linear combinations of the normalized local primitives. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem primitive_complex_combination_d
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {ι : Type} [Fintype ι] (U : Opens M) (d : ℤ)
    (a : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0)
    (hf : ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) = d • Intersection.CM.Construction.restrictSmoothForm U 1 (a i)) (t : ι → ℂ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (∑ i, t i • f i) =
      d • Intersection.CM.Construction.restrictSmoothForm U 1 (∑ i, t i • a i) := by
  simp only [map_sum, map_smul, hf, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm (t i) d _

theorem holomorphic_period_primitive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (q : ι → V.rationalCohomology 1)
    (U : Opens V.analyticSpace) (d : ℤ)
    (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0)
    (hf : ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) =
      d • Intersection.CM.Construction.restrictSmoothForm U 1 (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (q i)).val)
    (t : ι → ℂ)
    (ht : (∑ i, t i • (V.rationalCohomologyInclusion 1 (q i) : V.complexCohomology 1)) ∈
      V.pureBettiSubspace 1 0) :
    MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, ℂ)
      (HolomorphicPrimitive.CM.Construction.zeroFormScalar (∑ i, t i • f i)) := by
  let a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 :=
    fun i => CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (q i)
  have hsum : (∑ i, t i • a i).val = ∑ i, t i • (a i).val := by
    change (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1).subtype
      (∑ i, t i • a i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact map_smul _ _ _
  have hglobal : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0
      (∑ i, t i • (a i).val).val := by
    rw [← hsum]
    exact CanonicalRealOneForms.CM.Construction.canonicalRational_combination_holomorphic V q t ht
  have hlocal := Intersection.CM.Construction.hasManifoldBidegree_restrict U 1 0 (∑ i, t i • (a i).val) hglobal
  apply HolomorphicPrimitive.CM.Construction.zeroFormScalar_mdifferentiable
  rw [primitive_complex_combination_d U d (fun i => (a i).val) f hf t]
  exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule V.analyticModel U 1 0).toAddSubgroup.zsmul_mem hlocal d

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPeriodPrimitives.CM.Construction
