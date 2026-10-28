import OAI.Geometry.ComplexTorus.RiemannProjectivity.PeriodManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM

/-! # Intrinsic Period Comparison -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPeriodComparison.Constructions

noncomputable section

/-! # RiemannProjectivity: the projective model carries precisely the period torus's complex manifold -/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) {n : ℕ}
  (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem biholomorphic
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (j : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion j.left]
    (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t)) :
    MDifferentiable (𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) e ∧
    MDifferentiable (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)) e.symm := by
  let g : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun x => (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j x)
  have hg : Continuous g := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.continuous.comp
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map j)
  have hcomm (t) : g (e t) = f t := by
    change (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (e t)) = f t
    rw [he]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm_apply_apply (f t)
  have hgd (i : Fin (n + 1)) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hx : g x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
      MDifferentiableAt (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
        (𝓘(ℂ, Fin n → ℂ)) (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) x ∧
      Function.Injective (mfderiv
        (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
        (𝓘(ℂ, Fin n → ℂ)) (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) x) :=
    ⟨AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap j i hx,
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_coordinatesOfSchemeMap_injective j i hx⟩
  constructor
  · exact ManifoldProjective.Constructions.ProjectiveManifoldComparison.mdifferentiable_of_common_embedding f g hg e e.continuous hcomm
      (fun i x hx => (PeriodManifold.Constructions.PeriodManifoldImmersion.projective_chart_data Φ f hd i x hx).1) hgd
  · apply ManifoldProjective.Constructions.ProjectiveManifoldComparison.mdifferentiable_of_common_embedding g f hf e.symm e.symm.continuous
    · intro x
      exact (hcomm (e.symm x)).symm.trans (congrArg g (e.apply_symm_apply x))
    · exact fun i x hx => (hgd i x hx).1
    · exact PeriodManifold.Constructions.PeriodManifoldImmersion.projective_chart_data Φ f hd

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPeriodComparison.Constructions
