import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPeriodManifoldImmersion
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM

/-! # Intrinsic Period Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntrinsicPeriodComparison.CM.Abelian.Algebraization

noncomputable section

/-! # CMAbelianVariety: the projective model carries precisely the period torus's complex manifold -/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

variable (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) {n : ℕ}
  (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem biholomorphic
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (j : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion j.left]
    (e : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (e t) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t)) :
    MDifferentiable (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) e ∧
    MDifferentiable (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (𝓘(ℂ, Φ.space)) e.symm := by
  let g : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun x => (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j x)
  have hg : Continuous g := (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.continuous.comp
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map j)
  have hcomm (t) : g (e t) = f t := by
    change (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (e t)) = f t
    rw [he]
    exact (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm_apply_apply (f t)
  have hgd (i : Fin (n + 1)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hx : g x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
      MDifferentiableAt (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
        (𝓘(ℂ, Fin n → ℂ)) (fun y => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) x ∧
      Function.Injective (mfderiv
        (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
        (𝓘(ℂ, Fin n → ℂ)) (fun y => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) x) :=
    ⟨ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap j i hx,
      ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_coordinatesOfSchemeMap_injective j i hx⟩
  constructor
  · exact Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective.Constructions.ProjectiveManifoldComparison.mdifferentiable_of_common_embedding f g hg e e.continuous hcomm
      (fun i x hx => (AlgebraicPeriodManifoldImmersion.CM.Abelian.Algebraization.PeriodManifoldImmersion.projective_chart_data Φ f hd i x hx).1) hgd
  · apply Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective.Constructions.ProjectiveManifoldComparison.mdifferentiable_of_common_embedding g f hf e.symm e.symm.continuous
    · intro x
      exact (hcomm (e.symm x)).symm.trans (congrArg g (e.apply_symm_apply x))
    · exact fun i x hx => (hgd i x hx).1
    · exact AlgebraicPeriodManifoldImmersion.CM.Abelian.Algebraization.PeriodManifoldImmersion.projective_chart_data Φ f hd

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntrinsicPeriodComparison.CM.Abelian.Algebraization
