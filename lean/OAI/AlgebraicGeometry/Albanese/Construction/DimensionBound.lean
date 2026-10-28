import OAI.AlgebraicGeometry.Albanese.Construction.GeneratingForms
import OAI.AlgebraicGeometry.Albanese.Construction.HolomorphicInvariant
import OAI.AlgebraicGeometry.Albanese.Construction.FormsFinite

/-! # Dimension Bound -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.DimensionBound

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [ConnectedSpace X.carrier]
  (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)

/-- Pullback of the invariant holomorphic form associated to a target
covector, as a genuinely closed one-form on the source. -/
def generatedCovectorPullback : Module.Dual ℂ A.variety.analyticModel →ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (GeneratingForms.connectedVariety X).analyticModel (GeneratingForms.connectedVariety X).analyticSpace 1 := by
  let L := (AnalyticPullback.nativePullback a 1).comp
    ((AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1).subtype.comp
      (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace))
  refine L.codRestrict _ ?_
  intro α
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AnalyticPullback.nativePullback a 1
    (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace α).val) = 0
  have hc := AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms_closed
    (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace α).val
    (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace α).property
  have hnat := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map a ∞)
    (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace α).val
  exact hnat.trans ((congrArg (AnalyticPullback.nativePullback a 2) hc).trans (map_zero _))

@[simp]
theorem generatedCovectorPullback_val (α : Module.Dual ℂ A.variety.analyticModel) :
    (generatedCovectorPullback X A a α).val = AnalyticPullback.nativePullback a 1
      (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace α).val := rfl

theorem generatedCovectorPullback_pure (α : Module.Dual ℂ A.variety.analyticModel) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (GeneratingForms.connectedVariety X).analyticModel (GeneratingForms.connectedVariety X).analyticSpace
      1 0 (generatedCovectorPullback X A a α).val.val := by
  rw [generatedCovectorPullback_val]
  exact (HolomorphicInvariant.holomorphicInvariantOneForm_pure A.variety.analyticModel A.variety.analyticSpace α).pullback
    (E := AnalyticPullback.nativeModel X.toOver) (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ∞)

/-- The actual de Rham class of the pulled-back invariant holomorphic form. -/
def generatedCovectorClass : Module.Dual ℂ A.variety.analyticModel →ₗ[ℂ]
    (GeneratingForms.connectedVariety X).deRhamCohomology 1 :=
  (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (GeneratingForms.connectedVariety X).analyticModel (GeneratingForms.connectedVariety X).analyticSpace 1).comp
    (generatedCovectorPullback X A a)

/-- Generation and the compact holomorphic primitive theorem make this
class map injective. -/
theorem generatedCovectorClass_injective
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (hgen : GeneratedClosed.Generates X A a) :
    Function.Injective (generatedCovectorClass X A a) := by
  have hzero (α : Module.Dual ℂ A.variety.analyticModel)
      (hα : generatedCovectorClass X A a α = 0) : α = 0 := by
    have hform := ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.holomorphic_oneForm_eq_zero_of_class_eq_zero
      (generatedCovectorPullback X A a α) (generatedCovectorPullback_pure X A a α) hα
    have hpull : AnalyticPullback.nativePullback a 1
        (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace α).val = 0 := by
      rw [← generatedCovectorPullback_val, hform]
      rfl
    have hinv := GeneratingForms.generating_invariantOneForm_pullback_zero X A a
      (HolomorphicInvariant.holomorphicInvariantOneForm A.variety.analyticModel A.variety.analyticSpace α) x₀ hgen hpull
    apply HolomorphicInvariant.holomorphicInvariantOneForm_injective A.variety.analyticModel A.variety.analyticSpace
    rw [map_zero]
    exact hinv
  intro α β h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, h, sub_self]

/-- All generated abelian targets of the fixed source have dimension
bounded by its finite first complex de Rham dimension. -/
theorem generated_target_dimension_le
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (hgen : GeneratedClosed.Generates X A a) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤
      Module.finrank ℂ ((GeneratingForms.connectedVariety X).deRhamCohomology 1) := by
  let _ := FormsFinite.projective_deRhamCohomology_finite (GeneratingForms.connectedVariety X) 1
  have h := LinearMap.finrank_le_finrank_of_injective (f := generatedCovectorClass X A a)
    (generatedCovectorClass_injective X A a x₀ hgen)
  rwa [Subspace.dual_finrank_eq, A.variety.analyticModel_complex_finrank,
    A.variety.complexDimension_eq_transcendenceDimension] at h

end

end OAI.AlgebraicGeometry.Albanese.Construction.DimensionBound
