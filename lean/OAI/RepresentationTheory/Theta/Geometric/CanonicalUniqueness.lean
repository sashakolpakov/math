import OAI.RepresentationTheory.Theta.Geometric.AlbaneseFormFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.ComponentFormFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.SmoothPullbackFaithfulness
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

/-! # Canonical Uniqueness -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual canonical theta condition determines its Albanese lift
uniquely, using the genuine period differential and complementary components. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms
open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.canonicalThetaLift_principal_unique (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (Θ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (hΨ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ)
    (φ : D.sphericalInputs) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) (D.pel.albanesePullback hg (Θ φ)) =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) (D.pel.albanesePullback hg (Ψ φ)) := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  have hd (x : D.domain) : Function.Surjective
      (mfderiv 𝓘(ℝ, LinearTheta.BallCoordinates) 𝓘(ℝ, X.analyticModel) cover x) := by
    intro v
    obtain ⟨u, hu⟩ := (hcover.2.2.2.1 x).surjective v
    exact ⟨u, (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex
      (hc.of_le (by simp)).contMDiffAt u).trans hu⟩
  have hp : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety D hg Θ j X component φ) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety D hg Ψ j X component φ) := by
    apply SmoothPullbackFaithfulness.smoothOneForm_eq_of_preferredChart
    intro x u
    exact (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety_covector D hg Θ j X component cover hcover hΘ φ x u).trans
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety_covector D hg Ψ j X component cover hcover hΨ φ x u).symm
  have hs := SmoothPullbackFaithfulness.smoothFormPullback_injective cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc) hcover.1 hd 1 hp
  have ha := AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness.globalSmoothForm_injective X.toOver hs
  change AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
      (D.pel.albanesePullback hg (Θ φ)) =
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
      (D.pel.albanesePullback hg (Ψ φ)) at ha
  have he := congrArg (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback component.inv) ha
  have hmap : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback component.inv ∘ₗ
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j) =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) := by
    rw [← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, Iso.inv_hom_id_assoc]
  change (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback component.inv ∘ₗ
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j))
      (D.pel.albanesePullback hg (Θ φ)) =
    (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback component.inv ∘ₗ
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j))
      (D.pel.albanesePullback hg (Ψ φ)) at he
  rw [hmap] at he
  exact he

theorem Data.ActiveHeckeThetaData.canonicalThetaLift_unique (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (Θ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (hΨ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ) : Ψ = Θ := by
  apply LinearMap.ext
  intro φ
  apply D.albanesePullback_injective hg
  apply D.componentForms_jointly_injective hg
  intro i
  by_cases hi : i = j
  · subst i
    exact (D.canonicalThetaLift_principal_unique hg j X component cover hcover Θ Ψ hΘ hΨ φ).symm
  · exact (hΨ.2.2 i hi φ).trans (hΘ.2.2 i hi φ).symm

end

end OAI.RepresentationTheory.Theta.Geometric
