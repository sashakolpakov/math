import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity

/-! # Chern Pullback Laws -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChernPullbackLaws

noncomputable section

/-! Composition and identity for the actual native scheme Chern pullbacks. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity

theorem nativeChernPullback_comp {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : Y.toOver ⟶ Z.toOver) (c : Z.rationalCohomology 2) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.nativeChernPullback f (AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.nativeChernPullback g c) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.nativeChernPullback (f ≫ g) c := by
  have he : TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f) ≫
      TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous g) =
        TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (f ≫ g)) := by
    apply TopCat.ext
    intro p
    exact (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp f g p).symm
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))
      (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous g)) 2) c
  rw [he] at h
  exact h.symm

theorem nativeChernPullback_id (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (c : X.rationalCohomology 2) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.nativeChernPullback (𝟙 X.toOver) c = c := by
  have he : TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (𝟙 X.toOver)) =
      𝟙 (TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) := by
    apply TopCat.ext
    intro p
    exact Category.comp_id p
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (𝟙 X.toOver))) 2 c = c
  rw [he, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChernPullbackLaws
