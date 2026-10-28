import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalIso
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass
import OAI.RepresentationTheory.Theta.Geometric.ProductPicardClass

/-! # Cubical Class -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass

noncomputable section

/-! The native cubical tensor isomorphism gives the cubical identity in
the intrinsic Picard group, including the primitive theta quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem native_cubical_theta_class {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical) (hFi : Function.Injective F.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v)
    (j : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (hj : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t)) :
    CubeClass.nativeCubeDefect A
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback j.left (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1))) = 1 := by
  have H := ProductPicardClass.thetaProduct_classes_eq_of_iso _ _ (CubicalIso.native_cubical_theta_iso F hJ hFi hFd A e he j hj)
  apply (CubeClass.nativeCubeDefect_eq_one_iff A _).mpr
  change (∏ k : Fin 4, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubePositiveMap A k).left
    (Picard.PicardPullback.picardPullback j.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1)))) =
      ∏ k : Fin 3, Picard.PicardPullback.picardPullback (CubeMaps.nativeCubeNegativeMap A k).left
        (Picard.PicardPullback.picardPullback j.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1)))
  simp only [Picard.PicardPullback.picardPullback_comp]
  exact H.symm

theorem native_cubical_theta_quotient_class
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical)
    (hFi : Function.Injective F.projectiveMap) (hGi : Function.Injective G.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (hGd : ∀ p v : Φ.space, v ≠ 0 → G.Detects p v) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v)
    (jF : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (jG : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (hF : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jF (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (hG : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jG (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension (G.projectiveMap t)) :
    CubeClass.nativeCubeDefect A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicQuotient.algebraicThetaQuotient jF.left jG.left)) = 1 :=
  CubeClass.nativeCubeDefect_thetaQuotient A jF.left jG.left
    (native_cubical_theta_class F hJ hFi hFd A e he jF hF)
    (native_cubical_theta_class G hJ hGi hGd A e he jG hG)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass
