import OAI.RepresentationTheory.Theta.Geometric.TransformedHyperplaneIso
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation
import OAI.RepresentationTheory.Theta.Geometric.PowerAlgebraization

/-! # Translation Algebraization -/

namespace OAI.RepresentationTheory.Theta.Geometric.TranslationAlgebraization

noncomputable section

/-! A gauged theta translation produces an actual isomorphism of the
translated and original algebraic hyperplane bundles on the abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance translatedThetaModel_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance translatedThetaModel_smooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem thetaTranslation_algebraic_iso {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hFi : Function.Injective F.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (a : Φ.space) (c : Φ.space → ℂ)
    (hc : ∀ z, c z ≠ 0) (hT : ∀ i z, T (F.coordinate i) z = c z ^ F.degree * F.coordinate i (z + a))
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (hA : ∀ u v, e (u + v) = e u * e v)
    (f₀ : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (he₀ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₀ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t)) :
    Nonempty (((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f₀.left (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1)).pullback
      (AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk a))).left).sheaf ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f₀.left (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1)).sheaf) := by
  obtain ⟨f, _hf, he⟩ := (F.withSectionMap T).algebraic_embedding_on_model
    (F.withSectionMap_injective T hFi) (fun p v hv => F.withSectionMap_detects T p v (hFd p v hv)) A e hA
  let τ := AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk a))
  let f₁ := τ ≫ f₀
  have he₁ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₁ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap (t + QuotientAddGroup.mk a)) := by
    intro t
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₀ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map τ (e t)) = _
    rw [AlgebraicTranslation.abelianTranslation_period A e hA, he₀]
  obtain ⟨h⟩ := TransformedHyperplaneIso.transformedThetaHyperplane_iso F T a c hc hT f f₀ f₁ e e.surjective he he₀ he₁
  exact ⟨(Scheme.Modules.pullbackComp τ.left f₀.left).app (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1).sheaf ≪≫ h⟩

end

end OAI.RepresentationTheory.Theta.Geometric.TranslationAlgebraization
