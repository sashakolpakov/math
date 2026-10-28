import OAI.RepresentationTheory.Theta.Geometric.OddEmbedding
import OAI.RepresentationTheory.Theta.Geometric.ChosenAbelianModel
import OAI.RepresentationTheory.Theta.Geometric.AbelianPeriodModelIso

/-! # Two Algebraizations -/

namespace OAI.RepresentationTheory.Theta.Geometric.TwoAlgebraizations.CM.Torus.AutomorphicTheta

noncomputable section

/-! Two specified theta embeddings algebraize on one abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.AbelianPeriodModelIso

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem two_algebraic_embeddings {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hFi : Function.Injective F.projectiveMap)
    (hGi : Function.Injective G.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (hGd : ∀ p v : Φ.space, v ≠ 0 → G.Detects p v) :
    ∃ (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
      (jF : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
      (jG : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension)),
      IsClosedImmersion jF.left ∧ IsClosedImmersion jG.left ∧
      (∀ u v, e (u + v) = e u * e v) ∧
      (∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jF (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t)) ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jG (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension (G.projectiveMap t) := by
  obtain ⟨A, eA, jF, hjF, hA, hF⟩ := ChosenAbelianModel.CM.Torus.Algebraization.ChosenProjectiveModel.abelian_model
    Φ F.projectiveMap (F.projectiveMap_continuous.isClosedEmbedding hFi) (F.projective_all_charts hFd)
  obtain ⟨B, eB, jB, hjB, hB, hG⟩ := ChosenAbelianModel.CM.Torus.Algebraization.ChosenProjectiveModel.abelian_model
    Φ G.projectiveMap (G.projectiveMap_continuous.isClosedEmbedding hGi) (G.projective_all_charts hGd)
  obtain ⟨i, _, hi⟩ := AbelianPeriodModelIso.exists_abelian_period_iso Φ A B eA eB hA hB
  let : IsIso i.hom.left := inferInstanceAs (IsIso (((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso i).hom))
  let : IsClosedImmersion jB.left := hjB
  refine ⟨A, eA, jF, i.hom ≫ jB, hjF, ?_, hA, hF, ?_⟩
  · change IsClosedImmersion (i.hom.left ≫ jB.left)
    infer_instance
  · intro t
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jB (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i.hom (eA t)) = _
    rw [hi, hG]

end

end OAI.RepresentationTheory.Theta.Geometric.TwoAlgebraizations.CM.Torus.AutomorphicTheta
