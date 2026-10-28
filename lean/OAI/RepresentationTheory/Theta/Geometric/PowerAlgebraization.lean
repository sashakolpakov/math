import OAI.RepresentationTheory.Theta.Geometric.CommonPower
import OAI.RepresentationTheory.Theta.Geometric.TwoAlgebraizations

/-! # Power Algebraization -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerAlgebraization.CM.Torus.AutomorphicTheta.Family

noncomputable section

/-! Algebraize the common theta power on an already chosen abelian model.
The resulting native projective coordinates retain both original sets of
pure powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.algebraic_embedding_on_model (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (hFi : Function.Injective F.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (hA : ∀ u v, e (u + v) = e u * e v) :
    ∃ f : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension),
      IsClosedImmersion f.left ∧
        ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
          AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t) := by
  obtain ⟨B, eB, jB, hjB, hB, hF⟩ := ChosenAbelianModel.CM.Torus.Algebraization.ChosenProjectiveModel.abelian_model
    Φ F.projectiveMap (F.projectiveMap_continuous.isClosedEmbedding hFi) (F.projective_all_charts hFd)
  obtain ⟨i, _, hi⟩ := AbelianPeriodModelIso.exists_abelian_period_iso Φ A B e eB hA hB
  let : IsIso i.hom.left := inferInstanceAs (IsIso (((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso i).hom))
  let : IsClosedImmersion jB.left := hjB
  refine ⟨i.hom ≫ jB, ?_, ?_⟩
  · change IsClosedImmersion (i.hom.left ≫ jB.left)
    infer_instance
  · intro t
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jB (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i.hom (e t)) = _
    rw [hi, hF]

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower_algebraic_embedding (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hG : 0 < G.degree)
    (hFi : Function.Injective F.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (hA : ∀ u v, e (u + v) = e u * e v) :
    ∃ f : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonPower G).projectiveDimension),
      IsClosedImmersion f.left ∧
        ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
          AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonPower G).projectiveDimension ((F.commonPower G).projectiveMap t) :=
  (F.commonPower G).algebraic_embedding_on_model (F.commonPower_injective G hG hFi)
    (fun p v hv => F.commonPower_detects G hG p v (hFd p v hv)) A e hA

end

end OAI.RepresentationTheory.Theta.Geometric.PowerAlgebraization.CM.Torus.AutomorphicTheta.Family
