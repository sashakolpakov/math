import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ProductPeriod
import OAI.RepresentationTheory.Theta.Geometric.CommonCubicalEmbedding

/-! # Cubical Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalEmbedding

noncomputable section

/-! The common cubical theta embedding is algebraized on the actual
triple product of the original abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance nativeCube_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance nativeCube_smooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

def triplePeriodDiffeomorph (Φ : Torus.Data.CM.ProjectivePeriodData) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    Φ.triple.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.triple.space),
      𝓘(ℂ, AlgebraicAction.AbelianModel (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A))⟯
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A).toOver :=
  ProductPeriod.productPeriodDiffeomorph (Φ.product Φ) Φ (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A
    (ProductPeriod.productPeriodDiffeomorph Φ Φ A A e e) e

theorem triplePeriodDiffeomorph_mk (Φ : Torus.Data.CM.ProjectivePeriodData) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (u v w : Φ.space) :
    triplePeriodDiffeomorph Φ A e (QuotientAddGroup.mk ((u, v), w)) =
      lift (lift (e (QuotientAddGroup.mk u)) (e (QuotientAddGroup.mk v)))
        (e (QuotientAddGroup.mk w)) := rfl

theorem triplePeriodDiffeomorph_add (Φ : Torus.Data.CM.ProjectivePeriodData) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) (u v : Φ.triple.periodTorus) :
    triplePeriodDiffeomorph Φ A e (u + v) =
      triplePeriodDiffeomorph Φ A e u * triplePeriodDiffeomorph Φ A e v :=
  ProductPeriod.productPeriodDiffeomorph_add (Φ.product Φ) Φ (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A
    (ProductPeriod.productPeriodDiffeomorph Φ Φ A A e e) e (ProductPeriod.productPeriodDiffeomorph_add Φ Φ A A e e he he) he u v

theorem native_common_cubical_embedding {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical) (hFi : Function.Injective F.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) :
    ∃ f : (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A).toOver ⟶
        Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonTripleCube hJ).projectiveDimension),
      IsClosedImmersion f.left ∧ ∀ t,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (triplePeriodDiffeomorph Φ A e t) =
          AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonTripleCube hJ).projectiveDimension
            ((F.commonTripleCube hJ).projectiveMap t) :=
  F.commonTripleCube_algebraic_embedding hJ hFi hFd (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A)
    (triplePeriodDiffeomorph Φ A e) (triplePeriodDiffeomorph_add Φ A e he)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalEmbedding
