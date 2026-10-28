import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeMaps
import OAI.RepresentationTheory.Theta.Geometric.Cubical.ProductIso

/-! # Cubical Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalIso

noncomputable section

/-! The original theta hyperplane pullback satisfies the cubical tensor
identity on the actual triple product of its abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem native_cubical_theta_iso {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical) (hFi : Function.Injective F.projectiveMap)
    (hFd : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v)
    (j : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (hj : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t)) :
    Nonempty (ProductFrames.thetaProductModule (fun k => (CubeMaps.nativeCubeNegativeMap A k ≫ j).left) ≅
      ProductFrames.thetaProductModule (fun k => (CubeMaps.nativeCubePositiveMap A k ≫ j).left)) := by
  let C := AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A
  let : IsIntegral C.toOver.left := C.variety.property
  let : Smooth C.toOver.hom := C.variety.presentation.smooth
  obtain ⟨f, _, hf⟩ := CubicalEmbedding.native_common_cubical_embedding F hJ hFi hFd A e he
  apply Cubical.ProductIso.cubical_thetaProduct_iso F hJ f (CubicalEmbedding.triplePeriodDiffeomorph Φ A e)
    (CubicalEmbedding.triplePeriodDiffeomorph Φ A e).surjective hf
    (fun k => CubeMaps.nativeCubePositiveMap A k ≫ j) (fun k => CubeMaps.nativeCubeNegativeMap A k ≫ j)
  · intro k z
    exact (congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
      (CubeMaps.nativeCubePositiveMap_period Φ A e he k z)).trans (hj _)
  · intro k z
    exact (congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
      (CubeMaps.nativeCubeNegativeMap_period Φ A e he k z)).trans (hj _)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalIso
