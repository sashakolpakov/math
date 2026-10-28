import OAI.RepresentationTheory.Theta.Geometric.InvariantFormsFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Identity Dimension -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.IdentityDimension

noncomputable section

/-! An affine neighborhood of the identity has cotangent dimension equal
to the original smooth group's native complex tangent dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent

theorem affineGamma_smooth (U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine U.left] [Smooth U.hom] :
    Algebra.Smooth ℂ Γ(U.left, ⊤) := by
  let : IsIso (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv.left :=
    inferInstanceAs (IsIso ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).map (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv))
  have hs : Smooth (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ Γ(U.left, ⊤)).hom := by
    rw [← (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv.w]
    infer_instance
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(U.left, ⊤)))) at hs
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)

theorem identityChartCotangent_finiteDimensional (U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffine U.left] [Smooth U.hom] [Algebra Γ(U.left, ⊤) ℂ] :
    FiniteDimensional ℂ (InvariantAlgebraicForms.identityChartCotangent U) := by
  let : Algebra.Smooth ℂ Γ(U.left, ⊤) := affineGamma_smooth U
  change FiniteDimensional ℂ (PointCotangent.pointCotangent ℂ Γ(U.left, ⊤))
  infer_instance

theorem identityChartCotangent_finrank
    {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral G.left] [Smooth G.hom] [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left] (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U)
    [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a) :
    Module.finrank ℂ (InvariantAlgebraicForms.identityChartCotangent U) =
      Module.finrank ℂ (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ) := by
  let : Nonempty U.left := ⟨e.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  let : IsIntegral U.left := isIntegral_of_isOpenImmersion i.left
  let : Smooth U.hom := by rw [← i.w]; infer_instance
  let : Algebra.Smooth ℂ Γ(U.left, ⊤) := affineGamma_smooth U
  let A : CommAlgCat.{0} ℂ := CommAlgCat.of ℂ Γ(U.left, ⊤)
  let p := AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e
  let j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ G := (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv ≫ i
  let : IsIso (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv.left :=
    inferInstanceAs (IsIso ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).map (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv))
  let : IsOpenImmersion j.left := by
    change IsOpenImmersion ((AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv.left ≫ i.left)
    infer_instance
  let T := Fin (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ
  let V := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ
  let d : T →ₗ[ℂ] V :=
    (mfderiv 𝓘(ℂ, T) 𝓘(ℂ, V) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A j) p).toLinearMap
  let hd : T ≃ₗ[ℂ] V := LinearEquiv.ofBijective d (AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A j p)
  calc
    Module.finrank ℂ (InvariantAlgebraicForms.identityChartCotangent U) =
        Module.finrank ℂ (Module.Dual ℂ (PointCotangent.pointCotangent ℂ Γ(U.left, ⊤))) :=
      Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℂ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations p) := (PointCotangentPairing.pointCotangentPairingEquiv p hscalar).finrank_eq.symm
    _ = Module.finrank ℂ T := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations p).finrank_eq.symm
    _ = Module.finrank ℂ V := hd.finrank_eq

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.IdentityDimension
