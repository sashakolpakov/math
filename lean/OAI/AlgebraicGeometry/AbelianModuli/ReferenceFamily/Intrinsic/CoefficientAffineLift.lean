import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientPointDerivations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualOpen

/-! # Coefficient Affine Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CoefficientAffineLift

noncomputable section

/-! The coefficient-linear native affine tangent comparison produces
exactly the actual scheme lift constructed from its derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (B : Type) [CommRing B] [Algebra ℂ B] [Algebra B ℂ] [IsScalarTower ℂ B ℂ]
    [IsDomain B] [Algebra.Smooth ℂ B]

theorem nativeCoefficientAffineLift_eq
    (v : TangentSpace 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) (IsScalarTower.toAlgHom ℂ B ℂ)) :
    ((Affine.DualLiftConormal.affineDualLiftDerivationEquiv ℂ B ℂ).symm (CoefficientPointDerivations.nativeAffineCoefficientDerivationEquiv B v)).val =
      Affine.DualOpen.affineDualSchemeMap (AffineDualPoints.nativeAffineDualPointEquiv (IsScalarTower.toAlgHom ℂ B ℂ) v).val := by
  let f := (Affine.DualLiftConormal.affineDualLiftDerivationEquiv ℂ B ℂ).symm (CoefficientPointDerivations.nativeAffineCoefficientDerivationEquiv B v)
  have hd : Affine.DualLiftConormal.affineDualLiftDerivationEquiv ℂ B ℂ f = CoefficientPointDerivations.nativeAffineCoefficientDerivationEquiv B v :=
    (Affine.DualLiftConormal.affineDualLiftDerivationEquiv ℂ B ℂ).apply_symm_apply _
  have hr := (Affine.DualLiftReduction.affineDualLift_reduction_iff ℂ B ℂ (IsScalarTower.toAlgHom ℂ B ℂ) f.val).mp f.property
  have ha : Affine.OverMorphismAlgebra.affineOverMorphismAlgebra ℂ (DualNumber ℂ) B f.val =
      (AffineDualPoints.nativeAffineDualPointEquiv (IsScalarTower.toAlgHom ℂ B ℂ) v).val := by
    apply AlgHom.ext
    intro b
    apply TrivSqZeroExt.ext
    · exact (AlgHom.congr_fun hr b).trans (AffineDualPoints.nativeAffineDualPoint_fst _ v b).symm
    · exact (Affine.DualLiftConormal.affineDualLiftDerivationEquiv_apply ℂ B ℂ f b).symm.trans
        ((Derivation.congr_fun hd b).trans (CoefficientPointDerivations.nativeAffineCoefficientDerivationEquiv_apply B v b))
  apply Over.OverMorphism.ext
  change f.val.left = Spec.map (CommRingCat.ofHom
    (AffineDualPoints.nativeAffineDualPointEquiv (IsScalarTower.toAlgHom ℂ B ℂ) v).val.toRingHom)
  rw [← Affine.OverMorphismAlgebra.affineOverMorphismAlgebra_spec ℂ (DualNumber ℂ) B f.val, ha]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CoefficientAffineLift
