import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentFunctoriality

/-! # Conormal Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalFunctoriality

noncomputable section

/-! Constructed conormal pullbacks preserve identities and reverse
composition of actual complex group morphisms. Their complex dual maps
retain the corresponding covariant composition law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear Intrinsic.GroupConormalMap.constructedConormalPullback

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]

theorem nativeConormalDualMap_id : Intrinsic.GroupConormalMap.nativeConormalDualMap (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext
  intro l
  change Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A
      (Intrinsic.GroupConormalMap.nativeGroupTangentMap (𝟙 A) ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm l)) = l
  rw [Intrinsic.GroupTangentFunctoriality.nativeGroupTangentMap_id, LinearMap.id_apply, LinearEquiv.apply_symm_apply]

theorem constructedConormalPullback_id : Intrinsic.GroupConormalMap.constructedConormalPullback (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply (Module.evalEquiv ℂ (IdentityConormal.constructedIdentityConormal ℂ A)).injective
  apply LinearMap.ext
  intro l
  change l (Intrinsic.GroupConormalMap.constructedConormalPullback (𝟙 A) z) = l z
  rw [Intrinsic.GroupConormalMap.constructedConormalPullback_pairing, nativeConormalDualMap_id, LinearMap.id_apply]

variable {A} {B C : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B]
    [IsIntegral C.left] [Smooth C.hom] [GrpObj C]
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]

theorem nativeConormalDualMap_comp :
    Intrinsic.GroupConormalMap.nativeConormalDualMap (f ≫ g) = (Intrinsic.GroupConormalMap.nativeConormalDualMap g).comp (Intrinsic.GroupConormalMap.nativeConormalDualMap f) := by
  apply LinearMap.ext
  intro l
  change Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear C
      (Intrinsic.GroupConormalMap.nativeGroupTangentMap (f ≫ g) ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm l)) =
    Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear C
      (Intrinsic.GroupConormalMap.nativeGroupTangentMap g ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear B).symm
        (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear B (Intrinsic.GroupConormalMap.nativeGroupTangentMap f ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm l)))))
  rw [Intrinsic.GroupTangentFunctoriality.nativeGroupTangentMap_comp, LinearMap.comp_apply, LinearEquiv.symm_apply_apply]

theorem constructedConormalPullback_comp :
    Intrinsic.GroupConormalMap.constructedConormalPullback (f ≫ g) = (Intrinsic.GroupConormalMap.constructedConormalPullback f).comp (Intrinsic.GroupConormalMap.constructedConormalPullback g) := by
  apply LinearMap.ext
  intro z
  apply (Module.evalEquiv ℂ (IdentityConormal.constructedIdentityConormal ℂ A)).injective
  apply LinearMap.ext
  intro l
  change l (Intrinsic.GroupConormalMap.constructedConormalPullback (f ≫ g) z) = l (Intrinsic.GroupConormalMap.constructedConormalPullback f (Intrinsic.GroupConormalMap.constructedConormalPullback g z))
  rw [Intrinsic.GroupConormalMap.constructedConormalPullback_pairing, Intrinsic.GroupConormalMap.constructedConormalPullback_pairing,
    Intrinsic.GroupConormalMap.constructedConormalPullback_pairing, nativeConormalDualMap_comp, LinearMap.comp_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalFunctoriality
