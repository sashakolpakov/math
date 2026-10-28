import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalFunctoriality

/-! # Conormal Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalAddition

noncomputable section

/-! Conormal pullbacks are additive in actual homomorphisms of
commutative complex groups. All equalities retain the constructed
conormal module and its natural pairing with native tangent vectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear Intrinsic.GroupConormalMap.constructedConormalPullback

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B] [IsCommMonObj B]

theorem nativeConormalDualMap_mul (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] :
    Intrinsic.GroupConormalMap.nativeConormalDualMap (f * g) = Intrinsic.GroupConormalMap.nativeConormalDualMap f + Intrinsic.GroupConormalMap.nativeConormalDualMap g := by
  apply LinearMap.ext
  intro l
  change Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear B
      (Intrinsic.GroupConormalMap.nativeGroupTangentMap (f * g) ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm l)) =
    Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear B (Intrinsic.GroupConormalMap.nativeGroupTangentMap f ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm l)) +
      Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear B (Intrinsic.GroupConormalMap.nativeGroupTangentMap g ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm l))
  rw [Intrinsic.GroupTangentAddition.nativeGroupTangentMap_mul, LinearMap.add_apply, map_add]

theorem nativeConormalDualMap_one : Intrinsic.GroupConormalMap.nativeConormalDualMap (1 : A ⟶ B) = 0 := by
  apply LinearMap.ext
  intro l
  change Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear B
      (Intrinsic.GroupConormalMap.nativeGroupTangentMap (1 : A ⟶ B) ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm l)) = 0
  rw [Intrinsic.GroupTangentAddition.nativeGroupTangentMap_one, LinearMap.zero_apply, map_zero]

theorem constructedConormalPullback_mul (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] :
    Intrinsic.GroupConormalMap.constructedConormalPullback (f * g) = Intrinsic.GroupConormalMap.constructedConormalPullback f + Intrinsic.GroupConormalMap.constructedConormalPullback g := by
  apply LinearMap.ext
  intro z
  apply (Module.evalEquiv ℂ (IdentityConormal.constructedIdentityConormal ℂ A)).injective
  apply LinearMap.ext
  intro l
  change l (Intrinsic.GroupConormalMap.constructedConormalPullback (f * g) z) = l (Intrinsic.GroupConormalMap.constructedConormalPullback f z + Intrinsic.GroupConormalMap.constructedConormalPullback g z)
  rw [Intrinsic.GroupConormalMap.constructedConormalPullback_pairing, map_add, Intrinsic.GroupConormalMap.constructedConormalPullback_pairing,
    Intrinsic.GroupConormalMap.constructedConormalPullback_pairing, nativeConormalDualMap_mul, LinearMap.add_apply, LinearMap.add_apply]

theorem constructedConormalPullback_one : Intrinsic.GroupConormalMap.constructedConormalPullback (1 : A ⟶ B) = 0 := by
  apply LinearMap.ext
  intro z
  apply (Module.evalEquiv ℂ (IdentityConormal.constructedIdentityConormal ℂ A)).injective
  apply LinearMap.ext
  intro l
  change l (Intrinsic.GroupConormalMap.constructedConormalPullback (1 : A ⟶ B) z) = l 0
  rw [Intrinsic.GroupConormalMap.constructedConormalPullback_pairing, nativeConormalDualMap_one, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalAddition
