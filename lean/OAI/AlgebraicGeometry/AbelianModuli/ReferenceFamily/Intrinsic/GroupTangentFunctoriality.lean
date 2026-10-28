import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap

/-! # Group Tangent Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentFunctoriality

noncomputable section

/-! Native tangent maps of actual group morphisms preserve identity
and composition. The proof uses their already established action on
actual dual-number lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]

theorem nativeGroupTangentMap_id : GroupConormalMap.nativeGroupTangentMap (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply (SchemeDualTangent.nativeSchemeTangentDualEquiv A 1).injective
  apply Subtype.ext
  exact (GroupConormalMap.nativeGroupTangentMap_lift (𝟙 A) v).trans (Category.comp_id _)

variable {A} {B C : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B]
    [IsIntegral C.left] [Smooth C.hom] [GrpObj C]
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]

theorem nativeGroupTangentMap_comp :
    GroupConormalMap.nativeGroupTangentMap (f ≫ g) = (GroupConormalMap.nativeGroupTangentMap g).comp (GroupConormalMap.nativeGroupTangentMap f) := by
  apply LinearMap.ext
  intro v
  apply (SchemeDualTangent.nativeSchemeTangentDualEquiv C 1).injective
  apply Subtype.ext
  change (SchemeDualTangent.nativeSchemeTangentDualEquiv C 1 (GroupConormalMap.nativeGroupTangentMap (f ≫ g) v)).val =
    (SchemeDualTangent.nativeSchemeTangentDualEquiv C 1 (GroupConormalMap.nativeGroupTangentMap g (GroupConormalMap.nativeGroupTangentMap f v))).val
  rw [GroupConormalMap.nativeGroupTangentMap_lift, GroupConormalMap.nativeGroupTangentMap_lift, GroupConormalMap.nativeGroupTangentMap_lift]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentFunctoriality
