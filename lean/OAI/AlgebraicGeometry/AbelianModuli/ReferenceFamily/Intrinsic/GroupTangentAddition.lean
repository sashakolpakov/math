import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualAddition

/-! # Group Tangent Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentAddition

noncomputable section

/-! Addition of actual homomorphisms of complex groups induces
addition of the native tangent maps. The constant identity homomorphism
induces the zero tangent map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B] [IsCommMonObj B]

local instance nativeTangentOne_isMonHom : IsMonHom (1 : A ⟶ B) :=
  inferInstanceAs (IsMonHom (toUnit A ≫ η[B]))

local instance nativeTangentMul_isMonHom (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) :=
  inferInstanceAs (IsMonHom (lift f g ≫ μ[B]))

theorem nativeGroupTangentMap_mul (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] :
    GroupConormalMap.nativeGroupTangentMap (f * g) = GroupConormalMap.nativeGroupTangentMap f + GroupConormalMap.nativeGroupTangentMap g := by
  apply LinearMap.ext
  intro v
  apply (SchemeDualTangent.nativeSchemeTangentDualEquiv B 1).injective
  apply Subtype.ext
  change (SchemeDualTangent.nativeSchemeTangentDualEquiv B 1 (GroupConormalMap.nativeGroupTangentMap (f * g) v)).val =
    (SchemeDualTangent.nativeSchemeTangentDualEquiv B 1 (GroupConormalMap.nativeGroupTangentMap f v + GroupConormalMap.nativeGroupTangentMap g v)).val
  rw [GroupConormalMap.nativeGroupTangentMap_lift, SchemeDualAddition.nativeSchemeTangentDual_add,
    GroupConormalMap.nativeGroupTangentMap_lift, GroupConormalMap.nativeGroupTangentMap_lift]
  exact MonObj.comp_mul _ f g

theorem nativeGroupTangentMap_one : GroupConormalMap.nativeGroupTangentMap (1 : A ⟶ B) = 0 := by
  have h := nativeGroupTangentMap_mul (1 : A ⟶ B) 1
  rw [one_mul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentAddition
