import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslatedConormal

/-! # Group Conormal Lift Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalLiftNaturality

noncomputable section

/-! The conormal pullback induced by a group morphism agrees with
postcomposition of the actual complex-coefficient infinitesimal lifts,
including their original reference maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest
attribute [local irreducible] IdentityConormalLinear.nativeIdentityConormalLinear

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A)

theorem constructedConormalPullback_lift (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ A →ₗ[ℂ] ℂ) :
    ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B ℂ (c ≫ f)).symm (l.comp (GroupConormalMap.constructedConormalPullback f))).val =
      ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ c).symm l).val ≫ f := by
  let v := (IdentityConormalLinear.nativeIdentityConormalLinear A).symm l
  have hl : IdentityConormalLinear.nativeIdentityConormalLinear A v = l := (IdentityConormalLinear.nativeIdentityConormalLinear A).apply_symm_apply l
  have hA := TranslatedConormal.constructedIdentityLiftConormalEquiv_native_inverse A v c
  rw [hl] at hA
  have hB := TranslatedConormal.constructedIdentityLiftConormalEquiv_native_inverse B (GroupConormalMap.nativeGroupTangentMap f v) (c ≫ f)
  have hb : IdentityConormalLinear.nativeIdentityConormalLinear B (GroupConormalMap.nativeGroupTangentMap f v) = l.comp (GroupConormalMap.constructedConormalPullback f) :=
    GroupConormalMap.nativeConormalDualMap_pairing f l
  rw [hb] at hB
  rw [hB, hA, GroupConormalMap.nativeGroupTangentMap_lift]
  exact (MonObj.mul_comp _ _ f).symm

def groupConormalPostcomposeLift
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ c}) :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ B // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ (c ≫ f)} :=
  ⟨u.val ≫ f, by rw [← Category.assoc, u.property, Category.assoc]⟩

theorem constructedConormalPullback_coordinates
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ c}) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B ℂ (c ≫ f) (groupConormalPostcomposeLift f c u) =
      (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ c u).comp (GroupConormalMap.constructedConormalPullback f) := by
  have h := constructedConormalPullback_lift f c (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ c u)
  rw [(Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ c).symm_apply_apply] at h
  apply (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B ℂ (c ≫ f)).symm.injective
  apply Subtype.ext
  exact (congrArg Subtype.val ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B ℂ (c ≫ f)).symm_apply_apply
    (groupConormalPostcomposeLift f c u))).trans h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalLiftNaturality
