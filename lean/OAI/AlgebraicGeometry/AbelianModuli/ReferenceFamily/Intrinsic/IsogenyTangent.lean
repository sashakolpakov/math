import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap

/-! # Isogeny Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyTangent.AbelianIntrinsicAdapter

noncomputable section

/-! The native tangent map of the original isogeny is bijective:
its actual differential is the already constructed period-lift isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

local instance nativeIsogenyTangentIntegral (G : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) : IsIntegral G.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral G

theorem nativeIsogenyMap_eq_original : IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyMap A B PA PB f = f.hom := by
  apply Over.OverMorphism.ext
  change (𝟙 A.scheme.left ≫ f.hom.left) ≫ 𝟙 B.scheme.left = f.hom.left
  rw [Category.id_comp, Category.comp_id]

theorem nativeIsogenyComplexEquiv_tangent :
    (IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyComplexEquiv A B PA PB f).toLinearMap = GroupConormalMap.nativeGroupTangentMap f.hom := by
  have h := LiftDifferential.IntrinsicLinearMaps.linearLift_eq_nativeDifferential (IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyMap A B PA PB f)
  have he := congrArg (fun q : A.scheme ⟶ B.scheme => GroupConormalMap.nativeGroupTangentMap q)
    (nativeIsogenyMap_eq_original A B PA PB f)
  exact h.trans he

include PA PB in
theorem nativeGroupTangentMap_isogeny_bijective : Function.Bijective (GroupConormalMap.nativeGroupTangentMap f.hom) := by
  rw [← nativeIsogenyComplexEquiv_tangent A B PA PB f]
  exact (IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyComplexEquiv A B PA PB f).bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyTangent.AbelianIntrinsicAdapter
