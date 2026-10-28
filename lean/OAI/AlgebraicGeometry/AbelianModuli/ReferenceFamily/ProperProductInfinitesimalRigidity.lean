import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupProductLiftRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IntrinsicCoefficientPoint
import OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction

/-! # Proper Product Infinitesimal Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperProductInfinitesimalRigidity

noncomputable section

/-! Constructing the affine identity chart removes all chart choices
from rigidity of pointed maps on a proper group over dual numbers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine T.left] (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj Z]
    (S : Over Foundations.Scheme.ProjectiveSpace.complexBase) (r : S ⟶ T ⊗ A) [Surjective r.left]

theorem properGroupProduct_reduction_ext (f g : T ⊗ A ⟶ Z) (hfg : r ≫ f = r ≫ g)
    (he : lift (𝟙 T) (toUnit T ≫ η[A]) ≫ f = lift (𝟙 T) (toUnit T ≫ η[A]) ≫ g) : f = g := by
  let D := Constructed.IdentityConormal.selectedAffineIdentityChart ℂ Z
  let x : S ⟶ D.source := toUnit S ≫ Affine.IntrinsicCoefficientPoint.complexCoefficientBaseIso.inv ≫ D.point
  have hi : D.point ≫ D.inclusion = 1 := D.commutes
  have hx : x ≫ D.inclusion = 1 := by
    change (toUnit S ≫ Affine.IntrinsicCoefficientPoint.complexCoefficientBaseIso.inv ≫ D.point) ≫ D.inclusion = 1
    rw [Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one]
  exact GroupProductLiftRigidity.properGroupProduct_lift_ext ℂ A T Z D.source D.inclusion S r x hx f g hfg he

omit [IsAffine T.left] [Surjective r.left] in
theorem properGroupDual_reduction_ext
    (f g : LieRanks.dualNumberTest ℂ ⊗ A ⟶ Z)
    (hfg : RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A ≫ f = RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A ≫ g)
    (he : lift (𝟙 (LieRanks.dualNumberTest ℂ)) (toUnit (LieRanks.dualNumberTest ℂ) ≫ η[A]) ≫ f =
      lift (𝟙 (LieRanks.dualNumberTest ℂ)) (toUnit (LieRanks.dualNumberTest ℂ) ≫ η[A]) ≫ g) : f = g := by
  have : IsAffine (LieRanks.dualNumberTest ℂ).left := inferInstanceAs (IsAffine (Spec (.of (DualNumber ℂ))))
  have : Surjective (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A).left := RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective A
  exact properGroupProduct_reduction_ext A (LieRanks.dualNumberTest ℂ) Z A (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A) f g hfg he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperProductInfinitesimalRigidity
