import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualGroupLaw

/-! # Dual Group Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualGroupMorphism

noncomputable section

/-! The actual Picard dual morphism preserves the specified dual group
laws over locally noetherian bases, including nonreduced bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem dualPicardPullback_preserves_given_group
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g h : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    IsMonHom (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f) := by
  apply AbelianScheme.IsogenyQuotient.Noetherian.GroupRigidity.Construction.pointed_isMonHom_over_noetherian_base DB.abelian.scheme DA.abelian.scheme
  simpa only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using
    Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_one DA DB f (𝟙_ (Over S))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualGroupMorphism
