import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedGroupRigidity

/-! # Dual Family Morphism -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism

noncomputable section

/-! The constructed Picard dual morphism preserves the given group laws
on a reduced noetherian base. Its actual Poincare identity determines it
uniquely over every base, without any reducedness assumption. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction
universe u

variable {S : Scheme.{u}} {g h : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem dualPicardPullback_preserves_given_group [IsReduced S] [IsLocallyNoetherian S] :
    IsMonHom (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f) := by
  apply AbelianScheme.IsogenyQuotient.ReducedGroupRigidity.Construction.pointed_isMonHom_over_reduced_base DB.abelian.scheme DA.abelian.scheme
  simpa only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using
    Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_one DA DB f (𝟙_ (Over S))

theorem eq_dualPicardPullback_of_poincare
    (d : DB.abelian.scheme ⟶ DA.abelian.scheme)
    (hd : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) :
    d = Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f := by
  apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective DA DB.abelian.scheme
  have he := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_poincare DA DB f (𝟙 DB.abelian.scheme)
  rw [Category.id_comp, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply] at he
  have h := congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)) hd
  simpa only [Picard.Homomorphisms.PoincareDetection.Construction.poincareClass, tensorHom_id, id_tensorHom, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf,
    TypeCat.ofHom_apply] using h.trans he.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism
