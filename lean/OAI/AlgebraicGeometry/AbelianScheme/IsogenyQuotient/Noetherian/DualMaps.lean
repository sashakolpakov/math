import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback

/-! # Dual Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction

noncomputable section

/-! The original represented dual map preserves the original group
structures over Noetherian bases, including nonreduced bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback

theorem nativeDualMap_congr
    {S : Scheme.{0}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f g : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom g] (hfg : f = g) :
    FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB = FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap g DA DB := by
  subst g
  rfl

theorem noetherian_nativeDualMap_isMonHom
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) :
    IsMonHom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB) := by
  apply GroupRigidity.Construction.pointed_isMonHom_over_noetherian_base DB.abelian.scheme DA.abelian.scheme (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB)
  have h := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_one f DA DB (𝟙_ (Over S))
  simpa only [Hom.one_def, CategoryTheory.CartesianMonoidalCategory.toUnit_unit,
    Category.id_comp] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction
