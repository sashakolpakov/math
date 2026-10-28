import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupRigidity

/-! # Picard Group Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardGroupMap.Construction.IntrinsicPicardPullback

noncomputable section

/-!
Native Picard pullback preserves the abelian group law over a geometric
field. The origin comparison is already proved; Openness's geometric rigidity
then supplies the group-homomorphism property without a new premise.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

instance dualMap_isMonHom : IsMonHom (PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB) := by
  apply ArithmeticGeometry.OrdinaryLocus.Openness.GroupRigidity.Construction.isMonHom_of_preserves_unit DB.abelian.scheme DA.abelian.scheme (PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB)
  have h := PicardPullback.Construction.IntrinsicPicardPullback.dualMap_one f DA DB (𝟙_ (Over (Spec (.of k))))
  simpa only [Hom.one_def, CategoryTheory.CartesianMonoidalCategory.toUnit_unit,
    Category.id_comp] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardGroupMap.Construction.IntrinsicPicardPullback
