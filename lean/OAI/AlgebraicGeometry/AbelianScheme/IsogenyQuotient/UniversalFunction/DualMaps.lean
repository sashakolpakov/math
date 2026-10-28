import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualMaps

/-! # Dual Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps.Construction

noncomputable section

/-! The original represented dual map preserves the original group
whenever its source dual has universal global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem universalFunction_nativeDualMap_isMonHom
    {S : Scheme.{0}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (hDB : GlobalFunctions.Construction.HasUniversalGlobalFunctions DB.abelian.scheme) : IsMonHom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB) := by
  apply GroupRigidity.Construction.pointed_isMonHom_of_universal_functions DB.abelian.scheme DA.abelian.scheme hDB (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB)
  have h := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_one f DA DB (𝟙_ (Over S))
  simpa only [Hom.one_def, CategoryTheory.CartesianMonoidalCategory.toUnit_unit,
    Category.id_comp] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps.Construction
