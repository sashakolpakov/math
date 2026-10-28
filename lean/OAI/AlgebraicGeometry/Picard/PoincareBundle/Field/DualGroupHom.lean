import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SharedDualMapComparison

/-! # Dual Group Hom -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualGroupHom

noncomputable section

/-! The actual Picard dual pullback is a group homomorphism over any field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

variable {k : Type u} [Field k] {a b : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
  (f : A.scheme ⟶ B.scheme) [IsMonHom f] (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

/-- The canonical Picard pullback preserves the origin, so general-field rigidity proves its group compatibility. -/
theorem isMonHom : IsMonHom (DualMaps.representedDualMap
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f) := by
  rw [AbelianScheme.IsogenyQuotient.SharedDualMapComparison.Construction.e45SharedDualMap_eq_native]
  apply GroupRigidity.pointed_isMonHom DB.abelian.scheme DA.abelian.scheme
  have h := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_one f DA DB (𝟙_ (Over (Spec (.of k))))
  simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualGroupHom
