import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness

/-! # Family Frame Uniqueness -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.FamilyFrameUniqueness.Family

noncomputable section

/-! Zero-normalized family frames are unique over arbitrary affine parameters, including nonreduced ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (T : Over (Spec (.of k))) [IsAffine T.left]
  (L M : Line.Bundles.LineBundle (T ⊗ A).left)

/-- The actual zero section detects equality of isomorphisms between family lines. -/
theorem iso_eq_of_zero (d e : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map d.hom =
      (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map e.hom) : d = e := by
  have : IsIso (fst T A).left.appTop := Homomorphisms.ProperGroupFunctions.Construction.properGroupProduct_appTop_isIso A T
  exact PELModuli.IntegralModel.Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.iso_eq_of_section
    (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left
    (congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A)))
    (ConcreteCategory.bijective_of_isIso (fst T A).left.appTop).surjective L.isLine d e h

/-- The prescribed zero frames uniquely fix a trivialization or line-family comparison. -/
theorem normalized_iso_unique
    (eL : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (eM : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (d e : L.sheaf ≅ M.sheaf)
    (hd : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map d.hom ≫ eM.hom = eL.hom)
    (he : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map e.hom ≫ eM.hom = eL.hom) : d = e :=
  iso_eq_of_zero A T L M d e ((cancel_mono eM.hom).mp (hd.trans he.symm))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.FamilyFrameUniqueness.Family
