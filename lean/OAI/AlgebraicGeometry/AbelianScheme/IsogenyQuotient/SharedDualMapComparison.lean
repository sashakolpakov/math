import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualMapComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

/-! # Shared Dual Map Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SharedDualMapComparison.Construction

noncomputable section

/-! The shared PoincareBundle dual map and the original HilbertConstruction dual map use the
same homogeneous line classes and therefore the same morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}

set_option backward.isDefEq.respectTransparency false in
theorem e45SharedHomogeneousPresheafIso_eq_original :
    Picard.PoincareBundle.HomogeneousComparison.homogeneousPresheafIso A.scheme =
      HomogeneousPicardComparison.Construction.e45HomogeneousPicardPresheafIso A := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  rfl

theorem e45SharedHomogeneousSheafIso_eq_original :
    Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso A.scheme =
      HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A := by
  unfold Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso
  rw [e45SharedHomogeneousPresheafIso_eq_original]
  rfl

theorem e45SharedRepresentation_eq_original (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) :
    Picard.PoincareBundle.SharedRepresentation.representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) =
      Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation D := by
  unfold Picard.PoincareBundle.SharedRepresentation.representation Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation
  rw [e45SharedHomogeneousSheafIso_eq_original]
  rfl

theorem e45SharedDualMap_eq_native (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) :
    Picard.PoincareBundle.DualMaps.representedDualMap
      (Picard.PoincareBundle.SharedRepresentation.representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
      (Picard.PoincareBundle.SharedRepresentation.representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f =
        FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  rw [e45SharedRepresentation_eq_original, e45SharedRepresentation_eq_original]
  exact DualMapComparison.Construction.e45RepresentedDualMap_eq_native f DA DB

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SharedDualMapComparison.Construction
