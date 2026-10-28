import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.BilinearSelfSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorSymmetrySections

/-! # Tensor Self Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.TensorSelfSymmetry

noncomputable section

/-! Swapping two copies of one line bundle is the identity on their actual sheaf tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem commIso_self {X : Scheme.{u}} {M : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M M = Iso.refl (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M M) := by
  apply Iso.ext
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M M)).injective
  rw [AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction.tensorModuleCommIso_bilinear, BilinearSelfSymmetry.flip_eq hM]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.TensorSelfSymmetry
