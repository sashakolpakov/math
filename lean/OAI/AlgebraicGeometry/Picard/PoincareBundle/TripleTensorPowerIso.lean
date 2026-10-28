import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Gluing

/-! # Triple Tensor Power Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TripleTensorPowerIso

noncomputable section

/-! The actual three-factor tensor isomorphism for powers of line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Gluing

variable {X : Scheme.{u}}

/-- Three individual powers identify with the power of their actual tensor product. -/
def iso (L M N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (n : ℕ) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (L.tensorPower n).sheaf (M.tensorPower n).sheaf)
      (N.tensorPower n).sheaf) ≅ (((L.tensor M).tensor N).tensorPower n).sheaf :=
  AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (L.tensorPowerTensorIso M n).symm (Iso.refl _) ≪≫
    ((L.tensor M).tensorPowerTensorIso N n).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TripleTensorPowerIso
