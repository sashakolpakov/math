import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorMonoidal

/-! # Binary Tensor Construction Associativity -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorConstructionAssociativity.Construction.BinaryTensorAssociativity

noncomputable section

/-! Associativity of the actual sheafified tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {X : Scheme.{u}}

/-- Reassociate actual tensor sheaves using the proved sheafification comparison. -/
def iso (M N P : X.Modules) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P ≅ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P) :=
  (SheafCohomology.Projective.PullbackTensorMonoidal.Scheme.Modules.nonempty_tensorObj_assoc M N P).some

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorConstructionAssociativity.Construction.BinaryTensorAssociativity
