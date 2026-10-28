import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorConstructionAssociativity

/-! # Line Bundle Dual -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard

noncomputable section

/-! The Picard group of isomorphism classes of the actual line bundles used by FiniteDescent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem tensorClass_assoc (q r s : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass q r) s =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass r s) := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      induction s using Quotient.inductionOn with
      | h N => exact Quotient.sound ⟨BinaryTensorConstructionAssociativity.Construction.BinaryTensorAssociativity.iso L.sheaf M.sheaf N.sheaf⟩

/-- Tensor product, the trivial bundle, and the sheaf dual form an abelian group
on line-bundle isomorphism classes. -/
instance : CommGroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) where
  mul := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass
  one := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X
  inv := DualLine.Construction.DualLineBundle.dualClass
  mul_assoc := tensorClass_assoc
  one_mul := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_trivial_left
  mul_one := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_trivial_right
  inv_mul_cancel := DualEvaluationIs.Construction.DualEvaluation.dual_tensorClass
  mul_comm := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_comm

theorem dualClass_dualClass (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    DualLine.Construction.DualLineBundle.dualClass (DualLine.Construction.DualLineBundle.dualClass q) = q :=
  inv_inv q

theorem tensor_cancel_left (q r s : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass q r = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass q s ↔ r = s :=
  mul_left_cancel_iff

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard
