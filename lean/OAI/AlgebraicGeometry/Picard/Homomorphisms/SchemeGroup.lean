import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorAssociativity
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEvaluation

/-! # Scheme Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup

noncomputable section

/-! The intrinsic Picard group of actual line bundles on a scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

instance lineBundleClassCommGroup (X : Scheme.{u}) : CommGroup (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) where
  mul := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass
  one := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X
  inv := LineBundleDual.Construction.dualLineBundleClass
  mul_assoc := TensorAssociativity.Construction.tensorClass_assoc
  one_mul := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_trivial_left
  mul_one := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_trivial_right
  inv_mul_cancel := LineBundleEvaluation.Construction.tensorClass_dual
  mul_comm := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_comm

theorem lineBundleClass_mul {X : Scheme.{u}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor M) := rfl

theorem lineBundleClass_inv {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)⁻¹ = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (LineBundleDual.Construction.lineBundleDual L) := rfl

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup
