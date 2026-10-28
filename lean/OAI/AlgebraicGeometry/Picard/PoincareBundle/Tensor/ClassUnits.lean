import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Origin

/-! # Class Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassUnits

noncomputable section

/-! Trivial factors do not change actual line-bundle tensor classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Origin

@[simp]
theorem tensorClass_trivial_left {X : Scheme.{u}} (q : Line.Bundles.LineBundleClass X) :
    LineBundles.tensorClass (Origin.trivialLineClass X) q = q := by
  induction q using Quotient.inductionOn with
  | _ L => exact Quotient.sound ⟨AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso L.sheaf⟩

@[simp]
theorem tensorClass_trivial_right {X : Scheme.{u}} (q : Line.Bundles.LineBundleClass X) :
    LineBundles.tensorClass q (Origin.trivialLineClass X) = q :=
  (LineBundles.tensorClass_comm _ _).trans (tensorClass_trivial_left q)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassUnits
