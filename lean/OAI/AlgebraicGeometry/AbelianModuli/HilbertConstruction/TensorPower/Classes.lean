import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroTensorPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassMonoid

/-! # Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Powers in the monoid of bundle classes are represented by the constructed tensor-power sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem Line.Bundles.LineBundle.classOf_tensorPower (L : Line.Bundles.LineBundle X) (n : ℕ) :
    Line.Bundles.LineBundle.classOf (L.tensorPower n) = Line.Bundles.LineBundle.classOf L ^ n := by
  induction n with
  | zero => exact Quotient.sound ⟨L.tensorPowerZeroIso⟩
  | succ n ih =>
    have h : Line.Bundles.LineBundle.classOf (L.tensorPower (n + 1)) = Line.Bundles.LineBundle.classOf (L.tensorPower n) * Line.Bundles.LineBundle.classOf (L.tensorPower 1) :=
      Quotient.sound ⟨L.tensorPowerAddIso n 1⟩
    have h₁ : Line.Bundles.LineBundle.classOf (L.tensorPower 1) = Line.Bundles.LineBundle.classOf L := Quotient.sound ⟨L.tensorPowerOneIso⟩
    exact h.trans ((congrArg₂ (fun a b : Line.Bundles.LineBundle.IsoClass X => a * b) ih h₁).trans (pow_succ (Line.Bundles.LineBundle.classOf L) n).symm)

theorem Line.Bundles.LineBundle.iso_tensorPower_of_class_eq (L M : Line.Bundles.LineBundle X) (n : ℕ)
    (h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M ^ n) : Nonempty (L.sheaf ≅ (M.tensorPower n).sheaf) :=
  Quotient.exact (h.trans (Line.Bundles.LineBundle.classOf_tensorPower M n).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
