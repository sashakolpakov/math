import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPower
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleDual

/-! # Picard Powers Add -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers

noncomputable section

/-! Tensor powers of actual line bundles agree with powers in their Picard group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem class_add (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (m n : ℕ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (m + n)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower m) * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n) :=
  Quotient.sound ⟨TensorPower.Construction.TensorPowerAddition.iso L.sheaf m n⟩

theorem class_zero (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower 0) = 1 := by
  let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower 0)
  have h : q = q * q := class_add L 0 0
  exact mul_left_cancel (show q * q = q * 1 from h.symm.trans (mul_one q).symm)

theorem class_one (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower 1) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
  Quotient.sound ((L.tensorPower_isTensorPower 1).unique (AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one L.sheaf))

/-- The universal multilinear tensor powers and repeated binary tensor products
have the same actual line-bundle class. -/
theorem class_pow (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (n : ℕ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using class_zero L
  | succ n ih => rw [class_add, ih, class_one, pow_succ]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers
