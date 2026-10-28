import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd

/-! # Tensor Power Comparison -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPowerComparison.Construction

noncomputable section

/-! Comparison of universal multilinear powers and iterated binary tensor powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def lineBundleTensorPowerComparison {X : Scheme.{u}} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (n : ℕ) → (L.tensorPower n).sheaf ≅ TensorRestriction.Construction.sheafTensorPower L.sheaf n
  | 0 => (show Nonempty ((L.tensorPower 0).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) from
      Quotient.exact (AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_zero L)).some
  | n + 1 => AlgebraicGeometry.Quotients.FiniteDescent.TensorPower.Construction.TensorPowerAddition.iso L.sheaf n 1 ≪≫
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (lineBundleTensorPowerComparison L n)
        (((L.tensorPower_isTensorPower 1).unique (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one L.sheaf)).some)

theorem lineBundleClass_universalTensorPower {X : Scheme.{u}} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (n : ℕ) :
    PicardEq.Construction.lineBundleClass (L.tensorPower n).sheaf (L.tensorPower n).locallyTrivial =
      n • PicardEq.Construction.lineBundleClass L.sheaf L.locallyTrivial :=
  ((PicardEq.Construction.lineBundleClass_eq_iff _ _).mpr ⟨Construction.lineBundleTensorPowerComparison L n⟩).trans
    (PicardEq.Construction.lineBundleClass_tensorPower L.locallyTrivial n)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPowerComparison.Construction
