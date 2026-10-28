import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalenceCoherence

/-! # Left Tensor Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LeftTensorCoherence

noncomputable section

/-! Coherence of the left line-bundle tensor equivalence. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def lineBundleTensorLeftRightIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M ≅
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M :=
  LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso L M ≪≫ Tensor.ProductSheaf.tensorModuleCommIso L.sheaf M ≪≫
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso L M).symm

theorem lineBundleTensorLeft_quasicoherent {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) [M.IsQuasicoherent] :
    ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (lineBundleTensorLeftRightIso L M).symm (LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_quasicoherent L M)

theorem lineBundleTensorLeft_finiteType {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M).IsFiniteType := by
  have := LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_quasicoherent L M
  have := LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_finiteType L M
  have := lineBundleTensorLeft_quasicoherent L M
  exact Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso (lineBundleTensorLeftRightIso L M).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LeftTensorCoherence
