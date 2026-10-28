import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorCoherence

/-! # Tensor Equivalence Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalenceCoherence

noncomputable section

/-! The exact line-bundle tensor equivalence preserves coherent finite type, through its proved comparison with the actual tensor sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lineBundleRightTensor_quasicoherent {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) [M.IsQuasicoherent] :
    ((TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (TensorEquivalence.lineBundleRightTensorEquivalence_objIso L M).symm (TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M L)

theorem lineBundleRightTensor_finiteType {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M).IsFiniteType := by
  have : (Tensor.ProductSheaf.tensorModule M L.sheaf).IsQuasicoherent := TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M L
  have : (Tensor.ProductSheaf.tensorModule M L.sheaf).IsFiniteType := TensorCoherence.tensorModuleRight_lineBundle_finiteType M L
  have : ((TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M).IsQuasicoherent :=
    lineBundleRightTensor_quasicoherent L M
  exact Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso (TensorEquivalence.lineBundleRightTensorEquivalence_objIso L M).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalenceCoherence
