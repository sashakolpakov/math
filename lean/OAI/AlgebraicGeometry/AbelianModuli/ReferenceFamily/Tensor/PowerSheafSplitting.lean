import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerPresheafSplitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorObj

/-! # Power Sheaf Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerSheafSplitting

noncomputable section

/-! Sheafification transports the explicit tensor-power splitting to
the original module sheaves, using the proved tensor comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf

universe u
variable {X : Scheme.{u}}

def tensorPowerSuccSheafIso (L : X.Modules) (n : ℕ) :
    HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L (n + 1) ≅ HilbertConstruction.Tensor.ProductSheaf.tensorModule (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n) L := by
  let sh := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let e₁ := sh.mapIso (PowerPresheafSplitting.tensorPowerSuccPresheafIso L n)
  let e₂ := Classical.choice (SheafCohomology.Projective.PullbackTensorMonoidal.PresheafOfModules.nonempty_sheafify_tensor_idem
    X.sheaf.obj X.ringCatSheaf.property (HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n) L.val)
  exact e₁ ≪≫ e₂ ≪≫ HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n)) (SheafCohomology.Projective.Invertible.Scheme.Modules.sheafifyValIso L)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerSheafSplitting
