import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition

/-! # Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Addition

noncomputable section

/-! Adding projective twisting degrees is the actual tensor product of the constructed twisting sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwistingBundle_addIso (a b : ℕ) :
    (Bundle.projectiveTwistingBundle I (a + b)).sheaf ≅
      ((Bundle.projectiveTwistingBundle I a).tensor (Bundle.projectiveTwistingBundle I b)).sheaf :=
  (TensorPowers.projectiveTwistingBundle_tensorPowerIso I (a + b)).symm ≪≫
    (Bundle.projectiveTwistingBundle I 1).tensorPowerAddIso a b ≪≫
      Tensor.ProductSheaf.tensorModuleCongr (TensorPowers.projectiveTwistingBundle_tensorPowerIso I a)
        (TensorPowers.projectiveTwistingBundle_tensorPowerIso I b)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Addition
