import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Addition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorInverse
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AssociatorGluing

/-! # Shift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Shift

noncomputable section

/-! Tensoring a negative twist with a sufficiently positive twist gives the actual twist of the degree difference. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwisting_negative_add_iso (a b : ℕ) :
    ((Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I a).tensor (Bundle.projectiveTwistingBundle I (a + b))).sheaf ≅
      (Bundle.projectiveTwistingBundle I b).sheaf :=
  Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (Addition.projectiveTwistingBundle_addIso I a b) ≪≫
    ((Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I a).tensorAssocIso
      (Bundle.projectiveTwistingBundle I a) (Bundle.projectiveTwistingBundle I b)).symm ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (TensorInverse.projectiveTwisting_negative_positive_iso I a) (Iso.refl _) ≪≫
      Tensor.ProductSheaf.tensorModuleUnitLeftIso _

def projectiveTwisting_negative_sub_iso (a d : ℕ) (h : a ≤ d) :
    ((Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I a).tensor (Bundle.projectiveTwistingBundle I d)).sheaf ≅
      (Bundle.projectiveTwistingBundle I (d - a)).sheaf :=
  Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (eqToIso (congrArg (fun k ↦ (Bundle.projectiveTwistingBundle I k).sheaf)
    (Nat.add_sub_of_le h).symm)) ≪≫ projectiveTwisting_negative_add_iso I a (d - a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Shift
