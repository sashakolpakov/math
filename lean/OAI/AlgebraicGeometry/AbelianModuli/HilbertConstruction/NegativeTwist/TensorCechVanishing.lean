import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistedCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Shift

/-! # Tensor Cech Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.TensorCechVanishing

noncomputable section

/-! A negative projective twist has vanishing positive Čech cohomology after every sufficiently positive tensor twist. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem negativeTwist_tensorCech_vanish_of_bound (B : ℕ)
    (hB : ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).homology (q + 1)))
    (a d : ℕ) (hd : a + B ≤ d) (q : ℕ) :
    IsZero ((Projective.TwistedCech.projectiveTwistedCech I (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I a).sheaf d).homology (q + 1)) := by
  have ha : a ≤ d := (Nat.le_add_right a B).trans hd
  have hBd : B ≤ d - a := by omega
  let e : Projective.TwistedCech.projectiveTwistedCech I (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I a).sheaf d ≅
      (Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I (d - a)).sheaf :=
    Projective.TwistedCech.projectiveTwistedCechActualIso I _ d ≪≫
      (Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).mapIso (ProjectiveTwisting.Shift.projectiveTwisting_negative_sub_iso I a d ha)
  exact (hB (d - a) hBd q).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (q + 1)).mapIso e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.TensorCechVanishing
