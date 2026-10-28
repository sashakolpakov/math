import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechComplexIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadCohomology

/-! # Cech Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechVanishing

noncomputable section

/-! Every positive Čech cohomology group of the actual projective twists vanishes for all sufficiently large twisting degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem positiveTwistCech_eventually_vanish :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).homology
        (q + 1)) := by
  obtain ⟨B, hB⟩ := HilbertScheme.Presentations.Graded.CechVanishing.ProjectiveCech.moduleCech_eventual_exactness (σ := Fin (n + 1)) R
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
  refine ⟨B, fun d hd q ↦ ?_⟩
  let C := HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)
  have hC : C.ExactAt (q + 2) := Coordinate.CechExactness.coordinateCechComplex_exactAt_of_gradedExact I (d : ℤ) (q + 1)
    (hB (d : ℤ) (by exact_mod_cast hd) (q + 2))
  let e : (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).homology
      (q + 1)) ≅ C.homology (q + 2) :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (q + 1)).mapIso
      (CechComplexIsomorphism.positiveTwistCechComplexIso I d) ≪≫ Cochain.HeadCohomology.CochainHead.tailHomologyIso C q
  exact hC.isZero_homology.of_iso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechVanishing
