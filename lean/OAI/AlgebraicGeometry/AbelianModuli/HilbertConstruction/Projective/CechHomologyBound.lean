import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCech

/-! # Cech Homology Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechHomologyBound

noncomputable section

/-! Coordinate Čech cohomology vanishes beyond the length of the projective affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCech_homology_isZero (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules)
    (q : ℕ) (hq : n + 1 ≤ q) :
    IsZero (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂
    (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).sc q) (CoefficientCechBounded.projectiveCoefficientCech_bounded I M q hq)

theorem projectiveCech_homology_finite_of_bound (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules)
    (q : ℕ) (hq : n + 1 ≤ q) :
    Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).homology q) := by
  let : Subsingleton (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).homology q) :=
    ModuleCat.subsingleton_of_isZero (projectiveCech_homology_isZero I M q hq)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechHomologyBound
