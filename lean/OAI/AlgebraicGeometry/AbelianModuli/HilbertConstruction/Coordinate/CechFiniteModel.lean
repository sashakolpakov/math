import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FiniteProjectiveComplex

/-! # Cech Finite Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechFiniteModel

noncomputable section

/-! Construction of a bounded finite projective model for the actual coordinate Čech complex of a flat projective quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem flatProjectiveCoordinate_exists_finite_model
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ (D : CochainComplex (ModuleCat.{u} R) ℕ) (φ : D ⟶ CechComplex.coordinateNonnegativeCechComplex I),
      QuasiIso φ ∧ (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite R (D.X q)) ∧ (∀ q, Module.Projective R (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module R A], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ)) :=
  Bounded.FiniteProjectiveComplex.CochainFiniteModel.exists_finite_projective_complex (CechComplex.coordinateNonnegativeCechComplex I)
    ⟨n + 1, CechComplex.coordinateNonnegativeCechComplex_bounded I⟩
    (CechComplex.coordinateNonnegativeCechComplex_flat I) (CechComplex.coordinateNonnegativeCechComplex_homology_finite I)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechFiniteModel
