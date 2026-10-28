import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SectionsKernelMatrix

/-! # Global Functions Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsMatrix

noncomputable section

/-! One finite matrix computes actual global regular functions after every coefficient-ring change of a flat projective coordinate quotient over a Noetherian ring. -/

open _root_.AlgebraicGeometry

universe u

theorem flatProjectiveCoordinate_globalFunctions_uniform_matrix
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ (m k : ℕ) (B : Matrix (ULift.{u} (Fin k) ⊕ ULift.{u} (Fin m)) (ULift.{u} (Fin m)) R),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty (Coefficient.AlgebraPresheaf.coefficientAlgebraSections
          (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)))) ⊤ ≃ₗ[A]
          (Matrix.toLin' (B.map (algebraMap R A))).ker) := by
  obtain ⟨m, k, B, hB⟩ := Coordinate.SectionsKernelMatrix.flatProjectiveCoordinate_sections_uniform_matrix I
  exact ⟨m, k, B, fun A _ _ => ⟨(GlobalFunctionsCech.coordinateGlobalFunctionsCechEquiv
    (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).trans (Classical.choice (hB A))⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsMatrix
