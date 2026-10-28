import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechUniversalModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelMatrix
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech

/-! # Sections Kernel Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SectionsKernelMatrix

noncomputable section

/-! One finite matrix computes the degree-zero coordinate Čech section module after every coefficient-ring change of a flat projective quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateCechZeroKernelSectionsEquiv :
    ((CechComplex.coordinateNonnegativeCechComplex I).d 0 1).hom.ker ≃ₗ[R]
      HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 :=
  LinearEquiv.ofEq _ _ (congrArg (fun f : (CechComplex.coordinateNonnegativeCechComplex I).X 0 ⟶
    (CechComplex.coordinateNonnegativeCechComplex I).X 1 => f.hom.ker) (CechScalarExtension.coordinateNonnegativeCechComplex_d I 0))

theorem flatProjectiveCoordinate_sections_uniform_matrix [IsNoetherianRing R]
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ (m k : ℕ) (B : Matrix (ULift.{u} (Fin k) ⊕ ULift.{u} (Fin m)) (ULift.{u} (Fin m)) R),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty (HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) A
          (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing A n ⧸ (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal)
          (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)) 0 ≃ₗ[A]
          (Matrix.toLin' (B.map (algebraMap R A))).ker) := by
  obtain ⟨D, φ, _, _, hf, hp, ht⟩ := CechUniversalModel.flatProjectiveCoordinate_exists_universal_finite_model I
  have : Module.Finite R (D.X 0) := hf 0
  have : Module.Projective R (D.X 0) := hp 0
  have : Module.Finite R (D.X 1) := hf 1
  have : Module.Projective R (D.X 1) := hp 1
  refine ⟨HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize R (D.X 0), HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize R (D.X 1),
    HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveKernelMatrix (D.d 0 1).hom, ?_⟩
  intro A _ _
  have : QuasiIso (CechUniversalModel.coordinateCechModelBaseChangeMap I φ A) := ht A
  exact ⟨((CechUniversalModel.coordinateCechModelZeroKernelEquiv I φ A).trans
    (coordinateCechZeroKernelSectionsEquiv (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))).symm.trans
    (HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveKernelMatrixBaseChangeEquiv (D.d 0 1).hom A)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SectionsKernelMatrix
