import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechFiniteModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechScalarExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ExtensionQuasiIso

/-! # Cech Universal Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechUniversalModel

noncomputable section

/-! The finite projective coordinate model computes the actual extended-quotient Čech complex over every coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
variable {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ CechComplex.coordinateNonnegativeCechComplex I)

def coordinateCechModelBaseChangeMap (A : Type u) [CommRing A] [Algebra R A] :
    Cochain.ScalarExtensionKernel.cochainScalarExtension D A ⟶ CechComplex.coordinateNonnegativeCechComplex (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) :=
  ((Cochain.ScalarExtensionKernel.moduleScalarExtensionFunctor A).mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫
    (CechScalarExtension.coordinateCechScalarExtensionIso (A := A) I).hom

theorem coordinateCechModelBaseChangeMap_quasiIso
    (h : ∀ (B : Type u) [AddCommGroup B] [Module R B], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))
    (A : Type u) [CommRing A] [Algebra R A] : QuasiIso (coordinateCechModelBaseChangeMap I φ A) := by
  have hp : QuasiIso (((Cochain.ScalarExtensionKernel.moduleScalarExtensionFunctor (R := R) A).mapHomologicalComplex
    (ComplexShape.up ℕ)).map φ) := Scalar.ExtensionQuasiIso.scalarExtension_quasiIso_of_universal_tensor A φ h
  have hi : QuasiIso (CechScalarExtension.coordinateCechScalarExtensionIso (A := A) I).hom :=
    quasiIso_of_isIso (CechScalarExtension.coordinateCechScalarExtensionIso (A := A) I).hom
  exact quasiIso_comp (hφ := hp) (hφ' := hi)
    (((Cochain.ScalarExtensionKernel.moduleScalarExtensionFunctor A).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
    (CechScalarExtension.coordinateCechScalarExtensionIso (A := A) I).hom

theorem flatProjectiveCoordinate_exists_universal_finite_model [IsNoetherianRing R]
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ (D : CochainComplex (ModuleCat.{u} R) ℕ) (φ : D ⟶ CechComplex.coordinateNonnegativeCechComplex I),
      QuasiIso φ ∧ (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite R (D.X q)) ∧ (∀ q, Module.Projective R (D.X q)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], QuasiIso (coordinateCechModelBaseChangeMap I φ A)) := by
  obtain ⟨D, φ, hφ, hb, hf, hp, ht⟩ := CechFiniteModel.flatProjectiveCoordinate_exists_finite_model I
  exact ⟨D, φ, hφ, hb, hf, hp, fun A _ _ => coordinateCechModelBaseChangeMap_quasiIso I φ ht A⟩

def coordinateCechModelZeroKernelEquiv
    (A : Type u) [CommRing A] [Algebra R A] [QuasiIsoAt (coordinateCechModelBaseChangeMap I φ A) 0] :
    ((D.d 0 1).hom.baseChange A).ker ≃ₗ[A]
      ((CechComplex.coordinateNonnegativeCechComplex (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).d 0 1).hom.ker :=
  Cochain.ZeroKernel.cochainZeroKernelEquivOfQuasiIso (coordinateCechModelBaseChangeMap I φ A)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechUniversalModel
