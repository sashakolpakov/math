import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroDimensionOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseCohomologyModel

/-! # Intrinsic Cohomology Scalar Bridge -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCohomologyScalarBridge.Geometric

noncomputable section

/-! Compare the native extension-of-scalars cohomology model with the
explicit tensor model used by the determinantal dimension open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

def nativeCochainScalarExtensionIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    letI := f.toAlgebra
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj C ≅
      AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel.cochainScalarExtension C A := by
  letI := f.toAlgebra
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    (LinearEquiv.refl A (A ⊗[R] (C.X n))).toModuleIso) ?_
  intro i j hij
  apply ModuleCat.ExtendScalars.hom_ext (f := f) (M := C.X i)
  intro m
  rfl

def nativeCochainScalarHomologyEquiv {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    letI := f.toAlgebra
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj C).homology q ≃ₗ[A]
      (AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel.cochainScalarExtension C A).homology q :=
  (HomologicalComplex.homologyMapIso (nativeCochainScalarExtensionIso f C) q).toLinearEquiv

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCohomologyScalarBridge.Geometric
