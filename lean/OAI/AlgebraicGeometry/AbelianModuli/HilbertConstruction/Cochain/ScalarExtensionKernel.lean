import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroKernel
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive

/-! # Scalar Extension Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel

noncomputable section

/-! Degree-zero cohomology after scalar extension is the kernel of the scalar-extended first differential. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

def moduleScalarExtensionFunctor (A : Type u) [CommRing A] [Algebra R A] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} A where
  obj M := ModuleCat.of A (A ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange A)
  map_id M := ModuleCat.hom_ext (LinearMap.baseChange_id (A := A) (M := M))
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp (A := A) f.hom g.hom)

instance (A : Type u) [CommRing A] [Algebra R A] :
    (moduleScalarExtensionFunctor (R := R) A).Additive where
  map_add := by
    intro M N f g
    exact ModuleCat.hom_ext (LinearMap.baseChange_add (A := A) f.hom g.hom)

def cochainScalarExtension (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (A : Type u) [CommRing A] [Algebra R A] : CochainComplex (ModuleCat.{u} A) ℕ :=
  ((moduleScalarExtensionFunctor A).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

def cochainScalarExtensionZeroKernelEquiv (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (A : Type u) [CommRing A] [Algebra R A] :
    (cochainScalarExtension C A).homology 0 ≃ₗ[A] ((C.d 0 1).hom.baseChange A).ker :=
  ZeroKernel.cochainZeroHomologyKernelEquiv (cochainScalarExtension C A)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel
