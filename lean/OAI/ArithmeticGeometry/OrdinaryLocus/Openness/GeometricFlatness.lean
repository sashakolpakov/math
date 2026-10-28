import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalFlatness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Geometric Flatness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricFlatness.Construction

noncomputable section

/-! Descent from geometric closed fibers in the Openness flatness argument. -/

open IsLocalRing TensorProduct
open scoped TensorProduct

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

/-- The local finite-module flatness criterion can be checked after a
faithfully flat extension of the closed fiber ring. -/
theorem flat_of_faithfullyFlat_closedFiber
    (N D : Type*) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [Module.FinitePresentation A N] [Module.Flat R N]
    [CommRing D] [Algebra A D] [Algebra (A ⊗[R] ResidueField R) D]
    [IsScalarTower A (A ⊗[R] ResidueField R) D]
    [Module.FaithfullyFlat (A ⊗[R] ResidueField R) D]
    [Module.Flat D (D ⊗[A] N)] : Module.Flat A N := by
  let C := A ⊗[R] ResidueField R
  have : Module.Flat D (D ⊗[C] (C ⊗[A] N)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A C D D N)
  have : Module.Flat C (C ⊗[A] N) :=
    Module.Flat.of_flat_tensorProduct C (C ⊗[A] N) D
  exact LocalFlatness.Construction.flat_of_flat_residueField_fiber R A N

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A field extension of the residue field suffices to test the closed
fiber in the finite-module local flatness criterion. -/
theorem flat_of_flat_geometric_closedFiber
    (N K : Type*) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [Module.FinitePresentation A N] [Module.Flat R N]
    [Field K] [Algebra (ResidueField R) K]
    [Module.Flat ((A ⊗[R] ResidueField R) ⊗[ResidueField R] K)
      (((A ⊗[R] ResidueField R) ⊗[ResidueField R] K) ⊗[A] N)] :
    Module.Flat A N := by
  let C := A ⊗[R] ResidueField R
  let D := C ⊗[ResidueField R] K
  have : Module.FaithfullyFlat (ResidueField R) K := inferInstance
  have : Module.FaithfullyFlat C D := inferInstance
  exact flat_of_faithfullyFlat_closedFiber R A N D

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricFlatness.Construction
