import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Localization Free Refinement -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationFreeRefinement

noncomputable section

/-! A free base change remains free after refining its principal open. -/

open TensorProduct

universe u v
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

theorem free_baseChange_along_tower
    (A C : Type*) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra A C] [IsScalarTower R A C] [Module.Free A (A ⊗[R] M)] :
    Module.Free C (C ⊗[R] M) := by
  let : Module.Free C (C ⊗[A] (A ⊗[R] M)) := inferInstance
  exact Module.Free.of_equiv (AlgebraTensorModule.cancelBaseChange R A C C M)

theorem principalLocalization_free_refinement (s t : R) (hst : s ∣ t)
    [Module.Free (Localization.Away s) (Localization.Away s ⊗[R] M)] :
    Module.Free (Localization.Away t) (Localization.Away t ⊗[R] M) := by
  let A := Localization.Away s
  let C := Localization.Away t
  have ht : IsUnit (algebraMap R C s) := IsLocalization.Away.isUnit_of_dvd t hst
  let φ : A →+* C := IsLocalization.Away.lift s ht
  let : Algebra A C := φ.toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq
    (fun r => (IsLocalization.Away.lift_eq s ht r).symm)
  exact free_baseChange_along_tower M A C

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationFreeRefinement
