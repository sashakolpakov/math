import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FiniteModuleFieldDetection
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Algebra Surjectivity Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AlgebraSurjectivityFieldDetection

noncomputable section

/-! A finite algebra map is surjective if it is surjective after every
field-valued base change of the ground ring. The proof uses its finite
cokernel over the intermediate algebra, so no finiteness over the ground ring is assumed. -/
open scoped TensorProduct
universe u

theorem finiteAlgebraMap_surjective_of_field_baseChanges
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Module.Finite S T]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R S T))) :
    Function.Surjective (algebraMap S T) := by
  let φ := Algebra.linearMap S T
  let C := T ⧸ φ.range
  let q : T →ₗ[R] C := φ.range.mkQ.restrictScalars R
  have hqφ : q.comp (IsScalarTower.toAlgHom R S T).toLinearMap = 0 := by
    ext s
    exact (Submodule.Quotient.mk_eq_zero φ.range).mpr ⟨s, rfl⟩
  have hC : Subsingleton C := Relative.FiniteModuleFieldDetection.finiteAlgebraModule_subsingleton_of_fieldTensors R S C (by
    intro K _ _
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, rfl⟩ := q.lTensor_surjective K
      (show Function.Surjective q from φ.range.mkQ_surjective) x
    obtain ⟨z, rfl⟩ := h K y
    change (q.lTensor K) ((IsScalarTower.toAlgHom R S T).toLinearMap.lTensor K z) = 0
    rw [← LinearMap.lTensor_comp_apply, hqφ, LinearMap.lTensor_zero, LinearMap.zero_apply])
  intro t
  have ht : φ.range.mkQ t = 0 := @Subsingleton.elim C hC _ _
  exact (Submodule.Quotient.mk_eq_zero φ.range).mp ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AlgebraSurjectivityFieldDetection
