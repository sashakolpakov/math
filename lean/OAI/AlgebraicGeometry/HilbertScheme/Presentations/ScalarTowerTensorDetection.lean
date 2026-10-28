import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Maps

/-! # Scalar Tower Tensor Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarTowerTensorDetection

noncomputable section

/-! Nakayama detection after quotienting the coefficient ring, for
modules finite over a larger algebra rather than over the coefficient ring. -/

open TensorProduct

universe u v w
variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

theorem finiteAlgebraModule_subsingleton_of_quotientTensor
    (I : Ideal R) (hI : I.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (M : Type w) [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [Module.Finite B M] [Subsingleton ((R ⧸ I) ⊗[R] M)] : Subsingleton M := by
  let : Subsingleton (M ⧸ (I • ⊤ : Submodule R M)) :=
    (quotTensorEquivQuotSMul M I).symm.injective.subsingleton
  have hR : (I • ⊤ : Submodule R M) = ⊤ := Submodule.Quotient.subsingleton_iff.mp inferInstance
  have hB : (⊤ : Submodule B M) ≤ I.map (algebraMap R B) • ⊤ := by
    intro m _
    change m ∈ (I.map (algebraMap R B) • (⊤ : Submodule B M)).restrictScalars R
    rw [Ideal.smul_restrictScalars]
    change m ∈ (I • ⊤ : Submodule R M)
    rw [hR]
    trivial
  have hz : (⊤ : Submodule B M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top hB hI
  apply subsingleton_of_forall_eq 0
  intro m
  have hm : m ∈ (⊤ : Submodule B M) := trivial
  rw [hz] at hm
  exact hm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarTowerTensorDetection
