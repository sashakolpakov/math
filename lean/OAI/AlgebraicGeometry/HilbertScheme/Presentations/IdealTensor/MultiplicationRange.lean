import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChangeNaturality
import Mathlib.RingTheory.Ideal.Operations

/-! # Multiplication Range -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.MultiplicationRange

noncomputable section

/-! The image of ideal-tensor multiplication is the actual ideal multiple.
This identifies precisely which old presentation relations die modulo the
extended ideal once their tensor obstructions vanish. -/

open TensorProduct

universe u v w t
variable {B : Type u} [CommRing B]
variable (M : Type v) [AddCommGroup M] [Module B M]

theorem idealTensorMultiplication_range (I : Ideal B) :
    (Obstruction.idealTensorMultiplication B B M I).range = I • (⊤ : Submodule B M) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul m r => exact Submodule.smul_mem_smul r.property Submodule.mem_top
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro r hr m _
    exact ⟨m ⊗ₜ[B] (⟨r, hr⟩ : I), rfl⟩

variable {M}
variable {F : Type w} [AddCommGroup F] [Module B F]

theorem idealTensorMultiplication_natural (q : F →ₗ[B] M) (I : Ideal B) (x : F ⊗[B] I) :
    Obstruction.idealTensorMultiplication B B M I (q.rTensor I x) = q (Obstruction.idealTensorMultiplication B B F I x) := by
  induction x with
  | tmul m r => exact (q.map_smul r.val m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem baseChange_relation_reduction_zero_of_ideal_mem
    (A : Type t) [CommRing A] [Algebra B A]
    (q : F →ₗ[B] M) (hq : Function.Surjective q) (I : Ideal B)
    (hzero : ∀ x : (Obstruction.idealTensorMultiplication B B M I).ker,
      BaseChange.idealTensorBaseChangeMap B A M I x.val = 0)
    (z : q.ker) (hz : z.val ∈ I • (⊤ : Submodule B F)) :
    BaseChangeNaturality.baseChangePresentationRelationUnit B A q z ⊗ₜ[A]
      (1 : A ⧸ I.map (algebraMap B A)) = 0 := by
  obtain ⟨y, hy⟩ : z.val ∈ (Obstruction.idealTensorMultiplication B B F I).range := by
    rwa [idealTensorMultiplication_range]
  have hx : Obstruction.idealTensorMultiplication B B M I (q.rTensor I y) = 0 := by
    rw [idealTensorMultiplication_natural, hy]
    exact z.property
  exact BaseChangeNaturality.baseChange_obstruction_zero_relation_reduction B A q hq I y z hy.symm
    (hzero ⟨q.rTensor I y, hx⟩)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.MultiplicationRange
