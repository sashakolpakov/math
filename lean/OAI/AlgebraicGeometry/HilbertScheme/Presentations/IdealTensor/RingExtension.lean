import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.FlatCoefficientExtension
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.MultiplicationRange

/-! # Ring Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.RingExtension

noncomputable section

/-! Transfer ideal-tensor injectivity across module isomorphisms and
flat extensions of a coefficient algebra. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B]

theorem idealTensorMultiplication_injective_of_equiv
    {M : Type v} [AddCommGroup M] [Module B M]
    {N : Type w} [AddCommGroup N] [Module B N]
    (e : M ≃ₗ[B] N) (I : Ideal B)
    (h : Function.Injective (Obstruction.idealTensorMultiplication B B M I)) :
    Function.Injective (Obstruction.idealTensorMultiplication B B N I) := by
  intro x y hxy
  apply (e.symm.rTensor I).injective
  apply h
  change Obstruction.idealTensorMultiplication B B M I (e.symm.toLinearMap.rTensor I x) =
    Obstruction.idealTensorMultiplication B B M I (e.symm.toLinearMap.rTensor I y)
  rw [MultiplicationRange.idealTensorMultiplication_natural, MultiplicationRange.idealTensorMultiplication_natural]
  exact congrArg e.symm hxy

theorem idealTensorMultiplication_ring_flat_extension
    (S : Type v) [CommRing S] [Algebra B S]
    (T : Type w) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower B S T]
    [Module.Flat S T] (I : Ideal B)
    (h : Function.Injective (Obstruction.idealTensorMultiplication B B S I)) :
    Function.Injective (Obstruction.idealTensorMultiplication B B T I) := by
  have ht : Function.Injective (Obstruction.idealTensorMultiplication B B (T ⊗[S] S) I) :=
    FlatCoefficientExtension.idealTensorMultiplication_injective_of_flat_extension B S T S I h
  exact idealTensorMultiplication_injective_of_equiv
    ((AlgebraTensorModule.rid S T T).restrictScalars B) I ht

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.RingExtension
