import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MaximalIdealFlatReduction

/-! # Reduced Tensor Flatness Equiv -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedTensorFlatnessEquiv

noncomputable section

/-! Transport reduced flatness through the actual linear equivalences
identifying affine charts with coefficient tensor products. -/

open TensorProduct

universe u v w t
variable {B : Type u} [CommRing B]

theorem quotient_flat_of_reduced_tensor_equiv
    {M : Type v} [AddCommGroup M] [Module B M]
    {S : Type w} [CommRing S] [Algebra B S]
    (e : M ≃ₗ[B] S) (I : Ideal B)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)] :
    Module.Flat (B ⧸ I) (S ⧸ I.map (algebraMap B S)) := by
  have : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] S) :=
    Module.Flat.of_linearEquiv (e.symm.baseChange B (B ⧸ I) S M)
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv

theorem extendedMaximalIdeal_quotient_flat_of_equiv
    (A : Type v) [CommRing A] [Algebra B A]
    (M : Type w) [AddCommGroup M] [Module B M]
    {S : Type t} [CommRing S] [Algebra A S]
    (e : A ⊗[B] M ≃ₗ[A] S) (I : Ideal B) [I.IsMaximal] :
    Module.Flat (A ⧸ I.map (algebraMap B A))
      (S ⧸ (I.map (algebraMap B A)).map (algebraMap A S)) := by
  have := MaximalIdealFlatReduction.extendedMaximalIdeal_reduction_flat A M I
  exact quotient_flat_of_reduced_tensor_equiv e (I.map (algebraMap B A))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedTensorFlatnessEquiv
