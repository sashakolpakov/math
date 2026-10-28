import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatnessCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ReductionTensorInjectivity

/-! # Reduced Ideal Tensor Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedIdealTensorCriterion

noncomputable section

/-! The local flatness criterion with an arbitrary proper reduction ideal:
flat reduced module and a zero ideal-tensor obstruction imply flatness. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B]
variable {F : Type w} [AddCommGroup F] [Module B F] [Module.Flat B F]
variable {M : Type v} [AddCommGroup M] [Module B M]

theorem flatPresentation_idealTensor_injective_of_flat_reduction
    (q : F →ₗ[B] M) (hq : Function.Surjective q)
    (I J : Ideal B) (hIJ : I ≤ J)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)]
    (hI : Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M I)) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M J) := by
  have hT : Module.IsTorsionBySet B (B ⧸ J) I :=
    (Module.isTorsionBySet_quotient_iff J I).mpr fun x r hr => J.mul_mem_right x (hIJ hr)
  let : Module (B ⧸ I) (B ⧸ J) := hT.module
  let : IsScalarTower B (B ⧸ I) (B ⧸ J) := hT.isScalarTower
  have hfI : Function.Injective (q.ker.subtype.lTensor (B ⧸ I)) :=
    (IdealTensor.Presentation.presentation_tensor_quotient_injective_iff q hq I).mpr hI
  have hfJ : Function.Injective (q.ker.subtype.lTensor (B ⧸ J)) :=
    Presentations.Flat.ReductionTensorInjectivity.lTensor_injective_of_flat_reduction (B ⧸ I) (B ⧸ J) q.ker.subtype q
      q.exact_subtype_ker_map hq hfI
  exact (IdealTensor.Presentation.presentation_tensor_quotient_injective_iff q hq J).mp hfJ

omit [Module.Flat B F] in
theorem idealTensor_injective_of_flat_reduction
    (I J : Ideal B) (hIJ : I ≤ J)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)]
    (hI : Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M I)) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M J) := by
  let q : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
  exact flatPresentation_idealTensor_injective_of_flat_reduction q
    (Finsupp.linearCombination_id_surjective B M) I J hIJ hI

omit [Module.Flat B F] in
theorem flat_of_idealTensor_injective_of_flat_reduction
    [IsNoetherianRing B] [IsLocalRing B]
    (S : Type w) [CommRing S] [Algebra B S] [IsNoetherianRing S] [IsLocalRing S]
    [IsLocalHom (algebraMap B S)]
    [Module S M] [IsScalarTower B S M] [Module.Finite S M]
    (I : Ideal B) (hIproper : I ≠ ⊤)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)]
    (hI : Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M I)) :
    Module.Flat B M := by
  apply Local.FlatnessCriterion.flat_of_maximalIdeal_tensor_injective S M
  exact idealTensor_injective_of_flat_reduction I (IsLocalRing.maximalIdeal B)
    (IsLocalRing.le_maximalIdeal hIproper) hI

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedIdealTensorCriterion
