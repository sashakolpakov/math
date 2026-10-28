import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationBaseChangeCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.MultiplicationRange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorUnitMap

/-! # Ideal Obstruction Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealObstructionBaseChange

noncomputable section

/-! If the old maximal-ideal tensor obstructions vanish after base change,
the multiplication map for the extended ideal is injective. -/

open TensorProduct

universe u v w t
variable {B : Type u} [CommRing B] (A : Type v) [CommRing A] [Algebra B A]
variable {F : Type w} [AddCommGroup F] [Module B F] [Module.Flat B F]
variable {M : Type t} [AddCommGroup M] [Module B M]

theorem flatPresentation_baseChange_maximalIdeal_injective
    (q : F →ₗ[B] M) (hq : Function.Surjective q) (I : Ideal B) [I.IsMaximal]
    (hzero : ∀ x : (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker,
      IdealTensor.BaseChange.idealTensorBaseChangeMap B A M I x.val = 0) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication A A (A ⊗[B] M) (I.map (algebraMap B A))) := by
  let qA := q.baseChange A
  let IA := I.map (algebraMap B A)
  let N := (A ⧸ IA) ⊗[A] qA.ker
  have hg (z : q.ker) (hz : z.val ∈ I • (⊤ : Submodule B F)) :
      Quotient.TensorUnitMap.quotientTensorUnitMap qA.ker IA (IdealTensor.BaseChangeNaturality.baseChangePresentationRelationUnit B A q z) = 0 := by
    have ht := IdealTensor.MultiplicationRange.baseChange_relation_reduction_zero_of_ideal_mem (B := B) A q hq I hzero z hz
    have ht' := congrArg (TensorProduct.comm A qA.ker (A ⧸ IA)) ht
    simpa only [TensorProduct.comm_tmul, map_zero] using! ht'
  exact RelationBaseChangeCriterion.baseChange_idealTensor_injective_of_residue_relations (B := B) A
    (F := F) (M := M) (N := N) q hq I (Quotient.TensorUnitMap.quotientTensorUnitMap (B := A) qA.ker IA)
    (Quotient.TensorUnitMap.quotientTensorUnitMap_ker (B := A) qA.ker IA) (Quotient.TensorUnitMap.quotientTensor_isTorsionBySet (B := A) qA.ker IA) hg

omit [Module.Flat B F] in
theorem baseChange_maximalIdeal_injective_of_obstructions_zero
    (I : Ideal B) [I.IsMaximal]
    (hzero : ∀ x : (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker,
      IdealTensor.BaseChange.idealTensorBaseChangeMap B A M I x.val = 0) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication A A (A ⊗[B] M) (I.map (algebraMap B A))) := by
  let q : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
  exact flatPresentation_baseChange_maximalIdeal_injective A q
    (Finsupp.linearCombination_id_surjective B M) I hzero

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealObstructionBaseChange
