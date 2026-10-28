import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ConcreteIdealTensorBoundary

/-! # Base Change Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChangeNaturality

noncomputable section

/-! Vanishing of an actual ideal-tensor obstruction after coefficient
base change forces the corresponding presentation relation to vanish
after reduction by the extended ideal. -/

open TensorProduct

universe u v w t
variable (B : Type u) [CommRing B] (A : Type v) [CommRing A] [Algebra B A]
variable {F : Type w} [AddCommGroup F] [Module B F]
variable {M : Type t} [AddCommGroup M] [Module B M]

theorem idealTensorBaseChangeMap_natural (q : F →ₗ[B] M) (I : Ideal B) (x : F ⊗[B] I) :
    (q.baseChange A).rTensor (I.map (algebraMap B A)) (BaseChange.idealTensorBaseChangeMap B A F I x) =
      BaseChange.idealTensorBaseChangeMap B A M I (q.rTensor I x) := by
  induction x with
  | tmul m r =>
    simp only [BaseChange.idealTensorBaseChangeMap_tmul, LinearMap.rTensor_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

def baseChangePresentationRelationUnit (q : F →ₗ[B] M) :
    q.ker →ₗ[B] (q.baseChange A).ker :=
  (((TensorProduct.mk B A F) 1).comp q.ker.subtype).codRestrict
    ((q.baseChange A).ker.restrictScalars B) (fun z => by
    change q.baseChange A ((1 : A) ⊗ₜ[B] z.val) = 0
    rw [LinearMap.baseChange_tmul, z.property, TensorProduct.tmul_zero])

theorem baseChangePresentationRelationUnit_val (q : F →ₗ[B] M) (z : q.ker) :
    (baseChangePresentationRelationUnit B A q z).val = (1 : A) ⊗ₜ[B] z.val := rfl

theorem baseChange_obstruction_zero_relation_reduction
    (q : F →ₗ[B] M) (hq : Function.Surjective q) (I : Ideal B)
    (y : F ⊗[B] I) (z : q.ker)
    (hz : z.val = Obstruction.idealTensorMultiplication B B F I y)
    (hy : BaseChange.idealTensorBaseChangeMap B A M I (q.rTensor I y) = 0) :
    baseChangePresentationRelationUnit B A q z ⊗ₜ[A]
      (1 : A ⧸ I.map (algebraMap B A)) = 0 := by
  let qA := q.baseChange A
  let IA := I.map (algebraMap B A)
  let yA := BaseChange.idealTensorBaseChangeMap B A F I y
  let zA := baseChangePresentationRelationUnit B A q z
  have hqA : Function.Surjective qA := LinearMap.lTensor_surjective A hq
  have hyA : qA.rTensor IA yA = 0 := (idealTensorBaseChangeMap_natural B A q I y).trans hy
  have hzA : qA.ker.subtype zA = Obstruction.idealTensorMultiplication A A (A ⊗[B] F) IA yA := by
    change (1 : A) ⊗ₜ[B] z.val =
      Obstruction.idealTensorMultiplication A A (A ⊗[B] F) IA yA
    rw [BaseChange.idealTensorBaseChangeMap_multiplication, ← hz]
  have h := ConcreteIdealTensorBoundary.actualIdealTensorBoundary_eq_of_lift qA.ker.subtype qA
    qA.ker.subtype_injective qA.exact_subtype_ker_map hqA IA
    (0 : (Obstruction.idealTensorMultiplication A A (A ⊗[B] M) IA).ker) yA hyA zA hzA
  rw [map_zero] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChangeNaturality
