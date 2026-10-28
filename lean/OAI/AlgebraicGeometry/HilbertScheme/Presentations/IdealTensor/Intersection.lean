import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Obstruction
import Mathlib.LinearAlgebra.Prod

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Intersection

noncomputable section

/-! Ideal-tensor obstructions lift to an intersection whenever multiplication
on the sum ideal is injective. This is the diagram chase used in the local
flatness criterion. -/

open TensorProduct

universe u v
variable {B : Type u} [CommRing B]
variable (M : Type v) [AddCommGroup M] [Module B M]

def idealIntersectionDifference (I J : Ideal B) : ↥(I ⊓ J) →ₗ[B] I × J :=
  (Submodule.inclusion inf_le_left).prod (-Submodule.inclusion inf_le_right)

def idealSumAddition (I J : Ideal B) : I × J →ₗ[B] ↥(I ⊔ J) :=
  (Submodule.inclusion le_sup_left).coprod (Submodule.inclusion le_sup_right)

theorem idealSumAddition_surjective (I J : Ideal B) :
    Function.Surjective (idealSumAddition I J) := by
  intro x
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp x.property
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem idealIntersectionDifference_exact (I J : Ideal B) :
    Function.Exact (idealIntersectionDifference I J) (idealSumAddition I J) := by
  intro x
  constructor
  · intro hx
    have hsum : x.1.val + x.2.val = 0 := congrArg Subtype.val hx
    have heq : x.1.val = -x.2.val := eq_neg_of_add_eq_zero_left hsum
    let a : ↥(I ⊓ J) := ⟨x.1.val, x.1.property, heq ▸ J.neg_mem x.2.property⟩
    refine ⟨a, Prod.ext rfl ?_⟩
    apply Subtype.ext
    change -x.1.val = x.2.val
    rw [heq, neg_neg]
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    exact add_neg_cancel a.val

theorem idealTensorMultiplication_inclusion (I J : Ideal B) (h : I ≤ J)
    (x : M ⊗[B] I) :
    Obstruction.idealTensorMultiplication B B M J ((Submodule.inclusion h).lTensor M x) =
      Obstruction.idealTensorMultiplication B B M I x := by
  induction x with
  | tmul m r => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem idealTensorObstruction_lifts_to_intersection (I J : Ideal B)
    (hIJ : Function.Injective (Obstruction.idealTensorMultiplication B B M (I ⊔ J)))
    (x : M ⊗[B] I) (hx : Obstruction.idealTensorMultiplication B B M I x = 0) :
    ∃ y : M ⊗[B] ↥(I ⊓ J), (Submodule.inclusion inf_le_left).lTensor M y = x := by
  let a := idealIntersectionDifference I J
  let b := idealSumAddition I J
  let e : I →ₗ[B] I × J := LinearMap.inl B I J
  let p : I × J →ₗ[B] I := LinearMap.fst B I J
  have hbe : b.comp e = Submodule.inclusion le_sup_left := by
    ext r
    exact add_zero r.val
  have hpa : p.comp a = Submodule.inclusion inf_le_left := rfl
  have hpe : p.comp e = LinearMap.id := rfl
  have hz : b.lTensor M (e.lTensor M x) = 0 := by
    apply hIJ
    rw [map_zero]
    change Obstruction.idealTensorMultiplication B B M (I ⊔ J)
      ((b.lTensor M).comp (e.lTensor M) x) = 0
    rw [← LinearMap.lTensor_comp, hbe]
    exact (idealTensorMultiplication_inclusion M I (I ⊔ J) le_sup_left x).trans hx
  obtain ⟨y, hy⟩ := (lTensor_exact M (idealIntersectionDifference_exact I J)
    (idealSumAddition_surjective I J) (e.lTensor M x)).mp hz
  refine ⟨y, ?_⟩
  have h := congrArg (p.lTensor M) hy
  change (p.lTensor M).comp (a.lTensor M) y = (p.lTensor M).comp (e.lTensor M) x at h
  simpa only [← LinearMap.lTensor_comp, hpa, hpe, LinearMap.lTensor_id,
    LinearMap.id_apply] using h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Intersection
