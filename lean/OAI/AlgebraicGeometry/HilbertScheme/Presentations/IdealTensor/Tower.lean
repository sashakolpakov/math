import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChange

/-! # Tower -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Tower

noncomputable section

/-! Vanishing of an ideal-tensor obstruction persists through a tower
of coefficient algebras, including localization of a finite stage. -/

open TensorProduct

universe u v w t
variable (B : Type u) [CommRing B] (D : Type v) [CommRing D] (A : Type w) [CommRing A]
variable [Algebra B D] [Algebra D A] [Algebra B A] [IsScalarTower B D A]

def idealCoefficientTransition (I : Ideal B) :
    I.map (algebraMap B D) →ₗ[B] I.map (algebraMap B A) where
  toFun r := ⟨algebraMap D A r.val, by
    have h := Ideal.mem_map_of_mem (algebraMap D A) r.property
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq B D A] at h
    exact h⟩
  map_add' r s := Subtype.ext (map_add (algebraMap D A) r.val s.val)
  map_smul' r s := by
    apply Subtype.ext
    exact (IsScalarTower.toAlgHom B D A).toLinearMap.map_smul r s.val

theorem idealCoefficientTransition_comp (I : Ideal B) :
    (idealCoefficientTransition B D A I).comp (BaseChange.idealCoefficientInclusion B D I) =
      BaseChange.idealCoefficientInclusion B A I := by
  ext r
  exact (IsScalarTower.algebraMap_apply B D A r.val).symm

variable (M : Type t) [AddCommGroup M] [Module B M]

theorem idealTensorBaseChange_zero_of_tower (I : Ideal B) (x : M ⊗[B] I)
    (hx : BaseChange.idealTensorBaseChangeMap B D M I x = 0) :
    BaseChange.idealTensorBaseChangeMap B A M I x = 0 := by
  have hD : (BaseChange.idealCoefficientInclusion B D I).lTensor M x = 0 := by
    have h := congrArg (BaseChange.idealTensorBaseChangeComparison B D M I) hx
    simpa only [BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, map_zero] using h
  have hA : (BaseChange.idealCoefficientInclusion B A I).lTensor M x = 0 := by
    rw [← idealCoefficientTransition_comp B D A I, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hD, map_zero]
  apply (BaseChange.idealTensorBaseChangeComparison B A M I).injective
  simpa only [BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, map_zero] using hA

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Tower
