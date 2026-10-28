import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Cube Tensor Cocycles -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeTensorCocycles.Construction.CubeCech

noncomputable section

/-! The mixed degree-one tensor cocycle calculation for augmented complexes. -/

open scoped TensorProduct

universe u v w v' w'

variable {R : Type u} [CommRing R]
    {C₀ : Type v} {C₁ : Type v'} {D₀ : Type w} {D₁ : Type w'}
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
    [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁]

theorem tensor_map_sub_right (f : C₀ →ₗ[R] C₁) (g h : D₀ →ₗ[R] D₁) :
    TensorProduct.map f (g - h) = TensorProduct.map f g - TensorProduct.map f h := by
  apply TensorProduct.ext'
  intro x y
  simp [TensorProduct.tmul_sub]

theorem tensor_map_sub_left (f g : C₀ →ₗ[R] C₁) (h : D₀ →ₗ[R] D₁) :
    TensorProduct.map (f - g) h = TensorProduct.map f h - TensorProduct.map g h := by
  apply TensorProduct.ext'
  intro x y
  simp [TensorProduct.sub_tmul]

theorem mixed_tensor_cocycle_is_boundary
    (dC : C₀ →ₗ[R] C₁) (dD : D₀ →ₗ[R] D₁)
    (hC : C₁ →ₗ[R] C₀) (hD : D₁ →ₗ[R] D₀)
    (uC : R →ₗ[R] C₀) (uD : R →ₗ[R] D₀)
    (eC : C₀ →ₗ[R] R) (eD : D₀ →ₗ[R] R)
    (hc : hC.comp dC = LinearMap.id - uC.comp eC)
    (hd : hD.comp dD = LinearMap.id - uD.comp eD)
    (dc : dC.comp uC = 0)
    (a : C₁ ⊗[R] D₀) (b : C₀ ⊗[R] D₁)
    (hmix : TensorProduct.map LinearMap.id dD a = TensorProduct.map dC LinearMap.id b)
    (ha : TensorProduct.map LinearMap.id eD a = 0)
    (hb : TensorProduct.map eC LinearMap.id b = 0) :
    ∃ t : C₀ ⊗[R] D₀,
      TensorProduct.map dC LinearMap.id t = a ∧ TensorProduct.map LinearMap.id dD t = b := by
  have ha' : a = TensorProduct.map dC hD b := by
    have h := congrArg (TensorProduct.map (LinearMap.id : C₁ →ₗ[R] C₁) hD) hmix
    simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id, hd] at h
    rw [tensor_map_sub_right] at h
    simp only [TensorProduct.map_id, LinearMap.sub_apply, LinearMap.id_apply] at h
    have hz : TensorProduct.map (LinearMap.id : C₁ →ₗ[R] C₁) (uD.comp eD) a = 0 := by
      have hmap := TensorProduct.map_map (LinearMap.id : C₁ →ₗ[R] C₁) uD LinearMap.id eD a
      simp only [LinearMap.id_comp] at hmap
      exact hmap.symm.trans (by rw [ha, map_zero])
    simpa only [hz, sub_zero] using h
  have hb' : TensorProduct.map hC dD a = b := by
    have h := congrArg (TensorProduct.map hC (LinearMap.id : D₁ →ₗ[R] D₁)) hmix
    simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id, hc] at h
    rw [tensor_map_sub_left] at h
    simp only [TensorProduct.map_id, LinearMap.sub_apply, LinearMap.id_apply] at h
    have hz : TensorProduct.map (uC.comp eC) (LinearMap.id : D₁ →ₗ[R] D₁) b = 0 := by
      have hmap := TensorProduct.map_map uC (LinearMap.id : D₁ →ₗ[R] D₁) eC LinearMap.id b
      simp only [LinearMap.id_comp] at hmap
      exact hmap.symm.trans (by rw [hb, map_zero])
    simpa only [hz, sub_zero] using h
  refine ⟨TensorProduct.map hC LinearMap.id a, ?_, ?_⟩
  · rw [ha']
    simp only [TensorProduct.map_map, LinearMap.id_comp]
    have hdc : dC.comp (hC.comp dC) = dC := by
      rw [hc, LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, dc,
        LinearMap.zero_comp, sub_zero]
    simp only [hdc]
  · simpa only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id] using hb'

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeTensorCocycles.Construction.CubeCech
