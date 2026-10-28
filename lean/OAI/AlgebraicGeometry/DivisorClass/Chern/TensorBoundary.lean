import OAI.AlgebraicTopology.Kunneth.TensorHomologyD

/-! # Tensor Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorBoundary

noncomputable section

/-!
# ChernClass: the actual tensor differential on chain representatives

These formulas retain the native total-complex sign. They apply in every
degree, including a point or an interval crossed with a filling chain.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type} [Field k]
variable (C D : ChainComplex (ModuleCat.{0} k) ℕ)

theorem tensorBoundary_positive (p q : ℕ) :
    ιTensorObj C D (p + 1) (q + 1) (p + 1 + (q + 1)) rfl ≫
        (C ⊗ D).d (p + 1 + (q + 1)) (p + (q + 1)) =
      (C.d (p + 1) p ⊗ₘ 𝟙 (D.X (q + 1))) ≫
        ιTensorObj C D p (q + 1) (p + (q + 1)) rfl +
      (-1 : ℤˣ) ^ (p + 1) •
        ((𝟙 (C.X (p + 1)) ⊗ₘ D.d (q + 1) q) ≫
          ιTensorObj C D (p + 1) q (p + (q + 1)) (by omega)) := by
  change ιMapBifunctor C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    (p + 1) (q + 1) (p + 1 + (q + 1)) rfl ≫
      (mapBifunctor C D (curriedTensor (ModuleCat.{0} k))
        (ComplexShape.down ℕ)).d _ _ = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq C D _ _ (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)
      (q + 1) (p + (q + 1)) rfl,
    mapBifunctor.d₂_eq C D _ _ (p + 1)
      (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl)
      (p + (q + 1)) (by change p + 1 + q = p + (q + 1); omega)]
  change (1 : ℤˣ) • ((C.d (p + 1) p ▷ D.X (q + 1)) ≫ _) +
    (-1 : ℤˣ) ^ (p + 1) • ((C.X (p + 1) ◁ D.d (q + 1) q) ≫ _) = _
  rw [one_smul, tensorHom_id, id_tensorHom]

theorem tensorBoundary_leftZero (q : ℕ) :
    ιTensorObj C D 0 (q + 1) (q + 1) (by omega) ≫ (C ⊗ D).d (q + 1) q =
      (𝟙 (C.X 0) ⊗ₘ D.d (q + 1) q) ≫ ιTensorObj C D 0 q q (by omega) := by
  change ιMapBifunctor C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    0 (q + 1) (q + 1) _ ≫
      (mapBifunctor C D (curriedTensor (ModuleCat.{0} k))
        (ComplexShape.down ℕ)).d _ _ = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂, mapBifunctor.d₁_eq_zero C D _ _ 0 (q + 1) q (by simp),
    zero_add, mapBifunctor.d₂_eq C D _ _ 0
      (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) q (by change 0 + q = q; omega)]
  change ((-1 : ℤˣ) ^ 0) • ((C.X 0 ◁ D.d (q + 1) q) ≫ _) = _
  rw [pow_zero, one_smul, id_tensorHom]

theorem tensorBoundary_rightZero (p : ℕ) :
    ιTensorObj C D (p + 1) 0 (p + 1) (by omega) ≫ (C ⊗ D).d (p + 1) p =
      (C.d (p + 1) p ⊗ₘ 𝟙 (D.X 0)) ≫ ιTensorObj C D p 0 p (by omega) := by
  change ιMapBifunctor C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    (p + 1) 0 (p + 1) _ ≫
      (mapBifunctor C D (curriedTensor (ModuleCat.{0} k))
        (ComplexShape.down ℕ)).d _ _ = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq C D _ _ (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)
      0 p (by change p + 0 = p; omega),
    mapBifunctor.d₂_eq_zero C D _ _ (p + 1) 0 p (by simp), add_zero]
  change (1 : ℤˣ) • ((C.d (p + 1) p ▷ D.X 0) ≫ _) = _
  rw [one_smul, tensorHom_id]

theorem tensorBoundary_point_apply (q : ℕ) (x : C.X 0) (y : D.X (q + 1)) :
    (C ⊗ D).d (q + 1) q
      (ιTensorObj C D 0 (q + 1) (q + 1) (by omega) (x ⊗ₜ[k] y)) =
      ιTensorObj C D 0 q q (by omega) (x ⊗ₜ[k] D.d (q + 1) q y) := by
  have h := ConcreteCategory.congr_hom (tensorBoundary_leftZero C D q) (x ⊗ₜ[k] y)
  change (C ⊗ D).d (q + 1) q (ιTensorObj C D 0 (q + 1) (q + 1) _ _) =
    ιTensorObj C D 0 q q _ (TensorProduct.map LinearMap.id (D.d (q + 1) q).hom _) at h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using h

theorem tensorBoundary_interval_apply (q : ℕ) (x : C.X 1) (y : D.X (q + 1)) :
    (C ⊗ D).d (1 + (q + 1)) (0 + (q + 1))
      (ιTensorObj C D 1 (q + 1) (1 + (q + 1)) rfl (x ⊗ₜ[k] y)) =
      ιTensorObj C D 0 (q + 1) (0 + (q + 1)) rfl (C.d 1 0 x ⊗ₜ[k] y) -
      ιTensorObj C D 1 q (0 + (q + 1)) (by omega) (x ⊗ₜ[k] D.d (q + 1) q y) := by
  have hm := tensorBoundary_positive C D 0 q
  rw [pow_one, Units.smul_def] at hm
  change _ = _ + (-1 : ℤ) • _ at hm
  rw [neg_one_smul] at hm
  have h := ConcreteCategory.congr_hom hm (x ⊗ₜ[k] y)
  change (C ⊗ D).d (1 + (q + 1)) (0 + (q + 1))
      (ιTensorObj C D 1 (q + 1) (1 + (q + 1)) _ _) =
    ιTensorObj C D 0 (q + 1) (0 + (q + 1)) _
        (TensorProduct.map (C.d 1 0).hom LinearMap.id _) +
      -(ιTensorObj C D 1 q (0 + (q + 1)) _
        (TensorProduct.map LinearMap.id (D.d (q + 1) q).hom _)) at h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, sub_eq_add_neg] using h

theorem tensorBoundary_disk_apply (q : ℕ) (x : C.X 2) (y : D.X (q + 1)) :
    (C ⊗ D).d (2 + (q + 1)) (1 + (q + 1))
      (ιTensorObj C D 2 (q + 1) (2 + (q + 1)) rfl (x ⊗ₜ[k] y)) =
      ιTensorObj C D 1 (q + 1) (1 + (q + 1)) rfl (C.d 2 1 x ⊗ₜ[k] y) +
      ιTensorObj C D 2 q (1 + (q + 1)) (by omega) (x ⊗ₜ[k] D.d (q + 1) q y) := by
  have hm := tensorBoundary_positive C D 1 q
  norm_num only [neg_one_sq, one_smul] at hm
  have h := ConcreteCategory.congr_hom hm (x ⊗ₜ[k] y)
  change (C ⊗ D).d (2 + (q + 1)) (1 + (q + 1))
      (ιTensorObj C D 2 (q + 1) (2 + (q + 1)) _ _) =
    ιTensorObj C D 1 (q + 1) (1 + (q + 1)) _
        (TensorProduct.map (C.d 2 1).hom LinearMap.id _) +
      ιTensorObj C D 2 q (1 + (q + 1)) _
        (TensorProduct.map LinearMap.id (D.d (q + 1) q).hom _) at h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorBoundary
