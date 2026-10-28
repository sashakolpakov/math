import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Product Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductProjections

noncomputable section

/-! Projection formulas for an affine morphism into a fiber product described by a tensor product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] (φ : A ⊗[R] B →ₐ[R] C)

theorem affineProductComparison_fst :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso R A B).inv) ≫
      pullback.fst _ _ = Spec.map (CommRingCat.ofHom (φ.comp (Algebra.TensorProduct.includeLeft (S := R))).toRingHom) := by
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  rfl

theorem affineProductComparison_snd :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso R A B).inv) ≫
      pullback.snd _ _ = Spec.map (CommRingCat.ofHom (φ.comp Algebra.TensorProduct.includeRight).toRingHom) := by
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductProjections
