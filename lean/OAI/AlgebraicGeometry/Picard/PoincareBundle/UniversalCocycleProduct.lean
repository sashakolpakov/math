import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocyclePoints

/-! # Universal Cocycle Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.UniversalCocycleProduct

noncomputable section

/-! The two universal affine points identify the tensor spectrum with the actual product scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocyclePoints

variable (k R : Type u) [CommRing k] [CommRing R] [Bialgebra k R]

/-- The actual pair of universal algebra points. -/
def universalPair : (Spec (.of (R ⊗[k] R))).asOver (Spec (.of k)) ⟶
    ((Spec (.of R)).asOver (Spec (.of k))) ⊗ ((Spec (.of R)).asOver (Spec (.of k))) :=
  lift (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeLeft)
    (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeRight)

/-- This pair map is the inverse of the actual fiber-product coordinate isomorphism. -/
theorem universalPair_left : (universalPair k R).left = (pullbackSpecIso k R R).inv := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · exact (congrArg Over.Hom.left
      (lift_fst (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeLeft)
        (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeRight))).trans
      (pullbackSpecIso_inv_fst k R R).symm
  · exact (congrArg Over.Hom.left
      (lift_snd (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeLeft)
        (Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeRight))).trans
      (pullbackSpecIso_inv_snd k R R).symm

theorem universalPair_fst :
    universalPair k R ≫ fst ((Spec (.of R)).asOver (Spec (.of k)))
      ((Spec (.of R)).asOver (Spec (.of k))) =
      Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeLeft := lift_fst _ _

theorem universalPair_snd :
    universalPair k R ≫ snd ((Spec (.of R)).asOver (Spec (.of k)))
      ((Spec (.of R)).asOver (Spec (.of k))) =
      Affine.CocyclePoints.point k R (R ⊗[k] R) Algebra.TensorProduct.includeRight := lift_snd _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.UniversalCocycleProduct
