import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Product Modules -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProductModules

noncomputable section

/-! A product of two flat modules is flat. -/

open TensorProduct

universe u v w

theorem flat_product_modules (R : Type u) [CommSemiring R]
    (M : Type v) (N : Type w) [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  apply Module.Flat.iff_rTensor_injectiveₛ.mpr
  intro P _ _ K
  let e := TensorProduct.prodRight R R K M N
  let d := TensorProduct.prodRight R R P M N
  have he : d.toLinearMap.comp (K.subtype.rTensor (M × N)) =
      ((K.subtype.rTensor M).prodMap (K.subtype.rTensor N)).comp e.toLinearMap := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro x
    rfl
  intro x y hxy
  have h := congrArg d hxy
  change (d.toLinearMap.comp (K.subtype.rTensor (M × N))) x =
    (d.toLinearMap.comp (K.subtype.rTensor (M × N))) y at h
  rw [he] at h
  apply e.injective
  apply Prod.ext
  · exact Module.Flat.rTensor_preserves_injective_linearMap
      K.subtype Subtype.val_injective (congrArg Prod.fst h)
  · exact Module.Flat.rTensor_preserves_injective_linearMap
      K.subtype Subtype.val_injective (congrArg Prod.snd h)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProductModules
