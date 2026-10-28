import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Extension Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionComposition

noncomputable section

/-!
# Pure tensor formulas for canonical composition of scalar extensions
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T) (M : ModuleCat.{u} R)

/-- The canonical composition comparison inserts a unit in the intermediate scalar ring. -/
theorem composition_hom_tmul (t : T) (m : M) :
    (extendScalarsComp f g).hom.app M (t ⊗ₜ[R,g.comp f] m) =
      t ⊗ₜ[S,g] (show (extendScalars f).obj M from (1 : S) ⊗ₜ[R,f] m) := by
  have h := extendScalarsComp_hom_app_one_tmul f g M m
  have hs := ((extendScalarsComp f g).hom.app M).hom.map_smul t
    ((1 : T) ⊗ₜ[R,g.comp f] m)
  erw [ExtendScalars.smul_tmul, mul_one] at hs
  erw [hs, h, ExtendScalars.smul_tmul, mul_one]
  rfl

/-- Moving an intermediate scalar outwards in an iterated extension. -/
theorem iterated_tmul (t : T) (s : S) (m : M) :
    (t ⊗ₜ[S,g] (show (extendScalars f).obj M from s ⊗ₜ[R,f] m) :
        (extendScalars g).obj ((extendScalars f).obj M)) =
      (g s * t) ⊗ₜ[S,g] (show (extendScalars f).obj M from (1 : S) ⊗ₜ[R,f] m) := by
  have hm := (ModuleCat.ExtendScalars.smul_tmul f s 1 m).symm
  simp only [mul_one] at hm
  erw [hm]
  exact TensorProduct.tmul_smul (R := S) s
    (show (restrictScalars g).obj (of T T) from t)
    (show (extendScalars f).obj M from (1 : S) ⊗ₜ[R,f] m)

/-- The inverse canonical comparison multiplies the two scalar coefficients. -/
theorem composition_inv_tmul (t : T) (s : S) (m : M) :
    (extendScalarsComp f g).inv.app M
        (t ⊗ₜ[S,g] (show (extendScalars f).obj M from s ⊗ₜ[R,f] m)) =
      (g s * t) ⊗ₜ[R,g.comp f] m := by
  apply ((extendScalarsComp f g).app M).toLinearEquiv.injective
  change ((extendScalarsComp f g).app M).hom
      (((extendScalarsComp f g).app M).inv
        (t ⊗ₜ[S,g] (show (extendScalars f).obj M from s ⊗ₜ[R,f] m))) = _
  erw [Iso.inv_hom_id_apply, composition_hom_tmul]
  exact iterated_tmul f g M t s m

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionComposition
