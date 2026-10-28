import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Extension Twist -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTwist

noncomputable section

/-!
# Changing the coefficient ring in scalar extension for PoincareBundle

This keeps the actual extension-of-scalars objects and tracks the
semilinear action of a coefficient-ring isomorphism.
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

variable {S U V : Type u} [CommRing S] [CommRing U] [CommRing V]
  (f : S →+* U) (g : S →+* V) (e : U ≃+* V) (h : ∀ s, e (f s) = g s)

/-- A coefficient isomorphism intertwining the two scalar structures. -/
def coefficientEquiv :
    (restrictScalars f).obj (of U U) ≃ₗ[S] (restrictScalars g).obj (of V V) where
  __ := e.toAddEquiv
  map_smul' s x := by
    change e (f s * (show U from x)) = g s * e (show U from x)
    rw [map_mul, h]

/-- The induced additive equivalence on the actual scalar extensions. -/
def extensionEquiv (M : ModuleCat.{u} S) :
    (extendScalars f).obj M ≃+ (extendScalars g).obj M :=
  (TensorProduct.congr (coefficientEquiv f g e h) (LinearEquiv.refl S M)).toAddEquiv

@[simp]
theorem extensionEquiv_tmul (M : ModuleCat.{u} S) (x : U) (m : M) :
    extensionEquiv f g e h M (x ⊗ₜ[S,f] m) = e x ⊗ₜ[S,g] m := rfl

/-- The induced equivalence is semilinear for the coefficient isomorphism. -/
theorem extensionEquiv_smul (M : ModuleCat.{u} S) (x : U)
    (z : (extendScalars f).obj M) :
    extensionEquiv f g e h M (x • z) = e x • extensionEquiv f g e h M z := by
  let : Module U ((extendScalars f).obj M) := ((extendScalars f).obj M).isModule
  let : Module V ((extendScalars g).obj M) := ((extendScalars g).obj M).isModule
  have hz : x • (0 : (extendScalars f).obj M) = 0 := smul_zero x
  have hz' : e x • (0 : (extendScalars g).obj M) = 0 := smul_zero (e x)
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => erw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul y m =>
      change extensionEquiv f g e h M ((x * (show U from y)) ⊗ₜ[S,f] m) =
        (e x * e (show U from y)) ⊗ₜ[S,g] m
      rw [extensionEquiv_tmul, map_mul]

/-- Changing coefficients commutes with every original-module morphism. -/
theorem extensionEquiv_naturality {M N : ModuleCat.{u} S} (a : M ⟶ N)
    (z : (extendScalars f).obj M) :
    extensionEquiv f g e h N ((extendScalars f).map a z) =
      (extendScalars g).map a (extensionEquiv f g e h M z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => erw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul x m => rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTwist
