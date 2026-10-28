import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Module Base Change Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeCoordinates

noncomputable section

/-!
# Coordinates of the inverse canonical module base-change map
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (M : ModuleCat.{u} A)

/-- The inverse canonical base-change map moves the original scalar onto the module. -/
theorem objectIso_inv_tmul (a : A) (b : B) (m : M) :
    (ModuleBaseChangeFunctor.objectIso R A B M).inv
        ((a ⊗ₜ[R] b) ⊗ₜ[A,algebraMap A (A ⊗[R] B)] m) =
      b ⊗ₜ[R,algebraMap R B]
        (a • (show (restrictScalars (algebraMap R A)).obj M from m)) := by
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeCoordinates
