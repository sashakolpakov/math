import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct

/-! # Pairing Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PairingValues

/-! Pointwise evaluation of a pairing restricted to the first product factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct

variable {S : Scheme.{u}} {K D : Over S} [GrpObj K] [GrpObj D]
  (e : ∀ T : Over S, (T ⟶ K ⊗ D) →* (T ⟶ K ⊗ D) →* Γ(T.left, ⊤)ˣ)

/-- The first-factor pairing uses the two original product inclusions. -/
theorem firstPairing_apply {T : Over S} (x y : T ⟶ K) :
    CoprimeOrthogonalProduct.firstPairing e T x y = e T (x ≫ CoprimeOrthogonalProduct.first) (y ≫ CoprimeOrthogonalProduct.first) := rfl

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PairingValues
