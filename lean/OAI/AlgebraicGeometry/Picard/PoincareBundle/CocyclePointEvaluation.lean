import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.SymmetricCocycle

/-! # Cocycle Point Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation

noncomputable section

/-! A unit solving the tensor cocycle equation solves it on every algebra-valued point. -/

universe u v w

open Coalgebra TensorProduct

variable (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Bialgebra k R]
  (S : Type w) [CommRing S] [Algebra k S]

/-- Evaluation on a pair of points is the ordinary universal tensor algebra map. -/
def evaluate (x y : R →ₐ[k] S) : R ⊗[k] R →ₐ[k] S :=
  Algebra.TensorProduct.lift x y (fun _ _ ↦ Commute.all _ _)

/-- The affine-coordinate group multiplication. -/
def product (x y : R →ₐ[k] S) : R →ₐ[k] S :=
  (evaluate k R S x y).comp (Bialgebra.comulAlgHom k R)

theorem solution_at_points (c : (R ⊗[k] R)ˣ) (a : Rˣ)
    (hΔ : (c : R ⊗[k] R) * comul (a : R) = (a : R) ⊗ₜ[k] (a : R))
    (x y : R →ₐ[k] S) :
    Units.map (evaluate k R S x y).toMonoidHom c * Units.map (product k R S x y).toMonoidHom a =
      Units.map x.toMonoidHom a * Units.map y.toMonoidHom a := by
  apply Units.ext
  exact ((evaluate k R S x y).map_mul (c : R ⊗[k] R) (comul (a : R))).symm.trans
    (congrArg (evaluate k R S x y) hΔ)

/-- Evaluation of the splitting unit commutes with every change of test algebra. -/
theorem solution_natural (a : Rˣ) (x : R →ₐ[k] S)
    {T : Type*} [CommRing T] [Algebra k T] (f : S →ₐ[k] T) :
    Units.map f.toMonoidHom (Units.map x.toMonoidHom a) = Units.map (f.comp x).toMonoidHom a := by
  apply Units.ext
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation
