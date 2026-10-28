import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation

/-! # Natural Algebra Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle

noncomputable section

/-! Natural regular two-cocycles on the functor of points of an affine group. -/

universe u

open TensorProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation

variable (k R : Type u) [CommRing k] [CommRing R] [Bialgebra k R]

/-- The ordinary naturality, associativity, symmetry, and normalization laws of a unit cocycle. -/
structure NaturalCocycle where
  value {S : Type u} [CommRing S] [Algebra k S] (x y : R →ₐ[k] S) : Sˣ
  natural {S T : Type u} [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    (f : S →ₐ[k] T) (x y : R →ₐ[k] S) :
    Units.map f.toMonoidHom (value x y) = value (f.comp x) (f.comp y)
  one_left {S : Type u} [CommRing S] [Algebra k S] (x : R →ₐ[k] S) :
    value ((Algebra.ofId k S).comp (Bialgebra.counitAlgHom k R)) x = 1
  one_right {S : Type u} [CommRing S] [Algebra k S] (x : R →ₐ[k] S) :
    value x ((Algebra.ofId k S).comp (Bialgebra.counitAlgHom k R)) = 1
  symmetric {S : Type u} [CommRing S] [Algebra k S] (x y : R →ₐ[k] S) : value x y = value y x
  cocycle {S : Type u} [CommRing S] [Algebra k S] (x y z : R →ₐ[k] S) :
    value (CocyclePointEvaluation.product k R S x y) z * value x y = value x (CocyclePointEvaluation.product k R S y z) * value y z

variable (C : NaturalCocycle k R)

/-- The coefficient at the two universal points is an actual tensor coordinate. -/
def coordinate : (R ⊗[k] R)ˣ := C.value Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight

/-- Universal tensor evaluation recovers the natural cocycle at every pair of algebra points. -/
theorem evaluate_coordinate {S : Type u} [CommRing S] [Algebra k S] (x y : R →ₐ[k] S) :
    Units.map (CocyclePointEvaluation.evaluate k R S x y).toMonoidHom (coordinate k R C) = C.value x y := by
  have h := C.natural (CocyclePointEvaluation.evaluate k R S x y)
    Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
  have hl : (CocyclePointEvaluation.evaluate k R S x y).comp Algebra.TensorProduct.includeLeft = x := by
    ext a
    simp [CocyclePointEvaluation.evaluate]
  have hr : (CocyclePointEvaluation.evaluate k R S x y).comp Algebra.TensorProduct.includeRight = y := by
    ext a
    simp [CocyclePointEvaluation.evaluate]
  rw [hl, hr] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle
