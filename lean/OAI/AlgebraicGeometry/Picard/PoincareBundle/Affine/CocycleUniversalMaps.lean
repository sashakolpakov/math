import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle

/-! # Cocycle Universal Maps -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocycleUniversalMaps

noncomputable section

/-! The universal triple of affine points and its four pair maps. -/

universe u

open Coalgebra TensorProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation

variable (k R : Type u) [CommRing k] [CommRing R] [Bialgebra k R]

def first : R →ₐ[k] R ⊗[k] (R ⊗[k] R) := Algebra.TensorProduct.includeLeft

def middle : R →ₐ[k] R ⊗[k] (R ⊗[k] R) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft

def last : R →ₐ[k] R ⊗[k] (R ⊗[k] R) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight

def pair12 : R ⊗[k] R →ₐ[k] R ⊗[k] (R ⊗[k] R) :=
  (Algebra.TensorProduct.assoc k k k R R R).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : R ⊗[k] R →ₐ[k] (R ⊗[k] R) ⊗[k] R)

theorem evaluate_first_middle :
    CocyclePointEvaluation.evaluate k R (R ⊗[k] (R ⊗[k] R)) (first k R) (middle k R) = pair12 k R := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [CocyclePointEvaluation.evaluate, first, middle, pair12, Algebra.TensorProduct.one_def]

theorem evaluate_middle_last :
    CocyclePointEvaluation.evaluate k R (R ⊗[k] (R ⊗[k] R)) (middle k R) (last k R) =
      Algebra.TensorProduct.includeRight := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [CocyclePointEvaluation.evaluate, middle, last]

/-- Multiplying the first two universal points is comultiplication in the first coordinate. -/
theorem evaluate_product_last :
    CocyclePointEvaluation.evaluate k R (R ⊗[k] (R ⊗[k] R))
        (CocyclePointEvaluation.product k R (R ⊗[k] (R ⊗[k] R)) (first k R) (middle k R)) (last k R) =
      (Algebra.TensorProduct.assoc k k k R R R).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k R) (AlgHom.id k R)) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change CocyclePointEvaluation.evaluate k R (R ⊗[k] (R ⊗[k] R)) (first k R) (middle k R) (comul a) *
    last k R b = (Algebra.TensorProduct.assoc k k k R R R) (comul a ⊗ₜ[k] b)
  rw [evaluate_first_middle]
  change (Algebra.TensorProduct.assoc k k k R R R) (comul a ⊗ₜ[k] (1 : R)) *
      (Algebra.TensorProduct.assoc k k k R R R) ((1 : R ⊗[k] R) ⊗ₜ[k] b) = _
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Multiplying the last two universal points is comultiplication in the second coordinate. -/
theorem evaluate_first_product :
    CocyclePointEvaluation.evaluate k R (R ⊗[k] (R ⊗[k] R)) (first k R)
        (CocyclePointEvaluation.product k R (R ⊗[k] (R ⊗[k] R)) (middle k R) (last k R)) =
      Algebra.TensorProduct.map (AlgHom.id k R) (Bialgebra.comulAlgHom k R) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change first k R a *
    CocyclePointEvaluation.evaluate k R (R ⊗[k] (R ⊗[k] R)) (middle k R) (last k R) (comul b) = a ⊗ₜ[k] comul b
  rw [evaluate_middle_last]
  change (a ⊗ₜ[k] (1 : R ⊗[k] R)) * ((1 : R) ⊗ₜ[k] comul b) = a ⊗ₜ[k] comul b
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocycleUniversalMaps
