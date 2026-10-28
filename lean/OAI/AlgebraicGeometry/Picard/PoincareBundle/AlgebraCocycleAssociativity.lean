import OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocycleUniversalMaps

/-! # Algebra Cocycle Associativity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleAssociativity

noncomputable section

/-! The pointwise two-cocycle law implies the actual tensor coordinate cocycle identity. -/

universe u

open Coalgebra TensorProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle OAI.AlgebraicGeometry.Picard.PoincareBundle.CocyclePointEvaluation
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocycleUniversalMaps

variable (k R : Type u) [CommRing k] [CommRing R] [Bialgebra k R]
  (C : NaturalAlgebraCocycle.NaturalCocycle k R)

/-- Testing the cocycle law on the universal triple gives the tensor coalgebra cocycle identity. -/
theorem cocycle :
    TensorProduct.assoc k R R R
      (((NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) ⊗ₜ[k] (1 : R)) *
        (comul (R := k) (A := R)).rTensor R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R)) =
      ((1 : R) ⊗ₜ[k] (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R)) *
        (comul (R := k) (A := R)).lTensor R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) := by
  have h := C.cocycle (Affine.CocycleUniversalMaps.first k R) (Affine.CocycleUniversalMaps.middle k R) (Affine.CocycleUniversalMaps.last k R)
  rw [← NaturalAlgebraCocycle.evaluate_coordinate k R C, ← NaturalAlgebraCocycle.evaluate_coordinate k R C,
    ← NaturalAlgebraCocycle.evaluate_coordinate k R C, ← NaturalAlgebraCocycle.evaluate_coordinate k R C] at h
  rw [Affine.CocycleUniversalMaps.evaluate_product_last, Affine.CocycleUniversalMaps.evaluate_first_middle, Affine.CocycleUniversalMaps.evaluate_first_product, Affine.CocycleUniversalMaps.evaluate_middle_last] at h
  have hv := congrArg Units.val h
  change TensorProduct.assoc k R R R
      ((comul (R := k) (A := R)).rTensor R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R)) *
    TensorProduct.assoc k R R R ((NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) ⊗ₜ[k] (1 : R)) =
    (comul (R := k) (A := R)).lTensor R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) *
      ((1 : R) ⊗ₜ[k] (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R)) at hv
  rw [CoalgebraTensorMaps.assoc_mul]
  simpa only [mul_comm] using hv

/-- Every natural normalized symmetric regular cocycle yields the hypotheses of the finite splitting theorem. -/
theorem normalizedSymmetricCocycle :
    Symmetric.CocycleCoalgebra.IsNormalizedSymmetricCocycle k R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) where
  cocycle := AlgebraCocycleAssociativity.cocycle k R C
  counit_left := AlgebraCocycleNormalization.counit_left k R C
  counit_right := AlgebraCocycleNormalization.counit_right k R C
  symmetric := AlgebraCocycleNormalization.symmetric k R C

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleAssociativity
