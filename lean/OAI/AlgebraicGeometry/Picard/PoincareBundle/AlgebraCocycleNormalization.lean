import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle

/-! # Algebra Cocycle Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleNormalization

noncomputable section

/-! Naturality carries the cocycle unit and symmetry laws to its universal tensor coordinate. -/

universe u

open Coalgebra TensorProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle

variable (k R : Type u) [CommRing k] [CommRing R] [Bialgebra k R]
  (C : NaturalAlgebraCocycle.NaturalCocycle k R)

theorem counit_left :
    (counit (R := k) (A := R)).rTensor R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) = 1 := by
  let f := Algebra.TensorProduct.map (Bialgebra.counitAlgHom k R) (AlgHom.id k R)
  have h := C.natural f Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
  have hl : f.comp Algebra.TensorProduct.includeLeft =
      (Algebra.ofId k (k ⊗[k] R)).comp (Bialgebra.counitAlgHom k R) := by
    ext a
    simp [f]
  rw [hl, C.one_left] at h
  exact congrArg Units.val h

theorem counit_right :
    (counit (R := k) (A := R)).lTensor R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) = 1 := by
  let f := Algebra.TensorProduct.map (AlgHom.id k R) (Bialgebra.counitAlgHom k R)
  have h := C.natural f Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
  have hr : f.comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId k (R ⊗[k] k)).comp (Bialgebra.counitAlgHom k R) := by
    ext a
    simp [f, Algebra.TensorProduct.algebraMap_def]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [hr, C.one_right] at h
  exact congrArg Units.val h

theorem symmetric :
    TensorProduct.comm k R R (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) = (NaturalAlgebraCocycle.coordinate k R C : R ⊗[k] R) := by
  let f := (Algebra.TensorProduct.comm k R R).toAlgHom
  have h := C.natural f Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
  have hl : f.comp Algebra.TensorProduct.includeLeft = Algebra.TensorProduct.includeRight := by
    ext a
    rfl
  have hr : f.comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeLeft := by
    ext a
    rfl
  rw [hl, hr] at h
  exact congrArg Units.val (h.trans (C.symmetric _ _))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AlgebraCocycleNormalization
