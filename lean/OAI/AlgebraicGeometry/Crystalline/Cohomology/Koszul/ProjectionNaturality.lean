import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy

/-! # Projection Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ProjectionNaturality.KoszulProjectionNaturality

noncomputable section

/-! # Naturality of the successive coefficient projections -/

universe u

variable (R σ M N : Type u) [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (D S : σ → Module.End R M) (E T : σ → Module.End R N) (f : M →ₗ[R] N)
  (hD : ∀ i a, f (D i a) = E i (f a)) (hS : ∀ i a, f (S i a) = T i (f a))

include hD hS in
theorem coordinate (i : σ) (a : M) :
    f (CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ M D i (S i) a) =
      CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ N E i (T i) (f a) := by
  change f (a - S i (D i a)) = f a - T i (E i (f a))
  rw [map_sub, hS, hD]

include hD hS in
theorem successive (l : List σ) (a : M) :
    f (SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ M D S l a) =
      SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ N E T l (f a) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    change f (SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ M D S l
      (CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ M D i (S i) a)) =
        SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ N E T l
          (CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ N E i (T i) (f a))
    rw [ih, coordinate R σ M N D S E T f hD hS]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ProjectionNaturality.KoszulProjectionNaturality
