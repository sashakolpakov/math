import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates

/-! # Tensor Coordinate Naturality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.TensorCoordinateNaturality

/-! # A coefficient map commutes with each finite tensor coordinate -/

open scoped TensorProduct

variable {R M N E K : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
  [Module R M] [Module R N] [Module R E] [Fintype K] [DecidableEq K]

theorem coordinate_map (b : Module.Basis K R E) (f : M →ₗ[R] N) (x : M ⊗[R] E) (k : K) :
    FiniteTensorCoordinates.coordinates b (TensorProduct.map f LinearMap.id x) k =
      f (FiniteTensorCoordinates.coordinates b x k) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, FiniteTensorCoordinates.coordinates_tmul, map_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end OAI.NumberTheory.PadicHodge.PeriodInvariants.TensorCoordinateNaturality
