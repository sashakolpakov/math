import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedHomogeneousMatrices
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IdealIncidence

/-! # Lifted Generation Conditions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedGenerationConditions

noncomputable section

/-! Equality between relation modules and generated images is detected exactly in lifted monomial coordinates. -/

universe u v

variable (R : Type (max u v)) [CommRing R] (σ : Type v) [Finite σ] (d : ℕ)

theorem liftedHomogeneous_linearImage (i : σ)
    (N : Submodule R (MvPolynomial.homogeneousSubmodule σ R d)) :
    (N.map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)).map
      (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ (d + 1) R).toLinearMap =
        (N.map (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R).toLinearMap).map
          (Matrix.toLin' (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} R σ d i)) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  apply congrArg (fun f => N.map f)
  apply LinearMap.ext
  intro p
  exact (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix_represents R σ d i p).symm

theorem liftedHomogeneous_generation_iff
    (N : Submodule R (MvPolynomial.homogeneousSubmodule σ R d))
    (K : Submodule R (MvPolynomial.homogeneousSubmodule σ R (d + 1))) :
    K = ⨆ i : σ, N.map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i) ↔
      K.map (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ (d + 1) R).toLinearMap =
        ⨆ i : σ, (N.map (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R).toLinearMap).map
          (Matrix.toLin' (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} R σ d i)) := by
  have he : (⨆ i : σ, N.map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)).map
      (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ (d + 1) R).toLinearMap =
        ⨆ i : σ, (N.map (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R).toLinearMap).map
          (Matrix.toLin' (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} R σ d i)) := by
    rw [Submodule.map_iSup]
    exact congrArg iSup (funext (fun i => liftedHomogeneous_linearImage R σ d i N))
  constructor
  · intro h
    rw [h]
    exact he
  · intro h
    apply Submodule.map_injective_of_injective
      (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ (d + 1) R).injective
    exact h.trans he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedGenerationConditions
