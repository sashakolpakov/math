import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedHomogeneousMatrices
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedQuotientFamilies

/-! # Lifted Quotient Incidence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual homogeneous quotient relations satisfy the lifted parameter-scheme matrices. -/

universe u v

variable (R : Type (max u v)) [CommRing R] (σ : Type v) [Finite σ] (d : ℕ)

theorem LiftedQuotientIncidence.liftedHomogeneous_incidence_iff (i : σ)
    (N : Submodule R (MvPolynomial.homogeneousSubmodule σ R d))
    (K : Submodule R (MvPolynomial.homogeneousSubmodule σ R (d + 1))) :
    N.map (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R).toLinearMap ≤
      (K.map (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ (d + 1) R).toLinearMap).comap
        (Matrix.toLin' (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} R σ d i)) ↔
          N ≤ K.comap (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i) :=
  Homogeneous.IdealIncidence.coordinate_submodule_incidence_iff (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates σ d R)
    (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates σ (d + 1) R) (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)
    (Matrix.toLin' (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix R σ d i))
    (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix_represents R σ d i) N K

theorem GradedQuotientFamilies.GradedQuotientData.lifted_incidence {r : ℕ → ℕ}
    (D : GradedQuotientFamilies.GradedQuotientData R σ r) (i : σ) :
    (D.quotient d).toSubmodule.map (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R).toLinearMap ≤
      ((D.quotient (d + 1)).toSubmodule.map
        (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ (d + 1) R).toLinearMap).comap
          (Matrix.toLin' (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} R σ d i)) :=
  (LiftedQuotientIncidence.liftedHomogeneous_incidence_iff R σ d i _ _).mpr (D.variable_mul d i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
