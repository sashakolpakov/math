import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.LinearCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Coordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation

/-! # Quotient Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientParameters

noncomputable section

/-!
An actual projective parameter scheme for fixed-rank quotients of each
homogeneous polynomial degree, with classification over affine tests.
No Hilbert-family flatness or representability theorem is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (σ : Type v) [Finite σ] (d r : ℕ)

def homogeneousLiftedCoordinates (A : Type (max u v)) [CommRing A] :
    MvPolynomial.homogeneousSubmodule σ A d ≃ₗ[A]
      (ULift.{u} (Coordinates.HomogeneousMonomials σ d) → A) :=
  (Coordinates.homogeneousCoordinates A σ d).trans (LinearEquiv.funCongrLeft A A Equiv.ulift)

def homogeneousQuotientParameterScheme (S : Scheme.{max u v}) : Over S :=
  Grassmann.ParameterScheme.grassmannParameterScheme (ι := ULift.{max u v} (Fin r))
    (ν := ULift.{u} (Coordinates.HomogeneousMonomials σ d)) S

def homogeneousQuotientAffinePointEquiv {S : Scheme.{max u v}}
    (A : CommRingCat.{max u v}) (f : Spec A ⟶ S) :
    Module.Grassmannian A (MvPolynomial.homogeneousSubmodule σ A d) r ≃
      (Over.mk f ⟶ homogeneousQuotientParameterScheme σ d r S) := by
  have e := Grassmann.LinearCoordinates.grassmannCoordinateAffinePointEquiv (ι := ULift.{max u v} (Fin r))
    (ν := ULift.{u} (Coordinates.HomogeneousMonomials σ d)) A f (homogeneousLiftedCoordinates σ d A)
  simp only [Fintype.card_ulift, Fintype.card_fin] at e
  exact e

def homogeneousQuotientProjectivePresentation [Nonempty σ] (S : Scheme.{max u v}) :
    Projective.ProjectivePresentations.ProjectivePresentation (homogeneousQuotientParameterScheme σ d r S) :=
  Grassmann.ProjectivePresentation.grassmannProjectivePresentation (ι := ULift.{max u v} (Fin r))
    (ν := ULift.{u} (Coordinates.HomogeneousMonomials σ d)) S

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientParameters
