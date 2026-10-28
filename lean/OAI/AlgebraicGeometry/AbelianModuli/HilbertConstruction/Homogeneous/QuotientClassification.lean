import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientParameters

/-! # Quotient Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientClassification

noncomputable section

/-! Explicit coordinate quotients underlying homogeneous Grassmannian parameter maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def grassmannRankCast {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V]
    {k l : ℕ} (h : k = l) (N : Module.Grassmannian A V k) : Module.Grassmannian A V l where
  toSubmodule := N.toSubmodule
  finite_quotient := N.finite_quotient
  projective_quotient := N.projective_quotient
  rankAtStalk_eq p := (N.rankAtStalk_eq p).trans h

theorem grassmannEquiv_rankCast_apply {A V H : Type*}
    [CommRing A] [AddCommGroup V] [Module A V] {k l : ℕ} (h : k = l)
    (e : Module.Grassmannian A V k ≃ H) (N : Module.Grassmannian A V l) :
    (cast (congrArg (fun t => Module.Grassmannian A V t ≃ H) h) e) N =
      e (grassmannRankCast h.symm N) := by
  subst l
  rfl

variable (σ : Type v) [Finite σ] (d r : ℕ) (R : CommRingCat.{max u v})

def homogeneousLiftedQuotient
    (N : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) r) :
    Module.Grassmannian R (ULift.{u} (Coordinates.HomogeneousMonomials σ d) → R)
      (Fintype.card (ULift.{max u v} (Fin r))) :=
  Grassmann.LinearCoordinates.grassmannLinearTransport (QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R)
    (grassmannRankCast (by simp only [Fintype.card_ulift, Fintype.card_fin]) N)

theorem homogeneousLiftedQuotient_relations
    (N : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) r) :
    (homogeneousLiftedQuotient.{u, v} σ d r R N).toSubmodule =
      N.toSubmodule.map (QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R).toLinearMap := rfl

theorem homogeneousQuotientAffinePointEquiv_coordinates {S : Scheme.{max u v}} (f : Spec R ⟶ S)
    (N : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) r) :
    QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d r R f N =
      Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f (homogeneousLiftedQuotient.{u, v} σ d r R N) := by
  exact grassmannEquiv_rankCast_apply
    (by simp only [Fintype.card_ulift, Fintype.card_fin] :
      Fintype.card (ULift.{max u v} (Fin r)) = r)
    (Grassmann.LinearCoordinates.grassmannCoordinateAffinePointEquiv (ι := ULift.{max u v} (Fin r)) R f
      (QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R)) N

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientClassification
