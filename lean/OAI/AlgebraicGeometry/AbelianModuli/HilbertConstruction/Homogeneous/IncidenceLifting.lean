import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceLifting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedQuotientIncidence

/-! # Incidence Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IncidenceLifting

noncomputable section

/-! Actual multiplication-compatible homogeneous quotients satisfy the global parameter equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (σ : Type v) [Finite σ] (d r s : ℕ)
variable {S : Scheme.{max u v}} {M : Over S}
variable (q : M ⟶ QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d r S)
variable (k : M ⟶ QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ (d + 1) s S)

theorem homogeneousIncidenceCondition_of_affine_relations
    (R : CommRingCat.{max u v}) (f : Spec R ⟶ S) (x : Over.mk f ⟶ M)
    (N : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) r)
    (K : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R (d + 1)) s)
    (hN : x ≫ q = QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d r R f N)
    (hK : x ≫ k = QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ (d + 1) s R f K)
    (i : σ) (h : N.toSubmodule ≤ K.toSubmodule.comap (MultiplicationMatrices.homogeneousMultiplyX R σ d i)) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k
      (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} Γ(M.left, ⊤) σ d i) x := by
  have hF : (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} Γ(M.left, ⊤) σ d i).map
      x.left.appTop.hom =
        (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} R σ d i).map
          (Scheme.ΓSpecIso R).inv.hom :=
    (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix_map _ σ d x.left.appTop.hom i).trans
      (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix_map R σ d (Scheme.ΓSpecIso R).inv.hom i).symm
  apply Affine.IncidenceLifting.grassmannIncidenceCondition_of_affine_relations q k _ R f x
    (QuotientClassification.homogeneousLiftedQuotient.{u, v} σ d r R N)
    (QuotientClassification.homogeneousLiftedQuotient.{u, v} σ (d + 1) s R K)
    (hN.trans (QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates σ d r R f N))
    (hK.trans (QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates σ (d + 1) s R f K))
    (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} R σ d i) hF
  rw [QuotientClassification.homogeneousLiftedQuotient_relations, QuotientClassification.homogeneousLiftedQuotient_relations]
  exact (LiftedQuotientIncidence.liftedHomogeneous_incidence_iff R σ d i N.toSubmodule K.toSubmodule).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IncidenceLifting
