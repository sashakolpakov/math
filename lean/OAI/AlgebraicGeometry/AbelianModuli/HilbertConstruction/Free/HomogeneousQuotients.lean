import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Coordinates
import Mathlib.RingTheory.Grassmannian

/-! # Homogeneous Quotients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Free.HomogeneousQuotients

noncomputable section

/-! The full homogeneous degree module as a fixed-rank Grassmannian quotient with zero relations. -/

universe u v

variable (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (d : ℕ)

def freeHomogeneousQuotient :
    Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d)
      (Fintype.card (Homogeneous.Coordinates.HomogeneousMonomials σ d)) := by
  let e := (Submodule.quotEquivOfEqBot
    (⊥ : Submodule R (MvPolynomial.homogeneousSubmodule σ R d)) rfl).trans
      (Homogeneous.Coordinates.homogeneousCoordinates R σ d)
  exact
    { toSubmodule := ⊥
      finite_quotient := Module.Finite.equiv e.symm
      projective_quotient := Module.Projective.of_equiv e.symm
      rankAtStalk_eq p := by
        have : Nontrivial R := p.nontrivial
        exact (congrFun (Module.rankAtStalk_eq_of_equiv e) p).trans (by simp) }

theorem freeHomogeneousQuotient_relations : (freeHomogeneousQuotient R σ d).toSubmodule = ⊥ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Free.HomogeneousQuotients
